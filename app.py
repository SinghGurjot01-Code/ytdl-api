#!/usr/bin/env python3
from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
import yt_dlp
import os
import tempfile
import threading
import uuid
import subprocess
import shutil
import time
import logging
import random
from pathlib import Path
from datetime import datetime, timedelta
from PIL import Image, ImageDraw, ImageFont, ImageFilter
import io
import base64

# ------------------ CONFIG ------------------
YTDL_COOKIES_PATH = os.environ.get('YTDL_COOKIES_PATH')  # Path to cookies.txt

app = Flask(__name__)
CORS(app)  # Enable CORS for all routes

# ------------------ LOGGING ------------------
LOG_FILE_PATH = 'logs/ytdl.log'
LOG_CLEAR_INTERVAL = 10 * 60  # every 10 minutes

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(LOG_FILE_PATH, encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

def auto_clear_log():
    while True:
        try:
            if os.path.exists(LOG_FILE_PATH):
                with open(LOG_FILE_PATH, 'w', encoding='utf-8') as f:
                    f.truncate(0)
                logger.info("Auto-cleared ytdl.log file to prevent bloat")
        except Exception as e:
            logger.error("Error clearing log file: %s", e)
        time.sleep(LOG_CLEAR_INTERVAL)

threading.Thread(target=auto_clear_log, daemon=True).start()

# ------------------ GLOBAL STATE ------------------
download_status = {}
captcha_store = {}
verified_sessions = {}

# ------------------ HELPERS ------------------
class DownloadProgress:
    def __init__(self):
        self.status = 'queued'
        self.progress = 0.0
        self.filename = ''
        self.error = ''
        self.temp_dir = ''
        self.ffmpeg_available = False
        self.title = ''
        self.completed = False
        self.downloaded_bytes = 0
        self.total_bytes = 0
        self.speed = 0
        self.eta = 0

def safe_get_job(job_id):
    return download_status.get(job_id)

def check_ffmpeg():
    try:
        result = subprocess.run(['ffmpeg', '-version'], capture_output=True, text=True, timeout=10)
        return result.returncode == 0
    except Exception:
        return False

def bytes_to_mb(bytes_value):
    try:
        return round(bytes_value / (1024 * 1024), 2)
    except Exception:
        return 0

def format_duration(seconds):
    try:
        seconds = int(seconds)
    except Exception:
        return "00:00"
    if seconds <= 0:
        return "00:00"
    minutes, seconds = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    if hours > 0:
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"
    return f"{minutes:02d}:{seconds:02d}"

def format_eta(eta_seconds):
    try:
        eta_seconds = int(eta_seconds)
        if eta_seconds <= 0:
            return "00:00"
        minutes = eta_seconds // 60
        seconds = eta_seconds % 60
        return f"{minutes:02d}:{seconds:02d}"
    except Exception:
        return "00:00"

def progress_hook_factory(job_id):
    def hook(d):
        job = safe_get_job(job_id)
        if job is None or job.completed:
            return

        status = d.get('status')
        if status == 'downloading':
            job.status = 'downloading'
            p = d.get('_percent_str') or d.get('percent')
            if p:
                try:
                    if isinstance(p, str):
                        p = p.strip().strip('%')
                    job.progress = min(float(p), 99.9)
                except Exception:
                    pass
            elif d.get('total_bytes') and d.get('downloaded_bytes'):
                try:
                    total = d.get('total_bytes') or d.get('total_bytes_estimate', 0)
                    downloaded = d.get('downloaded_bytes', 0)
                    if total > 0:
                        job.progress = min((downloaded / total) * 100, 99.9)
                except Exception:
                    pass

            job.downloaded_bytes = d.get('downloaded_bytes', 0)
            job.total_bytes = d.get('total_bytes') or d.get('total_bytes_estimate', 0)
            job.speed = d.get('speed', 0)
            job.eta = d.get('eta', 0)

        elif status == 'finished':
            if not job.completed:
                job.progress = 99.9
                job.downloaded_bytes = job.total_bytes
                job.speed = 0
                job.eta = 0
            if 'filename' in d:
                try:
                    job.filename = os.path.abspath(d['filename'])
                except Exception:
                    job.filename = d['filename']
            logger.info("Progress hook finished for job %s: %s", job_id, d.get('filename', ''))

        elif status == 'error':
            if not job.completed:
                job.status = 'error'
                job.error = d.get('error', 'Unknown error reported by yt-dlp')
                logger.error("Progress hook error for job %s: %s", job_id, job.error)

    return hook

def get_ytdlp_opts_with_retry(temp_dir, job_id, format_str, file_ext, ffmpeg_available):
    base_opts = {
        'outtmpl': os.path.join(temp_dir, '%(title)s.%(ext)s'),
        'progress_hooks': [progress_hook_factory(job_id)],
        'restrictfilenames': False,
        'quiet': True,
        'no_warnings': True,
        'nopart': False,
        'noplaylist': True,
        'extractor_retries': 3,
        'retries': 10,
        'fragment_retries': 10,
        'skip_unavailable_fragments': True,
        'continuedl': True,
        'http_headers': {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
        },
    }

    # Cookie handling: file preferred, fallback to browser
    if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
        base_opts['cookiefile'] = YTDL_COOKIES_PATH
    else:
        base_opts['cookiesfrombrowser'] = ('chrome',)

    # Format handling
    if file_ext == 'mp3' and ffmpeg_available:
        base_opts.update({
            'format': 'bestaudio/best',
            'postprocessors': [{
                'key': 'FFmpegExtractAudio',
                'preferredcodec': file_ext,
                'preferredquality': '192',
            }],
        })
    else:
        base_opts['format'] = format_str

    return base_opts

def find_final_file_in_dir(temp_dir, title_hint=None):
    if not temp_dir or not os.path.isdir(temp_dir):
        return None
    try:
        files = [os.path.join(temp_dir, f) for f in os.listdir(temp_dir) if os.path.isfile(os.path.join(temp_dir, f))]
    except Exception as e:
        logger.error("Error listing temp_dir %s: %s", temp_dir, e)
        return None
    files = [f for f in files if not f.endswith('.part')]
    if not files:
        return None
    if title_hint:
        normalized = title_hint.replace('/', '_').strip()
        matches = [f for f in files if os.path.basename(f).startswith(normalized)]
        if matches:
            matches.sort(key=lambda p: os.path.getsize(p) if os.path.exists(p) else 0, reverse=True)
            return matches[0]
    files.sort(key=lambda p: os.path.getsize(p) if os.path.exists(p) else 0, reverse=True)
    return files[0]

# ------------------ DOWNLOAD WORKER ------------------
def download_worker(url, format_str, file_ext, job_id):
    job = safe_get_job(job_id)
    if job is None:
        logger.error("Download worker called with missing job_id: %s", job_id)
        return

    temp_dir = tempfile.mkdtemp(prefix='ytdl_')
    job.temp_dir = temp_dir
    job.ffmpeg_available = check_ffmpeg()
    job.status = 'downloading'
    job.progress = 0
    job.downloaded_bytes = 0
    job.total_bytes = 0

    max_retries = 3
    retry_count = 0

    while retry_count < max_retries:
        try:
            ydl_opts = get_ytdlp_opts_with_retry(temp_dir, job_id, format_str, file_ext, job.ffmpeg_available)
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=True)
                if isinstance(info, dict) and info.get('title'):
                    job.title = info.get('title')

                final = None
                if job.filename and os.path.exists(job.filename):
                    final = job.filename
                if not final and isinstance(info, dict):
                    candidate = ydl.prepare_filename(info)
                    if os.path.exists(candidate):
                        final = candidate
                if not final:
                    candidate = find_final_file_in_dir(temp_dir, title_hint=job.title)
                    if candidate:
                        final = candidate

                if final:
                    final = os.path.abspath(final)
                    job.filename = final
                    job.status = 'completed'
                    job.progress = 100.0
                    job.completed = True
                    file_size = os.path.getsize(final)
                    job.downloaded_bytes = file_size
                    job.total_bytes = file_size
                    if file_size < 100:
                        job.status = 'error'
                        job.error = 'Downloaded file too small or corrupted'
                    logger.info("Job %s - download completed: %s", job_id, final)
                    break
                else:
                    job.status = 'error'
                    job.error = 'Could not determine final output filename'
                    job.completed = True
                    break

        except yt_dlp.utils.DownloadError as e:
            error_msg = str(e)
            logger.warning("Job %s - DownloadError: %s", job_id, error_msg)
            if "Sign in to confirm" in error_msg or "Private video" in error_msg:
                job.status = 'error'
                job.error = 'Video requires login/cookies or is private'
                job.completed = True
                break
            retry_count += 1
            time.sleep(2)
        except Exception as e:
            logger.exception("Job %s - unexpected exception: %s", job_id, e)
            retry_count += 1
            time.sleep(2)
            if retry_count >= max_retries:
                job.status = 'error'
                job.error = str(e)
                job.completed = True
                break

# ------------------ API ENDPOINTS ------------------
@app.route('/api/video-info', methods=['POST'])
def get_video_info():
    data = request.get_json() or {}
    url = data.get('url')
    if not url:
        return jsonify({'error': 'URL required'}), 400
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'skip_download': True,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0',
            }
        }
        if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
            ydl_opts['cookiefile'] = YTDL_COOKIES_PATH
        else:
            ydl_opts['cookiesfrombrowser'] = ('chrome',)

        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            formats = []
            for f in info.get('formats', []) if isinstance(info, dict) else []:
                if f.get('format_id'):
                    formats.append({
                        'format_id': f.get('format_id'),
                        'ext': f.get('ext', ''),
                        'resolution': f.get('format_note') or f.get('resolution') or f.get('height'),
                        'filesize': f.get('filesize') or f.get('filesize_approx'),
                        'vcodec': f.get('vcodec', 'none'),
                        'acodec': f.get('acodec', 'none'),
                    })
            return jsonify({
                'title': info.get('title', 'Unknown'),
                'duration': format_duration(info.get('duration', 0)),
                'thumbnail': info.get('thumbnail', ''),
                'channel': info.get('uploader', 'Unknown'),
                'view_count': info.get('view_count', 0),
                'formats': formats
            })
    except Exception as e:
        logger.exception("Error fetching video info: %s", e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/download', methods=['POST'])
def download_video():
    data = request.get_json() or {}
    url = data.get('url')
    format_str = data.get('format')
    file_ext = data.get('file_ext', 'mp4')
    session_token = data.get('session_token')

    if not url or not format_str:
        return jsonify({'error': 'URL and format required'}), 400
    if not session_token or session_token not in verified_sessions:
        return jsonify({'error': 'CAPTCHA verification required'}, 403)

    session_data = verified_sessions.pop(session_token)
    if datetime.now() > session_data['expires']:
        return jsonify({'error': 'CAPTCHA session expired'}, 403)

    job_id = str(uuid.uuid4())
    download_status[job_id] = DownloadProgress()
    download_status[job_id].ffmpeg_available = check_ffmpeg()

    threading.Thread(target=download_worker, args=(url, format_str, file_ext, job_id), daemon=True).start()

    return jsonify({'job_id': job_id, 'ffmpeg_available': download_status[job_id].ffmpeg_available})

@app.route('/api/download-status/<job_id>')
def get_download_status(job_id):
    job = safe_get_job(job_id)
    if not job:
        return jsonify({'error': 'Invalid job ID'}), 404
    return jsonify({
        'status': job.status,
        'progress': round(job.progress, 2),
        'downloaded_mb': bytes_to_mb(job.downloaded_bytes),
        'total_mb': bytes_to_mb(job.total_bytes),
        'speed': bytes_to_mb(job.speed),
        'eta': format_eta(job.eta),
        'filename': os.path.basename(job.filename) if job.filename else ''
    })

# ------------------ RUN SERVER ------------------
if __name__ == '__main__':
    os.makedirs('logs', exist_ok=True)
    app.run(host='0.0.0.0', port=5000, debug=True)
