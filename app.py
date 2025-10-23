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
import urllib.parse

app = Flask(__name__)
CORS(app)  # Enable CORS for all routes

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('logs/ytdl.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

LOG_FILE_PATH = 'logs/ytdl.log'
LOG_CLEAR_INTERVAL = 10 * 60  # every 10 minutes

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

# Start background thread for log clearing
threading.Thread(target=auto_clear_log, daemon=True).start()


# In-memory tracking
download_status = {}
captcha_store = {}

# Verified CAPTCHA sessions (tracks which sessions have verified)
verified_sessions = {}

class DownloadProgress:
    def __init__(self):
        self.status = 'queued'
        self.progress = 0.0
        self.filename = ''
        self.error = ''
        self.temp_dir = ''
        self.ffmpeg_available = False
        self.title = ''
        self.completed = False  # Prevent race conditions
        # New progress tracking fields
        self.downloaded_bytes = 0
        self.total_bytes = 0
        self.speed = 0
        self.eta = 0

def format_duration(seconds):
    try:
        seconds = int(seconds)
    except Exception:
        return "Unknown"
    if seconds <= 0:
        return "00:00"
    minutes, seconds = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    if hours > 0:
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"
    else:
        return f"{minutes:02d}:{seconds:02d}"

def format_eta(eta_seconds):
    """Format ETA seconds into mm:ss format"""
    try:
        eta_seconds = int(eta_seconds)
        if eta_seconds <= 0:
            return "00:00"
        minutes = eta_seconds // 60
        seconds = eta_seconds % 60
        return f"{minutes:02d}:{seconds:02d}"
    except Exception:
        return "00:00"

def bytes_to_mb(bytes_value):
    """Convert bytes to megabytes with 2 decimal places"""
    try:
        return round(bytes_value / (1024 * 1024), 2)
    except Exception:
        return 0

def check_ffmpeg():
    """Return True if ffmpeg is available."""
    try:
        result = subprocess.run(['ffmpeg', '-version'], capture_output=True, text=True, timeout=10)
        return result.returncode == 0
    except Exception:
        return False

def safe_get_job(job_id):
    return download_status.get(job_id)

def progress_hook_factory(job_id):
    """Return a progress hook function bound to job_id."""
    def hook(d):
        job = safe_get_job(job_id)
        if job is None or job.completed:
            return
        
        status = d.get('status')
        if status == 'downloading':
            job.status = 'downloading'
            
            # Update progress percentage
            p = d.get('_percent_str') or d.get('percent')
            if p:
                try:
                    if isinstance(p, str):
                        p = p.strip().strip('%')
                    job.progress = min(float(p), 99.9)  # Cap at 99.9 until truly complete
                except Exception:
                    pass
            elif d.get('total_bytes') and d.get('downloaded_bytes'):
                # Calculate percentage from bytes if percent not available
                try:
                    total = d.get('total_bytes') or d.get('total_bytes_estimate', 0)
                    downloaded = d.get('downloaded_bytes', 0)
                    if total > 0:
                        job.progress = min((downloaded / total) * 100, 99.9)
                except Exception:
                    pass
            
            # Update new progress tracking fields
            job.downloaded_bytes = d.get('downloaded_bytes', 0)
            job.total_bytes = d.get('total_bytes') or d.get('total_bytes_estimate', 0)
            job.speed = d.get('speed', 0)
            job.eta = d.get('eta', 0)
            
        elif status == 'finished':
            if not job.completed:
                job.progress = 99.9  # Almost complete, final file selection pending
                # Set final values when download finishes
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

def find_final_file_in_dir(temp_dir, title_hint=None):
    """Return the best candidate file path inside temp_dir."""
    if not temp_dir or not os.path.isdir(temp_dir):
        return None
    
    try:
        files = [
            os.path.join(temp_dir, f) 
            for f in os.listdir(temp_dir) 
            if os.path.isfile(os.path.join(temp_dir, f))
        ]
    except Exception as e:
        logger.error("Error listing temp_dir %s: %s", temp_dir, e)
        return None
    
    if not files:
        return None
    
    # Filter out part files
    files = [f for f in files if not f.endswith('.part')]
    
    if not files:
        return None
    
    # If title hint provided, try to match
    if title_hint:
        normalized = title_hint.replace('/', '_').strip()
        matches = [f for f in files if os.path.basename(f).startswith(normalized)]
        if matches:
            matches.sort(key=lambda p: os.path.getsize(p) if os.path.exists(p) else 0, reverse=True)
            return matches[0]
    
    # Fallback: return biggest file
    files.sort(key=lambda p: os.path.getsize(p) if os.path.exists(p) else 0, reverse=True)
    return files[0]

def validate_format_string(format_str):
    """Validate format string to prevent injection attacks."""
    if not format_str or not isinstance(format_str, str):
        return False
    
    # Allow only safe characters and yt-dlp format syntax
    allowed_chars = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789[]+=/<>:,._-')
    if not all(c in allowed_chars for c in format_str):
        return False
    
    # Must not be too long
    if len(format_str) > 200:
        return False
    
    return True

def get_available_formats(url):
    """Get available formats for a YouTube URL"""
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'skip_download': True,
        }
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            return info.get('formats', []) if isinstance(info, dict) else []
    except Exception as e:
        logger.error("Error getting available formats: %s", e)
        return []

def is_format_available(formats, requested_format):
    """Check if the requested format is available"""
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'skip_download': True,
        }
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            # Try to process the format to see if it's available
            ydl.build_format_selector(requested_format)
            return True
    except Exception:
        return False

def get_ytdlp_opts_with_retry(temp_dir, job_id, format_str, file_ext, ffmpeg_available):
    """Get yt-dlp options with retry and anti-bot measures"""
    base_opts = {
        'outtmpl': os.path.join(temp_dir, '%(title)s.%(ext)s'),
        'progress_hooks': [progress_hook_factory(job_id)],
        'restrictfilenames': False,
        'quiet': True,
        'no_warnings': True,
        'nopart': False,
        'noplaylist': True,
        # Anti-bot evasion measures
        'extractor_retries': 3,
        'retries': 10,
        'fragment_retries': 10,
        'skip_unavailable_fragments': True,
        'continuedl': True,
        'throttled_rate': None,
        # HTTP headers to mimic browser
        'http_headers': {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'en-us,en;q=0.5',
            'Accept-Encoding': 'gzip,deflate',
            'Accept-Charset': 'ISO-8859-1,utf-8;q=0.7,*;q=0.7',
            'Connection': 'keep-alive',
        },
    }

    # Choose format options
    try:
        if file_ext == 'mp3':
            if ffmpeg_available:
                base_opts.update({
                    'format': 'bestaudio/best',
                    'postprocessors': [{
                        'key': 'FFmpegExtractAudio',
                        'preferredcodec': file_ext,
                        'preferredquality': '192',
                    }],
                })
                logger.info("Job %s - audio conversion via ffmpeg -> %s", job_id, file_ext)
            else:
                base_opts['format'] = 'bestaudio/best'
                logger.info("Job %s - ffmpeg not available, downloading best native audio", job_id)
        else:
            # For video formats, use a more flexible approach
            base_opts['format'] = format_str
            logger.info("Job %s - video format option set to: %s", job_id, format_str)
    except Exception as e:
        logger.exception("Job %s - error building ydl_opts: %s", job_id, e)

    return base_opts

def download_worker(url, format_str, file_ext, job_id):
    job = safe_get_job(job_id)
    if job is None:
        logger.error("Download worker called with missing job_id: %s", job_id)
        return

    temp_dir = tempfile.mkdtemp(prefix='ytdl_')
    job.temp_dir = temp_dir
    job.ffmpeg_available = check_ffmpeg()
    logger.info("Job %s - temp_dir: %s - ffmpeg_available: %s", job_id, temp_dir, job.ffmpeg_available)

    # Start download
    job.status = 'downloading'
    job.progress = 0.0
    job.downloaded_bytes = 0
    job.total_bytes = 0
    job.speed = 0
    job.eta = 0
    
    max_retries = 3
    retry_count = 0
    
    while retry_count < max_retries:
        try:
            ydl_opts = get_ytdlp_opts_with_retry(temp_dir, job_id, format_str, file_ext, job.ffmpeg_available)
            
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=True)
                title = info.get('title') if isinstance(info, dict) else None
                if title:
                    job.title = title

                # Give postprocessing a moment to complete
                time.sleep(1)

                # Find final file
                final = None
                
                # 1) Check progress hook filename
                if job.filename and os.path.exists(job.filename):
                    final = job.filename

                # 2) Try prepare_filename
                if not final:
                    try:
                        if isinstance(info, dict):
                            candidate = ydl.prepare_filename(info)
                            if os.path.exists(candidate):
                                final = candidate
                    except Exception:
                        pass

                # 3) Search temp dir
                if not final:
                    candidate = find_final_file_in_dir(temp_dir, title_hint=job.title)
                    if candidate:
                        final = candidate

                # 4) Check requested_downloads
                if not final and isinstance(info, dict):
                    req = info.get('requested_downloads')
                    if req and isinstance(req, list):
                        for r in req:
                            p = r.get('filepath') or r.get('path')
                            if p and os.path.exists(p):
                                final = p
                                break

                if final:
                    final = os.path.abspath(final)
                    job.filename = final
                    job.status = 'completed'
                    job.progress = 100.0
                    job.completed = True
                    
                    # Set final file size
                    try:
                        file_size = os.path.getsize(final)
                        job.downloaded_bytes = file_size
                        job.total_bytes = file_size
                    except Exception:
                        pass
                    
                    # Validate file size (lowered threshold)
                    try:
                        size = os.path.getsize(final)
                        if size < 100:  # Less than 100 bytes is suspicious
                            job.status = 'error'
                            job.error = 'Downloaded file is too small or corrupted'
                            logger.error("Job %s - file too small: %s (%d bytes)", job_id, final, size)
                    except Exception as e:
                        logger.error("Job %s - error checking file size: %s", job_id, e)
                    
                    logger.info("Job %s - download completed: %s", job_id, final)
                    break  # Success, exit retry loop
                else:
                    job.status = 'error'
                    job.error = 'Could not determine final output filename'
                    job.completed = True
                    logger.error("Job %s - final file not found in %s", job_id, temp_dir)
                    break  # File not found error, don't retry

        except yt_dlp.utils.DownloadError as e:
            error_msg = str(e)
            logger.warning("Job %s - DownloadError (attempt %d/%d): %s", job_id, retry_count + 1, max_retries, error_msg)
            
            # Check for specific errors that shouldn't be retried
            if any(msg in error_msg for msg in [
                "Requested format is not available",
                "Private video", 
                "Video unavailable",
                "Sign in to confirm",
                "This video is not available",
                "No video formats found"
            ]):
                job.status = 'error'
                if "Requested format is not available" in error_msg:
                    job.error = 'The requested quality is not available for this video. Please try a lower quality.'
                elif "Private video" in error_msg:
                    job.error = 'This video is private and cannot be downloaded.'
                elif "Video unavailable" in error_msg:
                    job.error = 'This video is unavailable.'
                elif "Sign in to confirm" in error_msg:
                    job.error = 'This video requires age verification and cannot be downloaded.'
                else:
                    job.error = f'Download failed: {error_msg}'
                job.completed = True
                break
            
            # For 403 errors, wait and retry with different options
            elif "HTTP Error 403" in error_msg or "Forbidden" in error_msg:
                retry_count += 1
                if retry_count < max_retries:
                    wait_time = 2 ** retry_count  # Exponential backoff
                    logger.info("Job %s - 403 error, waiting %d seconds before retry %d", job_id, wait_time, retry_count)
                    time.sleep(wait_time)
                    continue
                else:
                    job.status = 'error'
                    job.error = 'YouTube is blocking downloads. Please try again later or use a different video.'
                    job.completed = True
                    break
            else:
                # Other download errors
                job.status = 'error'
                job.error = f'Download failed: {error_msg}'
                job.completed = True
                break

        except Exception as e:
            logger.exception("Job %s - unexpected exception (attempt %d/%d): %s", job_id, retry_count + 1, max_retries, e)
            retry_count += 1
            if retry_count < max_retries:
                time.sleep(2)
                continue
            else:
                job.status = 'error'
                job.error = f'Unexpected error: {str(e)}'
                job.completed = True
                break

def generate_captcha_image(captcha_code):
    """Generate a CAPTCHA image with the given code"""
    try:
        width, height = 220, 100
        image = Image.new('RGB', (width, height), color=(255, 255, 255))
        draw = ImageDraw.Draw(image)
        
        font_size = 36
        try:
            font_paths = [
                "arial.ttf",
                "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
                "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
                "/System/Library/Fonts/Arial.ttf",
                "C:/Windows/Fonts/arial.ttf"
            ]
            font = None
            for font_path in font_paths:
                try:
                    font = ImageFont.truetype(font_path, font_size)
                    break
                except IOError:
                    continue
            if font is None:
                font = ImageFont.load_default()
        except Exception:
            font = ImageFont.load_default()
        
        # Background noise
        for _ in range(15):
            x1 = random.randint(0, width)
            y1 = random.randint(0, height)
            x2 = random.randint(x1, min(x1 + 30, width))
            y2 = random.randint(y1, min(y1 + 20, height))
            draw.ellipse([(x1, y1), (x2, y2)], 
                        fill=(random.randint(200, 255), random.randint(200, 255), random.randint(200, 255)),
                        outline=(random.randint(180, 220), random.randint(180, 220), random.randint(180, 220)))
        
        # Lines
        for _ in range(8):
            x1 = random.randint(0, width)
            y1 = random.randint(0, height)
            x2 = random.randint(0, width)
            y2 = random.randint(0, height)
            draw.line([(x1, y1), (x2, y2)], 
                     fill=(random.randint(150, 200), random.randint(150, 200), random.randint(150, 200)), 
                     width=random.randint(1, 3))
        
        # Dots
        for _ in range(150):
            x = random.randint(0, width)
            y = random.randint(0, height)
            radius = random.randint(1, 3)
            draw.ellipse([(x, y), (x + radius, y + radius)], 
                        fill=(random.randint(200, 255), random.randint(200, 255), random.randint(200, 255)))
        
        # Text
        text_bbox = draw.textbbox((0, 0), captcha_code, font=font)
        text_width = text_bbox[2] - text_bbox[0]
        text_height = text_bbox[3] - text_bbox[1]
        
        x = (width - text_width) // 2
        y = (height - text_height) // 2 - 5
        
        for i, char in enumerate(captcha_code):
            char_bbox = draw.textbbox((0, 0), char, font=font)
            char_width = char_bbox[2] - char_bbox[0]
            
            char_x = x + i * (text_width // len(captcha_code)) + random.randint(-3, 3)
            char_y = y + random.randint(-5, 5)
            
            color = (random.randint(0, 100), random.randint(0, 100), random.randint(0, 100))
            
            char_img = Image.new('RGBA', (char_width + 10, text_height + 10), (0, 0, 0, 0))
            char_draw = ImageDraw.Draw(char_img)
            char_draw.text((5, 5), char, font=font, fill=color)
            
            rotation_angle = random.uniform(-10, 10)
            rotated_char = char_img.rotate(rotation_angle, expand=1, resample=Image.BICUBIC)
            
            image.paste(rotated_char, (char_x, char_y), rotated_char)
        
        image = image.filter(ImageFilter.GaussianBlur(radius=0.8))
        draw.rectangle([0, 0, width-1, height-1], outline=(100, 100, 100), width=2)
        
        img_byte_arr = io.BytesIO()
        image.save(img_byte_arr, format='PNG', optimize=True)
        img_byte_arr = img_byte_arr.getvalue()
        
        img_base64 = base64.b64encode(img_byte_arr).decode('utf-8')
        return f"data:image/png;base64,{img_base64}"
        
    except Exception as e:
        logger.error(f"Error generating CAPTCHA image: {e}")
        return None

@app.route('/api/generate-captcha')
def generate_captcha():
    """Generate a new CAPTCHA code and store it"""
    try:
        captcha_code = str(random.randint(1000, 9999))
        captcha_id = str(uuid.uuid4())
        
        captcha_image = generate_captcha_image(captcha_code)
        
        captcha_store[captcha_id] = {
            'code': captcha_code,
            'expires': datetime.now() + timedelta(minutes=5),
            'image_data': captcha_image
        }
        
        cleanup_expired_captchas()
        
        logger.info("Generated CAPTCHA: %s with ID: %s", captcha_code, captcha_id)
        
        response_data = {
            'captcha_id': captcha_id,
            'captcha_code': captcha_code
        }
        
        if captcha_image:
            response_data['captcha_image'] = captcha_image
        else:
            logger.warning("CAPTCHA image generation failed, using text fallback")
        
        return jsonify(response_data)
        
    except Exception as e:
        logger.error("Error generating CAPTCHA: %s", e)
        return jsonify({'error': 'Failed to generate CAPTCHA'}), 500

@app.route('/api/verify-captcha', methods=['POST'])
def verify_captcha():
    """Verify CAPTCHA input and create session token"""
    try:
        data = request.get_json() or {}
        captcha_id = data.get('captcha_id')
        user_input = data.get('captcha_input')
        
        if not captcha_id or not user_input:
            return jsonify({'error': 'CAPTCHA ID and input required'}), 400
        
        cleanup_expired_captchas()
        
        captcha_data = captcha_store.get(captcha_id)
        if not captcha_data:
            logger.warning("CAPTCHA verification failed: ID %s not found", captcha_id)
            return jsonify({'valid': False, 'error': 'CAPTCHA expired or invalid'})
        
        if datetime.now() > captcha_data['expires']:
            captcha_store.pop(captcha_id, None)
            logger.warning("CAPTCHA verification failed: ID %s expired", captcha_id)
            return jsonify({'valid': False, 'error': 'CAPTCHA expired'})
        
        is_valid = user_input == captcha_data['code']
        
        if is_valid:
            # Create a session token for this verified CAPTCHA
            session_token = str(uuid.uuid4())
            verified_sessions[session_token] = {
                'verified_at': datetime.now(),
                'expires': datetime.now() + timedelta(minutes=10)  # Session valid for 10 minutes
            }
            captcha_store.pop(captcha_id, None)
            logger.info("CAPTCHA verification successful for ID: %s, session: %s", captcha_id, session_token)
            return jsonify({'valid': True, 'session_token': session_token})
        else:
            logger.warning("CAPTCHA verification failed: incorrect code for ID %s", captcha_id)
            return jsonify({'valid': False, 'error': 'Incorrect CAPTCHA code'})
            
    except Exception as e:
        logger.error("Error verifying CAPTCHA: %s", e)
        return jsonify({'error': 'Failed to verify CAPTCHA'}), 500

def cleanup_expired_captchas():
    """Remove expired CAPTCHAs and sessions"""
    try:
        now = datetime.now()
        
        # Clean up CAPTCHAs
        expired_keys = [
            key for key, data in captcha_store.items() 
            if now > data['expires']
        ]
        for key in expired_keys:
            captcha_store.pop(key, None)
        
        # Clean up sessions
        expired_sessions = [
            key for key, data in verified_sessions.items()
            if now > data['expires']
        ]
        for key in expired_sessions:
            verified_sessions.pop(key, None)
            
        if expired_keys or expired_sessions:
            logger.info("Cleaned up %d expired CAPTCHAs and %d expired sessions", 
                       len(expired_keys), len(expired_sessions))
    except Exception as e:
        logger.error("Error cleaning up expired items: %s", e)

@app.route('/api/ffmpeg-status')
def get_ffmpeg_status():
    return jsonify({'ffmpeg_available': check_ffmpeg()})

@app.route('/api/video-info', methods=['POST'])
def get_video_info():
    data = request.get_json() or {}
    url = data.get('url')
    if not url:
        return jsonify({'error': 'URL is required'}), 400
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'skip_download': True,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            },
        }
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
            video_info = {
                'title': info.get('title', 'Unknown'),
                'duration': format_duration(info.get('duration', 0)),
                'thumbnail': info.get('thumbnail', ''),
                'channel': info.get('uploader', 'Unknown'),
                'view_count': info.get('view_count', 0),
                'formats': formats
            }
            return jsonify(video_info)
    except Exception as e:
        logger.exception("Error fetching video info: %s", e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/download', methods=['POST'])
def download_video():
    """Download endpoint with CAPTCHA verification"""
    data = request.get_json() or {}
    url = data.get('url')
    format_str = data.get('format')
    file_ext = data.get('file_ext', 'mp4')
    session_token = data.get('session_token')

    if not url or not format_str:
        return jsonify({'error': 'URL and format are required'}), 400
    
    # Validate session token
    if not session_token or session_token not in verified_sessions:
        logger.warning("Download attempt without valid session token")
        return jsonify({'error': 'CAPTCHA verification required'}), 403
    
    # Check if session is expired
    session_data = verified_sessions[session_token]
    if datetime.now() > session_data['expires']:
        verified_sessions.pop(session_token, None)
        logger.warning("Download attempt with expired session token")
        return jsonify({'error': 'CAPTCHA session expired'}), 403
    
    # Validate format string
    if not validate_format_string(format_str):
        logger.warning("Invalid format string rejected: %s", format_str)
        return jsonify({'error': 'Invalid format specification'}), 400
    
    # Validate file extension
    allowed_extensions = ['mp4', 'mp3']
    if file_ext not in allowed_extensions:
        return jsonify({'error': f'Invalid file extension. Allowed: {", ".join(allowed_extensions)}'}), 400

    # Check if format is likely available
    try:
        formats = get_available_formats(url)
        if formats and not is_format_available(formats, format_str):
            logger.warning("Format %s may not be available for URL: %s", format_str, url)
            # We'll still try, but log the warning
    except Exception as e:
        logger.warning("Could not check format availability: %s", e)

    job_id = str(uuid.uuid4())
    download_status[job_id] = DownloadProgress()
    download_status[job_id].ffmpeg_available = check_ffmpeg()

    # Invalidate session token after use (one download per verification)
    verified_sessions.pop(session_token, None)
    logger.info("Session token %s consumed for job %s", session_token, job_id)

    # Start background thread
    t = threading.Thread(target=download_worker, args=(url, format_str, file_ext, job_id), daemon=True)
    t.start()

    return jsonify({'job_id': job_id, 'ffmpeg_available': download_status[job_id].ffmpeg_available})

@app.route('/api/download-status/<job_id>')
def get_download_status(job_id):
    job = safe_get_job(job_id)
    if job is None:
        return jsonify({'error': 'Download job not found'}), 404
    
    # Prepare response with all progress data
    response_data = {
        'status': job.status,
        'progress': job.progress,
        'filename': job.filename,
        'error': job.error,
        'ffmpeg_available': job.ffmpeg_available,
        'temp_dir': job.temp_dir,
        # New progress tracking fields
        'downloaded_bytes': job.downloaded_bytes,
        'total_bytes': job.total_bytes,
        'speed': job.speed,
        'eta': job.eta,
        # Formatted values for frontend display
        'downloaded_mb': bytes_to_mb(job.downloaded_bytes),
        'total_mb': bytes_to_mb(job.total_bytes),
        'speed_mb': bytes_to_mb(job.speed),
        'eta_formatted': format_eta(job.eta)
    }
    
    return jsonify(response_data)

@app.route('/api/download-file/<job_id>')
def download_file(job_id):
    job = safe_get_job(job_id)
    if job is None:
        return jsonify({'error': 'Download job not found'}), 404

    if job.status != 'completed':
        return jsonify({'error': 'File not ready', 'status': job.status, 'error_detail': job.error}), 400

    filename = job.filename
    if not filename or not os.path.exists(filename):
        candidate = find_final_file_in_dir(job.temp_dir, title_hint=job.title)
        if candidate:
            filename = candidate

    if not filename or not os.path.exists(filename):
        return jsonify({'error': 'File not found on server'}), 404

    original_filename = os.path.basename(filename)
    ext = os.path.splitext(original_filename)[1].lower().lstrip('.')
    mime_types = {
        'mp4': 'video/mp4',
        'mp3': 'audio/mpeg'
    }
    mimetype = mime_types.get(ext, 'application/octet-stream')

    abs_path = os.path.abspath(filename)

    # Schedule cleanup
    def schedule_cleanup_job(job_id_inner):
        time.sleep(300)  # Wait 5 minutes
        j = safe_get_job(job_id_inner)
        if j and j.temp_dir and os.path.exists(j.temp_dir):
            try:
                shutil.rmtree(j.temp_dir)
                logger.info("Scheduled cleanup removed %s for job %s", j.temp_dir, job_id_inner)
            except Exception as e:
                logger.error("Error removing temp dir %s: %s", j.temp_dir, e)
        download_status.pop(job_id_inner, None)

    threading.Thread(target=schedule_cleanup_job, args=(job_id,), daemon=True).start()

    return send_file(abs_path, as_attachment=True, download_name=original_filename, mimetype=mimetype)

def cleanup_old_files():
    """Remove completed files and temp dirs older than 1 hour."""
    now = time.time()
    one_hour_ago = now - 3600
    
    for jid, job in list(download_status.items()):
        try:
            if job.temp_dir and os.path.exists(job.temp_dir):
                # Check modification time
                mtime = os.path.getmtime(job.temp_dir)
                if mtime < one_hour_ago:
                    try:
                        shutil.rmtree(job.temp_dir)
                        logger.info("Cleanup removed temp_dir %s (job %s)", job.temp_dir, jid)
                    except Exception as e:
                        logger.error("Error removing %s: %s", job.temp_dir, e)
                    download_status.pop(jid, None)
        except Exception as e:
            logger.exception("Error in cleanup_old_files for job %s: %s", jid, e)

def schedule_cleanup():
    cleanup_old_files()
    cleanup_expired_captchas()
    threading.Timer(1800, schedule_cleanup).start()

@app.route('/')
def health_check():
    """Simple health check endpoint for Render and monitoring"""
    return jsonify({
        'status': 'healthy',
        'service': 'YTDL API Server',
        'timestamp': datetime.now().isoformat()
    })

if __name__ == '__main__':
    ffmpeg_available = check_ffmpeg()
    if not ffmpeg_available:
        logger.warning("FFmpeg not found - some features will be limited.")
        print("⚠️  Warning: FFmpeg not found. Some features may be limited.")
    else:
        logger.info("FFmpeg available - full functionality enabled.")
        print("✅ FFmpeg is available - Full functionality enabled")

    try:
        from PIL import Image
        print("✅ CAPTCHA image system initialized with Pillow")
        logger.info("CAPTCHA image system initialized with Pillow")
    except ImportError:
        print("⚠️  Pillow not found - CAPTCHA will use text fallback")
        logger.warning("Pillow not found - CAPTCHA will use text fallback")

    schedule_cleanup()

    # Use PORT environment variable for Render compatibility
    port = int(os.environ.get('PORT', 5000))
    
    print(f"✅ YTDL API Server starting on port {port}")
    logger.info(f"YTDL API Server starting on port {port}")
    

    app.run(debug=False, host='0.0.0.0', port=port, use_reloader=False)
