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
import re

YTDL_COOKIES_PATH = os.environ.get('YTDL_COOKIES_PATH')

app = Flask(__name__)
CORS(app)  # Enable CORS for all routes

# Setup logging
os.makedirs('logs', exist_ok=True)
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

# In-memory tracking with thread safety
download_status = {}
captcha_store = {}
verified_sessions = {}

# Thread locks for thread-safe operations
download_status_lock = threading.Lock()
captcha_store_lock = threading.Lock()
verified_sessions_lock = threading.Lock()

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
        self.created_at = datetime.now()  # Track creation time for cleanup
        self.last_accessed = datetime.now()  # Track last access

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

def format_file_size(bytes_value):
    """Convert bytes to human readable format"""
    try:
        if bytes_value >= 1024 * 1024 * 1024:
            return f"{round(bytes_value / (1024 * 1024 * 1024), 1)}GB"
        elif bytes_value >= 1024 * 1024:
            return f"{round(bytes_value / (1024 * 1024), 1)}MB"
        elif bytes_value >= 1024:
            return f"{round(bytes_value / 1024, 1)}KB"
        else:
            return f"{bytes_value}B"
    except Exception:
        return "Unknown"

def check_ffmpeg():
    """Return True if ffmpeg is available."""
    try:
        result = subprocess.run(['ffmpeg', '-version'], capture_output=True, text=True, timeout=10)
        return result.returncode == 0
    except Exception:
        return False

def safe_get_job(job_id):
    """Thread-safe job retrieval with access tracking"""
    with download_status_lock:
        job = download_status.get(job_id)
        if job:
            job.last_accessed = datetime.now()
        return job

def safe_set_job(job_id, job):
    """Thread-safe job setting"""
    with download_status_lock:
        download_status[job_id] = job

def safe_remove_job(job_id):
    """Thread-safe job removal"""
    with download_status_lock:
        return download_status.pop(job_id, None)

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
    
    files = [f for f in files if not f.endswith('.part')]
    
    if not files:
        return None
    
    if title_hint:
        normalized = title_hint.replace('/', '_').replace('\\', '_').strip()
        matches = [f for f in files if os.path.basename(f).startswith(normalized)]
        if matches:
            matches.sort(key=lambda p: os.path.getsize(p) if os.path.exists(p) else 0, reverse=True)
            return matches[0]
    
    files.sort(key=lambda p: os.path.getsize(p) if os.path.exists(p) else 0, reverse=True)
    return files[0]

def validate_format_string(format_str):
    """Validate format string to prevent injection attacks."""
    if not format_str or not isinstance(format_str, str):
        return False
    
    # More restrictive allowed characters
    allowed_chars = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789[]+/._-')
    if not all(c in allowed_chars for c in format_str):
        return False
    
    if len(format_str) > 100:  # Reduced from 200
        return False
    
    # Additional security checks
    if '..' in format_str or '//' in format_str:
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
        if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
            cleaned_cookies = clean_cookies_file(YTDL_COOKIES_PATH)
            ydl_opts['cookiefile'] = cleaned_cookies if cleaned_cookies else YTDL_COOKIES_PATH
        
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            return info.get('formats', []) if isinstance(info, dict) else []
    except Exception as e:
        logger.error("Error getting available formats: %s", e)
        return []

def is_format_available(url, requested_format):
    """Check if the requested format is available for the given video"""
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'skip_download': True,
        }
        
        # Use cookies if available
        if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
            cleaned_cookies = clean_cookies_file(YTDL_COOKIES_PATH)
            ydl_opts['cookiefile'] = cleaned_cookies if cleaned_cookies else YTDL_COOKIES_PATH
        
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            # Get all available formats
            info = ydl.extract_info(url, download=False)
            formats = info.get('formats', []) if isinstance(info, dict) else []
            
            # For audio formats, check if any audio format exists
            if 'bestaudio' in requested_format:
                audio_formats = [f for f in formats if f.get('acodec') != 'none']
                return len(audio_formats) > 0
            
            # For video formats, check if the requested resolution range is available
            if 'height<=' in requested_format:
                height_match = re.search(r'height<=(\d+)', requested_format)
                if height_match:
                    max_height = int(height_match.group(1))
                    video_formats = [f for f in formats if f.get('height') and f.get('height') <= max_height and f.get('vcodec') != 'none']
                    return len(video_formats) > 0
            
            # If we can't parse the format, assume it's available and let yt-dlp handle fallbacks
            return True
            
    except Exception as e:
        logger.error("Error checking format availability: %s", e)
        # If we can't check, assume it's available and let the download attempt handle it
        return True

def clean_cookies_file(cookies_path):
    """Clean and fix cookies file to ensure Netscape format compatibility"""
    try:
        if not os.path.exists(cookies_path):
            return None
        
        # Create unique temp file to avoid race conditions
        temp_cookies = os.path.join('/tmp', f'cookies_cleaned_{uuid.uuid4().hex}.txt')
        
        with open(cookies_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        # Filter and clean lines
        cleaned_lines = []
        seen_header = False
        
        for line in lines:
            stripped = line.strip()
            
            # Keep only the first Netscape header line
            if 'Netscape HTTP Cookie File' in line and not seen_header:
                cleaned_lines.append('# Netscape HTTP Cookie File\n')
                seen_header = True
                continue
            
            # Skip other comment lines except the main header
            if stripped.startswith('#'):
                if 'Netscape HTTP Cookie File' in line:
                    continue  # Already added
                # Skip other comments like the curl.haxx.se line
                continue
            
            # Skip empty lines at the start
            if not stripped and not cleaned_lines:
                continue
            
            # Keep cookie lines and one empty line after header
            if stripped or (cleaned_lines and not cleaned_lines[-1].strip()):
                cleaned_lines.append(line)
        
        with open(temp_cookies, 'w', encoding='utf-8') as f:
            f.writelines(cleaned_lines)
        
        logger.info("Created cleaned cookies file: %s", temp_cookies)
        return temp_cookies
        
    except Exception as e:
        logger.error("Error cleaning cookies file: %s", e)
        # If cleaning fails, try to use original
        return cookies_path

def get_ytdlp_opts_with_retry(temp_dir, job_id, format_str, file_ext, ffmpeg_available):
    """Get yt-dlp options with retry, anti-bot measures, and cookies"""
    base_opts = {
        'outtmpl': os.path.join(temp_dir, '%(title)s.%(ext)s'),
        'progress_hooks': [progress_hook_factory(job_id)],
        'restrictfilenames': False,
        'quiet': False,
        'no_warnings': False,
        'nopart': False,
        'noplaylist': True,
        'extractor_retries': 5,
        'retries': 15,
        'fragment_retries': 15,
        'skip_unavailable_fragments': True,
        'continuedl': True,
        
        # ADD THESE NEW OPTIONS FOR YOUTUBE ISSUES:
        'age_limit': None,  # Don't skip age-restricted videos
        'playlist_items': '1',  # Only download first item if somehow it's a playlist
        'allow_unplayable_formats': False,  # Skip unplayable formats
        'ignore_no_formats_error': False,  # Don't ignore format errors
        'format_sort': ['res', 'ext:mp4:m4a'],  # Prefer mp4/m4a formats
        'merge_output_format': 'mp4',  # Always merge to mp4 if needed
        
        # YouTube-specific extractor options
        'extractor_args': {
            'youtube': {
                'player_client': ['android', 'web'],  # Try multiple clients
                'skip': ['hls', 'dash'],  # Skip problematic formats initially
            }
        },
        
        'http_headers': {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'en-us,en;q=0.5',
            'Accept-Encoding': 'gzip,deflate',
            'Connection': 'keep-alive',
        },
    }
    

    # CRITICAL: Use cookies file if available
    cookies_loaded = False
    
    if YTDL_COOKIES_PATH:
        if os.path.exists(YTDL_COOKIES_PATH):
            try:
                # Clean the cookies file first
                cleaned_cookies = clean_cookies_file(YTDL_COOKIES_PATH)
                if cleaned_cookies:
                    base_opts['cookiefile'] = cleaned_cookies
                    logger.info("✅ Using cleaned cookies file: %s for job %s", cleaned_cookies, job_id)
                else:
                    # Fallback to original if cleaning fails
                    base_opts['cookiefile'] = YTDL_COOKIES_PATH
                    logger.info("✅ Using original cookies file: %s for job %s", YTDL_COOKIES_PATH, job_id)
                cookies_loaded = True
            except Exception as e:
                logger.error("Failed to set cookiefile: %s", e)
        else:
            logger.error("❌ Cookies file not found at: %s", YTDL_COOKIES_PATH)
    
    if not cookies_loaded:
        logger.warning("⚠️ No cookies loaded - trying browser fallback")
        try:
            base_opts['cookiesfrombrowser'] = ('chrome',)
        except Exception:
            pass

    anti_bot_opts = {
        'extract_flat': False,
        'ignoreerrors': False,
        'sleep_interval': 1,
        'max_sleep_interval': 5,
        'sleep_interval_requests': 1,
        'retry_sleep_functions': {
            'http': lambda n: min(2 ** n, 10),
            'fragment': lambda n: min(2 ** n, 10),
            'extractor': lambda n: min(2 ** n, 10),
        }
    }
    base_opts.update(anti_bot_opts)

    # Update the format selection part in get_ytdlp_opts_with_retry
# Replace the format selection section with this more robust version:

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
        else:
            base_opts['format'] = 'bestaudio/best'
    else:
        # More robust format selection with fallbacks
        # Try to use specific format, but have multiple fallbacks
        if format_str:
            # Build a format string with fallbacks
            format_with_fallback = f"{format_str}/best[height<=1080]/best"
            base_opts['format'] = format_with_fallback
            logger.info("Job %s - using format with fallback: %s", job_id, format_with_fallback)
        else:
            # Default safe format
            base_opts['format'] = 'best[height<=1080]/best'
            logger.info("Job %s - using default safe format", job_id)
        
except Exception as e:
    logger.exception("Job %s - error building ydl_opts: %s", job_id, e)
    # Fallback to the safest default
    base_opts['format'] = 'best'

return base_opts

def handle_download_error(job, job_id, error, retry_count, max_retries):
    """Handle download errors with appropriate retry logic"""
    error_msg = str(error)
    logger.warning("Job %s - DownloadError (attempt %d/%d): %s", job_id, retry_count + 1, max_retries, error_msg)
    
    if "sign in to confirm" in error_msg.lower() or "confirm you're not a bot" in error_msg.lower():
        job.status = 'error'
        job.error = '🤖 Bot detection triggered. Please ensure cookies.txt is uploaded and YTDL_COOKIES_PATH is configured correctly.'
        job.completed = True
        logger.error("❌ Bot detection error - cookies may be missing or invalid")
        return False
    
    non_retryable_errors = [
        "requested format is not available",
        "private video", 
        "video unavailable",
        "this video is not available",
        "no video formats found",
        "this video is private"
    ]
    
    for msg in non_retryable_errors:
        if msg in error_msg.lower():
            job.status = 'error'
            if "requested format is not available" in error_msg.lower():
                job.error = 'The requested quality is not available for this video. Please try a lower quality.'
            elif "private video" in error_msg.lower():
                job.error = 'This video is private and cannot be downloaded.'
            elif "video unavailable" in error_msg.lower():
                job.error = 'This video is unavailable.'
            else:
                job.error = f'Download failed: {error_msg}'
            job.completed = True
            return False
    
    retryable_errors = [
        "http error 403",
        "http error 429", 
        "forbidden",
        "too many requests",
        "age restricted",
        "rate limit"
    ]
    
    for msg in retryable_errors:
        if msg in error_msg.lower():
            if retry_count < max_retries - 1:  # Fixed: don't double increment
                wait_time = min(2 ** (retry_count + 1), 30)
                logger.info("Job %s - %s error, waiting %d seconds before retry %d", 
                           job_id, msg.upper(), wait_time, retry_count + 2)
                time.sleep(wait_time)
                return True
            else:
                job.status = 'error'
                job.error = 'YouTube is blocking downloads. Please ensure cookies are properly configured.'
                job.completed = True
                return False
    
    job.status = 'error'
    job.error = f'Download failed: {error_msg}'
    job.completed = True
    return False

def download_worker(url, format_str, file_ext, job_id):
    job = safe_get_job(job_id)
    if job is None:
        logger.error("Download worker called with missing job_id: %s", job_id)
        return

    temp_dir = tempfile.mkdtemp(prefix=f'ytdl_{uuid.uuid4().hex}_')
    job.temp_dir = temp_dir
    job.ffmpeg_available = check_ffmpeg()
    logger.info("Job %s - temp_dir: %s - ffmpeg_available: %s", job_id, temp_dir, job.ffmpeg_available)

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

                time.sleep(1)

                final = None
                
                if job.filename and os.path.exists(job.filename):
                    final = job.filename

                if not final:
                    try:
                        if isinstance(info, dict):
                            candidate = ydl.prepare_filename(info)
                            if os.path.exists(candidate):
                                final = candidate
                    except Exception:
                        pass

                if not final:
                    candidate = find_final_file_in_dir(temp_dir, title_hint=job.title)
                    if candidate:
                        final = candidate

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
                    
                    try:
                        file_size = os.path.getsize(final)
                        job.downloaded_bytes = file_size
                        job.total_bytes = file_size
                    except Exception:
                        pass
                    
                    try:
                        size = os.path.getsize(final)
                        # More reasonable minimum file size check
                        if size < 1024:  # 1KB minimum
                            job.status = 'error'
                            job.error = 'Downloaded file is too small or corrupted'
                            logger.error("Job %s - file too small: %s (%d bytes)", job_id, final, size)
                    except Exception as e:
                        logger.error("Job %s - error checking file size: %s", job_id, e)
                    
                    logger.info("✅ Job %s - download completed: %s", job_id, final)
                    break
                else:
                    job.status = 'error'
                    job.error = 'Could not determine final output filename'
                    job.completed = True
                    logger.error("Job %s - final file not found in %s", job_id, temp_dir)
                    break

        except yt_dlp.utils.DownloadError as e:
            should_retry = handle_download_error(job, job_id, e, retry_count, max_retries)
            if should_retry:
                retry_count += 1
                continue
            else:
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

    if job.status == 'error' and job.temp_dir and os.path.exists(job.temp_dir):
        try:
            shutil.rmtree(job.temp_dir)
            logger.info("Cleaned up temp directory for failed job %s", job_id)
        except Exception as e:
            logger.error("Error cleaning up temp dir for job %s: %s", job_id, e)

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
        
        # Add random circles for noise
        for _ in range(15):
            x1 = random.randint(0, width)
            y1 = random.randint(0, height)
            x2 = random.randint(x1, min(x1 + 30, width))
            y2 = random.randint(y1, min(y1 + 20, height))
            draw.ellipse([(x1, y1), (x2, y2)], 
                        fill=(random.randint(200, 255), random.randint(200, 255), random.randint(200, 255)),
                        outline=(random.randint(180, 220), random.randint(180, 220), random.randint(180, 220)))
        
        # Add random lines for noise
        for _ in range(8):
            x1 = random.randint(0, width)
            y1 = random.randint(0, height)
            x2 = random.randint(0, width)
            y2 = random.randint(0, height)
            draw.line([(x1, y1), (x2, y2)], 
                     fill=(random.randint(150, 200), random.randint(150, 200), random.randint(150, 200)), 
                     width=random.randint(1, 3))
        
        # Add random dots for noise
        for _ in range(150):
            x = random.randint(0, width)
            y = random.randint(0, height)
            radius = random.randint(1, 3)
            draw.ellipse([(x, y), (x + radius, y + radius)], 
                        fill=(random.randint(200, 255), random.randint(200, 255), random.randint(200, 255)))
        
        # Calculate text position
        text_bbox = draw.textbbox((0, 0), captcha_code, font=font)
        text_width = text_bbox[2] - text_bbox[0]
        text_height = text_bbox[3] - text_bbox[1]
        
        x = (width - text_width) // 2
        y = (height - text_height) // 2 - 5
        
        # Draw text with distortion
        for i, char in enumerate(captcha_code):
            char_bbox = draw.textbbox((0, 0), char, font=font)
            char_width = char_bbox[2] - char_bbox[0]
            
            char_x = x + i * (text_width // len(captcha_code)) + random.randint(-3, 3)
            char_y = y + random.randint(-5, 5)
            
            color = (random.randint(0, 100), random.randint(0, 100), random.randint(0, 100))
            
            # Create individual character image for rotation
            char_img = Image.new('RGBA', (char_width + 10, text_height + 10), (0, 0, 0, 0))
            char_draw = ImageDraw.Draw(char_img)
            char_draw.text((5, 5), char, font=font, fill=color)
            
            # Rotate character slightly
            rotation_angle = random.uniform(-10, 10)
            rotated_char = char_img.rotate(rotation_angle, expand=1, resample=Image.BICUBIC)
            
            # Paste rotated character onto main image
            image.paste(rotated_char, (char_x, char_y), rotated_char)
        
        # Apply slight blur
        image = image.filter(ImageFilter.GaussianBlur(radius=0.8))
        
        # Add border
        draw.rectangle([0, 0, width-1, height-1], outline=(100, 100, 100), width=2)
        
        # Convert to base64
        img_byte_arr = io.BytesIO()
        image.save(img_byte_arr, format='PNG', optimize=True)
        img_byte_arr = img_byte_arr.getvalue()
        
        img_base64 = base64.b64encode(img_byte_arr).decode('utf-8')
        return f"data:image/png;base64,{img_base64}"
        
    except Exception as e:
        logger.error(f"Error generating CAPTCHA image: {e}")
        return None

def cleanup_expired_captchas():
    """Remove expired CAPTCHAs and sessions"""
    try:
        now = datetime.now()
        
        # Clean expired CAPTCHAs with thread safety
        with captcha_store_lock:
            expired_keys = [
                key for key, data in captcha_store.items() 
                if now > data['expires']
            ]
            for key in expired_keys:
                captcha_store.pop(key, None)
        
        # Clean expired sessions with thread safety
        with verified_sessions_lock:
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

def extract_video_id(url):
    """Extract YouTube video ID from various URL formats"""
    try:
        # Handle different YouTube URL formats
        patterns = [
            r'(?:youtube\.com\/watch\?v=|youtu\.be\/|youtube\.com\/embed\/)([a-zA-Z0-9_-]{11})',
            r'youtube\.com\/watch\?.*?v=([a-zA-Z0-9_-]{11})',
        ]
        
        for pattern in patterns:
            match = re.search(pattern, url)
            if match:
                return match.group(1)
        
        # If no pattern matches, return None
        return None
    except Exception as e:
        logger.error("Error extracting video ID from URL %s: %s", url, e)
        return None

@app.route('/api/generate-captcha')
def generate_captcha():
    """Generate a new CAPTCHA code and store it"""
    try:
        captcha_code = str(random.randint(1000, 9999))
        captcha_id = str(uuid.uuid4())
        
        captcha_image = generate_captcha_image(captcha_code)
        
        if not captcha_image:
            logger.error("Failed to generate CAPTCHA image")
            return jsonify({'error': 'Failed to generate CAPTCHA image'}), 500
        
        # Store CAPTCHA data with thread safety
        with captcha_store_lock:
            captcha_store[captcha_id] = {
                'code': captcha_code,
                'expires': datetime.now() + timedelta(minutes=5),
                'image_data': captcha_image
            }
        
        # Clean up expired CAPTCHAs
        cleanup_expired_captchas()
        
        logger.info("Generated CAPTCHA: %s with ID: %s", captcha_code, captcha_id)
        
        response_data = {
            'captcha_id': captcha_id,
            'captcha_image': captcha_image
        }
        
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
        
        logger.info("CAPTCHA verification request - ID: %s, Input: %s", captcha_id, user_input)
        
        if not captcha_id or not user_input:
            return jsonify({'valid': False, 'error': 'CAPTCHA ID and input required'}), 400
        
        # Clean up expired CAPTCHAs first
        cleanup_expired_captchas()
        
        # Check if CAPTCHA exists and verify with thread safety
        with captcha_store_lock:
            captcha_data = captcha_store.get(captcha_id)
            
            if not captcha_data:
                logger.warning("CAPTCHA verification failed: ID %s not found in store", captcha_id)
                return jsonify({'valid': False, 'error': 'CAPTCHA not found or already used'}), 404
            
            # Check if CAPTCHA is expired
            if datetime.now() > captcha_data['expires']:
                captcha_store.pop(captcha_id, None)
                logger.warning("CAPTCHA verification failed: ID %s expired", captcha_id)
                return jsonify({'valid': False, 'error': 'CAPTCHA expired'}), 400
            
            # Store the code before removing from store
            stored_code = captcha_data['code']
            
            # Remove CAPTCHA immediately to prevent reuse (one-time use)
            captcha_store.pop(captcha_id, None)
            logger.info("CAPTCHA %s removed from store (one-time use)", captcha_id)
        
        # Verify the code AFTER removing from store (outside lock)
        is_valid = user_input.strip() == stored_code
        
        if not is_valid:
            logger.warning("CAPTCHA verification failed: incorrect code '%s' for ID %s (expected '%s')", 
                          user_input, captcha_id, stored_code)
            return jsonify({'valid': False, 'error': 'Incorrect CAPTCHA code'}), 400
        
        # Create session token only if CAPTCHA is valid
        session_token = str(uuid.uuid4())
        with verified_sessions_lock:
            verified_sessions[session_token] = {
                'verified_at': datetime.now(),
                'expires': datetime.now() + timedelta(minutes=10),
                'verified_videos': set()  # ADD THIS LINE
            }
        
        logger.info("✅ CAPTCHA verified successfully for ID: %s, session token: %s", captcha_id, session_token)
        return jsonify({'valid': True, 'session_token': session_token}), 200
            
    except Exception as e:
        logger.exception("Error verifying CAPTCHA: %s", e)
        return jsonify({'valid': False, 'error': 'Failed to verify CAPTCHA. Please try again.'}), 500

@app.route('/api/verify-video', methods=['POST'])
def verify_video():
    """Verify a specific video for download within an existing session"""
    try:
        data = request.get_json() or {}
        session_token = data.get('session_token')
        url = data.get('url')
        
        if not session_token or not url:
            return jsonify({'error': 'Session token and URL required'}), 400
        
        # Extract video ID
        video_id = extract_video_id(url)
        if not video_id:
            return jsonify({'error': 'Invalid YouTube URL'}), 400
        
        # Verify session and add video to verified set
        with verified_sessions_lock:
            if session_token not in verified_sessions:
                return jsonify({'error': 'Invalid or expired session'}), 403
            
            session_data = verified_sessions[session_token]
            if datetime.now() > session_data['expires']:
                verified_sessions.pop(session_token, None)
                return jsonify({'error': 'Session expired'}), 403
            
            # Initialize verified_videos if it doesn't exist
            if 'verified_videos' not in session_data:
                session_data['verified_videos'] = set()
            
            # Add this video to the verified set
            session_data['verified_videos'].add(video_id)
            
        logger.info("✅ Video %s verified for download in session %s", video_id, session_token)
        return jsonify({'success': True, 'video_id': video_id}), 200
        
    except Exception as e:
        logger.exception("Error verifying video: %s", e)
        return jsonify({'error': 'Failed to verify video'}), 500

def cleanup_old_jobs():
    """Remove old jobs and their temp directories"""
    try:
        now = datetime.now()
        expired_jobs = []
        
        with download_status_lock:
            for job_id, job in download_status.items():
                # Remove jobs older than 1 hour or completed jobs older than 30 minutes
                if (now - job.created_at).total_seconds() > 3600 or \
                   (job.completed and (now - job.last_accessed).total_seconds() > 1800):
                    expired_jobs.append((job_id, job))
        
        for job_id, job in expired_jobs:
            if job.temp_dir and os.path.exists(job.temp_dir):
                try:
                    shutil.rmtree(job.temp_dir)
                    logger.info("Cleanup removed temp_dir %s for expired job %s", job.temp_dir, job_id)
                except Exception as e:
                    logger.error("Error removing temp dir %s: %s", job.temp_dir, e)
            safe_remove_job(job_id)
            
        if expired_jobs:
            logger.info("Cleaned up %d expired jobs", len(expired_jobs))
            
    except Exception as e:
        logger.error("Error in cleanup_old_jobs: %s", e)

@app.route('/api/ffmpeg-status')
def get_ffmpeg_status():
    return jsonify({'ffmpeg_available': check_ffmpeg()})

class TimeoutException(Exception):
    pass

def extract_video_info_with_timeout(url, ydl_opts, timeout_seconds=30):
    """Extract video info with timeout using threading (replaces signal-based timeout)"""
    import queue
    
    result_queue = queue.Queue()
    exception_queue = queue.Queue()
    
    def worker():
        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                result_queue.put(info)
        except Exception as e:
            exception_queue.put(e)
    
    thread = threading.Thread(target=worker)
    thread.daemon = True
    thread.start()
    thread.join(timeout_seconds)
    
    if thread.is_alive():
        raise TimeoutException(f"Video info extraction timed out after {timeout_seconds} seconds")
    
    if not exception_queue.empty():
        raise exception_queue.get()
    
    if not result_queue.empty():
        return result_queue.get()
    
    raise Exception("Unknown error in video info extraction")

@app.route('/api/video-info', methods=['POST'])
def get_video_info():
    data = request.get_json() or {}
    url = data.get('url')
    if not url:
        return jsonify({'error': 'URL is required'}), 400
    
    # Basic URL validation
    if not url.startswith(('http://', 'https://')):
        return jsonify({'error': 'Invalid URL format'}), 400
    
    try:
        ydl_opts = {
            'quiet': False,
            'no_warnings': False,
            'skip_download': True,
            'socket_timeout': 30,
            'extract_flat': False,
            'ignoreerrors': False,
            'no_color': True,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
                'Accept-Language': 'en-us,en;q=0.5',
                'Accept-Encoding': 'gzip,deflate',
                'Connection': 'keep-alive',
            },
        }
        
        if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
            cleaned_cookies = clean_cookies_file(YTDL_COOKIES_PATH)
            ydl_opts['cookiefile'] = cleaned_cookies if cleaned_cookies else YTDL_COOKIES_PATH
            logger.info("Using cookies from: %s", ydl_opts['cookiefile'])
        
        # Try with timeout
        try:
            info = extract_video_info_with_timeout(url, ydl_opts, timeout_seconds=25)
        except TimeoutException:
            logger.error("Video info extraction timed out for URL: %s", url)
            return jsonify({
                'error': 'YouTube is taking too long to respond. This video may be heavily restricted. Please try a different video.',
                'suggestion': 'Try using a video that is publicly available and not age-restricted'
            }), 408  # 408 Request Timeout
        
        formats = []
        for f in info.get('formats', []) if isinstance(info, dict) else []:
            if f.get('format_id'):
                # Calculate file size
                filesize = f.get('filesize') or f.get('filesize_approx')
                if filesize:
                    filesize_display = format_file_size(filesize)
                else:
                    filesize_display = None
                
                # Determine format type
                is_audio = f.get('acodec') != 'none' and f.get('vcodec') == 'none'
                format_type = 'audio' if is_audio else 'video'
                
                # Get resolution/quality info
                resolution = None
                if f.get('height'):
                    resolution = f"{f.get('height')}p"
                elif f.get('format_note'):
                    resolution = f.get('format_note')
                
                # Get audio bitrate if available
                abr = f.get('abr')
                if abr:
                    quality = f"{abr}kbps"
                else:
                    quality = resolution or 'Best Quality'
                
                formats.append({
                    'format_id': f.get('format_id'),
                    'ext': f.get('ext', ''),
                    'resolution': resolution,
                    'quality': quality,
                    'filesize': filesize_display,
                    'filesize_bytes': filesize,
                    'vcodec': f.get('vcodec', 'none'),
                    'acodec': f.get('acodec', 'none'),
                    'format_note': f.get('format_note', ''),
                    'fps': f.get('fps'),
                    'type': format_type
                })
        
        # Escape HTML characters in title to prevent XSS
        title = info.get('title', 'Unknown')
        if isinstance(title, str):
            title = (title.replace('&', '&amp;')
                    .replace('<', '&lt;')
                    .replace('>', '&gt;')
                    .replace('"', '&quot;')
                    .replace("'", '&#039;'))
        
        video_info = {
            'title': title,
            'duration': format_duration(info.get('duration', 0)),
            'thumbnail': info.get('thumbnail', ''),
            'channel': info.get('uploader', 'Unknown'),
            'view_count': info.get('view_count', 0),
            'formats': formats
        }
        
        # Check if we have any downloadable formats
        downloadable_formats = [f for f in formats if f.get('vcodec') != 'none' or f.get('acodec') != 'none']
        if not downloadable_formats:
            video_info['warning'] = 'No downloadable formats available. This video may be restricted.'
        
        return jsonify(video_info)
        
    except yt_dlp.utils.DownloadError as e:
        error_msg = str(e)
        logger.error("DownloadError fetching video info: %s", error_msg)
        
        # Handle specific YouTube restrictions
        if "signature extraction failed" in error_msg.lower():
            return jsonify({
                'error': 'YouTube signature extraction failed. This video is heavily restricted.',
                'suggestion': 'Try using a different video or ensure your cookies are properly configured'
            }), 423  # 423 Locked
        
        elif "requested format is not available" in error_msg.lower():
            return jsonify({
                'error': 'No downloadable formats available for this video.',
                'suggestion': 'This video may be age-restricted, region-locked, or otherwise restricted by YouTube'
            }), 404
        
        elif "video unavailable" in error_msg.lower():
            return jsonify({
                'error': 'This video is unavailable.',
                'suggestion': 'The video may have been removed or made private'
            }), 404
        
        else:
            return jsonify({
                'error': 'YouTube is restricting access to this video.',
                'details': 'Please try a different video or check if the video is publicly available'
            }), 403
        
    except Exception as e:
        error_msg = str(e)
        logger.exception("Unexpected error fetching video info: %s", error_msg)
        return jsonify({
            'error': 'Failed to fetch video information.',
            'suggestion': 'Please try again with a different video URL'
        }), 500

# SIMPLIFIED APPROACH - Update the download_video() function in app.py
# This will automatically verify videos on download attempt
# REPLACE the download_video() function (around line 1092) with this:

@app.route('/api/download', methods=['POST'])
def download_video():
    """Download endpoint with CAPTCHA verification - auto-verify on first download"""
    data = request.get_json() or {}
    url = data.get('url')
    format_str = data.get('format')
    file_ext = data.get('file_ext', 'mp4')
    session_token = data.get('session_token')

    if not url or not format_str:
        return jsonify({'error': 'URL and format are required'}), 400
    
    # Basic URL validation
    if not url.startswith(('http://', 'https://')):
        return jsonify({'error': 'Invalid URL format'}), 400
    
    # Extract video ID for session tracking
    video_id = extract_video_id(url)
    if not video_id:
        return jsonify({'error': 'Invalid YouTube URL'}), 400
    
    # Verify CAPTCHA session with thread safety
    with verified_sessions_lock:
        if not session_token or session_token not in verified_sessions:
            logger.warning("Download attempt without valid session token")
            return jsonify({'error': 'CAPTCHA verification required'}), 403
        
        session_data = verified_sessions[session_token]
        if datetime.now() > session_data['expires']:
            verified_sessions.pop(session_token, None)
            logger.warning("Download attempt with expired session token")
            return jsonify({'error': 'CAPTCHA session expired'}), 403
        
        # Initialize verified_videos set if it doesn't exist
        if 'verified_videos' not in session_data:
            session_data['verified_videos'] = set()
        
        # AUTO-VERIFY: Add this video to verified set on first download attempt
        verified_videos = session_data['verified_videos']
        if video_id not in verified_videos:
            verified_videos.add(video_id)
            logger.info("✅ Auto-verified video %s for download in session %s", video_id, session_token)
    
    if not validate_format_string(format_str):
        logger.warning("Invalid format string rejected: %s", format_str)
        return jsonify({'error': 'Invalid format specification'}), 400
    
    allowed_extensions = ['mp4', 'mp3']
    if file_ext not in allowed_extensions:
        return jsonify({'error': f'Invalid file extension. Allowed: {", ".join(allowed_extensions)}'}), 400

    try:
        # Check if format is available, but don't block if check fails
        if not is_format_available(url, format_str):
            logger.warning("Format %s may not be available for URL: %s", format_str, url)
    except Exception as e:
        logger.warning("Could not check format availability: %s", e)

    job_id = str(uuid.uuid4())
    job = DownloadProgress()
    job.ffmpeg_available = check_ffmpeg()
    safe_set_job(job_id, job)

    logger.info("Processing download for video %s with job %s", video_id, job_id)

    t = threading.Thread(target=download_worker, args=(url, format_str, file_ext, job_id), daemon=True)
    t.start()

    return jsonify({'job_id': job_id, 'ffmpeg_available': job.ffmpeg_available})

@app.route('/api/download-status/<job_id>')
def get_download_status(job_id):
    job = safe_get_job(job_id)
    if job is None:
        return jsonify({'error': 'Download job not found'}), 404
    
    response_data = {
        'status': job.status,
        'progress': job.progress,
        'filename': job.filename,
        'error': job.error,
        'ffmpeg_available': job.ffmpeg_available,
        'temp_dir': job.temp_dir,
        'downloaded_bytes': job.downloaded_bytes,
        'total_bytes': job.total_bytes,
        'speed': job.speed,
        'eta': job.eta,
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

    # Security check: ensure file is within temp directory
    try:
        filename = os.path.abspath(filename)
        temp_dir = os.path.abspath(job.temp_dir)
        if not filename.startswith(temp_dir):
            logger.error("Security violation: file %s not in temp dir %s", filename, temp_dir)
            return jsonify({'error': 'Invalid file path'}), 403
    except Exception as e:
        logger.error("Error validating file path: %s", e)
        return jsonify({'error': 'File path validation failed'}), 500

    original_filename = os.path.basename(filename)
    ext = os.path.splitext(original_filename)[1].lower().lstrip('.')
    mime_types = {
        'mp4': 'video/mp4',
        'mp3': 'audio/mpeg'
    }
    mimetype = mime_types.get(ext, 'application/octet-stream')

    def schedule_cleanup_job(job_id_inner):
        time.sleep(300)  # 5 minutes delay
        j = safe_get_job(job_id_inner)
        if j and j.temp_dir and os.path.exists(j.temp_dir):
            try:
                shutil.rmtree(j.temp_dir)
                logger.info("Scheduled cleanup removed %s for job %s", j.temp_dir, job_id_inner)
            except Exception as e:
                logger.error("Error removing temp dir %s: %s", j.temp_dir, e)
        safe_remove_job(job_id_inner)

    threading.Thread(target=schedule_cleanup_job, args=(job_id,), daemon=True).start()

    return send_file(filename, as_attachment=True, download_name=original_filename, mimetype=mimetype)

def schedule_cleanup():
    """Run cleanup tasks periodically"""
    cleanup_old_jobs()
    cleanup_expired_captchas()
    # Reschedule itself
    threading.Timer(1800, schedule_cleanup).start()  # Every 30 minutes

@app.route('/')
def health_check():
    """Health check endpoint with cookie status"""
    cookie_status = "✅ Configured" if (YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH)) else "❌ Not found"
    
    # Read first few lines of cookies file for debugging
    cookie_preview = None
    if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
        try:
            with open(YTDL_COOKIES_PATH, 'r', encoding='utf-8') as f:
                lines = f.readlines()[:5]  # First 5 lines
                cookie_preview = ''.join(lines)
        except Exception as e:
            cookie_preview = f"Error reading file: {e}"
    
    return jsonify({
        'status': 'healthy',
        'service': 'YTDL API Server',
        'timestamp': datetime.now().isoformat(),
        'cookies_configured': bool(YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH)),
        'cookies_path': YTDL_COOKIES_PATH or 'Not set',
        'cookies_preview': cookie_preview,
        'ffmpeg_available': check_ffmpeg(),
        'active_jobs': len(download_status),
        'active_sessions': len(verified_sessions)
    })

@app.route('/api/debug-cookies')
def debug_cookies():
    """Debug endpoint to check cookies file"""
    if not YTDL_COOKIES_PATH:
        return jsonify({'error': 'YTDL_COOKIES_PATH not set'}), 400
    
    if not os.path.exists(YTDL_COOKIES_PATH):
        return jsonify({'error': f'File not found: {YTDL_COOKIES_PATH}'}), 404
    
    try:
        with open(YTDL_COOKIES_PATH, 'r', encoding='utf-8') as f:
            content = f.read()
        
        lines = content.split('\n')
        
        return jsonify({
            'file_path': YTDL_COOKIES_PATH,
            'file_size': len(content),
            'total_lines': len(lines),
            'first_10_lines': lines[:10],
            'has_netscape_header': 'Netscape' in content[:200],
            'has_tabs': '\t' in content,
            'encoding': 'utf-8'
        })
    except Exception as e:
        return jsonify({'error': str(e)}), 500

if __name__ == '__main__':
    print("\n" + "="*60)
    print("🚀 YTDL API Server Starting...")
    print("="*60)
    
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

    if YTDL_COOKIES_PATH:
        if os.path.exists(YTDL_COOKIES_PATH):
            print(f"✅ Cookies file found: {YTDL_COOKIES_PATH}")
            logger.info("✅ Cookies file configured and found: %s", YTDL_COOKIES_PATH)
        else:
            print(f"❌ Cookies file NOT found at: {YTDL_COOKIES_PATH}")
            print("   Please upload cookies.txt to fix bot detection errors!")
            logger.error("❌ YTDL_COOKIES_PATH set but file not found: %s", YTDL_COOKIES_PATH)
    else:
        print("❌ YTDL_COOKIES_PATH not set in environment variables")
        print("   Bot detection errors are likely - please configure cookies!")
        logger.warning("❌ YTDL_COOKIES_PATH environment variable not set")

    # Start cleanup scheduler
    schedule_cleanup()

    port = int(os.environ.get('PORT', 5000))
    
    print(f"\n✅ YTDL API Server starting on port {port}")
    print("="*60 + "\n")
    logger.info(f"YTDL API Server starting on port {port}")
    
    app.run(debug=False, host='0.0.0.0', port=port, use_reloader=False)



