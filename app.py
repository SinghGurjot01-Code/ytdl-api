#!/usr/bin/env python3
from flask import Flask, request, jsonify, send_file, session
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
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
import hashlib
import hmac
import secrets
from concurrent.futures import ThreadPoolExecutor, Future
import re
import signal
import queue
from typing import Dict, Optional, Any
import json

# Configuration
YTDL_COOKIES_PATH = os.environ.get('YTDL_COOKIES_PATH')
MAX_CONCURRENT_DOWNLOADS = int(os.environ.get('MAX_CONCURRENT_DOWNLOADS', 3))
MAX_FILE_AGE_HOURS = int(os.environ.get('MAX_FILE_AGE_HOURS', 1))

app = Flask(__name__)
app.secret_key = os.environ.get('FLASK_SECRET_KEY', secrets.token_hex(32))
CORS(app)

# Rate limiting
limiter = Limiter(
    app=app,
    key_func=get_remote_address,
    default_limits=["200 per day", "50 per hour"]
)

# Thread-safe download management
class DownloadManager:
    def __init__(self, max_workers: int = 3):
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.download_status: Dict[str, DownloadProgress] = {}
        self.lock = threading.Lock()
        self.futures: Dict[str, Future] = {}
    
    def submit_download(self, job_id: str, url: str, format_str: str, file_ext: str) -> None:
        """Submit a download job to the thread pool"""
        with self.lock:
            if job_id in self.futures:
                raise ValueError(f"Job {job_id} already exists")
            
            future = self.executor.submit(download_worker, url, format_str, file_ext, job_id)
            self.futures[job_id] = future
    
    def get_job(self, job_id: str) -> Optional['DownloadProgress']:
        """Get job status in a thread-safe manner"""
        with self.lock:
            return self.download_status.get(job_id)
    
    def cleanup_completed(self) -> None:
        """Clean up completed jobs and their futures"""
        with self.lock:
            completed_jobs = []
            for job_id, future in self.futures.items():
                if future.done():
                    completed_jobs.append(job_id)
            
            for job_id in completed_jobs:
                self.futures.pop(job_id, None)
    
    def shutdown(self) -> None:
        """Shutdown the executor"""
        self.executor.shutdown(wait=False)

# Initialize download manager
download_manager = DownloadManager(max_workers=MAX_CONCURRENT_DOWNLOADS)

# Enhanced logging with rotation
class RotatingFileHandlerWithClear(logging.Handler):
    def __init__(self, filename, max_size_mb=10, backup_count=1, clear_interval=600):
        super().__init__()
        self.filename = filename
        self.max_size = max_size_mb * 1024 * 1024
        self.backup_count = backup_count
        self.clear_interval = clear_interval
        self.last_clear = time.time()
        self.setup_logging()
    
    def setup_logging(self):
        os.makedirs('logs', exist_ok=True)
        self.should_rollover = os.path.exists(self.filename) and os.path.getsize(self.filename) > self.max_size
        if self.should_rollover:
            self.rollover()
    
    def rollover(self):
        if self.backup_count > 0:
            for i in range(self.backup_count - 1, 0, -1):
                sfn = f"{self.filename}.{i}"
                dfn = f"{self.filename}.{i + 1}"
                if os.path.exists(sfn):
                    if os.path.exists(dfn):
                        os.remove(dfn)
                    os.rename(sfn, dfn)
            dfn = f"{self.filename}.1"
            if os.path.exists(self.filename):
                if os.path.exists(dfn):
                    os.remove(dfn)
                os.rename(self.filename, dfn)
    
    def emit(self, record):
        try:
            current_time = time.time()
            if current_time - self.last_clear > self.clear_interval:
                self.clear_log()
                self.last_clear = current_time
            
            if self.should_rollover:
                self.rollover()
                self.should_rollover = False
            
            msg = self.format(record)
            with open(self.filename, 'a', encoding='utf-8') as f:
                f.write(msg + '\n')
        except Exception:
            pass
    
    def clear_log(self):
        try:
            if os.path.exists(self.filename) and os.path.getsize(self.filename) > self.max_size:
                with open(self.filename, 'w', encoding='utf-8') as f:
                    f.truncate(0)
        except Exception:
            pass

# Setup enhanced logging
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

formatter = logging.Formatter('%(asctime)s - %(levelname)s - [%(threadName)s] - %(message)s')

# File handler with rotation and auto-clear
file_handler = RotatingFileHandlerWithClear('logs/ytdl.log', max_size_mb=10, clear_interval=600)
file_handler.setFormatter(formatter)
logger.addHandler(file_handler)

# Console handler
console_handler = logging.StreamHandler()
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)

# Thread-safe CAPTCHA and session management
class SecurityManager:
    def __init__(self):
        self.captcha_store: Dict[str, dict] = {}
        self.verified_sessions: Dict[str, dict] = {}
        self.lock = threading.Lock()
        self.captcha_secret = os.environ.get('CAPTCHA_SECRET', secrets.token_hex(32))
    
    def generate_captcha_hash(self, code: str) -> str:
        """Generate HMAC hash for CAPTCHA code"""
        return hmac.new(
            self.captcha_secret.encode(),
            code.encode(),
            hashlib.sha256
        ).hexdigest()
    
    def verify_captcha_hash(self, code: str, hash_value: str) -> bool:
        """Verify CAPTCHA code against stored hash"""
        expected_hash = self.generate_captcha_hash(code)
        return hmac.compare_digest(expected_hash, hash_value)
    
    def store_captcha(self, captcha_id: str, code: str, expires: datetime) -> None:
        """Store CAPTCHA data securely"""
        with self.lock:
            self.captcha_store[captcha_id] = {
                'hash': self.generate_captcha_hash(code),
                'expires': expires,
                'attempts': 0
            }
    
    def verify_captcha(self, captcha_id: str, user_input: str) -> tuple[bool, Optional[str]]:
        """Verify CAPTCHA input"""
        with self.lock:
            captcha_data = self.captcha_store.get(captcha_id)
            if not captcha_data:
                return False, "CAPTCHA expired or invalid"
            
            if datetime.now() > captcha_data['expires']:
                self.captcha_store.pop(captcha_id, None)
                return False, "CAPTCHA expired"
            
            # Limit attempts
            if captcha_data['attempts'] >= 3:
                self.captcha_store.pop(captcha_id, None)
                return False, "Too many failed attempts"
            
            is_valid = self.verify_captcha_hash(user_input, captcha_data['hash'])
            if is_valid:
                session_token = str(uuid.uuid4())
                self.verified_sessions[session_token] = {
                    'verified_at': datetime.now(),
                    'expires': datetime.now() + timedelta(minutes=10)
                }
                self.captcha_store.pop(captcha_id, None)
                return True, session_token
            else:
                captcha_data['attempts'] += 1
                return False, "Incorrect CAPTCHA code"
    
    def verify_session(self, session_token: str) -> bool:
        """Verify session token"""
        with self.lock:
            session_data = self.verified_sessions.get(session_token)
            if not session_data:
                return False
            
            if datetime.now() > session_data['expires']:
                self.verified_sessions.pop(session_token, None)
                return False
            
            return True
    
    def cleanup_expired(self) -> None:
        """Clean up expired CAPTCHAs and sessions"""
        with self.lock:
            now = datetime.now()
            
            # Clean expired CAPTCHAs
            expired_captchas = [
                key for key, data in self.captcha_store.items()
                if now > data['expires']
            ]
            for key in expired_captchas:
                self.captcha_store.pop(key, None)
            
            # Clean expired sessions
            expired_sessions = [
                key for key, data in self.verified_sessions.items()
                if now > data['expires']
            ]
            for key in expired_sessions:
                self.verified_sessions.pop(key, None)
            
            if expired_captchas or expired_sessions:
                logger.info("Cleaned up %d expired CAPTCHAs and %d expired sessions",
                           len(expired_captchas), len(expired_sessions))

# Initialize security manager
security_manager = SecurityManager()

class DownloadProgress:
    """Thread-safe download progress tracking"""
    def __init__(self):
        self._lock = threading.Lock()
        self._status = 'queued'
        self._progress = 0.0
        self._filename = ''
        self._error = ''
        self._temp_dir = ''
        self._ffmpeg_available = False
        self._title = ''
        self._completed = False
        self._downloaded_bytes = 0
        self._total_bytes = 0
        self._speed = 0
        self._eta = 0
        self._created_at = datetime.now()
    
    @property
    def status(self):
        with self._lock:
            return self._status
    
    @status.setter
    def status(self, value):
        with self._lock:
            self._status = value
    
    @property
    def progress(self):
        with self._lock:
            return self._progress
    
    @progress.setter
    def progress(self, value):
        with self._lock:
            self._progress = min(float(value), 99.9)
    
    @property
    def filename(self):
        with self._lock:
            return self._filename
    
    @filename.setter
    def filename(self, value):
        with self._lock:
            self._filename = value
    
    @property
    def error(self):
        with self._lock:
            return self._error
    
    @error.setter
    def error(self, value):
        with self._lock:
            self._error = value
    
    @property
    def temp_dir(self):
        with self._lock:
            return self._temp_dir
    
    @temp_dir.setter
    def temp_dir(self, value):
        with self._lock:
            self._temp_dir = value
    
    @property
    def ffmpeg_available(self):
        with self._lock:
            return self._ffmpeg_available
    
    @ffmpeg_available.setter
    def ffmpeg_available(self, value):
        with self._lock:
            self._ffmpeg_available = value
    
    @property
    def title(self):
        with self._lock:
            return self._title
    
    @title.setter
    def title(self, value):
        with self._lock:
            self._title = value
    
    @property
    def completed(self):
        with self._lock:
            return self._completed
    
    @completed.setter
    def completed(self, value):
        with self._lock:
            self._completed = value
    
    @property
    def downloaded_bytes(self):
        with self._lock:
            return self._downloaded_bytes
    
    @downloaded_bytes.setter
    def downloaded_bytes(self, value):
        with self._lock:
            self._downloaded_bytes = value
    
    @property
    def total_bytes(self):
        with self._lock:
            return self._total_bytes
    
    @total_bytes.setter
    def total_bytes(self, value):
        with self._lock:
            self._total_bytes = value
    
    @property
    def speed(self):
        with self._lock:
            return self._speed
    
    @speed.setter
    def speed(self, value):
        with self._lock:
            self._speed = value
    
    @property
    def eta(self):
        with self._lock:
            return self._eta
    
    @eta.setter
    def eta(self, value):
        with self._lock:
            self._eta = value
    
    @property
    def created_at(self):
        with self._lock:
            return self._created_at
    
    def to_dict(self):
        """Convert to dictionary for JSON response"""
        with self._lock:
            return {
                'status': self._status,
                'progress': self._progress,
                'filename': self._filename,
                'error': self._error,
                'ffmpeg_available': self._ffmpeg_available,
                'temp_dir': self._temp_dir,
                'downloaded_bytes': self._downloaded_bytes,
                'total_bytes': self._total_bytes,
                'speed': self._speed,
                'eta': self._eta,
                'downloaded_mb': self.bytes_to_mb(self._downloaded_bytes),
                'total_mb': self.bytes_to_mb(self._total_bytes),
                'speed_mb': self.bytes_to_mb(self._speed),
                'eta_formatted': self.format_eta(self._eta),
                'completed': self._completed
            }
    
    @staticmethod
    def bytes_to_mb(bytes_value):
        try:
            return round(bytes_value / (1024 * 1024), 2)
        except Exception:
            return 0
    
    @staticmethod
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

def check_ffmpeg() -> bool:
    """Reliable FFmpeg detection"""
    try:
        result = subprocess.run(
            ['ffmpeg', '-version'],
            capture_output=True,
            text=True,
            timeout=10
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError, Exception):
        return False

def progress_hook_factory(job_id: str):
    """Thread-safe progress hook for yt-dlp"""
    def hook(d: dict):
        job = download_manager.get_job(job_id)
        if not job or job.completed:
            return
        
        status = d.get('status')
        if status == 'downloading':
            job.status = 'downloading'
            
            # Update progress
            if d.get('total_bytes') and d.get('downloaded_bytes'):
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
            
            logger.info("Download finished for job %s: %s", job_id, d.get('filename', ''))
            
        elif status == 'error':
            if not job.completed:
                job.status = 'error'
                job.error = d.get('error', 'Unknown error reported by yt-dlp')
                logger.error("Download error for job %s: %s", job_id, job.error)
    
    return hook

def validate_format_string(format_str: str) -> bool:
    """Strict format validation for MP4/MP3 only"""
    if not format_str or not isinstance(format_str, str):
        return False
    
    # Allow only specific format patterns for MP4/MP3
    allowed_patterns = [
        r'^best\[height<=\d+\]$',
        r'^bestvideo\[height<=\d+\]+bestaudio/best$',
        r'^bestaudio/best$',
        r'^worst\[height<=\d+\]$',
        r'^worstvideo\[height<=\d+\]+worstaudio/worst$',
        r'^worstaudio/worst$',
        r'^\d+$'  # Format ID
    ]
    
    for pattern in allowed_patterns:
        if re.match(pattern, format_str):
            return True
    
    return False

def get_ytdlp_opts(temp_dir: str, job_id: str, format_str: str, file_ext: str, ffmpeg_available: bool) -> dict:
    """Get validated yt-dlp options for MP4/MP3 only"""
    base_opts = {
        'outtmpl': os.path.join(temp_dir, '%(title).100s.%(ext)s'),
        'progress_hooks': [progress_hook_factory(job_id)],
        'restrictfilenames': True,
        'quiet': False,
        'no_warnings': False,
        'nopart': True,
        'noplaylist': True,
        'extractor_retries': 3,
        'retries': 10,
        'fragment_retries': 10,
        'skip_unavailable_fragments': True,
        'continuedl': True,
        'http_headers': {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        },
    }
    
    # Use cookies if available
    if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
        try:
            base_opts['cookiefile'] = YTDL_COOKIES_PATH
            logger.info("Using cookies file for job %s", job_id)
        except Exception as e:
            logger.error("Failed to set cookies file: %s", e)
    
    # Format-specific options
    if file_ext == 'mp3':
        if ffmpeg_available:
            base_opts.update({
                'format': 'bestaudio/best',
                'postprocessors': [{
                    'key': 'FFmpegExtractAudio',
                    'preferredcodec': 'mp3',
                    'preferredquality': '192',
                }],
            })
        else:
            base_opts['format'] = 'bestaudio/best'
    else:  # MP4
        base_opts['format'] = format_str
        if ffmpeg_available and '+' in format_str:
            # Format requires merging video+audio
            base_opts['postprocessors'] = [{
                'key': 'FFmpegVideoConvertor',
                'preferedformat': 'mp4',
            }]
    
    return base_opts

def download_worker(url: str, format_str: str, file_ext: str, job_id: str) -> None:
    """Main download worker with comprehensive error handling"""
    # Initialize job
    with download_manager.lock:
        download_manager.download_status[job_id] = DownloadProgress()
    
    job = download_manager.get_job(job_id)
    if not job:
        logger.error("Download worker called with missing job_id: %s", job_id)
        return
    
    # Create temp directory
    temp_dir = tempfile.mkdtemp(prefix=f'ytdl_{job_id}_')
    job.temp_dir = temp_dir
    job.ffmpeg_available = check_ffmpeg()
    
    logger.info("Starting download job %s: %s -> %s", job_id, url, format_str)
    
    job.status = 'downloading'
    job.progress = 0.0
    
    max_retries = 2
    retry_count = 0
    
    while retry_count <= max_retries:
        try:
            ydl_opts = get_ytdlp_opts(temp_dir, job_id, format_str, file_ext, job.ffmpeg_available)
            
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=True)
                if isinstance(info, dict):
                    job.title = info.get('title', 'Unknown')
                
                # Find the downloaded file
                final_file = find_final_file(temp_dir, job.title)
                if final_file and os.path.exists(final_file):
                    job.filename = final_file
                    job.status = 'completed'
                    job.progress = 100.0
                    job.completed = True
                    
                    # Verify file size
                    try:
                        file_size = os.path.getsize(final_file)
                        if file_size < 1024:  # Less than 1KB
                            raise ValueError("File too small, likely corrupted")
                    except Exception as e:
                        logger.error("File verification failed for job %s: %s", job_id, e)
                        job.status = 'error'
                        job.error = 'Downloaded file is corrupted'
                        break
                    
                    logger.info("Download completed successfully for job %s: %s", job_id, final_file)
                    break
                else:
                    job.status = 'error'
                    job.error = 'Download completed but file not found'
                    logger.error("Final file not found for job %s in %s", job_id, temp_dir)
                    break
        
        except yt_dlp.utils.DownloadError as e:
            error_msg = str(e)
            logger.warning("Download error for job %s (attempt %d/%d): %s", 
                         job_id, retry_count + 1, max_retries + 1, error_msg)
            
            if retry_count < max_retries:
                retry_count += 1
                wait_time = min(2 ** retry_count, 10)
                logger.info("Retrying job %s in %d seconds...", job_id, wait_time)
                time.sleep(wait_time)
                continue
            else:
                job.status = 'error'
                job.error = f'Download failed: {error_msg}'
                break
        
        except Exception as e:
            logger.exception("Unexpected error in download worker for job %s: %s", job_id, e)
            job.status = 'error'
            job.error = f'Unexpected error: {str(e)}'
            break
    
    # Cleanup on failure
    if job.status == 'error' and os.path.exists(temp_dir):
        try:
            shutil.rmtree(temp_dir)
            logger.info("Cleaned up temp directory for failed job %s", job_id)
        except Exception as e:
            logger.error("Error cleaning up temp dir for job %s: %s", job_id, e)
    
    job.completed = True

def find_final_file(temp_dir: str, title_hint: str = None) -> Optional[str]:
    """Find the final downloaded file in temp directory"""
    if not os.path.isdir(temp_dir):
        return None
    
    try:
        files = [
            os.path.join(temp_dir, f) 
            for f in os.listdir(temp_dir) 
            if os.path.isfile(os.path.join(temp_dir, f)) and not f.endswith('.part')
        ]
        
        if not files:
            return None
        
        # Prefer files matching the title
        if title_hint:
            normalized_title = re.sub(r'[^\w\s-]', '', title_hint)[:50]
            matching_files = [f for f in files if normalized_title.lower() in os.path.basename(f).lower()]
            if matching_files:
                # Return largest matching file
                return max(matching_files, key=lambda f: os.path.getsize(f))
        
        # Return largest file
        return max(files, key=lambda f: os.path.getsize(f))
        
    except Exception as e:
        logger.error("Error finding final file in %s: %s", temp_dir, e)
        return None

def generate_captcha_image(captcha_code: str) -> Optional[str]:
    """Generate CAPTCHA image with enhanced security"""
    try:
        width, height = 220, 100
        image = Image.new('RGB', (width, height), color=(255, 255, 255))
        draw = ImageDraw.Draw(image)
        
        # Load font
        font_size = 36
        try:
            font_paths = [
                "arial.ttf",
                "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
                "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
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
        
        # Add noise and distortion
        for _ in range(150):
            x = random.randint(0, width)
            y = random.randint(0, height)
            draw.point((x, y), fill=(
                random.randint(200, 255),
                random.randint(200, 255),
                random.randint(200, 255)
            ))
        
        for _ in range(10):
            x1 = random.randint(0, width)
            y1 = random.randint(0, height)
            x2 = random.randint(0, width)
            y2 = random.randint(0, height)
            draw.line([(x1, y1), (x2, y2)], 
                     fill=(random.randint(150, 200), random.randint(150, 200), random.randint(150, 200)), 
                     width=2)
        
        # Draw text with distortion
        text_bbox = draw.textbbox((0, 0), captcha_code, font=font)
        text_width = text_bbox[2] - text_bbox[0]
        text_height = text_bbox[3] - text_bbox[1]
        
        x = (width - text_width) // 2
        y = (height - text_height) // 2 - 5
        
        for i, char in enumerate(captcha_code):
            char_x = x + i * (text_width // len(captcha_code)) + random.randint(-2, 2)
            char_y = y + random.randint(-3, 3)
            
            color = (random.randint(0, 100), random.randint(0, 100), random.randint(0, 100))
            draw.text((char_x, char_y), char, font=font, fill=color)
        
        # Apply blur
        image = image.filter(ImageFilter.GaussianBlur(radius=0.5))
        
        # Convert to base64
        img_byte_arr = io.BytesIO()
        image.save(img_byte_arr, format='PNG', optimize=True)
        img_base64 = base64.b64encode(img_byte_arr.getvalue()).decode('utf-8')
        
        return f"data:image/png;base64,{img_base64}"
        
    except Exception as e:
        logger.error("Error generating CAPTCHA image: %s", e)
        return None

def cleanup_old_downloads():
    """Clean up old downloads and temp files"""
    try:
        now = time.time()
        max_age = MAX_FILE_AGE_HOURS * 3600
        
        with download_manager.lock:
            jobs_to_remove = []
            
            for job_id, job in download_manager.download_status.items():
                try:
                    # Remove jobs older than max age
                    job_age = now - job.created_at.timestamp()
                    if job_age > max_age:
                        jobs_to_remove.append(job_id)
                        
                        # Clean up temp directory
                        if job.temp_dir and os.path.exists(job.temp_dir):
                            shutil.rmtree(job.temp_dir)
                            logger.info("Cleaned up old temp dir: %s", job.temp_dir)
                
                except Exception as e:
                    logger.error("Error cleaning up job %s: %s", job_id, e)
            
            # Remove old jobs
            for job_id in jobs_to_remove:
                download_manager.download_status.pop(job_id, None)
                download_manager.futures.pop(job_id, None)
        
        # Clean up expired security data
        security_manager.cleanup_expired()
        
        # Clean up completed futures
        download_manager.cleanup_completed()
        
        logger.info("Cleanup completed: removed %d old jobs", len(jobs_to_remove))
        
    except Exception as e:
        logger.error("Error in cleanup_old_downloads: %s", e)

def schedule_cleanup():
    """Schedule periodic cleanup"""
    try:
        cleanup_old_downloads()
    except Exception as e:
        logger.error("Error in scheduled cleanup: %s", e)
    finally:
        # Schedule next cleanup in 30 minutes
        threading.Timer(1800, schedule_cleanup).start()

# API Routes
@app.route('/api/generate-captcha')
@limiter.limit("10 per minute")
def generate_captcha():
    """Generate new CAPTCHA"""
    try:
        captcha_code = str(random.randint(1000, 9999))
        captcha_id = str(uuid.uuid4())
        expires = datetime.now() + timedelta(minutes=5)
        
        # Store CAPTCHA securely
        security_manager.store_captcha(captcha_id, captcha_code, expires)
        
        # Generate image
        captcha_image = generate_captcha_image(captcha_code)
        
        response_data = {
            'captcha_id': captcha_id,
            'captcha_image': captcha_image
        }
        
        logger.info("Generated CAPTCHA with ID: %s", captcha_id)
        return jsonify(response_data)
        
    except Exception as e:
        logger.error("Error generating CAPTCHA: %s", e)
        return jsonify({'error': 'Failed to generate CAPTCHA'}), 500

@app.route('/api/verify-captcha', methods=['POST'])
@limiter.limit("10 per minute")
def verify_captcha():
    """Verify CAPTCHA input"""
    try:
        data = request.get_json() or {}
        captcha_id = data.get('captcha_id')
        user_input = data.get('captcha_input')
        
        if not captcha_id or not user_input:
            return jsonify({'error': 'CAPTCHA ID and input required'}), 400
        
        is_valid, result = security_manager.verify_captcha(captcha_id, user_input)
        
        if is_valid:
            logger.info("CAPTCHA verification successful for ID: %s", captcha_id)
            return jsonify({'valid': True, 'session_token': result})
        else:
            logger.warning("CAPTCHA verification failed for ID: %s", captcha_id)
            return jsonify({'valid': False, 'error': result})
            
    except Exception as e:
        logger.error("Error verifying CAPTCHA: %s", e)
        return jsonify({'error': 'Failed to verify CAPTCHA'}), 500

@app.route('/api/ffmpeg-status')
def get_ffmpeg_status():
    return jsonify({'ffmpeg_available': check_ffmpeg()})

@app.route('/api/video-info', methods=['POST'])
@limiter.limit("20 per minute")
def get_video_info():
    """Get video information"""
    data = request.get_json() or {}
    url = data.get('url')
    
    if not url:
        return jsonify({'error': 'URL is required'}), 400
    
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': False,
            'skip_download': True,
        }
        
        if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
            ydl_opts['cookiefile'] = YTDL_COOKIES_PATH
        
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            
            if not isinstance(info, dict):
                return jsonify({'error': 'Invalid video information'}), 400
            
            # Filter formats to only MP4/MP3 compatible
            formats = []
            for f in info.get('formats', []):
                if f.get('format_id'):
                    # Only include formats that can be converted to MP4/MP3
                    ext = f.get('ext', '').lower()
                    vcodec = f.get('vcodec', 'none')
                    acodec = f.get('acodec', 'none')
                    
                    # Include video formats (for MP4) and audio formats (for MP3)
                    if (vcodec != 'none' and ext in ['mp4', 'webm', 'avi', 'mov']) or \
                       (acodec != 'none' and ext in ['m4a', 'webm', 'mp3', 'ogg']):
                        
                        format_type = 'audio' if vcodec == 'none' else 'video'
                        resolution = f"{f.get('height', '')}p" if f.get('height') else 'Audio'
                        
                        formats.append({
                            'format_id': f.get('format_id'),
                            'ext': ext,
                            'resolution': resolution,
                            'quality': f.get('format_note', 'Unknown'),
                            'vcodec': vcodec,
                            'acodec': acodec,
                            'type': format_type
                        })
            
            video_info = {
                'title': info.get('title', 'Unknown'),
                'duration': info.get('duration', 0),
                'thumbnail': info.get('thumbnail', ''),
                'channel': info.get('uploader', 'Unknown'),
                'view_count': info.get('view_count', 0),
                'formats': formats
            }
            
            return jsonify(video_info)
        
    except yt_dlp.utils.DownloadError as e:
        logger.error("DownloadError fetching video info: %s", e)
        return jsonify({'error': 'Failed to fetch video information'}), 400
    except Exception as e:
        logger.error("Error fetching video info: %s", e)
        return jsonify({'error': 'Failed to fetch video information'}), 500

@app.route('/api/download', methods=['POST'])
@limiter.limit("5 per minute")
def download_video():
    """Start download with CAPTCHA verification"""
    data = request.get_json() or {}
    url = data.get('url')
    format_str = data.get('format')
    file_ext = data.get('file_ext', 'mp4')
    session_token = data.get('session_token')
    
    # Validate inputs
    if not url or not format_str:
        return jsonify({'error': 'URL and format are required'}), 400
    
    if not session_token or not security_manager.verify_session(session_token):
        return jsonify({'error': 'CAPTCHA verification required or expired'}), 403
    
    if not validate_format_string(format_str):
        return jsonify({'error': 'Invalid format specification'}), 400
    
    if file_ext not in ['mp4', 'mp3']:
        return jsonify({'error': 'Invalid file extension. Only MP4 and MP3 are supported.'}), 400
    
    # Check concurrent download limit
    with download_manager.lock:
        active_downloads = len([f for f in download_manager.futures.values() if not f.done()])
        if active_downloads >= MAX_CONCURRENT_DOWNLOADS:
            return jsonify({'error': 'Server busy. Please try again later.'}), 429
    
    # Create download job
    job_id = str(uuid.uuid4())
    
    try:
        download_manager.submit_download(job_id, url, format_str, file_ext)
        logger.info("Started download job %s for URL: %s", job_id, url)
        
        return jsonify({
            'job_id': job_id,
            'ffmpeg_available': download_manager.get_job(job_id).ffmpeg_available
        })
        
    except Exception as e:
        logger.error("Error starting download job: %s", e)
        return jsonify({'error': 'Failed to start download'}), 500

@app.route('/api/download-status/<job_id>')
def get_download_status(job_id):
    """Get download status"""
    job = download_manager.get_job(job_id)
    if not job:
        return jsonify({'error': 'Download job not found'}), 404
    
    return jsonify(job.to_dict())

@app.route('/api/download-file/<job_id>')
@limiter.limit("10 per minute")
def download_file(job_id):
    """Download completed file"""
    job = download_manager.get_job(job_id)
    if not job:
        return jsonify({'error': 'Download job not found'}), 404
    
    if job.status != 'completed':
        return jsonify({'error': 'File not ready', 'status': job.status}), 400
    
    filename = job.filename
    if not filename or not os.path.exists(filename):
        # Try to find the file
        filename = find_final_file(job.temp_dir, job.title)
        if not filename or not os.path.exists(filename):
            return jsonify({'error': 'File not found on server'}), 404
    
    original_filename = os.path.basename(filename)
    
    # Schedule cleanup after download
    def schedule_cleanup():
        time.sleep(300)  # 5 minutes
        try:
            if job.temp_dir and os.path.exists(job.temp_dir):
                shutil.rmtree(job.temp_dir)
                logger.info("Cleaned up temp dir for job %s", job_id)
        except Exception as e:
            logger.error("Error cleaning up temp dir for job %s: %s", job_id, e)
        
        with download_manager.lock:
            download_manager.download_status.pop(job_id, None)
            download_manager.futures.pop(job_id, None)
    
    threading.Thread(target=schedule_cleanup, daemon=True).start()
    
    mimetype = 'video/mp4' if filename.lower().endswith('.mp4') else 'audio/mpeg'
    
    return send_file(
        filename,
        as_attachment=True,
        download_name=original_filename,
        mimetype=mimetype
    )

@app.route('/')
def health_check():
    """Health check endpoint"""
    with download_manager.lock:
        active_downloads = len([f for f in download_manager.futures.values() if not f.done()])
        total_jobs = len(download_manager.download_status)
    
    return jsonify({
        'status': 'healthy',
        'service': 'YTDL API Server',
        'timestamp': datetime.now().isoformat(),
        'active_downloads': active_downloads,
        'total_jobs': total_jobs,
        'cookies_configured': bool(YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH)),
        'ffmpeg_available': check_ffmpeg(),
        'max_concurrent_downloads': MAX_CONCURRENT_DOWNLOADS
    })

@app.route('/api/queue-status')
def queue_status():
    """Get queue status"""
    with download_manager.lock:
        active_downloads = len([f for f in download_manager.futures.values() if not f.done()])
        queued_jobs = len(download_manager.futures) - active_downloads
    
    return jsonify({
        'active_downloads': active_downloads,
        'queued_jobs': queued_jobs,
        'max_concurrent': MAX_CONCURRENT_DOWNLOADS
    })

# Startup and shutdown
def startup():
    """Application startup tasks"""
    print("\n" + "="*60)
    print("🚀 YTDL API Server Starting...")
    print("="*60)
    
    # Check dependencies
    ffmpeg_available = check_ffmpeg()
    if ffmpeg_available:
        print("✅ FFmpeg is available - Full functionality enabled")
    else:
        print("⚠️  FFmpeg not found - MP3 conversion will be limited")
    
    # Check cookies
    if YTDL_COOKIES_PATH and os.path.exists(YTDL_COOKIES_PATH):
        print(f"✅ Cookies file found: {YTDL_COOKIES_PATH}")
    else:
        print("❌ Cookies file not found - bot detection may occur")
    
    print(f"✅ Maximum concurrent downloads: {MAX_CONCURRENT_DOWNLOADS}")
    print("✅ Security system initialized")
    print("✅ Download manager ready")
    print("="*60)
    
    # Start cleanup scheduler
    schedule_cleanup()

@app.before_request
def before_request():
    """Pre-request processing"""
    pass

def shutdown():
    """Application shutdown tasks"""
    logger.info("Shutting down download manager...")
    download_manager.shutdown()

# Register shutdown handler
import atexit
atexit.register(shutdown)

if __name__ == '__main__':
    startup()
    
    port = int(os.environ.get('PORT', 5000))
    debug = os.environ.get('DEBUG', 'false').lower() == 'true'
    
    logger.info("Starting YTDL API Server on port %d", port)
    
    app.run(
        debug=debug,
        host='0.0.0.0', 
        port=port, 
        use_reloader=False,
        threaded=True
    )
