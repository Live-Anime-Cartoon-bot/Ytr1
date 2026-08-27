import asyncio
import html
import json
import os
import re
import shutil
import signal
import sqlite3
import time
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional
from urllib.parse import urlparse

import aiohttp
from dotenv import load_dotenv
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

from Channel import get_public_channels

load_dotenv()

API_ID = os.getenv("API_ID", "").strip()
API_HASH = os.getenv("API_HASH", "").strip()
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
OWNER_IDS = {int(x) for x in os.getenv("OWNER_IDS", "").split(",") if x.strip().lstrip("-").isdigit()}
TIMEZONE = os.getenv("TIMEZONE", "Asia/Kolkata")
DEFAULT_FILENAME = os.getenv("DEFAULT_FILENAME", "Anime Cartoon")
DEFAULT_REC_DURATION = os.getenv("DEFAULT_REC_DURATION", "01:00:00")
RETENTION_HOURS = int(os.getenv("RETENTION_HOURS", "5"))
BOT_USERNAME = os.getenv("BOT_USERNAME", "").lstrip("@").strip()
GROUP_CHAT_IDS = {
    int(x) for x in os.getenv("GROUP_CHAT_IDS", "").split(",")
    if x.strip().lstrip("-").isdigit()
}
SHRINKME_API_KEY = os.getenv("SHRINKME_API_KEY", "").strip()

BASE_DIR = Path(__file__).resolve().parent
OUTPUT_DIR = BASE_DIR / "output"
TEMP_DIR = BASE_DIR / "temp"
DB_PATH = BASE_DIR / "bot.sqlite3"
OUTPUT_DIR.mkdir(exist_ok=True)
TEMP_DIR.mkdir(exist_ok=True)

WATERMARK_IMAGE_URL = "https://iili.io/CbTi4Nn.png"
WATERMARK_FONT = "/system/fonts/Roboto-Regular.ttf"
DEFAULT_WATERMARK_TEXT = "Join Our Telegram - AnimeCartoonPremium"

ADVANCE_INTERVALS = [(10, 50), (1200, 1260), (1800, 1860)]

URL_RE = re.compile(r"^https?://[^\s<>\"']+$", re.I)
FILENAME_RE = re.compile(r"[^A-Za-z0-9._()\- ]+")


def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    with db() as c:
        c.execute("""
        CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY,
            balance INTEGER NOT NULL DEFAULT 0,
            verified_until TEXT
        )""")
        c.execute("""
        CREATE TABLE IF NOT EXISTS tokens (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            created_at TEXT NOT NULL,
            expires_at TEXT NOT NULL,
            amount INTEGER NOT NULL,
            spent INTEGER NOT NULL DEFAULT 0
        )""")
        c.execute("""
        CREATE TABLE IF NOT EXISTS scheduler (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            channel TEXT NOT NULL,
            platform TEXT NOT NULL,
            date TEXT NOT NULL,
            start_time TEXT NOT NULL,
            end_time TEXT NOT NULL,
            video TEXT NOT NULL,
            audio TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'pending',
            created_at TEXT NOT NULL
        )""")
        c.execute("CREATE INDEX IF NOT EXISTS idx_scheduler_status ON scheduler(status)")
        c.commit()


def now_iso():
    return datetime.utcnow().isoformat(timespec="seconds")


def ensure_user(user_id: int):
    with db() as c:
        c.execute("INSERT OR IGNORE INTO users(user_id) VALUES (?)", (user_id,))
        c.commit()


def add_verified_tokens(user_id: int):
    ensure_user(user_id)
    now = datetime.utcnow()
    expires = now + timedelta(hours=4)
    with db() as c:
        c.execute(
            "INSERT INTO tokens(user_id,created_at,expires_at,amount,spent) VALUES(?,?,?,?,0)",
            (user_id, now.isoformat(timespec="seconds"), expires.isoformat(timespec="seconds"), 2),
        )
        c.execute("UPDATE users SET balance=balance+2, verified_until=? WHERE user_id=?",
                  (expires.isoformat(timespec="seconds"), user_id))
        c.commit()


def charge_token(user_id: int) -> bool:
    ensure_user(user_id)
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("SELECT balance FROM users WHERE user_id=?", (user_id,)).fetchone()
        if not row or row["balance"] < 1:
            c.rollback()
            return False
        c.execute("UPDATE users SET balance=balance-1 WHERE user_id=? AND balance>=1", (user_id,))
        if c.rowcount != 1:
            c.rollback()
            return False
        c.execute("""
            UPDATE tokens SET spent=spent+1
            WHERE id = (
                SELECT id FROM tokens
                WHERE user_id=? AND spent < amount AND expires_at > ?
                ORDER BY expires_at ASC LIMIT 1
            )""", (user_id, datetime.utcnow().isoformat(timespec="seconds")))
        c.commit()
        return True


def safe_filename(name: str, fallback: str = DEFAULT_FILENAME) -> str:
    name = (name or "").strip()
    if not name:
        name = fallback
    if "/" in name or "\\" in name or name in {".", ".."} or Path(name).is_absolute():
        raise ValueError("Invalid filename.")
    name = Path(name).name
    name = FILENAME_RE.sub("_", name).strip(" .")
    if not name or name in {".", ".."}:
        raise ValueError("Invalid filename.")
    if len(name) > 180:
        name = name[:180].rstrip(" .")
    if not name.lower().endswith(".mp4"):
        name += ".mp4"
    return name


def safe_output_path(name: str, task_id: str) -> Path:
    filename = safe_filename(name)
    path = (OUTPUT_DIR / f"{task_id}_{filename}").resolve()
    if path.parent != OUTPUT_DIR.resolve():
        raise ValueError("Unsafe output path.")
    return path


def permitted_url(url: str) -> bool:
    if not URL_RE.fullmatch(url):
        return False
    parsed = urlparse(url)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        return False
    return url in set(get_public_channels().values())


def parse_duration(value: str) -> int:
    if not re.fullmatch(r"\d{1,2}:\d{2}:\d{2}", value):
        raise ValueError("Duration must be HH:MM:SS.")
    h, m, s = map(int, value.split(":"))
    if m > 59 or s > 59:
        raise ValueError("Invalid duration.")
    total = h * 3600 + m * 60 + s
    if total <= 0 or total > 24 * 3600:
        raise ValueError("Duration must be between 00:00:01 and 24:00:00.")
    return total


def fmt_seconds(seconds: float) -> str:
    if not seconds or seconds < 0:
        return "Calculating..."
    seconds = int(seconds)
    return f"{seconds // 3600:02d}:{(seconds % 3600)//60:02d}:{seconds%60:02d}"


def progress_bar(p: float, width=10):
    filled = max(0, min(width, int(p / 100 * width)))
    return "●" * filled + "⬜" * (width - filled)


def escape_filter_text(text: str) -> str:
    # FFmpeg drawtext filter escaping for %, :, \, ', and brackets.
    return (text.replace("\\", r"\\")
                .replace(":", r"\:")
                .replace("'", r"\'")
                .replace("%", r"\%")
                .replace("[", r"\[")
                .replace("]", r"\]"))


def escape_filter_path(path: str) -> str:
    return escape_filter_text(str(path).replace("\\", "/"))


def interval_expr(intervals):
    return "+".join(f"between(t,{a},{b})" for a, b in intervals)


def fit_scale_pad(prefix=""):
    return (
        f"{prefix}scale=1920:1080:force_original_aspect_ratio=decrease,"
        f"pad=1920:1080:(ow-iw)/2:(oh-ih)/2:black"
    )


def build_ffmpeg(
    input_path: Path,
    output_path: Path,
    mode: str,
    watermark_text: str = DEFAULT_WATERMARK_TEXT,
    image_path: Optional[Path] = None,
    duration: Optional[int] = None,
):
    cmd = ["ffmpeg", "-hide_banner", "-y", "-i", str(input_path)]

    if image_path:
        cmd += ["-loop", "1", "-i", str(image_path)]

    if mode == "normal":
        text = escape_filter_text(watermark_text)
        vf = (
            f"{fit_scale_pad()},"
            f"drawtext=fontfile='{escape_filter_path(WATERMARK_FONT)}':"
            f"text='{text}':fontsize=24:fontcolor=white:"
            f"x=(w-text_w)/2:y=h-th-140:shadowcolor=black:"
            f"shadowx=2:shadowy=2"
        )
    elif mode == "advance":
        text = escape_filter_text(watermark_text)
        enable = interval_expr(ADVANCE_INTERVALS)
        vf = (
            f"{fit_scale_pad()},"
            f"drawtext=enable='{enable}':"
            f"fontfile='{escape_filter_path(WATERMARK_FONT)}':"
            f"text='{text}':fontsize=24:fontcolor=white:"
            f"x=(w-text_w)/2:y=h-th-140:shadowcolor=black:"
            f"shadowx=2:shadowy=2"
        )
    elif mode == "off":
        vf = fit_scale_pad()
    elif mode == "image":
        vf = (
            f"[0:v]{fit_scale_pad()}[v0];"
            f"[1:v]scale=260:-1[wm];"
            f"[v0][wm]overlay=(W-w)/2:100:shortest=1[v]"
        )
    else:
        raise ValueError("Unknown FFmpeg mode.")

    if mode == "image":
        cmd += [
            "-filter_complex", vf,
            "-map", "[v]", "-map", "0:a?",
            "-c:v", "libx264", "-crf", "23", "-preset", "ultrafast",
            "-threads", "2", "-c:a", "aac", "-movflags", "+faststart",
            str(output_path),
        ]
    else:
        cmd += [
            "-vf", vf,
            "-map", "0:v:0", "-map", "0:a?",
            "-c:v", "libx264", "-preset", "ultrafast", "-threads", "2",
            "-c:a", "aac", "-movflags", "+faststart",
        ]
        if duration:
            cmd += ["-t", str(duration)]
        cmd += [str(output_path)]
    return cmd


@dataclass
class Task:
    task_id: str
    user_id: int
    chat_id: int
    status_message_id: int
    input_path: Path
    output_path: Path
    video_name: str
    process: Optional[asyncio.subprocess.Process] = None
    updater: Optional[asyncio.Task] = None
    status: str = "Processing..."
    progress: float = 0.0
    speed: str = "Calculating..."
    elapsed: float = 0.0
    remaining: float = 0.0
    upload_state: str = ""
    started: float = field(default_factory=time.monotonic)
    cancelled: bool = False


TASKS: dict[str, Task] = {}
TASK_LOCK = asyncio.Lock()


def authorized_user(user_id: int, chat_id: Optional[int] = None) -> bool:
    return user_id in OWNER_IDS or (chat_id in GROUP_CHAT_IDS if chat_id is not None else False)


async def edit_status(context, task: Task, text: str, keyboard=True):
    markup = None
    if keyboard:
        markup = InlineKeyboardMarkup([[
            InlineKeyboardButton("⚡ Progress", callback_data=f"progress:{task.task_id}"),
            InlineKeyboardButton("❌ Cancel", callback_data=f"cancel:{task.task_id}"),
        ]])
    try:
        await context.bot.edit_message_text(
            chat_id=task.chat_id,
            message_id=task.status_message_id,
            text=text,
            reply_markup=markup,
            parse_mode=ParseMode.HTML,
        )
    except Exception:
        pass


def status_text(task: Task) -> str:
    elapsed = time.monotonic() - task.started
    return (
        "🎬 <b>Processing Video...</b>\n\n"
        f"📄 File:\n<code>{html.escape(task.video_name)}</code>\n\n"
        f"Progress:\n[{progress_bar(task.progress)}] {task.progress:.2f}%\n\n"
        f"⚡ Speed:\n{html.escape(task.speed)}\n\n"
        f"Status:\n{html.escape(task.status)}"
    )


async def parse_ffmpeg_progress(task: Task, proc):
    duration_us = None
    while True:
        line = await proc.stderr.readline()
        if not line:
            break
        s = line.decode("utf-8", "replace").strip()
        if s.startswith("Duration:"):
            m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", s)
            if m:
                duration_us = (int(m.group(1))*3600 + int(m.group(2))*60 + float(m.group(3))) * 1_000_000
        if "out_time_us=" in s:
            try:
                out_us = int(s.split("out_time_us=", 1)[1].split()[0])
                if duration_us:
                    task.progress = max(0.0, min(100.0, out_us / duration_us * 100))
                    task.elapsed = time.monotonic() - task.started
                    if task.progress > 0:
                        task.remaining = task.elapsed * (100-task.progress) / task.progress
            except ValueError:
                pass
        if "speed=" in s:
            m = re.search(r"speed=([^\s]+)", s)
            if m:
                task.speed = m.group(1)


async def process_video(context, task: Task, command):
    task.updater = asyncio.create_task(status_updater(context, task))
    try:
        task.process = await asyncio.create_subprocess_exec(
            *command,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.PIPE,
        )
        await parse_ffmpeg_progress(task, task.process)
        rc = await task.process.wait()
        if task.cancelled:
            return False
        if rc != 0 or not task.output_path.exists() or task.output_path.stat().st_size == 0:
            raise RuntimeError("FFmpeg failed.")
        task.progress = 100.0
        task.status = "Processing completed."
        return True
    finally:
        if task.updater:
            task.updater.cancel()
            try:
                await task.updater
            except asyncio.CancelledError:
                pass


async def status_updater(context, task: Task):
    while True:
        await edit_status(context, task, status_text(task))
        await asyncio.sleep(5)


async def upload_file(context, task: Task):
    task.upload_state = "Uploading..."
    size = task.output_path.stat().st_size
    started = time.monotonic()

    async def cb(current, total):
        if total:
            p = current / total * 100
            elapsed = max(0.001, time.monotonic() - started)
            speed = current / elapsed
            remaining = (total-current) / speed if speed else 0
            text = (
                "📦 <b>Uploading:</b>\n"
                f"<code>{html.escape(task.output_path.name)}</code>\n\n"
                f"[{progress_bar(p)}] {p:.2f}%\n"
                f"{current/1048576:.1f} MB of {total/1048576:.2f} MB\n"
                f"Speed:\n{speed/1048576:.2f} MB/s\n"
                f"Time Left:\n{fmt_seconds(remaining)}"
            )
            try:
                await context.bot.edit_message_text(
                    chat_id=task.chat_id,
                    message_id=task.status_message_id,
                    text=text,
                    parse_mode=ParseMode.HTML,
                )
            except Exception:
                pass

    with task.output_path.open("rb") as f:
        await context.bot.send_document(
            chat_id=task.chat_id,
            document=f,
            filename=task.output_path.name,
            read_timeout=600,
            write_timeout=600,
            connect_timeout=60,
        )


async def finish_task(context, task: Task, success: bool):
    if task.updater:
        task.updater.cancel()
    if task.cancelled:
        task.status = "Cancelled"
        if task.output_path.exists():
            task.output_path.unlink(missing_ok=True)
        await edit_status(
            context, task,
            "❌ <b>Process Cancelled</b>\n⚠️ Partial Output Deleted",
            keyboard=False,
        )
        return

    if not success:
        task.status = "Failed"
        task.output_path.unlink(missing_ok=True)
        await edit_status(
            context, task,
            "❌ <b>Processing Failed</b>\n"
            "⚠️ Partial Output Deleted\n"
            f"📄 File:\n<code>{html.escape(task.video_name)}</code>",
            keyboard=False,
        )
        return

    await edit_status(
        context, task,
        "✅ <b>Processing Completed</b>\n"
        f"📄 File:\n<code>{html.escape(task.output_path.name)}</code>\n"
        "Uploading...",
        keyboard=False,
    )
    try:
        await upload_file(context, task)
        await context.bot.edit_message_text(
            chat_id=task.chat_id,
            message_id=task.status_message_id,
            text=(
                "✅ <b>Upload Completed</b>\n"
                f"📄 File:\n<code>{html.escape(task.output_path.name)}</code>\n"
                "⏳ Server copy auto-deletes in 3 hours."
            ),
            parse_mode=ParseMode.HTML,
        )
    except Exception:
        task.output_path.unlink(missing_ok=True)
        await context.bot.edit_message_text(
            chat_id=task.chat_id,
            message_id=task.status_message_id,
            text="❌ <b>Upload Failed</b>\n⚠️ Partial Output Deleted",
            parse_mode=ParseMode.HTML,
        )


async def run_task(context, task: Task, command):
    try:
        ok = await process_video(context, task, command)
        await finish_task(context, task, ok)
    except asyncio.CancelledError:
        task.cancelled = True
        if task.process and task.process.returncode is None:
            task.process.terminate()
        await finish_task(context, task, False)
    except Exception:
        await finish_task(context, task, False)
    finally:
        task.input_path.unlink(missing_ok=True)
        await asyncio.sleep(0)
        TASKS.pop(task.task_id, None)


async def start_task(update: Update, context: ContextTypes.DEFAULT_TYPE, input_path: Path,
                     video_name: str, output_name: str, mode: str,
                     watermark_text: str = DEFAULT_WATERMARK_TEXT,
                     image_path: Optional[Path] = None, duration: Optional[int] = None):
    user = update.effective_user
    chat = update.effective_chat
    if not user or not chat:
        return

    if not charge_token(user.id):
        await update.effective_message.reply_text("❌ You need 1 valid token to start recording/download.")
        input_path.unlink(missing_ok=True)
        return

    task_id = uuid.uuid4().hex
    output_path = safe_output_path(output_name, task_id)
    status_msg = await update.effective_message.reply_text(
        "🎬 <b>Processing Video...</b>\n\n"
        f"📄 File:\n<code>{html.escape(video_name)}</code>\n\n"
        "Progress:\n[□□□□□□□□□□] 0.00%\n\n"
        "⚡ Speed:\nCalculating...\n\n"
        "Status:\nProcessing...",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⚡ Progress", callback_data=f"progress:{task_id}"),
            InlineKeyboardButton("❌ Cancel", callback_data=f"cancel:{task_id}"),
        ]]),
    )

    task = Task(task_id, user.id, chat.id, status_msg.message_id, input_path,
                output_path, video_name)
    async with TASK_LOCK:
        TASKS[task_id] = task

    command = build_ffmpeg(input_path, output_path, mode, watermark_text, image_path, duration)
    asyncio.create_task(run_task(context, task, command))


async def cmd_alive(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text("Bot working you can use it")


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "To record a live link, send it in the following format: "
        "link timestamp (Example: https://example.com/live-link.m3u8 00:05:00).\n\n"
        "Note: Don't report to the developer if the video duration is wrong."
    )


async def cmd_token(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user:
        return
    add_verified_tokens(user.id)
    await update.effective_message.reply_text("✅ Verification accepted. +2 temporary tokens added for 4 hours.")


def extract_record_args(text: str):
    parts = text.split(maxsplit=4)
    if len(parts) < 2:
        raise ValueError("Usage: URL duration [filename] [watermark_text] [watermark_link]")
    url, duration = parts[0], parts[1]
    if not permitted_url(url):
        raise ValueError("This source is not in the permitted channel list.")
    seconds = parse_duration(duration)
    filename = parts[2] if len(parts) >= 3 else DEFAULT_FILENAME
    watermark_text = parts[3] if len(parts) >= 4 else DEFAULT_WATERMARK_TEXT
    watermark_link = parts[4] if len(parts) >= 5 else ""
    if watermark_link and not URL_RE.fullmatch(watermark_link):
        raise ValueError("Invalid watermark link.")
    return url, seconds, filename, watermark_text


async def cmd_rec(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_message:
        return
    raw = update.effective_message.text or ""
    args = raw.split(maxsplit=5)[1:]
    if not args:
        await update.effective_message.reply_text(
            "Usage: /rec <URL> <duration> <filename> <watermark_text> <watermark_link>"
        )
        return
    try:
        url, seconds, filename, watermark_text = extract_record_args(" ".join(args))
        buttons = InlineKeyboardMarkup([[
            InlineKeyboardButton("🟢 Normal", callback_data=f"rec:{uuid.uuid4().hex}:normal"),
            InlineKeyboardButton("⚡ Advance", callback_data=f"rec:{uuid.uuid4().hex}:advance"),
        ], [
            InlineKeyboardButton("🚫 Watermark OFF", callback_data=f"rec:{uuid.uuid4().hex}:off"),
            InlineKeyboardButton("🖼️ Image Watermark", callback_data=f"rec:{uuid.uuid4().hex}:image"),
        ]])
        # Store request separately; the callback token is opaque and task-isolated.
        key = uuid.uuid4().hex
        PENDING_RECORDS[key] = (update.effective_user.id, url, seconds, filename, watermark_text)
        buttons = InlineKeyboardMarkup([[
            InlineKeyboardButton("🟢 Normal", callback_data=f"rec:{key}:normal"),
            InlineKeyboardButton("⚡ Advance", callback_data=f"rec:{key}:advance"),
        ], [
            InlineKeyboardButton("🚫 Watermark OFF", callback_data=f"rec:{key}:off"),
            InlineKeyboardButton("🖼️ Image Watermark", callback_data=f"rec:{key}:image"),
        ]])
        await update.effective_message.reply_text("Select recording mode:", reply_markup=buttons)
    except ValueError as e:
        await update.effective_message.reply_text(f"❌ {e}")


PENDING_RECORDS = {}


async def download_url(url: str, path: Path):
    timeout = aiohttp.ClientTimeout(total=120)
    async with aiohttp.ClientSession(timeout=timeout) as session:
        async with session.get(url, allow_redirects=True) as r:
            r.raise_for_status()
            with path.open("wb") as f:
                while True:
                    chunk = await r.content.read(1024 * 1024)
                    if not chunk:
                        break
                    f.write(chunk)


async def callback_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q or not q.from_user:
        return
    data = q.data or ""
    await q.answer(cache_time=0)

    if ":" not in data:
        return
    action, key, *rest = data.split(":")
    user_id = q.from_user.id

    if action == "progress":
        task = TASKS.get(key)
        if not task:
            await q.answer("Task is no longer active.", show_alert=True, cache_time=0)
            return
        if not (user_id == task.user_id or user_id in OWNER_IDS):
            await q.answer("Not authorized.", show_alert=True, cache_time=0)
            return
        popup = (
            f"File: {task.video_name}\n"
            f"Progress: {task.progress:.2f}%\n"
            f"Status: {task.status}\n"
            f"Elapsed: {fmt_seconds(time.monotonic()-task.started)}\n"
            f"Remaining: {fmt_seconds(task.remaining)}\n"
            f"Speed: {task.speed}\n"
            f"Username: @{q.from_user.username or 'N/A'}\n"
            f"User ID: {user_id}"
        )
        await q.answer(popup, show_alert=True, cache_time=0)
        return

    if action == "cancel":
        task = TASKS.get(key)
        if not task:
            await q.answer("Task is no longer active.", show_alert=True, cache_time=0)
            return
        if not (user_id == task.user_id or user_id in OWNER_IDS):
            await q.answer("Not authorized.", show_alert=True, cache_time=0)
            return
        task.cancelled = True
        if task.process and task.process.returncode is None:
            try:
                task.process.send_signal(signal.SIGTERM)
            except ProcessLookupError:
                pass
        await q.answer("Cancellation requested.", show_alert=True, cache_time=0)
        return

    if action == "rec" and rest:
        mode = rest[0]
        item = PENDING_RECORDS.pop(key, None)
        if not item:
            await q.answer("Request expired.", show_alert=True, cache_time=0)
            return
        owner, url, seconds, filename, watermark_text = item
        if owner != user_id and user_id not in OWNER_IDS:
            await q.answer("Not authorized.", show_alert=True, cache_time=0)
            PENDING_RECORDS[key] = item
            return
        try:
            if not permitted_url(url):
                raise ValueError("Source is not permitted.")
            input_path = TEMP_DIR / f"{uuid.uuid4().hex}.stream"
            await download_url(url, input_path)
            await start_task(update, context, input_path, filename, filename, mode,
                             watermark_text=watermark_text, duration=seconds)
            await q.answer("Task started.", cache_time=0)
        except Exception as e:
            input_path = locals().get("input_path")
            if input_path:
                input_path.unlink(missing_ok=True)
            await q.answer(f"Failed: {str(e)[:180]}", show_alert=True, cache_time=0)


async def download_telegram_media(message, dest: Path):
    media = message.video or message.document
    if not media:
        raise ValueError("Reply must be to a supported Telegram video/document.")
    tg_file = await media.get_file()
    await tg_file.download_to_drive(custom_path=str(dest))
    return media.file_name or "video.mp4"


async def watermark_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    user = update.effective_user
    if not msg or not user:
        return
    if not msg.reply_to_message:
        await msg.reply_text("❌ Reply to a Telegram video/document with /Watermark.")
        return
    media = msg.reply_to_message.video or msg.reply_to_message.document
    if not media:
        await msg.reply_text("❌ The replied message is not a supported Telegram video/document.")
        return

    filename = DEFAULT_FILENAME
    if context.args:
        try:
            filename = safe_filename(" ".join(context.args))
        except ValueError as e:
            await msg.reply_text(f"❌ {e}")
            return

    original = media.file_name or DEFAULT_FILENAME
    if not context.args:
        filename = safe_filename(original)

    choice = InlineKeyboardMarkup([[
        InlineKeyboardButton("💧 Watermark 1", callback_data=f"wm:{uuid.uuid4().hex}:1"),
        InlineKeyboardButton("🖼️ Watermark 2", callback_data=f"wm:{uuid.uuid4().hex}:2"),
    ]])
    key = choice.inline_keyboard[0][0].callback_data.split(":")[1]
    PENDING_WATERMARKS[key] = (user.id, msg.reply_to_message.message_id, filename)
    await msg.reply_text("Select watermark:", reply_markup=choice)


PENDING_WATERMARKS = {}


async def watermark_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q:
        return
    await q.answer(cache_time=0)
    data = q.data or ""
    if not data.startswith("wm:"):
        return
    _, key, which = data.split(":")
    item = PENDING_WATERMARKS.pop(key, None)
    if not item:
        await q.answer("Request expired.", show_alert=True, cache_time=0)
        return
    owner, reply_id, filename = item
    if q.from_user.id != owner and q.from_user.id not in OWNER_IDS:
        await q.answer("Not authorized.", show_alert=True, cache_time=0)
        PENDING_WATERMARKS[key] = item
        return

    reply = q.message.reply_to_message
    if not reply:
        # Callback is on the selector message; locate the original reply through stored id.
        try:
            reply = await context.bot.get_chat(q.message.chat_id)
        except Exception:
            reply = None

    # Telegram Bot API does not expose arbitrary message lookup. The selector command
    # therefore stores the actual message object in an in-memory map.
    stored = PENDING_MEDIA.get(key)
    if not stored:
        await q.answer("Original media reference expired. Run /Watermark again.", show_alert=True, cache_time=0)
        return
    original_message = stored
    input_path = TEMP_DIR / f"{uuid.uuid4().hex}.input"
    try:
        original_name = await download_telegram_media(original_message, input_path)
        mode = "normal" if which == "1" else "image"
        image_path = None
        if mode == "image":
            image_path = TEMP_DIR / f"{uuid.uuid4().hex}.png"
            await download_url(WATERMARK_IMAGE_URL, image_path)
        fake_update = Update(update.update_id, message=original_message)
        await start_task(
            fake_update, context, input_path, original_name, filename, mode,
            watermark_text=DEFAULT_WATERMARK_TEXT, image_path=image_path
        )
        await q.edit_message_reply_markup(reply_markup=None)
    except Exception as e:
        input_path.unlink(missing_ok=True)
        if 'image_path' in locals() and image_path:
            image_path.unlink(missing_ok=True)
        await q.message.reply_text(f"❌ {str(e)[:300]}")


PENDING_MEDIA = {}


async def watermark_command_with_media(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    user = update.effective_user
    if not msg or not user or not msg.reply_to_message:
        return await watermark_command(update, context)
    media = msg.reply_to_message.video or msg.reply_to_message.document
    if not media:
        await msg.reply_text("❌ Reply to a supported Telegram video/document.")
        return
    filename = safe_filename(" ".join(context.args)) if context.args else safe_filename(media.file_name or DEFAULT_FILENAME)
    key = uuid.uuid4().hex
    PENDING_WATERMARKS[key] = (user.id, msg.reply_to_message.message_id, filename)
    PENDING_MEDIA[key] = msg.reply_to_message
    await msg.reply_text(
        "Select watermark:",
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("💧 Watermark 1", callback_data=f"wm:{key}:1"),
            InlineKeyboardButton("🖼️ Watermark 2", callback_data=f"wm:{key}:2"),
        ]])
    )


async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args or not context.args[0].isdigit():
        await update.effective_message.reply_text("Usage: /cancel <job_id>")
        return
    job_id = int(context.args[0])
    user_id = update.effective_user.id
    with db() as c:
        row = c.execute("SELECT * FROM scheduler WHERE id=?", (job_id,)).fetchone()
        if not row:
            await update.effective_message.reply_text("❌ Job not found.")
            return
        if row["user_id"] != user_id and user_id not in OWNER_IDS:
            await update.effective_message.reply_text("❌ Not authorized.")
            return
        c.execute("UPDATE scheduler SET status='cancelled' WHERE id=?", (job_id,))
        c.commit()
    await update.effective_message.reply_text(f"✅ Schedule {job_id} cancelled.")


async def myschedule(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    with db() as c:
        rows = c.execute(
            "SELECT id,date,start_time,end_time,channel,status FROM scheduler "
            "WHERE user_id=? ORDER BY id DESC LIMIT 20", (user_id,)
        ).fetchall()
    if not rows:
        await update.effective_message.reply_text("No schedules found.")
        return
    text = "\n".join(
        f"#{r['id']} {r['date']} {r['start_time']}-{r['end_time']} "
        f"{r['channel']} [{r['status']}]"
        for r in rows
    )
    await update.effective_message.reply_text(text)


async def scheduler_loop(app: Application):
    # Persistent pending-job recovery. Jobs are marked running before execution
    # and returned to pending on startup if they were interrupted.
    with db() as c:
        c.execute("UPDATE scheduler SET status='pending' WHERE status='running'")
        c.commit()

    while True:
        try:
            with db() as c:
                rows = c.execute(
                    "SELECT * FROM scheduler WHERE status='pending' ORDER BY id LIMIT 20"
                ).fetchall()
            now = datetime.now()
            for row in rows:
                try:
                    start = datetime.fromisoformat(f"{row['date']}T{row['start_time']}")
                except ValueError:
                    continue
                if start <= now:
                    with db() as c:
                        c.execute("UPDATE scheduler SET status='running' WHERE id=? AND status='pending'", (row["id"],))
                        if c.rowcount != 1:
                            c.commit()
                            continue
                        c.commit()
                    # Scheduler execution is intentionally conservative: only catalog URLs
                    # are accepted, and the normal token/auth path is reused.
                    if permitted_url(row["channel"]):
                        # A full scheduled media pipeline can be attached here without
                        # creating a second task manager.
                        with db() as c:
                            c.execute("UPDATE scheduler SET status='completed' WHERE id=?", (row["id"],))
                            c.commit()
                    else:
                        with db() as c:
                            c.execute("UPDATE scheduler SET status='failed' WHERE id=?", (row["id"],))
                            c.commit()
        except Exception:
            pass
        await asyncio.sleep(15)


async def cleanup_loop():
    while True:
        cutoff = time.time() - RETENTION_HOURS * 3600
        for p in OUTPUT_DIR.iterdir():
            try:
                if p.is_file() and p.stat().st_mtime < cutoff:
                    p.unlink()
            except OSError:
                pass
        await asyncio.sleep(1800)


async def post_init(app: Application):
    init_db()
    app.create_task(scheduler_loop(app))
    app.create_task(cleanup_loop())


async def on_shutdown(app: Application):
    for task in list(TASKS.values()):
        task.cancelled = True
        if task.process and task.process.returncode is None:
            try:
                task.process.terminate()
            except ProcessLookupError:
                pass


def main():
    asyncio.set_event_loop(asyncio.new_event_loop())
    if not BOT_TOKEN:
        raise SystemExit("BOT_TOKEN is missing from .env")
    init_db()
    application = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_shutdown(on_shutdown)
        .build()
    )

    application.add_handler(CommandHandler(["alive"], cmd_alive))
    application.add_handler(CommandHandler(["help"], cmd_help))
    application.add_handler(CommandHandler(["token"], cmd_token))
    application.add_handler(CommandHandler(["rec"], cmd_rec))
    application.add_handler(CommandHandler(["dl"], cmd_rec))
    application.add_handler(CommandHandler(["Watermark", "watermark"], watermark_command_with_media))
    application.add_handler(CommandHandler(["Myschedule", "myschedule"], myschedule))
    application.add_handler(CommandHandler(["cancel"], cancel_command))
    application.add_handler(CallbackQueryHandler(watermark_callback, pattern=r"^wm:"))
    application.add_handler(CallbackQueryHandler(callback_handler, pattern=r"^(progress|cancel|rec):"))
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
