import html
import hashlib
import hmac
import json
import logging
import os
import random
import re
import secrets
import signal
import sqlite3
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import requests

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------


def env_int(name, default, lo=None, hi=None):
    raw = os.environ.get(name, "").strip()
    try:
        value = int(raw) if raw else default
    except ValueError:
        value = default
    if lo is not None:
        value = max(lo, value)
    if hi is not None:
        value = min(hi, value)
    return value


# NEVER hard-code the token. Set BOT_TOKEN in the environment (Render -> Environment).
BOT_TOKEN = os.environ.get("BOT_TOKEN", "8835540203:AAFItqY22ynNAOpjECygtA26rtZWAC62CRk").strip()
ADMIN_ID = env_int("ADMIN_ID", 8749547652)
ADMIN_IDS = {ADMIN_ID, 7569480901}
for admin_id_text in os.environ.get("ADMIN_IDS", "").split(","):
    try:
        configured_admin_id = int(admin_id_text.strip())
    except ValueError:
        continue
    if configured_admin_id > 0:
        ADMIN_IDS.add(configured_admin_id)
PORT = env_int("PORT", 10000, 1, 65535)
DATABASE_PATH = os.environ.get("DATABASE_PATH", "").strip() or os.path.join("data", "monitor.db")
CHECK_INTERVAL = env_int("CHECK_INTERVAL", 10, 5, 86400)   # seconds between checks of the same banned name
MAX_USERNAMES = env_int("MAX_USERNAMES", 5, 1, 50)
ADMIN_NAME = os.environ.get("ADMIN_NAME", "").strip() or "@r1uet"
BOT_TITLE = "r1uet Unban Monitor"
TELEGRAM_API_BASE = os.environ.get("TELEGRAM_API_BASE", "https://api.telegram.org").rstrip("/")
INSTAGRAM_BASE = os.environ.get("INSTAGRAM_BASE", "https://i.instagram.com").rstrip("/")

# The 2 extra Instagram checks (hard-coded). {username} is replaced by the name being checked.
# They run together with the built-in i.instagram.com check, so every name is checked by 3 sources.
EXTRA_APIS = [
    "https://www.instagram.com/api/v1/users/web_profile_info/?username={username}",  # API 1: web JSON endpoint
    "https://www.instagram.com/{username}/",                                          # API 2: public profile page
]

USER_GAP_DELAY = env_int("USER_GAP_DELAY", 2, 0, 600)  # seconds between two different usernames
MAX_FAILURES = 5            # consecutive failed checks before a name is shown as "Inconclusive"
RATE_LIMIT_COOLDOWN = 300   # seconds every check pauses after Instagram rate-limits us
CONFIRMATIONS = 2           # consecutive "active" results required before an alert is sent
MAX_BACKOFF = 3600          # upper bound for exponential backoff (seconds)
MAX_FILE_BYTES = 100_000    # largest accepted .txt upload
MAX_TOKENS = 500            # max usernames read from one message / file
MAX_ALERT_GIFS = 20
DEFAULT_MENU_GIF_URL = "https://www.image2url.com/r2/default/videos/1791990568912-0298b7cf-b8cd-49f8-a998-e32e025a2f38.mp4"
DEFAULT_ALERT_GIF_URL = "https://www.image2url.com/r2/default/videos/1791990613313-7393975c-f026-4ead-b448-55008c4683ff.mp4"

try:
    from zoneinfo import ZoneInfo
    LOCAL_TZ = ZoneInfo(os.environ.get("TIMEZONE", "").strip() or "Asia/Kolkata")
except Exception:  # missing tz database or bad name -> fixed India offset
    LOCAL_TZ = timezone(timedelta(hours=5, minutes=30))

# --------------------------------------------------------------------------
# Logging (secrets are redacted: bot token, Discord webhook URLs, API URLs)
# --------------------------------------------------------------------------

WEBHOOK_RE = re.compile(
    r"^https://(?:(?:ptb|canary)\.)?(?:discord|discordapp)\.com/api(?:/v\d+)?/webhooks/\d{5,25}/[A-Za-z0-9._-]{20,200}$"
)
_WEBHOOK_SCAN_RE = re.compile(r"https://[^\s\"']*webhooks/[^\s\"']+")


def redact(text):
    text = str(text)
    if BOT_TOKEN:
        text = text.replace(BOT_TOKEN, "<token>")
    for tpl in EXTRA_APIS:
        text = text.replace(tpl, "<api>")
    return _WEBHOOK_SCAN_RE.sub("<webhook>", text)


class RedactingFormatter(logging.Formatter):
    def format(self, record):
        return redact(super().format(record))


def setup_logging():
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(RedactingFormatter("%(asctime)s %(levelname)s [%(threadName)s] %(message)s"))
    root = logging.getLogger()
    root.handlers[:] = [handler]
    root.setLevel(logging.INFO)
    logging.getLogger("urllib3").setLevel(logging.WARNING)


log = logging.getLogger("unban-monitor")

# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------

USERNAME_RE = re.compile(r"^[a-z0-9._]{1,30}$")
IG_URL_RE = re.compile(r"^(?:https?://)?(?:www\.)?instagram\.com/([^/?#\s]+)/?(?:[?#].*)?$", re.I)


def esc(value):
    return html.escape(str(value), quote=True)


def fmt_ts(ts):
    return datetime.fromtimestamp(ts, LOCAL_TZ).strftime("%Y-%m-%d %H:%M:%S")


def fmt_duration(seconds):
    s = max(0, int(seconds))
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m {s % 60}s"
    if s < 86400:
        return f"{s // 3600}h {(s % 3600) // 60}m"
    return f"{s // 86400}d {(s % 86400) // 3600}h"


def normalize_username(token):
    t = token.strip()
    m = IG_URL_RE.match(t)
    if m:
        t = m.group(1)
    t = t.lstrip("@").lower()
    if not USERNAME_RE.match(t) or t.startswith(".") or t.endswith("."):
        return None
    return t


def parse_usernames(text):
    """Return (valid_unique, duplicates_in_input, invalid_tokens, truncated)."""
    text = text.replace("\ufeff", "").replace("\u200b", "")  # byte-order mark / zero-width space
    tokens = [t.strip() for t in re.split(r"[\r\n,;]+", text) if t.strip()]
    truncated = len(tokens) > MAX_TOKENS
    valid, dupes, invalid, seen = [], [], [], set()
    for tok in tokens[:MAX_TOKENS]:
        name = normalize_username(tok)
        if name is None:
            invalid.append(tok[:32])
        elif name in seen:
            dupes.append(name)
        else:
            seen.add(name)
            valid.append(name)
    return valid, dupes, invalid, truncated


def gap_delay():
    jitter = min(1.0, USER_GAP_DELAY / 2)
    return max(0.0, USER_GAP_DELAY + random.uniform(-jitter, jitter))


# --------------------------------------------------------------------------
# Database (SQLite, one connection guarded by a lock, parameterized queries)
# --------------------------------------------------------------------------

SCHEMA = """
CREATE TABLE IF NOT EXISTS usernames(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    owner_id INTEGER NOT NULL,
    username TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'pending',
    added_at REAL NOT NULL,
    last_checked REAL,
    last_changed REAL,
    next_check REAL NOT NULL DEFAULT 0,
    fail_count INTEGER NOT NULL DEFAULT 0,
    confirm_count INTEGER NOT NULL DEFAULT 0,
    UNIQUE(owner_id, username)
);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS gifs(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    kind TEXT NOT NULL,
    file_id TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS state(
    user_id INTEGER PRIMARY KEY,
    state TEXT NOT NULL,
    chat_id INTEGER,
    message_id INTEGER,
    updated REAL
);
CREATE TABLE IF NOT EXISTS access_keys(
    user_id INTEGER PRIMARY KEY,
    key_hash TEXT NOT NULL,
    created_at REAL NOT NULL,
    redeemed_at REAL
);
CREATE TABLE IF NOT EXISTS bot_users(
    user_id INTEGER PRIMARY KEY,
    first_seen REAL NOT NULL
);
"""

USER_COLUMNS = {"status", "last_checked", "last_changed", "next_check", "fail_count", "confirm_count"}


class DB:
    def __init__(self, path):
        directory = os.path.dirname(os.path.abspath(path))
        os.makedirs(directory, exist_ok=True)
        self.path = path
        self.lock = threading.RLock()
        self.conn = sqlite3.connect(path, check_same_thread=False, timeout=30, isolation_level=None)
        self.conn.row_factory = sqlite3.Row
        try:
            self.conn.execute("PRAGMA journal_mode=WAL")
        except sqlite3.DatabaseError:
            pass
        self.conn.execute("PRAGMA busy_timeout=30000")
        self.conn.executescript(SCHEMA)
        for row in self.q("SELECT key FROM settings WHERE key LIKE 'joined_user:%'"):
            try:
                user_id = int(row["key"].split(":", 1)[1])
            except ValueError:
                continue
            self.x("INSERT OR IGNORE INTO bot_users(user_id,first_seen) VALUES(?,?)", (user_id, time.time()))

    def close(self):
        with self.lock:
            try:
                self.conn.close()
            except sqlite3.Error:
                pass

    @contextmanager
    def tx(self):
        with self.lock:
            self.conn.execute("BEGIN IMMEDIATE")
            try:
                yield self.conn
            except BaseException:
                self.conn.execute("ROLLBACK")
                raise
            else:
                self.conn.execute("COMMIT")

    def q(self, sql, params=()):
        with self.lock:
            return self.conn.execute(sql, params).fetchall()

    def x(self, sql, params=()):
        with self.lock:
            return self.conn.execute(sql, params).rowcount

    # ---- settings -------------------------------------------------------
    def get_setting(self, key, default=None):
        rows = self.q("SELECT value FROM settings WHERE key=?", (key,))
        return rows[0]["value"] if rows else default

    def set_setting(self, key, value):
        self.x(
            "INSERT INTO settings(key,value) VALUES(?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, str(value)),
        )

    def del_setting(self, key):
        self.x("DELETE FROM settings WHERE key=?", (key,))

    def register_bot_user(self, user_id):
        self.x("INSERT OR IGNORE INTO bot_users(user_id,first_seen) VALUES(?,?)", (user_id, time.time()))

    def bot_users(self):
        return [row["user_id"] for row in self.q("SELECT user_id FROM bot_users ORDER BY first_seen")]

    def set_access_key(self, user_id, key_hash):
        self.x(
            "INSERT INTO access_keys(user_id,key_hash,created_at,redeemed_at) VALUES(?,?,?,NULL) "
            "ON CONFLICT(user_id) DO UPDATE SET key_hash=excluded.key_hash, "
            "created_at=excluded.created_at, redeemed_at=NULL",
            (user_id, key_hash, time.time()),
        )

    def has_access(self, user_id):
        return bool(self.q("SELECT 1 FROM access_keys WHERE user_id=? AND redeemed_at IS NOT NULL", (user_id,)))

    def remove_access_key(self, user_id):
        return self.x("DELETE FROM access_keys WHERE user_id=?", (user_id,)) > 0

    def redeem_access_key(self, user_id, key):
        key_hash = hashlib.sha256(key.strip().encode("utf-8")).hexdigest()
        with self.tx() as conn:
            row = conn.execute(
                "SELECT key_hash,redeemed_at FROM access_keys WHERE user_id=?", (user_id,)
            ).fetchone()
            if not row or row["redeemed_at"] is not None:
                return False
            if not hmac.compare_digest(row["key_hash"], key_hash):
                return False
            conn.execute("UPDATE access_keys SET redeemed_at=? WHERE user_id=?", (time.time(), user_id))
        return True

    # ---- usernames ------------------------------------------------------
    def count_all(self):
        return self.q("SELECT COUNT(*) c FROM usernames")[0]["c"]

    def count_owner(self, owner):
        return self.q("SELECT COUNT(*) c FROM usernames WHERE owner_id=?", (owner,))[0]["c"]

    def list_users(self, owner):
        return self.q("SELECT * FROM usernames WHERE owner_id=? ORDER BY added_at, id", (owner,))

    def add_usernames(self, owner, names, limit):
        added, dup, over = [], [], []
        t = time.time()
        with self.tx() as conn:
            count = conn.execute("SELECT COUNT(*) c FROM usernames WHERE owner_id=?", (owner,)).fetchone()["c"]
            for name in names:
                exists = conn.execute(
                    "SELECT 1 FROM usernames WHERE owner_id=? AND username=?", (owner, name)
                ).fetchone()
                if exists:
                    dup.append(name)
                elif count >= limit:
                    over.append(name)
                else:
                    conn.execute(
                        "INSERT INTO usernames(owner_id,username,status,added_at,next_check) "
                        "VALUES(?,?,'pending',?,?)",
                        (owner, name, t, t),
                    )
                    count += 1
                    added.append(name)
        return {"added": added, "dup": dup, "over": over, "count": count}

    def remove_user(self, owner, name):
        return self.x("DELETE FROM usernames WHERE owner_id=? AND username=?", (owner, name)) > 0

    def remove_by_id(self, uid):
        self.x("DELETE FROM usernames WHERE id=?", (uid,))

    def due_users(self, t, limit=10):
        return self.q("SELECT * FROM usernames WHERE next_check<=? ORDER BY next_check LIMIT ?", (t, limit))

    def next_due_delay(self, t):
        rows = self.q("SELECT MIN(next_check) m FROM usernames")
        m = rows[0]["m"] if rows else None
        return None if m is None else m - t

    def update_user(self, uid, **fields):
        if not fields:
            return
        bad = set(fields) - USER_COLUMNS
        if bad:
            raise ValueError(f"unknown column(s): {bad}")
        cols = ", ".join(f"{c}=?" for c in fields)
        self.x(f"UPDATE usernames SET {cols} WHERE id=?", (*fields.values(), uid))

    # ---- gifs -----------------------------------------------------------
    def gifs(self, kind):
        return [r["file_id"] for r in self.q("SELECT file_id FROM gifs WHERE kind=? ORDER BY id", (kind,))]

    def set_menu_gif(self, file_id):
        with self.tx() as conn:
            conn.execute("DELETE FROM gifs WHERE kind='menu'")
            conn.execute("INSERT INTO gifs(kind,file_id) VALUES('menu',?)", (file_id,))

    def add_alert_gif(self, file_id):
        """Returns False if the folder is full."""
        with self.tx() as conn:
            n = conn.execute("SELECT COUNT(*) c FROM gifs WHERE kind='alert'").fetchone()["c"]
            if n >= MAX_ALERT_GIFS:
                return False
            if conn.execute("SELECT 1 FROM gifs WHERE kind='alert' AND file_id=?", (file_id,)).fetchone():
                return True
            conn.execute("INSERT INTO gifs(kind,file_id) VALUES('alert',?)", (file_id,))
        return True

    def clear_gifs(self, kind):
        self.x("DELETE FROM gifs WHERE kind=?", (kind,))

    # ---- conversation state --------------------------------------------
    def get_state(self, user_id):
        rows = self.q("SELECT * FROM state WHERE user_id=?", (user_id,))
        return dict(rows[0]) if rows else None

    def set_state(self, user_id, state, chat_id=None, message_id=None):
        self.x(
            "INSERT INTO state(user_id,state,chat_id,message_id,updated) VALUES(?,?,?,?,?) "
            "ON CONFLICT(user_id) DO UPDATE SET state=excluded.state, chat_id=excluded.chat_id, "
            "message_id=excluded.message_id, updated=excluded.updated",
            (user_id, state, chat_id, message_id, time.time()),
        )

    def clear_state(self, user_id):
        self.x("DELETE FROM state WHERE user_id=?", (user_id,))


db = None  # created in main()
MONITOR = None
STOP = threading.Event()

# --------------------------------------------------------------------------
# Telegram Bot API (thin wrapper around requests)
# --------------------------------------------------------------------------

tg_session = requests.Session()


class TelegramError(Exception):
    def __init__(self, code, description, retry_after=0):
        super().__init__(f"{code}: {description}")
        self.code = code
        self.description = description
        self.retry_after = retry_after


def tg(method, params=None, timeout=(10, 25), retries=2):
    url = f"{TELEGRAM_API_BASE}/bot{BOT_TOKEN}/{method}"
    attempt = 0
    while True:
        try:
            resp = tg_session.post(url, json=params or {}, timeout=timeout)
        except requests.RequestException as exc:
            attempt += 1
            if attempt > retries:
                raise TelegramError(0, f"network error: {type(exc).__name__}")
            time.sleep(min(2 ** attempt, 10))
            continue
        try:
            data = resp.json()
        except ValueError:
            data = {}
        if data.get("ok"):
            return data.get("result")
        code = data.get("error_code", resp.status_code)
        desc = data.get("description", "unknown error")
        retry_after = (data.get("parameters") or {}).get("retry_after", 0)
        if code == 429 and attempt < retries:
            attempt += 1
            time.sleep(min(retry_after + 1, 30))
            continue
        raise TelegramError(code, desc, retry_after)


def tg_quiet(method, params=None, **kw):
    """Call tg() but never raise (for best-effort actions)."""
    try:
        return tg(method, params, **kw)
    except TelegramError as exc:
        log.info("Telegram %s failed: %s", method, redact(exc))
        return None


def clip(text, limit):
    return text if len(text) <= limit else text[: limit - 1] + "…"


def send_screen(chat_id, text, kb=None):
    """Send a bot screen: the menu GIF with a caption if a GIF is set, else a text message."""
    gifs = db.gifs("menu") or [DEFAULT_MENU_GIF_URL]
    if gifs and len(text) <= 1024:
        try:
            return tg(
                "sendAnimation",
                {
                    "chat_id": chat_id,
                    "animation": gifs[0],
                    "caption": text,
                    "parse_mode": "HTML",
                    "reply_markup": kb,
                },
            )
        except TelegramError as exc:
            log.warning("sendAnimation failed (%s); falling back to text", redact(exc))
    return tg(
        "sendMessage",
        {
            "chat_id": chat_id,
            "text": clip(text, 4096),
            "parse_mode": "HTML",
            "disable_web_page_preview": True,
            "reply_markup": kb,
        },
    )


def edit_screen(msg, text, kb=None):
    """Edit the message a button was pressed on, in place (caption for GIF messages)."""
    chat_id, message_id = msg["chat"]["id"], msg["message_id"]
    is_text = "text" in msg
    params = {"chat_id": chat_id, "message_id": message_id, "parse_mode": "HTML"}
    if kb is not None:
        params["reply_markup"] = kb
    try:
        if is_text:
            params.update(text=clip(text, 4096), disable_web_page_preview=True)
            return tg("editMessageText", params)
        params["caption"] = clip(text, 1024)
        return tg("editMessageCaption", params)
    except TelegramError as exc:
        if "not modified" in exc.description.lower():
            return None
        log.info("edit failed (%s); sending a new message", redact(exc))
        return send_screen(chat_id, text, kb)


def strip_buttons(chat_id, message_id):
    if chat_id and message_id:
        tg_quiet(
            "editMessageReplyMarkup",
            {"chat_id": chat_id, "message_id": message_id, "reply_markup": {"inline_keyboard": []}},
            retries=0,
        )


# --------------------------------------------------------------------------
# Keyboards & screen texts
# --------------------------------------------------------------------------


def btn(text, data, style="success"):
    if style not in {"success", "primary", "danger"}:
        style = "success"
    return {"text": text, "callback_data": data, "style": style}


def url_btn(text, url):
    return {"text": text, "url": url, "style": "success"}


MAIN_KB = {
    "inline_keyboard": [
        [btn("Add Username", "add"), btn("Remove Username", "remove")],
        [btn("Settings", "settings")],
        [btn("Status", "status"), btn("My List", "list")],
        [btn("Close", "close")],
        [btn("Admin Panel", "admin_panel")],
        [url_btn("Contact Admin", "https://t.me/r1uet")],
        [{"text": "Developer", "url": "https://t.me/fameneedsme", "style": "primary"}],
    ]
}
USER_KB = {
    "inline_keyboard": [
        [btn("Add Username", "add"), btn("Remove Username", "remove")],
        [btn("Status", "status"), btn("My List", "list")],
        [btn("Close", "close")],
        [url_btn("Contact Admin", "https://t.me/r1uet")],
        [{"text": "Developer", "url": "https://t.me/fameneedsme", "style": "primary"}],
    ]
}
ACCESS_KB = {
    "inline_keyboard": [
        [btn("Enter Access Key", "enter_access_key")],
        [url_btn("Contact Admin", "https://t.me/r1uet")],
        [{"text": "Developer", "url": "https://t.me/fameneedsme", "style": "primary"}],
    ]
}
ACCESS_ENTRY_KB = {
    "inline_keyboard": [
        [btn("Cancel", "cancel_key_entry")],
        [url_btn("Contact Admin", "https://t.me/r1uet")],
        [{"text": "Developer", "url": "https://t.me/fameneedsme", "style": "primary"}],
    ]
}
ADMIN_PANEL_KB = {
    "inline_keyboard": [
        [btn("Create Key", "create_access_key"), btn("Remove Access Key", "remove_access")],
        [btn("Broadcast", "broadcast")],
        [btn("Maintenance ON", "maintenance:on"), btn("Maintenance OFF", "maintenance:off")],
        [btn("Add Welcome GIF", "gif:menu"), btn("Remove Welcome GIF", "gif:remove:menu")],
        [btn("Add Unbanned GIF", "gif:alert"), btn("Remove Unbanned GIF", "gif:remove:alert")],
        [btn("Back", "back_menu")],
    ]
}
SETTINGS_KB = {
    "inline_keyboard": [
        [btn("Add Gif", "gif")],
        [btn("Webhook", "webhook")],
        [btn("Back", "back_menu")],
    ]
}
CANCEL_KB = {"inline_keyboard": [[btn("Cancel", "cancel")]]}
BACK_SETTINGS_KB = {"inline_keyboard": [[btn("Back", "back_settings")]]}
BACK_MENU_KB = {"inline_keyboard": [[btn("Back", "back_menu")]]}
GIF_KB = {
    "inline_keyboard": [
        [btn("Add Welcome GIF", "gif:menu"), btn("Add Unbanned GIF", "gif:alert")],
        [btn("Remove Welcome GIF", "gif:remove:menu"), btn("Remove Unbanned GIF", "gif:remove:alert")],
        [btn("Back", "back_settings")],
    ]
}

WELCOME = (
    f"<b>{esc(BOT_TITLE)}</b>\n"
    f"Admin: {esc(ADMIN_NAME)}\n\n"
    "<blockquote>ℹ️ This bot does NOT unban accounts. It only checks whether an Instagram "
    "account is active, and alerts you when a banned account becomes active again.\n\n"
    "⚠️ Please don't add active usernames. Only add usernames that are currently "
    "unavailable or banned.</blockquote>\n\n"
    "<b>Choose an action below to manage your monitoring list.</b>"
)

ACCESS_REQUIRED = (
    "<b>Access required</b>\n\n"
    "Contact <a href=\"https://t.me/r1uet\">@r1uet</a> to request access. "
    "After you receive your key, send it here. Each key is assigned to one Telegram user ID."
)
def keyboard_for(user_id):
    return MAIN_KB if user_id in ADMIN_IDS else USER_KB

STATUS_LABELS = {
    "pending": "Checking…",
    "banned": "Banned",
    "active": "Active",
    "inconclusive": "Inconclusive (verify manually)",
}


def ig_link(name):
    return f'<a href="https://www.instagram.com/{esc(name)}">@{esc(name)}</a>'


def list_text(owner):
    rows = db.list_users(owner)
    if not rows:
        return "<b>My List</b>\n\nYour list is empty."
    t = time.time()
    out = "<b>My List</b>"
    shown = 0
    for r in rows:
        block = (
            f"\n\n{ig_link(r['username'])}\n"
            f"Status: {STATUS_LABELS.get(r['status'], r['status'])}\n"
            f"Taken Time: <code>{fmt_duration(t - r['added_at'])}</code>"
        )
        if len(out) + len(block) > 900:
            out += f"\n\n…and {len(rows) - shown} more"
            break
        out += block
        shown += 1
    return out


def status_text(owner):
    mon = MONITOR
    alive = bool(mon and mon.is_alive() and time.time() - mon.heartbeat < 180)
    maintenance = db.get_setting("maintenance", "0") == "1"
    checker = "Running" if alive else "Stopped"
    if alive and mon.cooldown_left() > 0:
        checker += f" (rate-limit cooldown {int(mon.cooldown_left())}s)"
    return (
        f"Users monitored total: {db.count_all()}\n"
        f"Your monitored: {db.count_owner(owner)}/{MAX_USERNAMES}\n"
        f"Loaded APIs: {1 + len(EXTRA_APIS)} (built-in + {len(EXTRA_APIS)} extra)\n"
        f"Check interval: {CHECK_INTERVAL}s\n"
        f"Checker: {checker}\n"
        f"Maintenance: {'ON' if maintenance else 'OFF'}\n"
        f"Proxy cooldown: {RATE_LIMIT_COOLDOWN}s  Max failures: {MAX_FAILURES}"
    )


def webhook_screen():
    if db.get_setting("webhook"):
        return (
            "<b>Webhook</b>\n\nStatus: <b>Configured</b>",
            {
                "inline_keyboard": [
                    [btn("Change Webhook", "wh_set"), btn("Remove Webhook", "wh_remove")],
                    [btn("Back", "back_settings")],
                ]
            },
        )
    return (
        "<b>Webhook</b>\n\nStatus: <b>Not configured</b>",
        {"inline_keyboard": [[btn("Set Webhook", "wh_set")], [btn("Back", "back_settings")]]},
    )


WEBHOOK_PROMPT = (
    "Send your Discord webhook URL (https://discord.com/api/webhooks/...) "
    "or send 'clear' to remove your webhook."
)

# --------------------------------------------------------------------------
# Account checks: built-in Instagram endpoint + your 2 extra APIs
# --------------------------------------------------------------------------

ACTIVE, UNAVAILABLE, BLOCKED, ERROR, INCONCLUSIVE = "active", "unavailable", "blocked", "error", "inconclusive"
ig_session = requests.Session()
IG_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 "
        "(KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1"
    ),
    "X-IG-App-ID": "936619743392459",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
}
NOT_FOUND_HINTS = ("user not found", "not found", "does not exist", "doesn't exist", "no such user", "page isn't available")

# When APIs disagree, the first match in this order wins.
PRIORITY = [ACTIVE, UNAVAILABLE, BLOCKED, ERROR, INCONCLUSIVE]


def _check_builtin(username):
    try:
        resp = ig_session.get(
            f"{INSTAGRAM_BASE}/api/v1/users/web_profile_info/",
            params={"username": username},
            headers=IG_HEADERS,
            timeout=(8, 15),
            allow_redirects=False,
        )
    except requests.Timeout:
        return ERROR, "timeout"
    except requests.RequestException as exc:
        return ERROR, type(exc).__name__
    code = resp.status_code
    if code == 404:
        return UNAVAILABLE, "404"
    if code in (401, 403, 429) or 300 <= code < 400:
        return BLOCKED, str(code)
    if code >= 500:
        return ERROR, str(code)
    if code == 200:
        try:
            payload = resp.json()
        except ValueError:
            return INCONCLUSIVE, "200 non-JSON (login wall?)"
        user = ((payload or {}).get("data") or {}).get("user") if isinstance(payload, dict) else None
        if isinstance(user, dict) and str(user.get("username", "")).lower() == username:
            return ACTIVE, "200"
        return INCONCLUSIVE, "200 without matching profile"
    return INCONCLUSIVE, str(code)


def _check_extra(template, username):
    """
    Generic checker for a custom API (GET request).
      404                                   -> UNAVAILABLE (banned)
      200 + response contains "username":"<name>" -> ACTIVE
      200 + 'not found' style text          -> UNAVAILABLE
    If your API answers in a different format, change the 200 branch below.
    """
    url = template.replace("{username}", username)
    try:
        resp = requests.get(url, headers=IG_HEADERS, timeout=(8, 15), allow_redirects=False)
    except requests.Timeout:
        return ERROR, "timeout"
    except requests.RequestException as exc:
        return ERROR, type(exc).__name__
    code = resp.status_code
    if code == 404:
        return UNAVAILABLE, "404"
    if code in (401, 403, 429) or 300 <= code < 400:
        return BLOCKED, str(code)
    if code >= 500:
        return ERROR, str(code)
    if code == 200:
        is_json = True
        try:
            flat = json.dumps(resp.json()).lower()
        except ValueError:
            is_json = False
            flat = resp.text.lower()
        if re.search(r'"username"\s*:\s*"' + re.escape(username) + r'"', flat):
            return ACTIVE, "200"
        if not is_json and re.search(
            r'property="og:url"\s+content="https://www\.instagram\.com/' + re.escape(username) + r'/?"', flat
        ):
            return ACTIVE, "200 html"
        if is_json and any(h in flat for h in NOT_FOUND_HINTS):
            return UNAVAILABLE, "200 not-found"
        return INCONCLUSIVE, "200 without matching profile"
    return INCONCLUSIVE, str(code)


def check_username(username):
    """
    Runs the built-in check and every extra API at the same time.
    Returns (result, detail). ACTIVE if any source says active; the alert is still only
    sent after CONFIRMATIONS consecutive ACTIVE results.
    """
    jobs = [("ig", lambda: _check_builtin(username))]
    for i, tpl in enumerate(EXTRA_APIS, 1):
        jobs.append((f"api{i}", lambda tpl=tpl: _check_extra(tpl, username)))

    with ThreadPoolExecutor(max_workers=len(jobs)) as pool:
        futures = [(label, pool.submit(fn)) for label, fn in jobs]
        results = []
        for label, fut in futures:
            try:
                res, detail = fut.result()
            except Exception as exc:  # never let one API crash the monitor
                res, detail = ERROR, type(exc).__name__
            results.append((label, res, detail))

    detail = ", ".join(f"{label}:{res}({d})" for label, res, d in results)
    for wanted in PRIORITY:
        if any(res == wanted for _, res, _ in results):
            return wanted, detail
    return INCONCLUSIVE, detail


# --------------------------------------------------------------------------
# Alerts
# --------------------------------------------------------------------------


def post_discord(url, content):
    for attempt in range(2):
        try:
            resp = requests.post(
                url,
                json={"content": content, "allowed_mentions": {"parse": []}},
                timeout=(8, 15),
            )
        except requests.RequestException as exc:
            log.warning("Discord webhook failed: %s", type(exc).__name__)
            return False
        if resp.status_code == 429 and attempt == 0:
            try:
                wait = float(resp.json().get("retry_after", 2))
            except (ValueError, AttributeError):
                wait = 2
            time.sleep(min(wait, 10))
            continue
        if resp.status_code >= 300:
            log.warning("Discord webhook returned HTTP %s", resp.status_code)
            return False
        return True
    return False


def send_alert(owner, row, t):
    """Send 'You can use @x again'. Returns True when the Telegram alert was delivered."""
    name = row["username"]
    taken = fmt_duration(t - row["added_at"])
    since = fmt_ts(row["added_at"])
    caption = (
        f"<b>You can use {ig_link(name)} unbanned successfully</b>\n\n"
        f"<b>Taken Time:</b> <code>{taken}</code>\n"
        f"<b>Monitored since:</b> <code>{since}</code>"
    )
    delivered = False
    gifs = db.gifs("alert") or [DEFAULT_ALERT_GIF_URL]
    if gifs:
        try:
            tg(
                "sendAnimation",
                {"chat_id": owner, "animation": random.choice(gifs), "caption": caption, "parse_mode": "HTML"},
            )
            delivered = True
        except TelegramError as exc:
            log.warning("alert GIF failed (%s); sending text", redact(exc))
    if not delivered:
        try:
            tg(
                "sendMessage",
                {"chat_id": owner, "text": caption, "parse_mode": "HTML", "disable_web_page_preview": True},
            )
            delivered = True
        except TelegramError as exc:
            log.error("alert delivery failed: %s", redact(exc))
    webhook = db.get_setting("webhook")
    if webhook and delivered:
        post_discord(
            webhook,
            f"**You can use [@{name}](https://www.instagram.com/{name}) again.**\n\n"
            f"Taken Time: {taken}\nMonitored since: {since}",
        )
    return delivered


# --------------------------------------------------------------------------
# Monitoring worker (own thread, sequential per username, backoff + jitter)
# --------------------------------------------------------------------------


class Monitor(threading.Thread):
    def __init__(self):
        super().__init__(name="monitor", daemon=True)
        self.wake = threading.Event()
        self.heartbeat = time.time()
        self.cooldown_until = 0.0
        self.block_streak = 0

    def cooldown_left(self):
        return max(0.0, self.cooldown_until - time.time())

    def run(self):
        log.info("Monitor started (interval %ss, %s extra API(s))", CHECK_INTERVAL, len(EXTRA_APIS))
        while not STOP.is_set():
            try:
                self.tick()
            except Exception:
                log.exception("monitor tick failed; continuing")
                STOP.wait(5)
        log.info("Monitor stopped")

    def tick(self):
        self.heartbeat = time.time()
        self.wake.clear()
        if db.get_setting("maintenance", "0") == "1":
            STOP.wait(5)
            return
        if self.cooldown_left() > 0:
            STOP.wait(min(5, self.cooldown_left()))
            return
        rows = db.due_users(time.time())
        if not rows:
            delay = db.next_due_delay(time.time())
            wait = 30 if delay is None else min(max(delay, 0.5), 30)
            self.wake.wait(wait)
            return
        for row in rows:
            if STOP.is_set() or self.cooldown_left() > 0:
                break
            if db.get_setting("maintenance", "0") == "1":
                break
            self.heartbeat = time.time()
            self.process(row)
            STOP.wait(gap_delay())  # spacing between different usernames

    def process(self, row):
        uid, name = row["id"], row["username"]
        result, detail = check_username(name)
        t = time.time()
        log.info("check @%s -> %s [%s]", name, result, detail)
        if result in (ACTIVE, UNAVAILABLE):
            self.block_streak = 0
        if result == ACTIVE:
            confirmations = row["confirm_count"] + 1
            if confirmations >= CONFIRMATIONS:
                if send_alert(row["owner_id"], row, t):
                    db.remove_by_id(uid)  # alerted names leave the list
                else:
                    db.update_user(uid, confirm_count=confirmations, last_checked=t, next_check=t + 20)
            else:
                db.update_user(
                    uid, confirm_count=confirmations, fail_count=0, last_checked=t,
                    next_check=t + max(1.0, gap_delay()),
                )
        elif result == UNAVAILABLE:
            changed = {"last_changed": t} if row["status"] != "banned" else {}
            db.update_user(
                uid, status="banned", confirm_count=0, fail_count=0, last_checked=t,
                next_check=t + CHECK_INTERVAL * random.uniform(0.9, 1.2), **changed,
            )
        else:
            fails = row["fail_count"] + 1
            if result == BLOCKED:
                self.block_streak += 1
                pause = min(RATE_LIMIT_COOLDOWN * 2 ** (self.block_streak - 1), MAX_BACKOFF)
                self.cooldown_until = t + pause + random.uniform(0, 30)
                log.warning("Rate limited / blocked; pausing all checks for ~%ss", pause)
            delay = min(CHECK_INTERVAL * (2 ** min(fails, 6)), MAX_BACKOFF) * random.uniform(0.8, 1.3)
            fields = {"fail_count": fails, "confirm_count": 0, "last_checked": t, "next_check": t + delay}
            if fails >= MAX_FAILURES and row["status"] != "banned":
                fields["status"] = "inconclusive"
            db.update_user(uid, **fields)


# --------------------------------------------------------------------------
# Update handling
# --------------------------------------------------------------------------

_stranger_warned = {}


def notify_admin_new_user(user):
    user_id = (user or {}).get("id")
    if not user_id:
        return
    legacy_setting_key = f"joined_user:{user_id}"
    name = " ".join(filter(None, [(user or {}).get("first_name"), (user or {}).get("last_name")]))
    username = (user or {}).get("username")
    details = [f"Name: {esc(name or 'Unknown')}"]
    if username:
        details.append(f"Username: @{esc(username)}")
    details.append(f"User ID: <code>{user_id}</code>")
    delivered = False
    for admin_id in sorted(ADMIN_IDS):
        setting_key = f"{legacy_setting_key}:admin:{admin_id}"
        if db.get_setting(setting_key):
            continue
        result = tg_quiet(
            "sendMessage",
            {
                "chat_id": admin_id,
                "text": "<b>New user started the bot</b>\n" + "\n".join(details),
                "parse_mode": "HTML",
            },
            retries=0,
        )
        if result is not None:
            db.set_setting(setting_key, "1")
            delivered = True
    if delivered:
        db.set_setting(legacy_setting_key, "1")


def is_admin(user):
    return bool(user) and user.get("id") in ADMIN_IDS


def add_result_text(res, invalid, truncated, source):
    lines = [
        f"<b>Added:</b> {len(res['added'])}",
        f"<b>Your monitored:</b> {res['count']}/{MAX_USERNAMES}",
    ]
    if res["dup"]:
        lines.append("Already in your list: " + ", ".join("@" + esc(n) for n in res["dup"][:10]))
    if res["over"]:
        lines.append(
            f"List limit ({MAX_USERNAMES}) reached, not added: "
            + ", ".join("@" + esc(n) for n in res["over"][:10])
        )
    if invalid:
        word = "lines" if source == "file" else "entries"
        shown = ", ".join(esc(i) for i in invalid[:5])
        more = f" (+{len(invalid) - 5} more)" if len(invalid) > 5 else ""
        lines.append(f"Invalid {word} skipped: {len(invalid)} — {shown}{more}")
    if truncated:
        lines.append(f"Only the first {MAX_TOKENS} entries were read.")
    return "\n".join(lines)


def process_add(chat_id, text, state, owner_id, source="text"):
    valid, dupes_in_input, invalid, truncated = parse_usernames(text)
    if not valid and not dupes_in_input:
        msg = "No valid usernames found. Use letters, numbers, dots and underscores (max 30 characters)."
        if invalid:
            msg += "\nInvalid: " + ", ".join(esc(i) for i in invalid[:5])
        msg += "\n\nSend usernames (one per line) or upload a .txt file."
        send_screen(chat_id, msg, CANCEL_KB)
        return
    res = db.add_usernames(owner_id, valid, MAX_USERNAMES)
    res["dup"] = dupes_in_input + res["dup"]
    db.clear_state(owner_id)
    strip_buttons(state.get("chat_id"), state.get("message_id"))
    send_screen(chat_id, add_result_text(res, invalid, truncated, source), keyboard_for(owner_id))
    if res["added"] and MONITOR:
        MONITOR.wake.set()


def download_txt(document):
    """Download a Telegram document (size-capped). Returns text or raises ValueError with a user message."""
    name = (document.get("file_name") or "").lower()
    mime = (document.get("mime_type") or "").lower()
    if not (name.endswith(".txt") or mime == "text/plain"):
        raise ValueError("Please upload a plain .txt file.")
    if (document.get("file_size") or 0) > MAX_FILE_BYTES:
        raise ValueError(f"File too large (max {MAX_FILE_BYTES // 1000} KB).")
    try:
        info = tg("getFile", {"file_id": document["file_id"]})
        url = f"{TELEGRAM_API_BASE}/file/bot{BOT_TOKEN}/{info['file_path']}"
        with tg_session.get(url, timeout=(10, 30), stream=True) as resp:
            if resp.status_code != 200:
                raise ValueError("Could not download the file from Telegram. Please try again.")
            data = b""
            for chunk in resp.iter_content(chunk_size=8192):
                data += chunk
                if len(data) > MAX_FILE_BYTES:
                    break
    except TelegramError as exc:
        raise ValueError(f"Could not fetch the file: {exc.description}")
    except requests.RequestException:
        raise ValueError("Network error while downloading the file. Please try again.")
    if len(data) > MAX_FILE_BYTES:
        raise ValueError(f"File too large (max {MAX_FILE_BYTES // 1000} KB).")
    if b"\x00" in data:
        raise ValueError("That file doesn't look like plain text.")
    try:
        return data.decode("utf-8-sig")
    except UnicodeDecodeError:
        raise ValueError("The file must be UTF-8 text.")


def handle_state_message(msg, state, owner_id):
    chat_id = msg["chat"]["id"]
    st = state["state"]
    text = (msg.get("text") or "").strip()

    if st == "access_key_user_id":
        if text.lower() == "cancel":
            db.clear_state(owner_id)
            send_screen(chat_id, "Access key creation cancelled.", ADMIN_PANEL_KB)
            return
        try:
            target_id = int(text)
        except ValueError:
            send_screen(chat_id, "Send a numeric Telegram user ID, or send 'cancel'.", CANCEL_KB)
            return
        if target_id <= 0 or target_id in ADMIN_IDS:
            send_screen(chat_id, "Enter a valid non-admin Telegram user ID.", CANCEL_KB)
            return
        key = secrets.token_urlsafe(24)
        db.set_access_key(target_id, hashlib.sha256(key.encode("utf-8")).hexdigest())
        db.clear_state(owner_id)
        strip_buttons(state.get("chat_id"), state.get("message_id"))
        send_screen(
            chat_id,
            f"<b>Access key created</b>\nUser ID: <code>{target_id}</code>\n"
            f"Key: <code>{esc(key)}</code>\n\nThis key is valid only for that user ID and can be used once.",
            ADMIN_PANEL_KB,
        )
        return

    if st == "remove_access_user_id":
        if text.lower() == "cancel":
            db.clear_state(owner_id)
            send_screen(chat_id, "Access removal cancelled.", ADMIN_PANEL_KB)
            return
        try:
            target_id = int(text)
        except ValueError:
            send_screen(chat_id, "Send a numeric Telegram user ID, or send 'cancel'.", CANCEL_KB)
            return
        removed = db.remove_access_key(target_id)
        db.clear_state(owner_id)
        strip_buttons(state.get("chat_id"), state.get("message_id"))
        result = "Access removed." if removed else "No access key found for that user ID."
        send_screen(chat_id, f"{result}\nUser ID: <code>{target_id}</code>", ADMIN_PANEL_KB)
        return

    if st == "broadcast_message":
        if text.lower() == "cancel":
            db.clear_state(owner_id)
            send_screen(chat_id, "Broadcast cancelled.", ADMIN_PANEL_KB)
            return
        if not text:
            send_screen(chat_id, "Send the broadcast text, or send 'cancel'.", CANCEL_KB)
            return
        db.clear_state(owner_id)
        sent = failed = 0
        for target_id in db.bot_users():
            if target_id in ADMIN_IDS:
                continue
            if tg_quiet("sendMessage", {"chat_id": target_id, "text": text}, retries=0) is None:
                failed += 1
            else:
                sent += 1
            STOP.wait(0.05)
        strip_buttons(state.get("chat_id"), state.get("message_id"))
        send_screen(chat_id, f"Broadcast complete. Sent: {sent}; failed: {failed}.", ADMIN_PANEL_KB)
        return

    if st == "add":
        if msg.get("document"):
            try:
                content = download_txt(msg["document"])
            except ValueError as exc:
                send_screen(chat_id, f"⚠️ {esc(exc)}\n\nSend usernames (one per line) or upload a .txt file.", CANCEL_KB)
                return
            process_add(chat_id, content, state, owner_id, source="file")
        elif text:
            process_add(chat_id, text, state, owner_id)
        else:
            send_screen(chat_id, "Send usernames (one per line) or upload a .txt file.", CANCEL_KB)
        return

    if st == "webhook":
        if not text:
            send_screen(chat_id, WEBHOOK_PROMPT, BACK_SETTINGS_KB)
            return
        tg_quiet("deleteMessage", {"chat_id": chat_id, "message_id": msg["message_id"]}, retries=0)  # hide secret
        strip_buttons(state.get("chat_id"), state.get("message_id"))
        if text.lower() == "clear":
            db.del_setting("webhook")
            db.clear_state(owner_id)
            body, kb = webhook_screen()
            send_screen(chat_id, "✅ Webhook removed.\n\n" + body, kb)
            return
        if not WEBHOOK_RE.match(text):
            db.set_state(owner_id, "webhook", chat_id, None)
            send_screen(chat_id, "⚠️ That is not a valid Discord webhook URL.\n\n" + esc(WEBHOOK_PROMPT), BACK_SETTINGS_KB)
            return
        try:
            probe = requests.get(text, timeout=(8, 10))
            if probe.status_code in (401, 404):
                db.set_state(owner_id, "webhook", chat_id, None)
                send_screen(chat_id, "⚠️ Discord says this webhook does not exist (it may have been deleted).\n\n" + esc(WEBHOOK_PROMPT), BACK_SETTINGS_KB)
                return
        except requests.RequestException:
            log.info("webhook verification skipped (network error); saving anyway")
        db.set_setting("webhook", text)
        db.clear_state(owner_id)
        _, kb = webhook_screen()
        send_screen(chat_id, "✅ Webhook saved successfully.", kb)
        return

    if st in ("gif:menu", "gif:alert"):
        kind = st.split(":")[1]
        strip_buttons(state.get("chat_id"), state.get("message_id"))
        if text.lower() == "clear":
            db.clear_gifs(kind)
            db.clear_state(owner_id)
            send_screen(chat_id, f"✅ {kind.title()} GIF removed.", BACK_SETTINGS_KB)
            return
        anim = msg.get("animation")
        doc = msg.get("document")
        if not anim and doc and (doc.get("mime_type") or "") in ("image/gif", "video/mp4"):
            anim = doc
        if not anim:
            db.set_state(owner_id, st, chat_id, None)
            send_screen(chat_id, "⚠️ Please send a GIF (animation), or send 'clear'.", BACK_SETTINGS_KB)
            return
        if kind == "menu":
            db.set_menu_gif(anim["file_id"])
        elif not db.add_alert_gif(anim["file_id"]):
            db.clear_state(owner_id)
            send_screen(chat_id, f"⚠️ Alert GIF folder is full ({MAX_ALERT_GIFS}). Send 'clear' to empty it.", BACK_SETTINGS_KB)
            return
        db.clear_state(owner_id)
        send_screen(chat_id, f"✅ {kind.title()} GIF saved successfully.", BACK_SETTINGS_KB)
        return

    db.clear_state(owner_id)
    send_screen(chat_id, WELCOME, keyboard_for(owner_id))


def handle_message(msg):
    chat = msg.get("chat") or {}
    if chat.get("type") != "private":
        return
    chat_id = chat["id"]
    user = msg.get("from")
    user_id = (user or {}).get("id")
    if not user_id:
        return
    text = (msg.get("text") or "").strip()
    low = text.lower()
    command = low.split(maxsplit=1)[0].split("@", 1)[0] if low else ""
    admin = is_admin(user)

    if not admin:
        db.register_bot_user(user_id)
        if command == "/start":
            notify_admin_new_user(user)
        if db.get_setting("maintenance", "0") == "1":
            send_screen(chat_id, "The bot is under maintenance. Please try again later.", ACCESS_KB)
            return
    if not admin and not db.has_access(user_id):
        if command in ("/start", "/menu", "/help") or not text:
            db.clear_state(user_id)
            send_screen(chat_id, ACCESS_REQUIRED, ACCESS_KB)
        elif db.redeem_access_key(user_id, text):
            db.clear_state(user_id)
            send_screen(chat_id, "<b>Access granted.</b>\n\n" + WELCOME, USER_KB)
        else:
            entering_key = (db.get_state(user_id) or {}).get("state") == "redeem_access_key"
            if entering_key:
                send_screen(chat_id, "That key is invalid or assigned to another user. Try again.", ACCESS_ENTRY_KB)
            else:
                send_screen(chat_id, "That key is invalid or is assigned to another user.\n\n" + ACCESS_REQUIRED, ACCESS_KB)
        return

    if admin and command == "/admin":
        db.clear_state(user_id)
        send_screen(chat_id, "<b>Admin panel</b>\n\nManage access, broadcasts, maintenance, and GIFs.", ADMIN_PANEL_KB)
        return

    if command in ("/start", "/menu", "/help"):
        db.clear_state(user_id)
        send_screen(chat_id, WELCOME, keyboard_for(user_id))
        return
    if command == "/maintenance" and admin:
        arg = low.split()[1] if len(low.split()) > 1 else ""
        if arg in ("on", "off"):
            db.set_setting("maintenance", "1" if arg == "on" else "0")
            send_screen(chat_id, f"Maintenance: {arg.upper()}", MAIN_KB)
        else:
            send_screen(chat_id, "Usage: /maintenance on  or  /maintenance off", MAIN_KB)
        return

    state = db.get_state(user_id)
    if state:
        handle_state_message(msg, state, user_id)
    else:
        send_screen(chat_id, "Use the buttons below to manage your monitoring list.", keyboard_for(user_id))


def handle_callback(cq):
    cq_id = cq["id"]
    user = cq.get("from") or {}
    owner_id = user.get("id")
    msg = cq.get("message")
    data = cq.get("data") or ""
    if not owner_id or not msg or len(data) > 64:
        tg_quiet("answerCallbackQuery", {"callback_query_id": cq_id}, retries=0)
        return
    admin = is_admin(user)
    authorized = admin or db.has_access(owner_id)
    if data == "developer":
        tg_quiet("answerCallbackQuery", {"callback_query_id": cq_id}, retries=0)
        edit_screen(msg, "Bot developed by @fameneedsme", keyboard_for(owner_id) if authorized else ACCESS_KB)
        return
    if data == "cancel_key_entry":
        tg_quiet("answerCallbackQuery", {"callback_query_id": cq_id}, retries=0)
        db.clear_state(owner_id)
        edit_screen(msg, ACCESS_REQUIRED, ACCESS_KB)
        return
    if not admin and db.get_setting("maintenance", "0") == "1":
        tg_quiet(
            "answerCallbackQuery",
            {"callback_query_id": cq_id, "text": "The bot is under maintenance.", "show_alert": True},
            retries=0,
        )
        edit_screen(msg, "The bot is under maintenance. Please try again later.", ACCESS_KB)
        return
    if not authorized:
        if data == "enter_access_key":
            tg_quiet("answerCallbackQuery", {"callback_query_id": cq_id}, retries=0)
            db.set_state(owner_id, "redeem_access_key", msg["chat"]["id"], msg["message_id"])
            edit_screen(msg, "Send the access key provided by the admin.", ACCESS_ENTRY_KB)
            return
        tg_quiet(
            "answerCallbackQuery",
            {"callback_query_id": cq_id, "text": "Access key required.", "show_alert": True},
            retries=0,
        )
        edit_screen(msg, ACCESS_REQUIRED, ACCESS_KB)
        return
    admin_only = {
        "admin_panel", "settings", "back_settings", "gif", "gif:menu", "gif:alert",
        "gif:remove:menu", "gif:remove:alert", "webhook", "wh_set", "wh_remove",
        "create_access_key", "remove_access", "broadcast",
        "maintenance:on", "maintenance:off",
    }
    if not admin and data in admin_only:
        tg_quiet(
            "answerCallbackQuery",
            {"callback_query_id": cq_id, "text": "Admin only.", "show_alert": True},
            retries=0,
        )
        return
    tg_quiet("answerCallbackQuery", {"callback_query_id": cq_id}, retries=0)
    chat_id, message_id = msg["chat"]["id"], msg["message_id"]

    if data in ("menu", "back_menu", "cancel"):
        db.clear_state(owner_id)
        edit_screen(msg, "Main menu", keyboard_for(owner_id))

    elif data == "admin_panel":
        db.clear_state(owner_id)
        edit_screen(msg, "<b>Admin panel</b>", ADMIN_PANEL_KB)

    elif data == "create_access_key":
        db.set_state(owner_id, "access_key_user_id", chat_id, message_id)
        edit_screen(msg, "Send the Telegram user ID for this key, or send 'cancel'.", CANCEL_KB)

    elif data == "remove_access":
        db.set_state(owner_id, "remove_access_user_id", chat_id, message_id)
        edit_screen(msg, "Send the Telegram user ID whose access should be removed, or send 'cancel'.", CANCEL_KB)

    elif data == "broadcast":
        db.set_state(owner_id, "broadcast_message", chat_id, message_id)
        edit_screen(msg, "Send the broadcast text, or send 'cancel'.", CANCEL_KB)

    elif data in ("maintenance:on", "maintenance:off"):
        enabled = data.endswith(":on")
        db.set_setting("maintenance", "1" if enabled else "0")
        if not enabled and MONITOR:
            MONITOR.wake.set()
        edit_screen(msg, f"Maintenance {'ON' if enabled else 'OFF'}.", ADMIN_PANEL_KB)

    elif data == "add":
        db.set_state(owner_id, "add", chat_id, message_id)
        edit_screen(msg, "Send usernames (one per line) or upload a .txt file.", CANCEL_KB)

    elif data == "remove":
        db.clear_state(owner_id)
        rows = db.list_users(owner_id)
        if not rows:
            edit_screen(msg, "<b>Remove Username</b>\n\nYour list is empty.", BACK_MENU_KB)
        else:
            buttons = [btn("@" + r["username"], "rm:" + r["username"]) for r in rows]
            keyboard = [buttons[i:i + 2] for i in range(0, len(buttons), 2)]
            keyboard.append([btn("Back", "back_menu")])
            edit_screen(msg, "<b>Remove Username</b>\n\nSelect a username to remove:", {"inline_keyboard": keyboard})

    elif data.startswith("rm:"):
        name = data[3:]
        if not USERNAME_RE.match(name):
            return
        removed = db.remove_user(owner_id, name)
        head = f"Removed: @{esc(name)}" if removed else f"@{esc(name)} is not in your list."
        edit_screen(msg, f"{head}\n<b>Your monitored:</b> {db.count_owner(owner_id)}/{MAX_USERNAMES}", keyboard_for(owner_id))

    elif data in ("settings", "back_settings"):
        db.clear_state(owner_id)
        edit_screen(msg, "<b>Settings</b>\n\nSelect a setting:", SETTINGS_KB)

    elif data == "gif":
        db.clear_state(owner_id)
        edit_screen(msg, "<b>Add Gif</b>\n\nWhich GIF do you want to set?", GIF_KB)

    elif data == "gif:remove:menu":
        db.clear_gifs("menu")
        edit_screen(msg, "Welcome GIF removed. The default GIF is active.", ADMIN_PANEL_KB)

    elif data == "gif:remove:alert":
        db.clear_gifs("alert")
        edit_screen(msg, "Unbanned GIFs removed. The default GIF is active.", ADMIN_PANEL_KB)

    elif data in ("gif:menu", "gif:alert"):
        db.set_state(owner_id, data, chat_id, message_id)
        if data == "gif:menu":
            prompt = "Send a GIF to use as the menu GIF, or send 'clear' to remove it."
        else:
            prompt = ("Send a GIF to add to the alert GIF folder (one is picked at random for each alert), "
                      "or send 'clear' to empty the folder.")
        edit_screen(msg, prompt, BACK_SETTINGS_KB)

    elif data == "webhook":
        db.clear_state(owner_id)
        body, kb = webhook_screen()
        edit_screen(msg, body, kb)

    elif data == "wh_set":
        db.set_state(owner_id, "webhook", chat_id, message_id)
        edit_screen(msg, WEBHOOK_PROMPT, BACK_SETTINGS_KB)

    elif data == "wh_remove":
        db.del_setting("webhook")
        db.clear_state(owner_id)
        body, kb = webhook_screen()
        edit_screen(msg, "✅ Webhook removed.\n\n" + body, kb)

    elif data == "status":
        db.clear_state(owner_id)
        edit_screen(msg, status_text(owner_id), keyboard_for(owner_id))

    elif data == "list":
        db.clear_state(owner_id)
        edit_screen(msg, list_text(owner_id), keyboard_for(owner_id))

    elif data == "close":
        db.clear_state(owner_id)
        try:
            tg("deleteMessage", {"chat_id": chat_id, "message_id": message_id}, retries=0)
        except TelegramError:
            edit_screen(msg, "Closed. Send /start to open the menu again.", {"inline_keyboard": []})

    else:
        log.info("unknown callback data ignored")


def handle_update(update):
    if "callback_query" in update:
        handle_callback(update["callback_query"])
    elif "message" in update:
        handle_message(update["message"])


# --------------------------------------------------------------------------
# Health-check web server (so Render sees an open port)
# --------------------------------------------------------------------------


class HealthHandler(BaseHTTPRequestHandler):
    def _reply(self, send_body):
        body = b"ok"
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        if send_body:
            self.wfile.write(body)

    def do_GET(self):
        self._reply(True)

    def do_HEAD(self):
        self._reply(False)

    def log_message(self, *args):
        pass


def start_health_server(port):
    server = ThreadingHTTPServer(("0.0.0.0", port), HealthHandler)
    server.daemon_threads = True
    threading.Thread(target=server.serve_forever, name="health", daemon=True).start()
    log.info("Health server listening on port %s", port)
    return server


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def acquire_single_instance_lock(db_path):
    try:
        import fcntl
    except ImportError:  # e.g. Windows
        return None
    handle = open(db_path + ".lock", "w")
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log.error("Another bot process is already using this database. Exiting.")
        sys.exit(1)
    return handle


def poll_loop():
    offset = None
    backoff = 1.0
    while not STOP.is_set():
        params = {"timeout": 25, "allowed_updates": ["message", "callback_query"]}
        if offset is not None:
            params["offset"] = offset
        try:
            updates = tg("getUpdates", params, timeout=(10, 40), retries=0)
            backoff = 1.0
        except TelegramError as exc:
            if exc.code == 401:
                log.critical("Telegram rejected BOT_TOKEN (401). Check the BOT_TOKEN environment variable.")
                STOP.set()
                return
            if exc.code == 409:
                log.warning("Another instance is polling this bot (409 Conflict). Waiting...")
                wait = 5 + random.uniform(0, 5)
            else:
                log.warning("getUpdates failed: %s", redact(exc))
                wait = backoff + random.uniform(0, 1)
                backoff = min(backoff * 2, 60)
            STOP.wait(wait)
            continue
        for update in updates or []:
            offset = update["update_id"] + 1
            try:
                handle_update(update)
            except Exception:
                log.exception("failed to handle update %s", update.get("update_id"))
                chat = ((update.get("message") or {}).get("chat") or {}).get("id")
                if chat and is_admin(update["message"].get("from")):
                    tg_quiet("sendMessage", {"chat_id": chat, "text": "⚠️ Something went wrong. Please try again."}, retries=0)


def main():
    global db, MONITOR
    setup_logging()
    if not BOT_TOKEN:
        log.critical("BOT_TOKEN is not set. Add it in Render -> Environment, then redeploy.")
        sys.exit(1)

    db = DB(DATABASE_PATH)
    lock_handle = acquire_single_instance_lock(DATABASE_PATH)
    log.info("Database: %s", os.path.abspath(DATABASE_PATH))
    log.info("Extra APIs loaded: %s", len(EXTRA_APIS))

    server = start_health_server(PORT)

    def shutdown(signum, _frame):
        log.info("Signal %s received; shutting down", signum)
        STOP.set()

    signal.signal(signal.SIGTERM, shutdown)
    signal.signal(signal.SIGINT, shutdown)

    # Verify the token (retry on network trouble, stop on a bad token).
    while not STOP.is_set():
        try:
            me = tg("getMe")
            log.info("Logged in as @%s", me.get("username"))
            break
        except TelegramError as exc:
            if exc.code == 401:
                log.critical("Telegram rejected BOT_TOKEN (401). Check the BOT_TOKEN environment variable.")
                STOP.set()
            else:
                log.warning("getMe failed: %s; retrying", redact(exc))
                STOP.wait(5)

    if not STOP.is_set():
        tg_quiet("deleteWebhook", {"drop_pending_updates": False})
        tg_quiet(
            "setMyCommands",
            {"commands": [{"command": "start", "description": "Open the main menu"},
                          {"command": "menu", "description": "Open the main menu"},
                          {"command": "admin", "description": "Manage user access keys"}]},
        )
        MONITOR = Monitor()
        MONITOR.start()
        try:
            poll_loop()
        finally:
            STOP.set()

    log.info("Stopping...")
    if MONITOR:
        MONITOR.wake.set()
        MONITOR.join(timeout=10)
    server.shutdown()
    db.close()
    if lock_handle:
        lock_handle.close()
    log.info("Bye")
    sys.exit(0 if BOT_TOKEN else 1)


if __name__ == "__main__":
    main()
