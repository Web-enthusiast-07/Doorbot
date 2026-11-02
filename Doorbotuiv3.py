#!/usr/bin/env python3
"""Smart Doorbell - touchscreen dashboard for Raspberry Pi 4.

    python3 doorbell_ui.py                       window
    python3 doorbell_ui.py --fullscreen          full screen
    python3 doorbell_ui.py --fullscreen --touch  full screen, hide mouse pointer
    python3 doorbell_ui.py --demo                try the UI on any PC (no Pi needed)

Telegram: put BOT_TOKEN and CHAT_ID in a file called config.py next to this
script (or type them in below). Keyboard: Space = ring the bell, Esc = home.
"""

import glob
import json
import math
import os
import queue
import shutil
import sys
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
import traceback
from collections import OrderedDict
from datetime import datetime

import requests
from PIL import Image, ImageDraw, ImageOps, ImageTk

# ======================================================================
# SETTINGS - change these if needed
# ======================================================================
BOT_TOKEN = ""             # or put both in config.py (recommended)
CHAT_ID = ""
BUTTON_PIN = 17            # doorbell push button   (GPIO17, pin 11)
BUZZER_PIN = 27            # buzzer signal          (GPIO27, pin 13)
LOCK_PIN = 22              # optional door relay    (GPIO22, pin 15)
LOCK_ACTIVE_HIGH = True    # set False for relay boards that switch on LOW
PHOTO_WIDTH = 1920         # saved photo width (height follows the camera view)
FULL_RES_PHOTOS = False    # True = save full 16MP photos (slower, bigger files)
RING_COOLDOWN = 3          # ignore repeat presses within this many seconds
PHOTO_DIR = os.path.expanduser("~/photos")
SETTINGS_FILE = os.path.expanduser("~/.doorbell_settings.json")

try:
    from config import BOT_TOKEN, CHAT_ID  # noqa: F811
except ImportError:
    pass
TG_READY = bool(BOT_TOKEN and CHAT_ID)
TELEGRAM_URL = f"https://api.telegram.org/bot{BOT_TOKEN}/sendPhoto"

# ======================================================================
# Hardware (falls back to a simulation when not running on a Pi)
# ======================================================================
DEMO = "--demo" in sys.argv
if not DEMO:
    try:
        from gpiozero import Button, Buzzer, OutputDevice
        from picamera2 import Picamera2
    except ImportError as err:
        print(f"Pi libraries not found ({err}) - starting in demo mode.")
        DEMO = True
if DEMO:
    class _Dummy:
        def __init__(self, *a, **k):
            self.when_pressed = None

        def on(self): pass
        def off(self): pass
        def beep(self, *a, **k): pass
        def close(self): pass

    Button = Buzzer = OutputDevice = _Dummy

RESAMPLE = getattr(Image, "Resampling", Image).BILINEAR
SMOOTH = getattr(Image, "Resampling", Image).LANCZOS

# ======================================================================
# Colours
# ======================================================================
WHITE = "#ffffff"
SUB = "#d9cfec"          # secondary text
INK = "#33295c"          # dark purple (icons on white tiles)
PANEL = "#2f2252"        # dark cards
PANEL2 = "#3e2f69"       # raised cards / dialogs
OFF = "#6b5a8f"          # switched-off tile / switch track
GREEN = "#2fbf71"
RED = "#e5484d"
ACCENT = "#ff6277"       # capture button
BLACK = "#0d0818"


def shade(color, f):
    h = color.lstrip("#")
    r, g, b = (int(h[i:i + 2], 16) for i in (0, 2, 4))
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(v * f))) for v in (r, g, b))


def make_gradient(w, h):
    """Purple to copper diagonal gradient, like a video-intercom home screen."""
    base = Image.linear_gradient("L")
    vert = base.resize((w, h), RESAMPLE)
    horz = base.rotate(90).resize((w, h), RESAMPLE)
    mix = Image.blend(vert, horz, 0.6)
    return ImageOps.colorize(mix, black="#241a4d", mid="#52346e", white="#a2685a")


def rrect(c, x1, y1, x2, y2, r, **kw):
    r = max(0, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
    # doubled points keep the straight edges straight when smooth=True
    pts = [x1 + r, y1, x1 + r, y1, x2 - r, y1, x2 - r, y1, x2, y1, x2, y1 + r,
           x2, y1 + r, x2, y2 - r, x2, y2 - r, x2, y2, x2 - r, y2, x2 - r, y2,
           x1 + r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y2 - r, x1, y1 + r,
           x1, y1 + r, x1, y1]
    return c.create_polygon(pts, smooth=True, **kw)


def fit(box_w, box_h, aspect):
    w = min(box_w, box_h * aspect)
    return max(2, int(w)), max(2, int(w / aspect))


# ======================================================================
# Icons drawn with canvas shapes (no emoji or image files needed)
# ======================================================================
def draw_icon(c, name, cx, cy, r, col, bg=WHITE, tags=()):
    u = r / 10.0
    w = max(2, int(round(u * 1.5)))

    def P(pts):
        return [cx + v * u if i % 2 == 0 else cy + v * u for i, v in enumerate(pts)]

    def line(*pts, width=None):
        c.create_line(*P(pts), fill=col, width=width or w, capstyle="round",
                      joinstyle="round", tags=tags)

    def poly(*pts, fill=None):
        c.create_polygon(*P(pts), fill=fill or col, outline="", tags=tags)

    def oval(x1, y1, x2, y2, fill=""):
        a = P([x1, y1, x2, y2])
        if fill:
            c.create_oval(*a, fill=fill, outline="", tags=tags)
        else:
            c.create_oval(*a, fill="", outline=col, width=w, tags=tags)

    def arc(x1, y1, x2, y2, start, extent):
        c.create_arc(*P([x1, y1, x2, y2]), start=start, extent=extent, style="arc",
                     outline=col, width=w, tags=tags)

    def box(x1, y1, x2, y2, rad, fill=""):
        a = P([x1, y1, x2, y2])
        rrect(c, *a, rad * u, fill=fill, outline="" if fill else col,
              width=w, tags=tags)

    if name == "camera":
        box(-9, -5, 9, 7, 2)
        line(-4, -5, -2.5, -8, 2.5, -8, 4, -5)
        oval(-3.5, -3, 3.5, 4)
    elif name == "live":
        box(-9, -7, 9, 4, 2)
        line(0, 4, 0, 8)
        line(-4, 8, 4, 8)
        poly(-2, -4.5, -2, 1.5, 3, -1.5)
    elif name == "gallery":
        box(-9, -8, 9, 8, 2)
        oval(2.5, -5, 5.5, -2, fill=col)
        line(-8, 6, -3, 0, 1, 4, 4, 1, 8, 6)
    elif name in ("lock", "unlock"):
        box(-7, -1, 7, 9, 2, fill=col)
        oval(-1.4, 2.3, 1.4, 5.1, fill=bg)
        if name == "lock":
            arc(-4.5, -9.5, 4.5, -0.5, 0, 180)
            line(-4.5, -5, -4.5, -1)
            line(4.5, -5, 4.5, -1)
        else:
            arc(-4.5, -11.5, 4.5, -2.5, 0, 180)
            line(-4.5, -7, -4.5, -1)
            line(4.5, -7, 4.5, -5)
    elif name == "bell":
        c.create_arc(*P([-6, -8, 6, 4]), start=0, extent=180, style="chord",
                     fill=col, outline="", tags=tags)
        poly(-6, -2, 6, -2, 8.5, 5, -8.5, 5)
        oval(-2, 6, 2, 9.5, fill=col)
        oval(-1, -10.5, 1, -8.5, fill=col)
    elif name in ("sound", "mute"):
        poly(-9, -3, -5, -3, 0, -8, 0, 8, -5, 3, -9, 3)
        if name == "sound":
            arc(-2, -4.5, 5.5, 4.5, -60, 120)
            arc(-2, -8.5, 9.5, 8.5, -60, 120)
        else:
            line(3, -4, 9, 4)
            line(9, -4, 3, 4)
    elif name == "send":
        poly(-9, -1, 9, -8, 3, 9, -1, 3)
        c.create_line(*P([-1, 3, 5, -3]), fill=bg, width=max(1, w - 1),
                      capstyle="round", tags=tags)
    elif name == "gear":
        oval(-5, -5, 5, 5)
        oval(-1.8, -1.8, 1.8, 1.8)
        for k in range(8):
            a = math.radians(k * 45)
            line(6.5 * math.cos(a), 6.5 * math.sin(a), 9.2 * math.cos(a),
                 9.2 * math.sin(a), width=int(w * 1.7))
    elif name == "power":
        arc(-7, -6, 7, 8, 120, 300)
        line(0, -9, 0, 0)
    elif name == "back":
        line(3.5, -8, -4.5, 0, 3.5, 8)
    elif name == "left":
        line(3, -8, -4, 0, 3, 8)
    elif name == "right":
        line(-3, -8, 4, 0, -3, 8)
    elif name == "trash":
        line(-8, -6, 8, -6)
        line(-3, -6, -3, -9, 3, -9, 3, -6)
        line(-6, -4, -5, 9, 5, 9, 6, -4)
        line(-2, -1, -2, 6)
        line(2, -1, 2, 6)
    elif name in ("wifi", "nowifi"):
        arc(-4, 2, 4, 10, 45, 90)
        arc(-8, -2, 8, 14, 45, 90)
        arc(-12, -6, 12, 18, 45, 90)
        oval(-1.2, 5, 1.2, 7.4, fill=col)
        if name == "nowifi":
            line(-9, -8, 9, 9)
    elif name == "check":
        line(-7, 0, -2, 6, 8, -6)
    elif name == "plus":
        line(-7, 0, 7, 0)
        line(0, -7, 0, 7)
    elif name == "minus":
        line(-7, 0, 7, 0)
    elif name == "person":
        oval(-3.5, -9, 3.5, -2)
        arc(-8, 1, 8, 17, 0, 180)


# ======================================================================
# Helpers for photos
# ======================================================================
def list_photos():
    return sorted(glob.glob(os.path.join(PHOTO_DIR, "*.jpg")), reverse=True)


def describe(path):
    name = os.path.basename(path)
    kind = "Visitor" if name.startswith("visitor") else "Manual" if name.startswith("manual") else "Photo"
    try:
        stamp = datetime.strptime(name.split("_", 1)[1].rsplit(".", 1)[0].split("-")[0],
                                  "%Y%m%d_%H%M%S")
    except Exception:
        stamp = datetime.fromtimestamp(os.path.getmtime(path))
    return kind, stamp


def day_label(stamp):
    days = (datetime.now().date() - stamp.date()).days
    if days == 0:
        return "Today"
    if days == 1:
        return "Yesterday"
    return stamp.strftime("%d %b %Y")


def clock12(stamp):
    return stamp.strftime("%I:%M %p").lstrip("0")


def new_photo_path(prefix):
    os.makedirs(PHOTO_DIR, exist_ok=True)
    base = os.path.join(PHOTO_DIR, datetime.now().strftime(f"{prefix}_%Y%m%d_%H%M%S"))
    path, n = base + ".jpg", 0
    while os.path.exists(path):
        n += 1
        path = f"{base}-{n}.jpg"
    return path


DEFAULTS = {"telegram": True, "sound": True, "chime": "Double", "open_seconds": 5}
CHIMES = {"Single": 1, "Double": 2, "Triple": 3}


def load_settings():
    cfg = dict(DEFAULTS)
    try:
        with open(SETTINGS_FILE) as f:
            cfg.update(json.load(f))
    except Exception:
        pass
    if cfg["chime"] not in CHIMES:
        cfg["chime"] = DEFAULTS["chime"]
    try:
        cfg["open_seconds"] = max(2, min(30, int(cfg["open_seconds"])))
    except Exception:
        cfg["open_seconds"] = DEFAULTS["open_seconds"]
    return cfg


def save_settings(cfg):
    try:
        with open(SETTINGS_FILE, "w") as f:
            json.dump(cfg, f)
    except Exception:
        pass


# ======================================================================
# Camera worker: the only thread that touches the camera
# ======================================================================
def demo_frame(size, t):
    w, h = size
    img = ImageOps.colorize(Image.linear_gradient("L").resize(size), "#1d3557", "#a8dadc")
    d = ImageDraw.Draw(img)
    d.rectangle((0, int(h * 0.72), w, h), fill="#2a9d8f")
    x, y, rad = int((math.sin(t) * 0.3 + 0.5) * w), int(h * 0.55), h // 9
    d.ellipse((x - rad, y - rad, x + rad, y + rad), fill="#f4a261")
    d.text((12, 12), "DEMO CAMERA  " + time.strftime("%H:%M:%S"), fill="white")
    return img


class CameraWorker(threading.Thread):
    def __init__(self, events):
        super().__init__(daemon=True)
        self.events = events
        self.cmds = queue.Queue()
        self.want_preview = False
        self.target = (640, 480)
        self.aspect = 4 / 3
        self.alive = True
        self.ok = False
        self.error = ""
        self.cam = None
        self.still_cfg = None
        self._frame = None
        self._lock = threading.Lock()

    def take_frame(self):
        with self._lock:
            frame, self._frame = self._frame, None
        return frame

    def capture(self, path, tag):
        self.cmds.put((path, tag))

    # -- setup -----------------------------------------------------------
    def open(self):
        if DEMO:
            self.ok = True
            return
        cam = Picamera2()
        full = tuple(cam.camera_properties["PixelArraySize"])
        modes = list(cam.sensor_modes)

        def area(m):
            return m["size"][0] * m["size"][1]

        # Only sensor modes that see the WHOLE picture. Small modes such as 1080p
        # are cropped, which is what made the old preview look zoomed in.
        wide = [m for m in modes if m["crop_limits"][2] >= 0.95 * full[0]
                and m["crop_limits"][3] >= 0.95 * full[1]] or modes
        enough = [m for m in wide if m["size"][0] >= PHOTO_WIDTH]
        mode = min(enough, key=area) if enough else max(wide, key=area)
        mw, mh = mode["size"]
        pw = min(PHOTO_WIDTH, mw)
        pw -= pw % 2
        ph = int(round(pw * mh / mw))
        ph -= ph % 2
        self.aspect = pw / ph

        cfg = cam.create_preview_configuration(
            main={"size": (pw, ph), "format": "BGR888"},   # BGR888 = RGB byte order
            sensor={"output_size": mode["size"], "bit_depth": mode["bit_depth"]},
            controls={"ScalerCrop": tuple(mode["crop_limits"])},
        )
        if FULL_RES_PHOTOS:
            big = max(wide, key=area)
            self.still_cfg = cam.create_still_configuration(
                main={"size": big["size"]},
                sensor={"output_size": big["size"], "bit_depth": big["bit_depth"]},
            )
        cam.configure(cfg)
        cam.start()
        time.sleep(1.5)          # let auto exposure settle
        self.cam = cam
        self.ok = True

    # -- thread ----------------------------------------------------------
    def run(self):
        try:
            self.open()
        except Exception as e:
            self.error = f"{type(e).__name__}: {e}"
            print("Camera error:", self.error)
            self.events.put(("cam_error", self.error))
        t0 = time.time()
        while self.alive:
            try:
                path, tag = self.cmds.get_nowait()
            except queue.Empty:
                path = None
            try:
                if path:
                    self._do_capture(path, tag)
                elif self.ok and self.want_preview:
                    self._grab(time.time() - t0)
                else:
                    time.sleep(0.04)
            except Exception as e:
                msg = f"{type(e).__name__}"
                print("Camera loop error:", e)
                if path:
                    self.events.put(("capture_failed", tag, msg))
                else:
                    time.sleep(0.2)
        if self.cam is not None:
            try:
                self.cam.stop()
                self.cam.close()
            except Exception:
                pass

    def _grab(self, t):
        if DEMO:
            img = demo_frame(self.target, t)
            time.sleep(0.05)
        else:
            img = Image.fromarray(self.cam.capture_array("main"))
            if img.size != self.target:
                img = img.resize(self.target, RESAMPLE, reducing_gap=2.0)
        with self._lock:
            self._frame = img

    def _do_capture(self, path, tag):
        if not self.ok:
            raise RuntimeError("camera not ready")
        if DEMO:
            demo_frame((1920, 1440), time.time()).save(path, quality=88)
        elif self.still_cfg is not None:
            self.cam.switch_mode_and_capture_file(self.still_cfg, path)
        else:
            self.cam.capture_file(path)
        self.events.put(("captured", path, tag))


# ======================================================================
# The app
# ======================================================================
class DoorbellApp:
    def __init__(self, root, fullscreen=False, touch=False):
        self.root = root
        self.cfg = load_settings()
        self.events = queue.Queue()
        self.page = "home"
        self.W = self.H = 0
        self.s = 1.0
        self.hh = 72
        self.nbtn = 0
        self.page_refs = []
        self.bg_img = None
        self.bg_key = None
        self.pil_cache = OrderedDict()
        self.fonts = {}
        self.resize_job = self.toast_job = self.relock_job = self.visitor_job = None
        self.unlocked = False
        self.unlock_until = 0.0
        self.online = None
        self.closing = False
        self.last_ring = 0.0
        self.last_manual = 0.0
        self.visitor_photo = None
        self.tg_text = ""
        self.gal_files = []
        self.gal_idx = 0
        self.live_ref = None
        self.live_box = (0, 0, 2, 2)
        self.modal = False
        self.dirty = False
        self.is_full = fullscreen

        os.makedirs(PHOTO_DIR, exist_ok=True)

        root.title("Smart Doorbell")
        root.configure(bg=BLACK)
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        root.geometry(f"{min(1024, sw)}x{min(600, sh - 60)}+0+0")
        if fullscreen:
            root.attributes("-fullscreen", True)
        self.c = tk.Canvas(root, bg=BLACK, highlightthickness=0, bd=0)
        if fullscreen and touch:
            try:
                self.c.configure(cursor="none")
            except tk.TclError:
                pass
        self.c.pack(fill="both", expand=True)
        root.bind("<space>", lambda e: self.events.put(("ring",)))
        root.bind("<Escape>", self.on_escape)
        root.bind("<F11>", lambda e: self.set_fullscreen(not self.is_full))
        root.bind("<Left>", lambda e: self.gal_step(-1))
        root.bind("<Right>", lambda e: self.gal_step(1))
        root.protocol("WM_DELETE_WINDOW", self.quit_app)

        self.button_in = Button(BUTTON_PIN, bounce_time=0.05)
        # gpiozero calls this from its own thread: only queue a message here
        self.button_in.when_pressed = lambda: self.events.put(("ring",))
        self.buzzer = Buzzer(BUZZER_PIN)
        try:
            self.lock = OutputDevice(LOCK_PIN, active_high=LOCK_ACTIVE_HIGH,
                                     initial_value=False)
        except Exception:
            self.lock = None

        self.cam = CameraWorker(self.events)
        self.cam.start()
        threading.Thread(target=self.net_loop, daemon=True).start()

        self.c.bind("<Configure>", self.on_resize)   # first draw happens on this event
        self.tick()
        self.poll()

    # ------------------------------------------------------------------
    # Basics
    # ------------------------------------------------------------------
    def font(self, px, bold=False):
        px = max(8, int(px * self.s))
        return ("Helvetica", -px, "bold" if bold else "normal")

    def measure(self, text, px, bold=False):
        key = (self.font(px, bold))
        if key not in self.fonts:
            self.fonts[key] = tkfont.Font(family=key[0], size=key[1], weight=key[2])
        return self.fonts[key].measure(text)

    def T(self, x, y, text, px, fill=WHITE, anchor="center", bold=False, tags=(), **kw):
        return self.c.create_text(x, y, text=text, fill=fill, anchor=anchor,
                                  font=self.font(px, bold), tags=tags, **kw)

    def on_resize(self, e):
        if (e.width, e.height) == (self.W, self.H):
            return
        first = self.W == 0
        self.W, self.H = e.width, e.height
        self.s = max(0.6, min(self.W / 800, self.H / 480))
        self.hh = int(72 * self.s)
        if self.resize_job:
            self.root.after_cancel(self.resize_job)
        if first:
            self.redraw()
        else:
            self.resize_job = self.root.after(120, self.redraw)

    def go(self, page):
        if self.modal:
            self.c.delete("modal")
            self.modal = False
            self.dirty = False
        if self.visitor_job:
            self.root.after_cancel(self.visitor_job)
            self.visitor_job = None
        self.page = page
        self.cam.want_preview = page == "live"
        self.redraw()

    def refresh(self):
        if self.page in ("home", "settings", "visitor"):
            self.redraw()

    def redraw(self):
        if self.W < 100:
            return
        if self.modal:          # don't wipe an open dialog; redraw when it closes
            self.dirty = True
            return
        self.resize_job = None
        self.c.delete("all")
        self.nbtn = 0
        self.page_refs = []
        if self.bg_key != (self.W, self.H):
            self.bg_img = ImageTk.PhotoImage(make_gradient(self.W, self.H))
            self.bg_key = (self.W, self.H)
        self.c.create_image(0, 0, anchor="nw", image=self.bg_img)
        getattr(self, "draw_" + self.page)()
        if DEMO:
            self.T(self.W - 10, self.H - 8, "DEMO MODE", 11, SUB, anchor="se")

    def on_escape(self, e=None):
        if self.is_full:
            self.set_fullscreen(False)
        else:
            self.go("home")

    def set_fullscreen(self, on):
        self.is_full = on
        self.root.attributes("-fullscreen", on)
        self.refresh()

    # ------------------------------------------------------------------
    # Widgets
    # ------------------------------------------------------------------
    def bind_tap(self, tag, command, shape=None, fill=None, pressed=None):
        c = self.c

        def down(e):
            if shape is not None and pressed:
                c.itemconfigure(shape, fill=pressed)

        def up(e):
            if shape is not None and fill:
                c.itemconfigure(shape, fill=fill)
            box = c.bbox(shape if shape is not None else tag)
            if box and command and box[0] <= e.x <= box[2] and box[1] <= e.y <= box[3]:
                self.root.after(1, command)

        c.tag_bind(tag, "<ButtonPress-1>", down)
        c.tag_bind(tag, "<ButtonRelease-1>", up)

    def button(self, x1, y1, x2, y2, command, label="", icon=None, fill=WHITE, fg=INK,
               px=15, group=None, radius=None, icon_r=None, bold=True):
        c, s = self.c, self.s
        self.nbtn += 1
        tag = f"b{self.nbtn}"
        tags = (tag,) + ((group,) if group else ())
        if radius is None:
            radius = min(16 * s, (y2 - y1) / 2)
        shape = rrect(c, x1, y1, x2, y2, radius, fill=fill, outline="", tags=tags)
        mx, my = (x1 + x2) / 2, (y1 + y2) / 2
        ir = icon_r or (y2 - y1) * 0.27
        if icon and label:
            tw = self.measure(label, px, bold)
            gap = 10 * s
            start = mx - (2 * ir + gap + tw) / 2
            draw_icon(c, icon, start + ir, my, ir, fg, bg=fill, tags=tags)
            self.T(start + 2 * ir + gap, my, label, px, fg, anchor="w", bold=bold, tags=tags)
        elif icon:
            draw_icon(c, icon, mx, my, ir, fg, bg=fill, tags=tags)
        elif label:
            self.T(mx, my, label, px, fg, bold=bold, tags=tags)
        self.bind_tap(tag, command, shape, fill, shade(fill, 0.86))
        return tag

    def tile(self, cx, cy, size, icon, label, command, state="on"):
        s = self.s
        fill, fg = {"on": (WHITE, INK), "off": (OFF, SUB), "good": (GREEN, WHITE)}[state]
        tag = self.button(cx - size / 2, cy - size / 2, cx + size / 2, cy + size / 2, command,
                          icon=icon, fill=fill, fg=fg, radius=size * 0.24, icon_r=size * 0.30)
        self.T(cx, cy + size / 2 + 8 * s, label, 13, SUB if state == "off" else WHITE,
               anchor="n", tags=(tag,))

    def switch(self, right, ymid, on, command):
        c, s = self.c, self.s
        w, h = int(58 * s), int(30 * s)
        self.nbtn += 1
        tag = f"b{self.nbtn}"
        x1, y1 = right - w, ymid - h / 2
        rrect(c, x1, y1, right, y1 + h, h / 2, fill=GREEN if on else OFF, outline="", tags=(tag,))
        kx = right - h / 2 if on else x1 + h / 2
        c.create_oval(kx - h / 2 + 3 * s, ymid - h / 2 + 3 * s, kx + h / 2 - 3 * s,
                      ymid + h / 2 - 3 * s, fill=WHITE, outline="", tags=(tag,))
        self.bind_tap(tag, command)

    def header(self, title, sub="", back="home", clock=False):
        s, W = self.s, self.W
        pad, r = int(16 * s), int(20 * s)
        self.button(pad, pad, pad + 2 * r, pad + 2 * r, lambda: self.go(back), icon="back",
                    radius=r, icon_r=r * 0.5)
        x = pad + 2 * r + 14 * s
        self.T(x, pad + r - (9 * s if sub else 0), title, 24, WHITE, anchor="w", bold=True)
        if sub:
            self.T(x, pad + r + 15 * s, sub, 13, SUB, anchor="w", tags=("hsub",))
        if clock:
            self.T(W - pad, pad + r, datetime.now().strftime("%I:%M %p").lstrip("0"), 16, SUB,
                   anchor="e", tags=("hclock",))

    def toast(self, text, ms=2600):
        c, s = self.c, self.s
        if self.toast_job:
            self.root.after_cancel(self.toast_job)
        c.delete("toast")
        tw = self.measure(text, 15, True)
        w, h = min(self.W - 20, tw + 44 * s), 40 * s
        x, y = self.W / 2, self.H - 34 * s
        rrect(c, x - w / 2, y - h / 2, x + w / 2, y + h / 2, h / 2, fill=BLACK, outline=SUB,
              tags=("toast",))
        self.T(x, y, text, 15, WHITE, bold=True, tags=("toast",))
        self.toast_job = self.root.after(ms, lambda: c.delete("toast"))

    def close_modal(self):
        self.c.delete("modal")
        self.modal = False
        if self.dirty:
            self.dirty = False
            self.redraw()

    def confirm(self, title, text, yes_label, on_yes, color=GREEN):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.modal = True
        c.create_rectangle(0, 0, W, H, fill="#000000", stipple="gray25", outline="",
                           tags=("modal",))
        pw, ph = min(W - 40, 440 * s), 190 * s
        x1, y1 = (W - pw) / 2, (H - ph) / 2
        rrect(c, x1 + 4 * s, y1 + 8 * s, x1 + pw + 4 * s, y1 + ph + 8 * s, 22 * s,
              fill="#150e2b", outline="", tags=("modal",))
        rrect(c, x1, y1, x1 + pw, y1 + ph, 22 * s, fill=PANEL2, outline="", tags=("modal",))
        self.T(W / 2, y1 + 38 * s, title, 21, WHITE, bold=True, tags=("modal",))
        self.T(W / 2, y1 + 78 * s, text, 14, SUB, tags=("modal",), width=pw - 40 * s,
               justify="center")

        def close():
            self.close_modal()

        def yes():
            close()
            on_yes()

        bw, bh = (pw - 60 * s) / 2, 48 * s
        by = y1 + ph - bh - 22 * s
        self.button(x1 + 20 * s, by, x1 + 20 * s + bw, by + bh, close, "Cancel", fill=WHITE,
                    group="modal")
        self.button(x1 + 40 * s + bw, by, x1 + 40 * s + 2 * bw, by + bh, yes, yes_label,
                    fill=color, fg=WHITE, group="modal")

    # ------------------------------------------------------------------
    # Pictures
    # ------------------------------------------------------------------
    def get_pil(self, path, box):
        box = (max(2, int(box[0])), max(2, int(box[1])))
        key = (path, box)
        if key in self.pil_cache:
            self.pil_cache.move_to_end(key)
            return self.pil_cache[key]
        try:
            im = Image.open(path)
            im.draft("RGB", box)          # fast JPEG decode at reduced size
            im = im.convert("RGB")
            im.thumbnail(box, SMOOTH)
        except Exception:
            im = None
        self.pil_cache[key] = im
        while len(self.pil_cache) > 40:
            self.pil_cache.popitem(last=False)
        return im

    def put_image(self, x, y, pil, anchor="center", tags=()):
        ph = ImageTk.PhotoImage(pil)
        self.page_refs.append(ph)
        return self.c.create_image(x, y, image=ph, anchor=anchor, tags=tags)

    # ------------------------------------------------------------------
    # Home
    # ------------------------------------------------------------------
    def door_text(self):
        if self.unlocked:
            return f"Unlocked  {max(0, int(math.ceil(self.unlock_until - time.time())))}s"
        return "Door locked"

    def chip(self, x, y, w, h, dot, text, tag=""):
        s = self.s
        rrect(self.c, x, y, x + w, y + h, h / 2, fill=PANEL, outline="")
        self.c.create_oval(x + 12 * s, y + h / 2 - 5 * s, x + 22 * s, y + h / 2 + 5 * s,
                           fill=dot, outline="")
        self.T(x + 30 * s, y + h / 2, text, 13, WHITE, anchor="w", tags=(tag,) if tag else ())

    def draw_home(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        left = int(40 * s)
        now = datetime.now()

        # status icons (top right)
        r = int(15 * s)
        x = W - int(24 * s) - r
        y = int(22 * s) + r
        status = [
            ("power", INK, self.confirm_quit),
            ("sound" if self.cfg["sound"] else "mute", INK, self.toggle_sound),
            ("unlock" if self.unlocked else "lock", GREEN if self.unlocked else INK, None),
            ("nowifi" if self.online is False else "wifi", RED if self.online is False else INK, None),
        ]
        for icon, col, cmd in status:
            self.button(x - r, y - r, x + r, y + r, cmd, icon=icon, fg=col, radius=r,
                        icon_r=r * 0.55)
            x -= 2 * r + 10 * s

        # clock
        self.T(left, int(48 * s), now.strftime("%H:%M"), 94, WHITE, anchor="nw", tags=("clk",))
        self.T(left + 4 * s, int(166 * s), now.strftime("%A"), 24, WHITE, anchor="nw", bold=True,
               tags=("clk_day",))
        self.T(left + 4 * s, int(200 * s), now.strftime("%d %B %Y"), 17, SUB, anchor="nw",
               tags=("clk_date",))

        # status chips
        cw = int(152 * s)
        cy = int(244 * s)
        self.chip(left, cy, cw, 34 * s, GREEN if self.unlocked else RED, self.door_text(), "door_txt")
        if not TG_READY:
            dot, txt = "#c9a227", "Telegram: set up"
        elif not self.cfg["telegram"]:
            dot, txt = OFF, "Telegram off"
        elif self.online is False:
            dot, txt = RED, "No internet"
        else:
            dot, txt = GREEN, "Telegram on"
        self.chip(left + cw + 12 * s, cy, cw, 34 * s, dot, txt)

        # last visitor card
        y1, y2 = int(294 * s), H - int(26 * s)
        x2 = left + cw * 2 + 12 * s
        tag = self.button(left, y1, x2, y2, lambda: self.open_gallery(0), fill=PANEL, radius=18 * s)
        visitors = [p for p in list_photos() if os.path.basename(p).startswith("visitor")]
        if visitors:
            pad = 8 * s
            th = y2 - y1 - 2 * pad
            pil = self.get_pil(visitors[0], (th * 4 / 3, th))
            if pil:
                self.put_image(left + pad, y1 + pad, pil, anchor="nw", tags=(tag,))
                tx = left + pad + pil.width + 14 * s
                _, stamp = describe(visitors[0])
                self.T(tx, y1 + pad + 6 * s, "Last visitor", 13, SUB, anchor="nw", tags=(tag,))
                self.T(tx, y1 + pad + 30 * s, day_label(stamp), 17, WHITE, anchor="nw", bold=True, tags=(tag,))
                self.T(tx, y1 + pad + 56 * s, clock12(stamp), 17, WHITE, anchor="nw", tags=(tag,))
                self.T(tx, y2 - pad - 4 * s, "Tap for gallery", 12, SUB, anchor="sw", tags=(tag,))
        else:
            self.T((left + x2) / 2, (y1 + y2) / 2, "No visitors yet", 16, SUB, tags=(tag,))

        # tile grid
        gx0, gx1 = int(392 * s), W - int(26 * s)
        gy0, gy1 = int(78 * s), H - int(22 * s)
        cwid, chei = (gx1 - gx0) / 3, (gy1 - gy0) / 3
        size = min(cwid - 14 * s, chei - 34 * s)
        tiles = [
            ("live", "Live view", lambda: self.go("live"), "on"),
            ("camera", "Capture", self.capture_manual, "on"),
            ("gallery", "Gallery", lambda: self.open_gallery(0), "on"),
            ("unlock", "Unlocked" if self.unlocked else "Unlock", self.ask_unlock,
             "good" if self.unlocked else "on"),
            ("lock", "Lock", self.do_lock, "on"),
            ("bell", "Test bell", self.test_bell, "on"),
            ("sound" if self.cfg["sound"] else "mute", "Sound on" if self.cfg["sound"] else "Muted",
             self.toggle_sound, "on" if self.cfg["sound"] else "off"),
            ("send", "Telegram on" if self.cfg["telegram"] else "Telegram off", self.toggle_telegram,
             "on" if self.cfg["telegram"] else "off"),
            ("gear", "Settings", lambda: self.go("settings"), "on"),
        ]
        for i, (icon, label, cmd, state) in enumerate(tiles):
            col, row = i % 3, i // 3
            self.tile(gx0 + cwid * (col + 0.5), gy0 + chei * row + size / 2 + 4 * s, size,
                      icon, label, cmd, state)

    # ------------------------------------------------------------------
    # Live view
    # ------------------------------------------------------------------
    def draw_live(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.header("Live view")
        pad, side, gap = int(16 * s), int(176 * s), int(12 * s)
        ax1, ay1, ax2, ay2 = pad, self.hh, W - pad - side - gap, H - pad
        vw, vh = fit(ax2 - ax1, ay2 - ay1, self.cam.aspect)
        vx = ax1 + (ax2 - ax1 - vw) / 2
        vy = ay1 + (ay2 - ay1 - vh) / 2
        c.create_rectangle(vx, vy, vx + vw, vy + vh, fill=BLACK, outline="")
        c.create_image(vx + vw / 2, vy + vh / 2, anchor="center", tags=("live_img",))
        msg = ("Camera not available\n" + self.cam.error) if self.cam.error else "Starting camera..."
        self.T(vx + vw / 2, vy + vh / 2, msg, 15, SUB, tags=("live_msg",), justify="center",
               width=vw - 30)
        self.cam.target = (vw - vw % 2, vh - vh % 2)
        self.live_box = (vx, vy, vw, vh)
        rrect(c, vx + 10 * s, vy + 10 * s, vx + 74 * s, vy + 34 * s, 12 * s, fill=RED, outline="")
        self.T(vx + 42 * s, vy + 22 * s, "LIVE", 12, WHITE, bold=True)

        bx1 = W - pad - side
        bh = min(74 * s, (ay2 - ay1 - 3 * gap) / 4)
        items = [
            ("Capture", "camera", self.capture_manual, ACCENT, WHITE),
            ("Unlock", "unlock", self.ask_unlock, GREEN, WHITE),
            ("Lock", "lock", self.do_lock, WHITE, INK),
            ("Gallery", "gallery", lambda: self.open_gallery(0), WHITE, INK),
        ]
        for i, (label, icon, cmd, fill, fg) in enumerate(items):
            y = ay1 + i * (bh + gap)
            self.button(bx1, y, bx1 + side, y + bh, cmd, label, icon, fill=fill, fg=fg, px=16)

    def update_live(self):
        img = self.cam.take_frame()
        if img is None:
            if self.cam.error:
                self.c.itemconfigure("live_msg", text="Camera not available\n" + self.cam.error)
            return
        self.live_ref = ImageTk.PhotoImage(img)
        self.c.itemconfigure("live_img", image=self.live_ref)
        self.c.itemconfigure("live_msg", state="hidden")

    def flash(self):
        x, y, w, h = self.live_box
        self.c.create_rectangle(x, y, x + w, y + h, fill=WHITE, outline="", tags=("flash",))
        self.root.after(130, lambda: self.c.delete("flash"))

    # ------------------------------------------------------------------
    # Gallery
    # ------------------------------------------------------------------
    def open_gallery(self, idx=0):
        self.gal_files = list_photos()
        self.gal_idx = max(0, min(idx, len(self.gal_files) - 1))
        self.go("gallery")

    def gal_step(self, d):
        if self.page == "gallery" and self.gal_files:
            self.gal_idx = (self.gal_idx + d) % len(self.gal_files)
            self.redraw()

    def gal_select(self, i):
        self.gal_idx = i
        self.redraw()

    def draw_gallery(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        files, n = self.gal_files, len(self.gal_files)
        pad = int(16 * s)
        if not n:
            self.header("Gallery", "No photos yet")
            self.T(W / 2, H / 2 - 10 * s, "No photos yet", 24, WHITE, bold=True)
            self.T(W / 2, H / 2 + 24 * s, "Press the doorbell or use Capture", 15, SUB)
            return
        self.gal_idx = max(0, min(self.gal_idx, n - 1))
        path = files[self.gal_idx]
        kind, stamp = describe(path)
        self.header("Gallery", f"{self.gal_idx + 1} of {n}")

        # action buttons (top right)
        bh = int(40 * s)
        by = pad + (2 * int(20 * s) - bh) / 2
        bw = int(122 * s)
        self.button(W - pad - bw, by, W - pad, by + bh, self.ask_delete, "Delete", "trash",
                    fill=RED, fg=WHITE, px=14)
        self.button(W - pad - 2 * bw - 10 * s, by, W - pad - bw - 10 * s, by + bh, self.send_current,
                    "Send", "send", fill=WHITE, fg=INK, px=14)

        # big viewer
        strip_h = int(78 * s)
        vx1, vy1 = pad, self.hh
        vx2, vy2 = W - pad, H - strip_h - int(20 * s)
        view = rrect(c, vx1, vy1, vx2, vy2, 16 * s, fill=BLACK, outline="", tags=("viewer",))
        inset = 6 * s
        pil = self.get_pil(path, (vx2 - vx1 - 2 * inset, vy2 - vy1 - 2 * inset))
        if pil:
            self.put_image((vx1 + vx2) / 2, (vy1 + vy2) / 2, pil, tags=("viewer",))
        else:
            self.T((vx1 + vx2) / 2, (vy1 + vy2) / 2, "Could not open this photo", 16, SUB)
        cap = f"{kind}  -  {day_label(stamp)}, {clock12(stamp)}"
        tw = self.measure(cap, 13, True)
        cy = vy2 - 22 * s
        rrect(c, vx1 + 14 * s, cy - 14 * s, vx1 + 14 * s + tw + 24 * s, cy + 14 * s, 14 * s,
              fill="#000000", outline="", tags=("viewer",))
        self.T(vx1 + 26 * s, cy, cap, 13, WHITE, anchor="w", bold=True, tags=("viewer",))

        # swipe left / right on the picture
        start = {}

        def swipe_end(e):
            dx = e.x - start.get("x", e.x)
            if dx < -60 * s:
                self.root.after(1, lambda: self.gal_step(1))
            elif dx > 60 * s:
                self.root.after(1, lambda: self.gal_step(-1))

        c.tag_bind("viewer", "<ButtonPress-1>", lambda e: start.update(x=e.x))
        c.tag_bind("viewer", "<ButtonRelease-1>", swipe_end)

        if n > 1:
            ar = 24 * s
            for sign, icon in ((-1, "left"), (1, "right")):
                x = vx1 + 14 * s + ar if sign < 0 else vx2 - 14 * s - ar
                self.button(x - ar, (vy1 + vy2) / 2 - ar, x + ar, (vy1 + vy2) / 2 + ar,
                            lambda d=sign: self.gal_step(d), icon=icon, fill="#1a1230", fg=WHITE,
                            radius=ar, icon_r=ar * 0.5)

        # thumbnail strip
        th = strip_h - 10 * s
        tw_ = th * 4 / 3
        gap = 8 * s
        cap_n = max(1, int((W - 2 * pad + gap) // (tw_ + gap)))
        first = max(0, min(self.gal_idx - cap_n // 2, n - cap_n))
        total = min(cap_n, n) * (tw_ + gap) - gap
        x = (W - total) / 2
        y = H - strip_h - 8 * s
        for i in range(first, min(n, first + cap_n)):
            sel = i == self.gal_idx
            tag = f"t{i}"
            rrect(c, x - 3 * s, y - 3 * s, x + tw_ + 3 * s, y + th + 3 * s, 9 * s,
                  fill=WHITE if sel else PANEL, outline="", tags=(tag,))
            tp = self.get_pil(files[i], (tw_, th))
            if tp:
                self.put_image(x + tw_ / 2, y + th / 2, tp, tags=(tag,))
            self.bind_tap(tag, lambda i=i: self.gal_select(i))
            x += tw_ + gap

    def send_current(self):
        if self.gal_files:
            path = self.gal_files[self.gal_idx]
            self.send_photo(path, "Photo from your doorbell")

    def ask_delete(self):
        if not self.gal_files:
            return
        path = self.gal_files[self.gal_idx]
        kind, stamp = describe(path)
        self.confirm("Delete this photo?", f"{kind} photo from {day_label(stamp)}, {clock12(stamp)}.\n"
                     "It will be removed from the Pi.", "Delete", self.do_delete, RED)

    def do_delete(self):
        path = self.gal_files[self.gal_idx]
        try:
            os.remove(path)
        except OSError as e:
            self.toast(f"Could not delete ({type(e).__name__})")
            return
        for k in [k for k in self.pil_cache if k[0] == path]:
            del self.pil_cache[k]
        self.gal_files = list_photos()
        self.gal_idx = min(self.gal_idx, max(0, len(self.gal_files) - 1))
        self.redraw()
        self.toast("Photo deleted")

    # ------------------------------------------------------------------
    # Visitor popup
    # ------------------------------------------------------------------
    def draw_visitor(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.header("Someone is at the door", datetime.now().strftime("%d %b, %I:%M %p").lstrip("0"))
        pad, side, gap = int(16 * s), int(190 * s), int(12 * s)
        x1, y1, x2, y2 = pad, self.hh, W - pad - side - gap, H - pad
        rrect(c, x1, y1, x2, y2, 16 * s, fill=BLACK, outline="")
        pil = self.get_pil(self.visitor_photo, (x2 - x1 - 12 * s, y2 - y1 - 12 * s)) \
            if self.visitor_photo else None
        if pil:
            self.put_image((x1 + x2) / 2, (y1 + y2) / 2, pil)
        else:
            self.T((x1 + x2) / 2, (y1 + y2) / 2, "Taking photo...", 20, SUB)
        bx = W - pad - side
        bh = 64 * s
        self.button(bx, y1, bx + side, y1 + bh, self.ask_unlock, "Unlock", "unlock", fill=GREEN,
                    fg=WHITE, px=17)
        self.button(bx, y1 + bh + gap, bx + side, y1 + 2 * bh + gap, lambda: self.open_gallery(0),
                    "Gallery", "gallery", px=16)
        self.button(bx, y1 + 2 * bh + 2 * gap, bx + side, y1 + 3 * bh + 2 * gap,
                    lambda: self.go("home"), "Dismiss", "check", px=16)
        if self.tg_text:
            self.T(bx + side / 2, y1 + 3 * bh + 4 * gap, self.tg_text, 13, SUB, anchor="n",
                   width=side, justify="center")

    # ------------------------------------------------------------------
    # Settings
    # ------------------------------------------------------------------
    def draw_settings(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.header("Settings", clock=True)
        pad = int(16 * s)
        rh, gap = int(50 * s), int(8 * s)
        x1, x2 = pad, W - pad
        y0 = self.hh + 6 * s

        def row(i, label):
            y = y0 + i * (rh + gap)
            rrect(c, x1, y, x2, y + rh, 14 * s, fill=PANEL, outline="")
            self.T(x1 + 18 * s, y + rh / 2, label, 16, WHITE, anchor="w", bold=True)
            return y + rh / 2

        right = x2 - 18 * s
        m = row(0, "Send visitor photos to Telegram")
        self.switch(right, m, self.cfg["telegram"], self.toggle_telegram)
        m = row(1, "Doorbell sound")
        self.switch(right, m, self.cfg["sound"], self.toggle_sound)

        m = row(2, "Chime")
        bw, bh = int(84 * s), int(34 * s)
        for k, name in enumerate(reversed(list(CHIMES))):
            sel = self.cfg["chime"] == name
            xr = right - k * (bw + 6 * s)
            self.button(xr - bw, m - bh / 2, xr, m + bh / 2, lambda n=name: self.set_chime(n), name,
                        fill=WHITE if sel else "#4b3a78", fg=INK if sel else WHITE, px=13,
                        radius=bh / 2)

        m = row(3, "Door stays unlocked for")
        cr = int(17 * s)
        self.button(right - cr * 2, m - cr, right, m + cr, lambda: self.step_open(1), icon="plus",
                    radius=cr, icon_r=cr * 0.5)
        self.T(right - cr * 2 - 34 * s, m, f"{self.cfg['open_seconds']} s", 17, WHITE, bold=True)
        self.button(right - cr * 4 - 68 * s, m - cr, right - cr * 2 - 68 * s, m + cr,
                    lambda: self.step_open(-1), icon="minus", radius=cr, icon_r=cr * 0.5)

        m = row(4, "Full screen")
        self.switch(right, m, self.is_full, lambda: self.set_fullscreen(not self.is_full))

        y = y0 + 5 * (rh + gap) + 2 * s
        bh2 = 44 * s
        half = (x2 - x1 - 10 * s) / 2
        self.button(x1, y, x1 + half, y + bh2, self.test_bell, "Test bell", "bell", px=15)
        self.button(x1 + half + 10 * s, y, x2, y + bh2, self.confirm_quit, "Quit app", "power",
                    fill=RED, fg=WHITE, px=15)
        files = list_photos()
        mb = sum(os.path.getsize(p) for p in files) / 1e6
        free = shutil.disk_usage(PHOTO_DIR).free / 1e9
        self.T(W / 2, y + bh2 + 16 * s, f"{len(files)} photos  -  {mb:.0f} MB used  -  {free:.1f} GB free",
               12, SUB)

    def set_chime(self, name):
        self.cfg["chime"] = name
        save_settings(self.cfg)
        self.chime(force=True)
        self.redraw()

    def step_open(self, d):
        self.cfg["open_seconds"] = max(2, min(30, self.cfg["open_seconds"] + d))
        save_settings(self.cfg)
        self.redraw()

    def toggle_sound(self):
        self.cfg["sound"] = not self.cfg["sound"]
        save_settings(self.cfg)
        self.refresh()
        self.toast("Doorbell sound on" if self.cfg["sound"] else "Doorbell muted")

    def toggle_telegram(self):
        if not TG_READY:
            self.toast("Add BOT_TOKEN and CHAT_ID to config.py first")
            return
        self.cfg["telegram"] = not self.cfg["telegram"]
        save_settings(self.cfg)
        self.refresh()
        self.toast("Telegram on" if self.cfg["telegram"] else "Telegram off")

    # ------------------------------------------------------------------
    # Actions: bell, camera, door, Telegram
    # ------------------------------------------------------------------
    def chime(self, force=False):
        if force or self.cfg["sound"]:
            self.buzzer.beep(on_time=0.25, off_time=0.15, n=CHIMES[self.cfg["chime"]],
                             background=True)

    def test_bell(self):
        self.chime(force=True)
        self.toast("Bell test")

    def on_ring(self):
        now = time.time()
        if now - self.last_ring < RING_COOLDOWN:
            return
        self.last_ring = now
        self.chime()
        self.visitor_photo = None
        self.tg_text = ""
        self.go("visitor")
        self.visitor_job = self.root.after(60000, lambda: self.go("home") if self.page == "visitor" else None)
        self.cam.capture(new_photo_path("visitor"), "visitor")

    def capture_manual(self):
        if time.time() - self.last_manual < 1.0:
            return
        self.last_manual = time.time()
        self.cam.capture(new_photo_path("manual"), "manual")

    def on_captured(self, path, tag):
        if tag == "visitor":
            self.visitor_photo = path
            if TG_READY and self.cfg["telegram"]:
                self.send_photo(path, "Someone is at your door! " + datetime.now().strftime("%d %b %Y, %I:%M %p"))
            elif not TG_READY:
                self.tg_text = "Telegram not set up"
            else:
                self.tg_text = "Telegram is off"
            if self.page == "visitor":
                self.redraw()
        else:
            self.toast("Photo saved")
            if self.page == "live":
                self.flash()

    def ask_unlock(self):
        n = self.cfg["open_seconds"]
        self.confirm("Unlock the door?", f"The door will unlock for {n} seconds, then lock again.",
                     "Unlock", self.do_unlock)

    def do_unlock(self):
        if self.relock_job:
            self.root.after_cancel(self.relock_job)
        n = self.cfg["open_seconds"]
        if self.lock:
            self.lock.on()
        self.unlocked = True
        self.unlock_until = time.time() + n
        self.relock_job = self.root.after(n * 1000, self.do_lock)
        self.refresh()
        self.toast(f"Door unlocked for {n} seconds")

    def do_lock(self):
        if self.relock_job:
            self.root.after_cancel(self.relock_job)
            self.relock_job = None
        was = self.unlocked
        if self.lock:
            self.lock.off()
        self.unlocked = False
        self.refresh()
        self.toast("Door locked" if was else "Door is locked")

    def send_photo(self, path, caption):
        if not TG_READY:
            self.toast("Add BOT_TOKEN and CHAT_ID to config.py first")
            return
        self.tg_text = "Sending to Telegram..."
        self.toast("Sending to Telegram...")
        threading.Thread(target=self._send, args=(path, caption), daemon=True).start()
        if self.page == "visitor":
            self.redraw()

    def _send(self, path, caption):
        # Background thread: report back through the queue only. Errors are
        # reported by type only because request errors can contain the bot token.
        try:
            with open(path, "rb") as f:
                r = requests.post(TELEGRAM_URL, data={"chat_id": CHAT_ID, "caption": caption},
                                  files={"photo": f}, timeout=30)
            if r.ok and r.json().get("ok"):
                self.events.put(("tg", "Sent to Telegram", True))
            else:
                self.events.put(("tg", f"Telegram error (HTTP {r.status_code})", False))
        except requests.RequestException as e:
            self.events.put(("tg", "No internet - photo saved on the Pi", False))
            print("Telegram send failed:", type(e).__name__)
        except Exception as e:
            self.events.put(("tg", "Telegram error", False))
            print("Telegram send failed:", type(e).__name__)

    def net_loop(self):
        while not self.closing:
            try:
                requests.get("https://api.telegram.org", timeout=5)
                self.events.put(("online", True))
            except requests.RequestException:
                self.events.put(("online", False))
            for _ in range(30):
                if self.closing:
                    return
                time.sleep(1)

    # ------------------------------------------------------------------
    # Timers
    # ------------------------------------------------------------------
    def tick(self):
        now = datetime.now()
        c = self.c
        c.itemconfigure("clk", text=now.strftime("%H:%M"))
        c.itemconfigure("clk_day", text=now.strftime("%A"))
        c.itemconfigure("clk_date", text=now.strftime("%d %B %Y"))
        c.itemconfigure("hclock", text=now.strftime("%I:%M %p").lstrip("0"))
        if self.unlocked:
            c.itemconfigure("door_txt", text=self.door_text())
        self.root.after(1000, self.tick)

    def poll(self):
        try:
            while True:
                ev = self.events.get_nowait()
                try:
                    self.handle(ev)
                except Exception:
                    traceback.print_exc()
        except queue.Empty:
            pass
        if self.page == "live":
            self.update_live()
        if not self.closing:
            self.root.after(40, self.poll)

    def handle(self, ev):
        kind = ev[0]
        if kind == "ring":
            self.on_ring()
        elif kind == "captured":
            self.on_captured(ev[1], ev[2])
        elif kind == "capture_failed":
            self.toast("Could not take photo - check the camera")
            if self.page == "visitor":
                self.tg_text = "Camera error"
                self.redraw()
        elif kind == "cam_error":
            self.toast("Camera not available")
        elif kind == "tg":
            self.tg_text = ev[1]
            if self.page == "visitor":
                self.redraw()
            else:
                self.toast(ev[1])
        elif kind == "online":
            if self.online != ev[1]:
                self.online = ev[1]
                self.refresh()

    # ------------------------------------------------------------------
    # Quit
    # ------------------------------------------------------------------
    def confirm_quit(self):
        self.confirm("Quit doorbell?", "The doorbell will stop working until you start it again.",
                     "Quit", self.quit_app, RED)

    def quit_app(self):
        if self.closing:
            return
        self.closing = True
        self.cam.alive = False
        self.cam.join(timeout=3)
        for dev in (self.buzzer, self.lock):
            try:
                if dev:
                    dev.off()
            except Exception:
                pass
        self.root.destroy()


def main():
    root = tk.Tk()
    DoorbellApp(root, fullscreen="--fullscreen" in sys.argv, touch="--touch" in sys.argv)
    root.mainloop()


if __name__ == "__main__":
    main()