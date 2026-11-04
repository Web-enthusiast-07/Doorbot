#!/usr/bin/env python3
"""Smart Doorbell - touchscreen dashboard for Raspberry Pi 4, with face unlock.

    python3 doorbell_ui.py                       window
    python3 doorbell_ui.py --fullscreen          full screen
    python3 doorbell_ui.py --fullscreen --touch  full screen, hide mouse pointer
    python3 doorbell_ui.py --demo                try the UI on any PC (no Pi needed)

Needs next to this file:  config.py (BOT_TOKEN, CHAT_ID) and face_engine.py
Face recognition setup:   sudo apt install python3-opencv python3-numpy
                          python3 face_engine.py --download
Keyboard: Space = ring the bell, Esc = home.
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

try:
    import numpy as np
except ImportError:      # the face engine needs numpy as well
    np = None

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
REGISTER_SHOTS = 5         # photos taken when registering a face
RING_COOLDOWN = 3          # ignore repeat presses within this many seconds
PHOTO_DIR = os.path.expanduser("~/photos")
SETTINGS_FILE = os.path.expanduser("~/.doorbell_settings.json")

try:
    from config import BOT_TOKEN, CHAT_ID  # noqa: F811
except ImportError:
    pass
TG_READY = bool(BOT_TOKEN and CHAT_ID)
TELEGRAM_URL = f"https://api.telegram.org/bot{BOT_TOKEN}/sendPhoto"

try:
    from face_engine import FaceEngine, COSINE_THRESHOLD
    ENGINE_ERROR = ""
except Exception as err:       # file missing, OpenCV missing, ...
    FaceEngine, COSINE_THRESHOLD = None, 0.5
    ENGINE_ERROR = f"{type(err).__name__}: {err}"
MATCH_THRESHOLD = COSINE_THRESHOLD   # cosine similarity needed to accept a face (higher = stricter)

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

    class DemoFaceEngine:
        """Stand-in so the face screens can be tried with --demo (no model needed)."""

        def __init__(self, threshold=0.5):
            self.people = {"Mihir": 5, "Guest": 3}
            self.calls = 0

        def count(self): return len(self.people)
        def names(self): return dict(self.people)

        def register(self, name, frames):
            time.sleep(0.8)
            self.people[name] = len(frames)
            return True, f"Registered {name} ({len(frames)} samples)"

        def delete(self, name): self.people.pop(name, None)

        def identify(self, frame):
            time.sleep(0.4)
            self.calls += 1
            k = self.calls % 3
            if k == 1:
                return {"name": "Mihir", "score": 0.81, "faces": 1, "closest": "Mihir"}
            if k == 2:
                return {"name": None, "score": 0.31, "faces": 1, "closest": "Guest"}
            return {"name": None, "score": 0.0, "faces": 0, "closest": None}

    if FaceEngine is None:
        FaceEngine, ENGINE_ERROR = DemoFaceEngine, ""

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
    elif name == "people":
        oval(-7.5, -8.5, -0.5, -1.5)
        arc(-11, 1, 3, 15, 0, 180)
        oval(2.5, -6.5, 8.5, -0.5)
        arc(1, 2.5, 12, 14.5, 0, 180)
    elif name == "face":
        line(-9, -4, -9, -9, -4, -9)
        line(4, -9, 9, -9, 9, -4)
        line(9, 4, 9, 9, 4, 9)
        line(-4, 9, -9, 9, -9, 4)
        oval(-4, -4.5, 4, 4.5)
        oval(-2.3, -1.7, -0.9, -0.3, fill=col)
        oval(0.9, -1.7, 2.3, -0.3, fill=col)
        arc(-2.4, 0.2, 2.4, 3.6, 200, 140)


# ======================================================================
# Helpers for photos
# ======================================================================
def list_photos():
    return sorted(glob.glob(os.path.join(PHOTO_DIR, "*.jpg")), reverse=True)


def describe(path):
    name = os.path.basename(path)
    kind = {"visitor": "Visitor", "manual": "Manual", "scan": "Scan"}.get(name.split("_")[0], "Photo")
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


DEFAULTS = {"telegram": True, "sound": True, "chime": "Double", "open_seconds": 5,
            "auto_open": True}
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
    RETRY_SECONDS = 5

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
        self.cmds.put(("photo", path, tag))

    def grab(self, tag):
        """Ask for one full-size frame as a BGR numpy array (event 'frame')."""
        self.cmds.put(("frame", tag))

    # -- setup -----------------------------------------------------------
    def open(self):
        if DEMO:
            self.ok = True
            return
        cam = Picamera2()
        try:
            self._configure(cam)
            cam.start()
            time.sleep(1.5)          # let auto exposure settle
        except Exception:
            try:
                cam.close()
            except Exception:
                pass
            raise
        self.cam = cam
        self.ok = True

    def _configure(self, cam):
        """Pick a sensor mode that sees the whole picture (no zoom), but never
        depend on any one camera property: ArduCam drivers don't all report the
        same ones. Falls back step by step to a plain configuration."""
        try:
            modes = list(cam.sensor_modes)
        except Exception as e:
            print("Could not read sensor modes:", type(e).__name__, e)
            modes = []

        def area(m):
            return m["size"][0] * m["size"][1]

        def view(m):                      # size of the sensor area this mode uses
            cl = m.get("crop_limits")
            return cl[2] * cl[3] if cl and len(cl) == 4 else 0

        # Cropped modes (e.g. 1080p) see a smaller area = zoomed in. Keep only the
        # modes with the widest view.
        widest = max((view(m) for m in modes), default=0)
        if widest:
            wide = [m for m in modes if view(m) >= 0.95 * widest]
        elif modes:      # no crop info from the driver: modes shaped like the biggest one see the same view
            big = max(modes, key=area)
            ratio = big["size"][0] / big["size"][1]
            wide = [m for m in modes if abs(m["size"][0] / m["size"][1] - ratio) < 0.02]
        else:
            wide = []
        mode = None
        if wide:
            enough = [m for m in wide if m["size"][0] >= PHOTO_WIDTH]
            mode = min(enough, key=area) if enough else max(wide, key=area)

        attempts = []
        if mode:
            mw, mh = mode["size"]
            pw = min(PHOTO_WIDTH, mw)
            pw -= pw % 2
            ph = int(round(pw * mh / mw))
            ph -= ph % 2
            main = {"size": (pw, ph), "format": "BGR888"}     # BGR888 = RGB byte order
            sensor = {"output_size": tuple(mode["size"])}
            if mode.get("bit_depth"):
                sensor["bit_depth"] = mode["bit_depth"]
            if mode.get("crop_limits") and len(mode["crop_limits"]) == 4:
                crop = {"ScalerCrop": tuple(int(v) for v in mode["crop_limits"])}
                attempts.append(dict(main=main, sensor=sensor, controls=crop))
            attempts.append(dict(main=main, sensor=sensor))
        attempts.append(dict(main={"size": (1280, 960), "format": "BGR888"}))   # last resort

        last_err = None
        for kw in attempts:
            try:
                cam.configure(cam.create_preview_configuration(**kw))
                self.aspect = kw["main"]["size"][0] / kw["main"]["size"][1]
                print("Camera configured:", kw["main"]["size"],
                      "sensor", kw.get("sensor", "default"))
                break
            except Exception as e:
                last_err = e
                print("Camera setup attempt failed:", type(e).__name__, e)
        else:
            raise last_err

        if FULL_RES_PHOTOS and wide:
            try:
                big = max(wide, key=area)
                self.still_cfg = cam.create_still_configuration(
                    main={"size": tuple(big["size"])},
                    sensor={"output_size": tuple(big["size"])})
            except Exception as e:
                print("Full-resolution photos unavailable:", type(e).__name__, e)

    # -- thread ----------------------------------------------------------
    def run(self):
        t0 = time.time()
        next_try, shown = 0.0, ""
        while self.alive:
            if not self.ok and time.time() >= next_try:
                # not open yet (or the camera was busy): try again every 5 seconds
                try:
                    self.open()
                    self.error = ""
                    shown = ""
                    self.events.put(("cam_ready",))
                except Exception as e:
                    self.error = f"{type(e).__name__}: {e}"
                    traceback.print_exc()
                    if self.error != shown:
                        shown = self.error
                        self.events.put(("cam_error", self.error))
                    next_try = time.time() + self.RETRY_SECONDS
            try:
                cmd = self.cmds.get_nowait()
            except queue.Empty:
                cmd = None
            try:
                if cmd:
                    self._do_command(cmd)
                elif self.ok and self.want_preview:
                    self._grab(time.time() - t0)
                else:
                    time.sleep(0.04)
            except Exception as e:
                print("Camera loop error:", type(e).__name__, e)
                if cmd:
                    self.events.put(("capture_failed", cmd[-1], type(e).__name__))
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

    def _do_command(self, cmd):
        if not self.ok:
            raise RuntimeError("camera not ready")
        if cmd[0] == "photo":
            self._do_capture(cmd[1], cmd[2])
        else:
            self.events.put(("frame", cmd[1], self._grab_bgr()))

    def _grab_bgr(self):
        if DEMO:
            arr = np.asarray(demo_frame((1920, 1440), time.time()))
        else:
            arr = self.cam.capture_array("main")        # RGB order (format "BGR888")
        return np.ascontiguousarray(arr[:, :, ::-1])    # BGR order, as OpenCV expects

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
        self.engine = None
        self.engine_lock = threading.Lock()
        self.engine_msg = ""
        self.engine_loading = False
        self.faces = {}
        self.faces_page = 0
        self.face_result = None
        self.visit_kind = "visitor"
        self.kb_text = ""
        self.kb_shift = True
        self.reg = {}

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
        root.bind("<space>", self.on_space)
        root.bind("<Key>", self.on_key)
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
        self.load_engine()
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
        if self.page == "register" and page != "register":
            self.reg_abort()
        self.page = page
        self.cam.want_preview = page in ("live", "register")
        self.redraw()

    def refresh(self):
        if self.page in ("home", "settings", "visitor", "faces"):
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

    def chip(self, x, y, w, h, dot, text, tag="", command=None):
        s = self.s
        self.nbtn += 1
        btag = f"b{self.nbtn}"
        shape = rrect(self.c, x, y, x + w, y + h, h / 2, fill=PANEL, outline="", tags=(btag,))
        self.c.create_oval(x + 12 * s, y + h / 2 - 5 * s, x + 22 * s, y + h / 2 + 5 * s,
                           fill=dot, outline="", tags=(btag,))
        self.T(x + 30 * s, y + h / 2, text, 13, WHITE, anchor="w",
               tags=(btag, tag) if tag else (btag,))
        if command:
            self.bind_tap(btag, command, shape, PANEL, shade(PANEL, 1.3))

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
        cw, gap = int(148 * s), 12 * s
        row1, row2, chh = int(238 * s), int(276 * s), 32 * s
        self.chip(left, row1, cw, chh, GREEN if self.unlocked else RED, self.door_text(), "door_txt")
        if not TG_READY:
            dot, txt = "#c9a227", "Telegram: set up"
        elif not self.cfg["telegram"]:
            dot, txt = OFF, "Telegram off"
        elif self.online is False:
            dot, txt = RED, "No internet"
        else:
            dot, txt = GREEN, "Telegram on"
        self.chip(left + cw + gap, row1, cw, chh, dot, txt)
        n = len(self.faces)
        if self.engine is None:
            dot, txt = "#c9a227", "Loading face ID..." if self.engine_loading else "Face ID unavailable"
        elif n == 0:
            dot, txt = "#c9a227", "No faces registered"
        else:
            dot = GREEN
            txt = f"{n} face{'s' if n != 1 else ''}" + ("  -  auto-open" if self.cfg["auto_open"] else "")
        self.chip(left, row2, 2 * cw + gap, chh, dot, txt, command=lambda: self.go("faces"))

        # last visitor card
        y1, y2 = int(318 * s), H - int(26 * s)
        x2 = left + 2 * cw + gap
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
                self.T(tx, y1 + pad + 4 * s, "Last visitor", 13, SUB, anchor="nw", tags=(tag,))
                self.T(tx, y1 + pad + 26 * s, day_label(stamp), 17, WHITE, anchor="nw", bold=True, tags=(tag,))
                self.T(tx, y1 + pad + 52 * s, clock12(stamp), 17, WHITE, anchor="nw", tags=(tag,))
                self.T(tx, y2 - pad - 2 * s, "Tap for gallery", 12, SUB, anchor="sw", tags=(tag,))
        else:
            self.T((left + x2) / 2, (y1 + y2) / 2, "No visitors yet", 16, SUB, tags=(tag,))

        # tile grid: 4 x 3
        gx0, gx1 = int(380 * s), W - int(24 * s)
        gy0, gy1 = int(78 * s), H - int(22 * s)
        cwid, chei = (gx1 - gx0) / 4, (gy1 - gy0) / 3
        size = min(cwid - 12 * s, chei - 34 * s)
        tiles = [
            ("live", "Live view", lambda: self.go("live"), "on"),
            ("camera", "Capture", self.capture_manual, "on"),
            ("gallery", "Gallery", lambda: self.open_gallery(0), "on"),
            ("people", "Faces", lambda: self.go("faces"), "on"),
            ("unlock", "Unlocked" if self.unlocked else "Unlock", self.ask_unlock,
             "good" if self.unlocked else "on"),
            ("lock", "Lock", self.do_lock, "on"),
            ("face", "Scan face", self.scan_face, "on"),
            ("bell", "Test bell", self.test_bell, "on"),
            ("sound" if self.cfg["sound"] else "mute", "Sound" if self.cfg["sound"] else "Muted",
             self.toggle_sound, "on" if self.cfg["sound"] else "off"),
            ("send", "Telegram" if self.cfg["telegram"] else "Telegram off", self.toggle_telegram,
             "on" if self.cfg["telegram"] else "off"),
            ("person", "Auto-open" if self.cfg["auto_open"] else "Auto-open off", self.toggle_auto_open,
             "on" if self.cfg["auto_open"] else "off"),
            ("gear", "Settings", lambda: self.go("settings"), "on"),
        ]
        for i, (icon, label, cmd, state) in enumerate(tiles):
            col, row = i % 4, i // 4
            self.tile(gx0 + cwid * (col + 0.5), gy0 + chei * row + size / 2 + 4 * s, size,
                      icon, label, cmd, state)

    # ------------------------------------------------------------------
    # Live view
    # ------------------------------------------------------------------
    def place_video(self, extra, badge=True):
        """Video box that keeps the camera's own aspect ratio (no stretching / zoom)."""
        c, s, W, H = self.c, self.s, self.W, self.H
        pad = int(16 * s)
        ax1, ay1, ax2, ay2 = pad, self.hh, W - pad - extra, H - pad
        vw, vh = fit(ax2 - ax1, ay2 - ay1, self.cam.aspect)
        vx = ax1 + (ax2 - ax1 - vw) / 2
        vy = ay1 + (ay2 - ay1 - vh) / 2
        c.create_rectangle(vx, vy, vx + vw, vy + vh, fill=BLACK, outline="")
        c.create_image(vx + vw / 2, vy + vh / 2, anchor="center", tags=("live_img",))
        msg = ("Camera not available - retrying...\n" + self.cam.error) if self.cam.error \
            else "Starting camera..."
        self.T(vx + vw / 2, vy + vh / 2, msg, 15, SUB, tags=("live_msg",), justify="center",
               width=vw - 30)
        self.cam.target = (vw - vw % 2, vh - vh % 2)
        self.live_box = (vx, vy, vw, vh)
        if badge:
            rrect(c, vx + 10 * s, vy + 10 * s, vx + 74 * s, vy + 34 * s, 12 * s, fill=RED, outline="")
            self.T(vx + 42 * s, vy + 22 * s, "LIVE", 12, WHITE, bold=True)

    def draw_live(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.header("Live view")
        pad, side, gap = int(16 * s), int(176 * s), int(12 * s)
        self.place_video(side + gap)
        ay1, ay2 = self.hh, H - pad
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
                self.c.itemconfigure("live_msg", text="Camera not available - retrying...\n" + self.cam.error)
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
        titles = {"visitor": "Someone is at the door", "scan": "Face check"}
        self.header(titles.get(self.visit_kind, "Visitor"),
                    datetime.now().strftime("%d %b, %I:%M %p").lstrip("0"))
        pad, side, gap = int(16 * s), int(200 * s), int(12 * s)
        x1, y1, x2, y2 = pad, self.hh, W - pad - side - gap, H - pad
        rrect(c, x1, y1, x2, y2, 16 * s, fill=BLACK, outline="")
        pil = self.get_pil(self.visitor_photo, (x2 - x1 - 12 * s, y2 - y1 - 12 * s)) \
            if self.visitor_photo else None
        if pil:
            self.put_image((x1 + x2) / 2, (y1 + y2) / 2, pil)
        else:
            self.T((x1 + x2) / 2, (y1 + y2) / 2, "Taking photo...", 20, SUB)
        bx = W - pad - side
        y = y1
        fr = self.face_result
        if fr:
            st = fr["state"]
            if st == "match":
                title, sub, col = (f"Welcome, {fr['name']}", f"Match {fr['score']:.2f}"
                                   + ("  -  door unlocked" if fr.get("opened") else ""), GREEN)
            elif st == "unknown":
                title, sub, col = "Unknown visitor", f"Best match {fr.get('score', 0):.2f}", RED
            elif st == "noface":
                title, sub, col = "No face found", "Look at the camera", "#b98a1d"
            elif st == "checking":
                title, sub, col = "Checking face...", "", "#4b3a78"
            elif st == "error":
                title, sub, col = "Face check failed", fr.get("error", ""), "#4b3a78"
            elif st == "empty":
                title, sub, col = "No faces registered", "Add one under Faces", "#4b3a78"
            else:
                title, sub, col = "Face ID is off", "", "#4b3a78"
            chh = 80 * s
            rrect(c, bx, y, bx + side, y + chh, 14 * s, fill=col, outline="")
            self.T(bx + 14 * s, y + 12 * s, title, 16, WHITE, anchor="nw", bold=True,
                   width=side - 28 * s)
            if sub:
                self.T(bx + 14 * s, y + chh - 12 * s, sub, 12, WHITE, anchor="sw", width=side - 28 * s)
            y += chh + gap
        bh = max(40 * s, min(58 * s, (y2 - y - 2 * gap - 36 * s) / 3))
        self.button(bx, y, bx + side, y + bh, self.ask_unlock, "Unlock", "unlock", fill=GREEN,
                    fg=WHITE, px=17)
        self.button(bx, y + bh + gap, bx + side, y + 2 * bh + gap, lambda: self.open_gallery(0),
                    "Gallery", "gallery", px=16)
        self.button(bx, y + 2 * bh + 2 * gap, bx + side, y + 3 * bh + 2 * gap,
                    lambda: self.go("home"), "Dismiss", "check", px=16)
        if self.tg_text:
            self.T(bx + side / 2, y + 3 * bh + 3 * gap + 4 * s, self.tg_text, 13, SUB, anchor="n",
                   width=side, justify="center")

    # ------------------------------------------------------------------
    # Face recognition engine (your face_engine.py), run off the UI thread
    # ------------------------------------------------------------------
    def load_engine(self):
        if FaceEngine is None or np is None:
            self.engine_msg = ENGINE_ERROR or "numpy is missing"
            print("Face recognition unavailable:", self.engine_msg)
            return
        self.engine_loading = True

        def work():
            try:
                eng = FaceEngine(threshold=MATCH_THRESHOLD)
                self.events.put(("engine", eng, dict(eng.names()), ""))
            except Exception as e:
                self.events.put(("engine", None, {}, f"{type(e).__name__}: {e}"))

        threading.Thread(target=work, daemon=True).start()

    def on_engine(self, eng, faces, err):
        self.engine_loading = False
        self.engine, self.faces, self.engine_msg = eng, faces, err
        if eng:
            print(f"Face recognition ready ({len(faces)} registered)", flush=True)
        else:
            print("Face recognition unavailable:", err, flush=True)
            self.toast("Face recognition unavailable")
        self.refresh()

    def engine_task(self, fn, then):
        """Run fn() in a thread (one engine call at a time); then(result) runs in the UI."""
        def work():
            with self.engine_lock:
                try:
                    res = fn()
                except Exception as e:
                    res = e
            self.events.put(("task", then, res))

        threading.Thread(target=work, daemon=True).start()

    def refresh_faces(self):
        if self.engine:
            self.engine_task(lambda: dict(self.engine.names()), self._faces_loaded)

    def _faces_loaded(self, res):
        if isinstance(res, dict):
            self.faces = res
            self.refresh()

    def stamped(self, caption):
        return f"{caption} - {datetime.now().strftime('%d %b %Y, %I:%M:%S %p')}"

    def load_bgr(self, path):
        arr = np.asarray(Image.open(path).convert("RGB"))
        return np.ascontiguousarray(arr[:, :, ::-1])      # BGR, as OpenCV / the engine expect

    def _identify(self, path):
        frame = self.load_bgr(path)
        t0 = time.time()
        r = dict(self.engine.identify(frame))
        r["ms"] = int((time.time() - t0) * 1000)
        return r

    def start_recognition(self, path):
        if self.engine is None or not self.faces:
            self.face_result = {"state": "off" if self.engine is None else "empty"}
            print("Face scan skipped: " + ("engine not loaded" if self.engine is None
                  else "no faces registered"), flush=True)
            self.deliver(path, "Someone is at your door!")
            return
        self.face_result = {"state": "checking"}
        print(f"[{datetime.now().strftime('%H:%M:%S')}] Scanning face...", flush=True)
        self.engine_task(lambda: self._identify(path), lambda r: self.on_face_result(path, r))

    def on_face_result(self, path, r):
        if isinstance(r, Exception):
            r = {"error": type(r).__name__}
        stamp = datetime.now().strftime("%H:%M:%S")
        opened = False
        if "error" in r:
            print(f"[{stamp}] FACE ERROR: {r['error']}", flush=True)
            state, caption = "error", "Someone is at your door!"
        elif r.get("name"):
            print(f"[{stamp}] FACE MATCHED: {r['name']}  score={r['score']:.3f} "
                  f"(threshold {MATCH_THRESHOLD})  {r.get('ms', 0)} ms", flush=True)
            state, caption = "match", f"{r['name']} recognised ({r['score']:.2f})"
            if self.cfg["auto_open"]:
                self.do_unlock(f"Welcome {r['name']}")
                caption += " - door opened"
                opened = True
        elif r.get("faces", 0) == 0:
            print(f"[{stamp}] NO FACE DETECTED in photo", flush=True)
            state, caption = "noface", "Someone is at your door! (no face detected)"
        else:
            print(f"[{stamp}] FACE NOT MATCHED: closest={r.get('closest')}  "
                  f"score={r.get('score', 0):.3f} < threshold {MATCH_THRESHOLD}", flush=True)
            state, caption = "unknown", "Unknown visitor at your door!"
        self.face_result = dict(r, state=state, opened=opened)
        self.deliver(path, caption)

    def deliver(self, path, caption):
        """Send the photo to Telegram (if on) and refresh the visitor screen."""
        if TG_READY and self.cfg["telegram"]:
            self.send_photo(path, self.stamped(caption))
        else:
            self.tg_text = "Telegram not set up" if not TG_READY else "Telegram is off"
        if self.page == "visitor":
            self.redraw()

    # ------------------------------------------------------------------
    # Faces page
    # ------------------------------------------------------------------
    def draw_faces(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        n = len(self.faces)
        if self.engine is None:
            sub = "Loading..." if self.engine_loading else "Not available"
        else:
            sub = f"{n} registered"
        self.header("Faces", sub)
        pad = int(16 * s)
        if self.engine is None:
            y = self.hh + 10 * s
            rrect(c, pad, y, W - pad, y + 160 * s, 16 * s, fill=PANEL, outline="")
            if self.engine_loading:
                self.T(W / 2, y + 80 * s, "Loading face recognition...", 18, SUB)
            else:
                self.T(W / 2, y + 36 * s, "Face recognition is not available", 19, WHITE, bold=True)
                self.T(W / 2, y + 84 * s, self.engine_msg or "Unknown error", 13, SUB,
                       width=W - 2 * pad - 40 * s, justify="center")
                self.T(W / 2, y + 128 * s, "Run:  python3 face_engine.py --download", 14, SUB)
            return
        bw, bh = int(176 * s), int(40 * s)
        by = pad + (2 * int(20 * s) - bh) / 2
        self.button(W - pad - bw, by, W - pad, by + bh, self.start_register, "Register new", "plus",
                    fill=ACCENT, fg=WHITE, px=14)
        items = sorted(self.faces.items(), key=lambda kv: kv[0].lower())
        if not items:
            self.T(W / 2, H / 2 - 10 * s, "No faces registered yet", 24, WHITE, bold=True)
            self.T(W / 2, H / 2 + 24 * s, "Tap Register new to add the first person", 15, SUB)
            return
        y0 = self.hh + 6 * s
        rh, gap = 54 * s, 8 * s
        per = max(1, int((H - y0 - 56 * s) // (rh + gap)))
        pages = (len(items) + per - 1) // per
        self.faces_page = max(0, min(self.faces_page, pages - 1))
        for i, (name, cnt) in enumerate(items[self.faces_page * per:(self.faces_page + 1) * per]):
            y = y0 + i * (rh + gap)
            rrect(c, pad, y, W - pad, y + rh, 14 * s, fill=PANEL, outline="")
            draw_icon(c, "person", pad + 34 * s, y + rh / 2, 13 * s, WHITE, bg=PANEL)
            self.T(pad + 66 * s, y + rh / 2 - 9 * s, name, 17, WHITE, anchor="w", bold=True)
            self.T(pad + 66 * s, y + rh / 2 + 13 * s, f"{cnt} sample{'s' if cnt != 1 else ''}", 12, SUB,
                   anchor="w")
            self.button(W - pad - 124 * s, y + 8 * s, W - pad - 10 * s, y + rh - 8 * s,
                        lambda nm=name: self.ask_delete_face(nm), "Delete", "trash", fill=RED,
                        fg=WHITE, px=13)
        if pages > 1:
            yb = H - 46 * s
            self.button(W / 2 - 100 * s, yb, W / 2 - 56 * s, yb + 36 * s,
                        lambda: self.faces_step(-1), icon="left", radius=18 * s, icon_r=8 * s)
            self.T(W / 2, yb + 18 * s, f"{self.faces_page + 1} / {pages}", 15, WHITE, bold=True)
            self.button(W / 2 + 56 * s, yb, W / 2 + 100 * s, yb + 36 * s,
                        lambda: self.faces_step(1), icon="right", radius=18 * s, icon_r=8 * s)

    def faces_step(self, d):
        self.faces_page += d
        self.redraw()

    def ask_delete_face(self, name):
        self.confirm(f"Remove {name}?", "Their face will no longer be recognised.", "Remove",
                     lambda: self.delete_face(name), RED)

    def delete_face(self, name):
        def work():
            self.engine.delete(name)
            return dict(self.engine.names())

        self.engine_task(work, lambda res: self._face_deleted(name, res))

    def _face_deleted(self, name, res):
        if isinstance(res, dict):
            self.faces = res
            self.toast(f"Removed {name}")
        else:
            self.toast(f"Could not remove ({type(res).__name__})")
        self.refresh()

    def toggle_auto_open(self):
        self.cfg["auto_open"] = not self.cfg["auto_open"]
        save_settings(self.cfg)
        self.refresh()
        self.toast("Door opens on a face match" if self.cfg["auto_open"] else "Auto-open off")

    def scan_face(self):
        self.begin_visit("scan")

    # ------------------------------------------------------------------
    # On-screen keyboard for the name
    # ------------------------------------------------------------------
    def start_register(self):
        self.kb_text, self.kb_shift = "", True
        self.go("name")

    def draw_name(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.header("Register face", "Type the person's name", back="faces")
        pad = int(16 * s)
        fy, fh = self.hh, 54 * s
        rrect(c, pad, fy, W - pad, fy + fh, 14 * s, fill=WHITE, outline="")
        self.T(pad + 18 * s, fy + fh / 2, self.kb_text + "|", 24, INK, anchor="w", bold=True,
               tags=("kb_text",))
        gap = 6 * s
        top = fy + fh + 10 * s
        kh = (H - top - pad - 4 * gap) / 5
        kw = (W - 2 * pad - 9 * gap) / 10
        rows = [
            [(ch, 1.0, ("char", ch)) for ch in "1234567890"],
            [(ch, 1.0, ("char", ch)) for ch in "QWERTYUIOP"],
            [(ch, 1.0, ("char", ch)) for ch in "ASDFGHJKL"],
            [("Shift", 1.5, ("shift",))] + [(ch, 1.0, ("char", ch)) for ch in "ZXCVBNM"]
            + [("Delete", 1.5, ("back",))],
            [("Cancel", 2.5, ("cancel",)), ("space", 5.0, ("char", " ")), ("Next", 2.5, ("next",))],
        ]
        for r, row in enumerate(rows):
            widths = [u * kw + (u - 1) * gap for _, u, _ in row]
            x = (W - (sum(widths) + (len(row) - 1) * gap)) / 2
            y = top + r * (kh + gap)
            for (label, u, act), w in zip(row, widths):
                kind = act[0]
                if len(label) == 1 and label.isalpha():
                    label = label.upper() if self.kb_shift else label.lower()
                fill, fg = (WHITE, INK) if kind == "char" else ("#4b3a78", WHITE)
                if kind == "shift" and self.kb_shift:
                    fill = ACCENT
                if kind == "next":
                    fill = GREEN
                self.button(x, y, x + w, y + kh, lambda a=act: self.kb_action(a), label, fill=fill,
                            fg=fg, px=17 if kind == "char" else 14, radius=10 * s)
                x += w + gap

    def kb_action(self, act):
        kind = act[0]
        if kind == "char":
            self.kb_type(act[1])
        elif kind == "back":
            self.kb_back()
        elif kind == "shift":
            self.kb_shift = not self.kb_shift
            self.redraw()
        elif kind == "cancel":
            self.go("faces")
        elif kind == "next":
            self.kb_next()

    def kb_type(self, ch, raw=False):
        if len(self.kb_text) >= 20:
            return
        if not raw and ch.isalpha():
            ch = ch.upper() if self.kb_shift else ch.lower()
        self.kb_text += ch
        self._kb_update(ch == " ")

    def kb_back(self):
        self.kb_text = self.kb_text[:-1]
        self._kb_update(self.kb_text == "" or self.kb_text.endswith(" "))

    def _kb_update(self, shift):
        changed = shift != self.kb_shift
        self.kb_shift = shift
        if changed:
            self.redraw()
        else:
            self.c.itemconfigure("kb_text", text=self.kb_text + "|")

    def kb_next(self):
        name = self.kb_text.strip()
        if not name:
            self.toast("Type a name first")
            return
        self.reg = {"name": name, "frames": [], "state": "ready", "msg": "", "ok": False, "job": None}
        self.go("register")

    def on_space(self, e=None):
        if self.page != "name":
            self.events.put(("ring",))

    def on_key(self, e):
        if self.page != "name" or self.modal:
            return
        if e.keysym == "BackSpace":
            self.kb_back()
        elif e.keysym in ("Return", "KP_Enter"):
            self.kb_next()
        elif e.char and (e.char.isalnum() or e.char in " -."):
            self.kb_type(e.char, raw=True)

    # ------------------------------------------------------------------
    # Registering a face: several photos, then the engine learns them
    # ------------------------------------------------------------------
    def draw_register(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        reg = self.reg
        self.header("Register face", reg.get("name", ""), back="faces")
        pad, side, gap = int(16 * s), int(200 * s), int(12 * s)
        self.place_video(side + gap, badge=False)
        bx = W - pad - side
        y = self.hh
        state = reg.get("state")
        n = len(reg.get("frames", []))
        if state == "ready":
            self.T(bx, y + 4 * s, f"Ask {reg['name']} to look at the camera.\n\n{REGISTER_SHOTS} photos "
                   "will be taken - turn the head slightly between shots.", 14, WHITE, anchor="nw",
                   width=side)
            self.button(bx, H - pad - 62 * s, bx + side, H - pad, self.reg_start, "Start", "camera",
                        fill=GREEN, fg=WHITE, px=17)
        elif state == "capturing":
            self.T(bx, y + 4 * s, f"Photo {min(n + 1, REGISTER_SHOTS)} of {REGISTER_SHOTS}", 20, WHITE,
                   anchor="nw", bold=True)
            for i in range(REGISTER_SHOTS):
                cx = bx + 10 * s + i * 28 * s
                c.create_oval(cx - 9 * s, y + 56 * s, cx + 9 * s, y + 74 * s,
                              fill=WHITE if i < n else OFF, outline="")
            self.T(bx, y + 96 * s, "Look at the camera and turn your head slightly each time.", 14,
                   SUB, anchor="nw", width=side)
            self.button(bx, H - pad - 56 * s, bx + side, H - pad, lambda: self.go("faces"), "Cancel",
                        px=16)
        elif state == "saving":
            self.T(bx, y + 4 * s, "Saving face...", 20, WHITE, anchor="nw", bold=True)
            self.T(bx, y + 40 * s, "This can take a few seconds.", 14, SUB, anchor="nw", width=side)
        else:
            ok = reg.get("ok")
            card = 120 * s
            rrect(c, bx, y, bx + side, y + card, 14 * s, fill=GREEN if ok else "#b98a1d", outline="")
            self.T(bx + 14 * s, y + 14 * s, "Face saved" if ok else "Not saved", 17, WHITE,
                   anchor="nw", bold=True)
            self.T(bx + 14 * s, y + 44 * s, reg.get("msg", ""), 13, WHITE, anchor="nw",
                   width=side - 28 * s)
            self.button(bx, H - pad - 56 * s, bx + side, H - pad, lambda: self.go("faces"), "Done",
                        "check", px=16)

    def reg_abort(self):
        job = self.reg.get("job")
        if job:
            self.root.after_cancel(job)
        if self.reg.get("state") in ("ready", "capturing"):
            self.reg["state"] = "cancelled"
        self.reg["job"] = None

    def reg_start(self):
        self.reg.update(state="capturing", frames=[])
        self.redraw()
        self.reg["job"] = self.root.after(1500, self.reg_shoot)

    def reg_shoot(self):
        self.reg["job"] = None
        if self.reg.get("state") == "capturing":
            self.cam.grab("register")

    def on_frame(self, tag, frame):
        if tag != "register" or self.reg.get("state") != "capturing":
            return
        self.reg["frames"].append(frame)
        n = len(self.reg["frames"])
        done = n >= REGISTER_SHOTS
        if done:
            self.reg["state"] = "saving"
        self.redraw()
        self.flash()
        if done:
            name, frames = self.reg["name"], list(self.reg["frames"])
            self.engine_task(lambda: self.engine.register(name, frames), self.on_registered)
        else:
            self.reg["job"] = self.root.after(1100, self.reg_shoot)

    def on_registered(self, res):
        if isinstance(res, Exception):
            ok, msg = False, f"Registration failed ({type(res).__name__})"
        else:
            ok, msg = bool(res[0]), str(res[1])
        print("Register face:", msg, flush=True)
        self.reg.update(state="done", ok=ok, msg=msg, frames=[])
        self.refresh_faces()
        if self.page == "register":
            self.redraw()
        else:
            self.toast(msg)

    # ------------------------------------------------------------------
    # Settings
    # ------------------------------------------------------------------
    def draw_settings(self):
        c, s, W, H = self.c, self.s, self.W, self.H
        self.header("Settings", clock=True)
        pad = int(16 * s)
        gap = int(8 * s)
        y0 = self.hh + 6 * s
        rows_n = 6
        avail = H - y0 - 44 * s - 40 * s
        rh = max(32 * s, min(50 * s, avail / rows_n - gap))
        x1, x2 = pad, W - pad

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
        bw, bh = int(84 * s), int(min(34 * s, rh - 6 * s))
        for k, name in enumerate(reversed(list(CHIMES))):
            sel = self.cfg["chime"] == name
            xr = right - k * (bw + 6 * s)
            self.button(xr - bw, m - bh / 2, xr, m + bh / 2, lambda n=name: self.set_chime(n), name,
                        fill=WHITE if sel else "#4b3a78", fg=INK if sel else WHITE, px=13,
                        radius=bh / 2)

        m = row(3, "Door stays unlocked for")
        cr = int(min(17 * s, rh / 2 - 3 * s))
        self.button(right - cr * 2, m - cr, right, m + cr, lambda: self.step_open(1), icon="plus",
                    radius=cr, icon_r=cr * 0.5)
        self.T(right - cr * 2 - 34 * s, m, f"{self.cfg['open_seconds']} s", 17, WHITE, bold=True)
        self.button(right - cr * 4 - 68 * s, m - cr, right - cr * 2 - 68 * s, m + cr,
                    lambda: self.step_open(-1), icon="minus", radius=cr, icon_r=cr * 0.5)

        m = row(4, "Unlock the door when a face is recognised")
        self.switch(right, m, self.cfg["auto_open"], self.toggle_auto_open)
        m = row(5, "Full screen")
        self.switch(right, m, self.is_full, lambda: self.set_fullscreen(not self.is_full))

        y = y0 + rows_n * (rh + gap) + 2 * s
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

    def begin_visit(self, kind):
        """Show the visitor screen, take a photo, then (when it arrives) check the face."""
        self.visit_kind = kind
        self.visitor_photo = None
        self.face_result = None
        self.tg_text = ""
        self.go("visitor")
        self.visitor_job = self.root.after(
            60000, lambda: self.go("home") if self.page == "visitor" else None)
        self.cam.capture(new_photo_path(kind), kind)

    def on_ring(self):
        now = time.time()
        if now - self.last_ring < RING_COOLDOWN:
            return
        self.last_ring = now
        self.chime()
        self.begin_visit("visitor")

    def capture_manual(self):
        if time.time() - self.last_manual < 1.0:
            return
        self.last_manual = time.time()
        self.cam.capture(new_photo_path("manual"), "manual")

    def on_captured(self, path, tag):
        if tag in ("visitor", "scan"):
            self.visitor_photo = path
            self.start_recognition(path)
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

    def do_unlock(self, reason=""):
        if self.relock_job:
            self.root.after_cancel(self.relock_job)
        n = self.cfg["open_seconds"]
        if self.lock:
            self.lock.on()
        self.unlocked = True
        self.unlock_until = time.time() + n
        self.relock_job = self.root.after(n * 1000, self.do_lock)
        self.refresh()
        self.toast(f"{reason} - door unlocked" if reason else f"Door unlocked for {n} seconds")

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
        if self.page in ("live", "register"):
            self.update_live()
        if not self.closing:
            self.root.after(40, self.poll)

    def handle(self, ev):
        kind = ev[0]
        if kind == "ring":
            self.on_ring()
        elif kind == "captured":
            self.on_captured(ev[1], ev[2])
        elif kind == "frame":
            self.on_frame(ev[1], ev[2])
        elif kind == "capture_failed":
            self.toast("Could not take photo - check the camera")
            if ev[1] == "register" and self.reg.get("state") == "capturing":
                self.reg.update(state="done", ok=False,
                                msg="Camera error - check the camera and try again")
                self.redraw()
            elif self.page == "visitor":
                self.tg_text = "Camera error"
                self.redraw()
        elif kind == "cam_error":
            self.toast("Camera not available")
        elif kind == "cam_ready":
            self.toast("Camera ready")
            if self.page in ("live", "register"):
                self.redraw()
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
        elif kind == "engine":
            self.on_engine(ev[1], ev[2], ev[3])
        elif kind == "task":
            ev[1](ev[2])

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