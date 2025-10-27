import math
import os
import threading
import tkinter as tk
from tkinter import filedialog, messagebox, ttk, colorchooser
from PIL import Image, ImageTk
import traceback
import sys
import json
import csv
import colorsys
from tkinter import simpledialog
import time
import random

# Base directory of this script; all app data lives here
BASE_DIR = os.path.dirname(os.path.abspath(__file__))


max_distance = math.sqrt(255**2 * 3)  # distance between (0,0,0) and (255,255,255)
max_distance_sq = max_distance * max_distance

# Module-level progress variable (0.0 .. 100.0). You can edit this variable elsewhere
# or call set_progress(value) to update it. The GUI polls this variable and updates the bar.
progress = 0.0
_progress_lock = threading.Lock()

# Cancellation and progress details
_cancel_event = threading.Event()
processed_pixels = 0
total_pixels = 0

similarity_threshold = 95  # percentage (kept for backward compatibility)
saved_colors = []
# replace big pallettes dict with a minimal set (user palettes are loaded from files/directory)
# provide a small default so the UI shows something
pallettes = {}

# Keep only the essential default options; user palettes will be discovered from the palettes directory
DEFAULT_PALETTE_OPTIONS = ["Simplify Pallette"]

# Ensure default palette entries exist in memory so the UI can display them
for _opt in DEFAULT_PALETTE_OPTIONS:
    if _opt != "Simplify Pallette":
        pallettes.setdefault(_opt, [])

# Persistence for user palettes
# All app data stays alongside this script
_CONFIG_STORE = os.path.join(BASE_DIR, "palette_optimizer_config.json")
_PALETTES_DIR = os.path.join(BASE_DIR, "palettes")
# persist last selected palette
_LAST_SELECTED_PALETTE = None


def save_config():
    try:
        data = {
            "palettes_dir": _PALETTES_DIR,
            "last_palette": _LAST_SELECTED_PALETTE,
            "similarity_threshold": similarity_threshold,
        }
        with open(_CONFIG_STORE, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2)
    except Exception:
        pass


def load_config():
    global _PALETTES_DIR, _LAST_SELECTED_PALETTE, similarity_threshold
    try:
        if not os.path.exists(_CONFIG_STORE):
            return
        with open(_CONFIG_STORE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        # Force palettes dir to stay under the app directory
        _PALETTES_DIR = os.path.join(BASE_DIR, "palettes")
        lp = data.get('last_palette')
        if isinstance(lp, str) and lp.strip():
            _LAST_SELECTED_PALETTE = lp.strip()
        st = data.get('similarity_threshold')
        if isinstance(st, int):
            similarity_threshold = max(0, min(100, st))
    except Exception:
        pass


def _hex_from_rgb(t):
    return '#{:02x}{:02x}{:02x}'.format(t[0], t[1], t[2])


def _rgb_from_hex(h):
    h = h.lstrip('#')
    if len(h) == 3:
        h = ''.join(ch*2 for ch in h)
    v = int(h, 16)
    return ((v >> 16) & 0xFF, (v >> 8) & 0xFF, v & 0xFF)


def _slugify(name: str) -> str:
    # simple slug: replace non-alnum with underscore
    valid = []
    for ch in name:
        if ch.isalnum() or ch in ('-', '_'):
            valid.append(ch)
        else:
            valid.append('_')
    s = ''.join(valid).strip('_')
    if not s:
        s = 'palette'
    return s


def save_palettes():
    """Save each palette as a separate JSON file in _PALETTES_DIR. File contents are a JSON list of hex strings."""
    try:
        os.makedirs(_PALETTES_DIR, exist_ok=True)
        for name, cols in pallettes.items():
            try:
                fname = _slugify(name) + '.json'
                path = os.path.join(_PALETTES_DIR, fname)
                data = [_hex_from_rgb(c) for c in cols]
                with open(path, 'w', encoding='utf-8') as f:
                    json.dump(data, f, indent=2)
            except Exception:
                pass
    except Exception:
        pass


def _parse_palette_file(path: str):
    """Parse a palette file (json/txt/csv). Returns list of RGB tuples.
    Supported formats:
      - JSON: list of hex strings (e.g. ["#ffffff","#000000"]) or dict {name: [...]}.
      - TXT: one hex per line.
      - CSV: first column entries are hex values (header optional).
    """
    try:
        ext = os.path.splitext(path)[1].lower()
        if ext == '.json':
            with open(path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            # If dict, try to take first list value
            if isinstance(data, dict):
                # if it's a mapping of name -> colors, pick the first entry
                for v in data.values():
                    if isinstance(v, list):
                        data = v
                        break
            if isinstance(data, list):
                cols = []
                for hx in data:
                    if isinstance(hx, str):
                        try:
                            cols.append(_rgb_from_hex(hx))
                        except Exception:
                            pass
                return cols
        elif ext == '.txt':
            cols = []
            with open(path, 'r', encoding='utf-8') as f:
                for ln in f:
                    hx = ln.strip()
                    if not hx:
                        continue
                    try:
                        cols.append(_rgb_from_hex(hx))
                    except Exception:
                        pass
            return cols
        elif ext == '.csv':
            cols = []
            with open(path, 'r', encoding='utf-8') as f:
                reader = csv.reader(f)
                for row in reader:
                    if not row:
                        continue
                    hx = row[0].strip()
                    if not hx:
                        continue
                    try:
                        cols.append(_rgb_from_hex(hx))
                    except Exception:
                        pass
            return cols
    except Exception:
        pass
    return None


def _sort_palette_colors(cols):
    """Return a new list of colors sorted by perceived luminance (dark -> light).
    Each color is an (r,g,b) tuple. Tie-breaker uses the RGB tuple.
    """
    try:
        def luminance(c):
            # Rec. 709 luma
            return 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2]
        return sorted(cols, key=lambda c: (luminance(c), c))
    except Exception:
        return list(cols)


def _sort_palette_colors_hsv(cols):
    """Return colors sorted by hue, then saturation, then value."""
    try:
        def hsv_key(c):
            r, g, b = c
            h, s, v = colorsys.rgb_to_hsv(r/255.0, g/255.0, b/255.0)
            return (h, s, v)
        return sorted(cols, key=hsv_key)
    except Exception:
        return list(cols)


def load_palettes():
    """Load palettes from the palettes directory. Each supported file becomes a palette named after its filename.
    This augments built-in palettes; user palettes saved in the dir are loaded.
    """
    try:
        # keep existing built-ins and then overlay/load user palettes
        if not os.path.exists(_PALETTES_DIR):
            return
        for fname in os.listdir(_PALETTES_DIR):
            path = os.path.join(_PALETTES_DIR, fname)
            if not os.path.isfile(path):
                continue
            cols = _parse_palette_file(path)
            if not cols:
                continue
            name = os.path.splitext(os.path.basename(path))[0]
            # make a user-friendly name by replacing underscores
            name = name.replace('_', ' ')
            # Avoid clobbering built-in palettes
            if name in pallettes:
                # append suffix
                i = 1
                newname = f"{name} {i}"
                while newname in pallettes:
                    i += 1
                    newname = f"{name} {i}"
                name = newname
            pallettes[name] = cols
            if name not in DEFAULT_PALETTE_OPTIONS:
                DEFAULT_PALETTE_OPTIONS.append(name)
            # sort loaded palette colors
            try:
                pallettes[name] = _sort_palette_colors(pallettes[name])
            except Exception:
                pass
    except Exception:
        pass

# Load config and persisted palettes at module import time
load_config()
load_palettes();

# Ensure default palettes exist in memory (so UI shows something even if no files on disk)
for _opt in DEFAULT_PALETTE_OPTIONS:
    if _opt != "Simplify Pallette" and _opt not in pallettes:
        pallettes[_opt] = []

class ImageViewer(tk.Tk):
    def __init__(self):
        super().__init__()
        global _LAST_SELECTED_PALETTE
        # Change the app window title
        self.title("Palette Optimizer")
        self.geometry("1200x600")  # wider window for side-by-side

        # Track open popup dialogs so we can close them when main window closes
        self._open_dialogs = []
        # Ensure popups are closed when the main window is closed
        self.protocol("WM_DELETE_WINDOW", self._on_close_main)

        # State
        self.file_path = None            # path opened by user
        self.save_path = None            # path to save to (updated by Save As)
        self.original_image = None
        self.converted_image = None
        self._img_tk = None  # keep reference to avoid GC
        # Default to last selected palette if present; otherwise fall back to Simplify
        startup_palette = _LAST_SELECTED_PALETTE
        try:
            exists = bool(startup_palette) and (startup_palette in DEFAULT_PALETTE_OPTIONS or startup_palette in pallettes)
        except Exception:
            exists = False
        if not exists:
            startup_palette = "Simplify Pallette"
            try:
                _LAST_SELECTED_PALETTE = startup_palette
                save_config()
            except Exception:
                pass
        self.pal_choice = tk.StringVar(value=startup_palette)
        self.similarity_threshold_var = tk.IntVar(value=similarity_threshold)
        # Persist palette selection changes
        try:
            self.pal_choice.trace_add('write', lambda *_: self._on_palette_var_changed())
        except Exception:
            pass

        # Per-canvas zoom state
        self.scale_orig = 1.0
        self.scale_conv = 1.0
        self._init_view_done_orig = False
        self._init_view_done_conv = False
        self.show_after_on_right = True  # Space toggles

        # Top menu (File + Options)
        self._build_menu()

        # Top controls
        ctrl = tk.Frame(self)
        ctrl.pack(fill="x", padx=6, pady=6)

        # Old toolbar palette dropdown removed per request
        self.open_btn = None

        # Run/Cancel buttons on the right-hand side
        btns_fr = tk.Frame(ctrl)
        btns_fr.pack(side="right")
        self.run_btn = tk.Button(btns_fr, text="Run", command=self.start_analyze_thread)
        self.run_btn.pack(side="left", padx=(4, 0))
        self.cancel_btn = tk.Button(btns_fr, text="Cancel", state="disabled", command=self._on_cancel)
        self.cancel_btn.pack(side="left", padx=(4, 0))

        # Progress bar and percentage label (right side)
        self.progress_var = tk.DoubleVar(value=0.0)
        self.progress_bar = ttk.Progressbar(ctrl, variable=self.progress_var, maximum=100, length=200)
        self.progress_bar.pack(side="right", padx=(8, 4))
        self._progress_label = tk.Label(ctrl, text="0%")
        self._progress_label.pack(side="right", padx=(0, 8))

        self.path_label = tk.Label(ctrl, text="No file selected", anchor="w")
        self.path_label.pack(side="left", fill="x", expand=True, padx=(8, 0))

        # Canvas + scrollbars (side-by-side)
        container = tk.Frame(self)
        container.pack(fill="both", expand=True)

        # Left: original image
        left_frame = tk.Frame(container)
        left_frame.pack(side="left", fill="both", expand=True)
        self.canvas_orig = tk.Canvas(left_frame, background="#222")
        self.hbar_orig = tk.Scrollbar(left_frame, orient="horizontal", command=self.canvas_orig.xview)
        self.vbar_orig = tk.Scrollbar(left_frame, orient="vertical", command=self.canvas_orig.yview)
        self.canvas_orig.configure(xscrollcommand=self.hbar_orig.set, yscrollcommand=self.vbar_orig.set)
        self.vbar_orig.pack(side="right", fill="y")
        self.hbar_orig.pack(side="bottom", fill="x")
        self.canvas_orig.pack(side="left", fill="both", expand=True)

        # Right: converted image
        right_frame = tk.Frame(container)
        right_frame.pack(side="left", fill="both", expand=True)
        self.canvas_conv = tk.Canvas(right_frame, background="#222")
        self.hbar_conv = tk.Scrollbar(right_frame, orient="horizontal", command=self.canvas_conv.xview)
        self.vbar_conv = tk.Scrollbar(right_frame, orient="vertical", command=self.canvas_conv.yview)
        self.canvas_conv.configure(xscrollcommand=self.hbar_conv.set, yscrollcommand=self.vbar_conv.set)
        self.vbar_conv.pack(side="right", fill="y")
        self.hbar_conv.pack(side="bottom", fill="x")
        self.canvas_conv.pack(side="left", fill="both", expand=True)

        # Bind canvas interactions
        self._bind_canvas(self.canvas_orig, which="orig")
        self._bind_canvas(self.canvas_conv, which="conv")

        # Re-render when either canvas is resized
        self.canvas_orig.bind("<Configure>", lambda e: self._render_image())
        self.canvas_conv.bind("<Configure>", lambda e: self._render_image())

        # Status bar (bottom)
        status = tk.Frame(self, relief="sunken", borderwidth=1)
        status.pack(fill="x", side="bottom")
        self.status_left = tk.Label(status, text="Orig: -,-  RGB: -  HEX: -", anchor="w")
        self.status_left.pack(side="left", padx=6)
        self.status_right = tk.Label(status, text="Conv: -,-  RGB: -  HEX: -", anchor="w")
        self.status_right.pack(side="left", padx=12)
        self.status_prog = tk.Label(status, text="", anchor="e")
        self.status_prog.pack(side="right", padx=6)

        # Start polling the module-level progress variable
        self._poll_progress()

        # Keyboard shortcuts
        self.bind("<Return>", self._on_return_main)  # Run
        self.bind("<F5>", lambda e: (self._on_return_main(e)))
        self.bind("<Control-o>", lambda e: (self.open_image(), "break"))
        self.bind("<Control-s>", lambda e: (self.save_image(), "break"))
        self.bind("<Control-Shift-S>", lambda e: (self.save_image_as(), "break"))
        self.bind("<Escape>", lambda e: (self._close_top_dialog(), "break"))
        # Zoom with +/-"
        self.bind("<plus>", lambda e: (self._zoom_both(1.1), "break"))
        self.bind("<minus>", lambda e: (self._zoom_both(1/1.1), "break"))
        self.bind("<KP_Add>", lambda e: (self._zoom_both(1.1), "break"))
        self.bind("<KP_Subtract>", lambda e: (self._zoom_both(1/1.1), "break"))
        # Pan with arrows
        self.bind("<Left>", lambda e: (self._pan_both(-0.1, 0.0), "break"))
        self.bind("<Right>", lambda e: (self._pan_both(0.1, 0.0), "break"))
        self.bind("<Up>", lambda e: (self._pan_both(0.0, -0.1), "break"))
        self.bind("<Down>", lambda e: (self._pan_both(0.0, 0.1), "break"))
        # Toggle before/after on right
        self.bind("<space>", lambda e: (self._toggle_right_image(), "break"))

    def _on_palette_var_changed(self):
        global _LAST_SELECTED_PALETTE
        try:
            _LAST_SELECTED_PALETTE = self.pal_choice.get()
            save_config()
        except Exception:
            pass

    def _bind_canvas(self, canvas, which: str):
        canvas.bind("<ButtonPress-1>", lambda e: canvas.scan_mark(e.x, e.y))
        canvas.bind("<B1-Motion>", lambda e: canvas.scan_dragto(e.x, e.y, gain=1))
        # Mouse wheel zoom (Windows/macOS)
        canvas.bind("<MouseWheel>", lambda e: self._on_wheel(which, e))
        # Mouse wheel zoom (Linux)
        canvas.bind("<Button-4>", lambda e: self._on_wheel(which, e, delta=120))
        canvas.bind("<Button-5>", lambda e: self._on_wheel(which, e, delta=-120))
        # Motion to update status
        canvas.bind("<Motion>", lambda e: self._on_canvas_motion(which, e))

    def _on_cancel(self):
        try:
            _cancel_event.set()
        except Exception:
            pass
        try:
            self.cancel_btn.configure(state="disabled")
        except Exception:
            pass

    def _close_top_dialog(self):
        if not self._open_dialogs:
            return
        dlg = self._open_dialogs[-1]
        try:
            dlg.destroy()
        except Exception:
            pass
        try:
            self._open_dialogs.remove(dlg)
        except ValueError:
            pass

    def _center_over(self, parent, win):
        """Center toplevel 'win' over 'parent' window."""


        try:
            parent.update_idletasks()
            win.update_idletasks()
            px = parent.winfo_rootx()
            py = parent.winfo_rooty()
            pw = parent.winfo_width() or parent.winfo_reqwidth()
            ph = parent.winfo_height() or parent.winfo_reqheight()
            ww = win.winfo_width() or win.winfo_reqwidth()
            wh = win.winfo_height() or win.winfo_reqheight()
            x = max(px + (pw - ww) // 2, 0)
            y = max(py + (ph - wh) // 2, 0)
            win.geometry(f"+{x}+{y}")
        except Exception:
            pass

    def _on_canvas_motion(self, which: str, e):
        img = self.original_image if which == "orig" else (self.converted_image if self.show_after_on_right else self.original_image)
        if img is None:
            if which == "orig":
                self.status_left.config(text="Orig: -,-  RGB: -  HEX: -")
            else:
                self.status_right.config(text="Conv: -,-  RGB: -  HEX: -")
            return
        canvas = self.canvas_orig if which == "orig" else self.canvas_conv
        scale = self.scale_orig if which == "orig" else self.scale_conv
        # Base fit scale
        cw = max(canvas.winfo_width(), 1)
        ch = max(canvas.winfo_height(), 1)
        iw, ih = img.size
        base = min(1.0, cw / iw, ch / ih)
        eff = base * max(0.01, float(scale))
        # Map canvas coords to image pixel
        cx = canvas.canvasx(e.x)
        cy = canvas.canvasy(e.y)
        ix = int(cx / eff)
        iy = int(cy / eff)
        if 0 <= ix < iw and 0 <= iy < ih:
            try:
                r, g, b = img.getpixel((ix, iy))
                hx = _hex_from_rgb((r, g, b))
                txt = f"{('Orig' if which=='orig' else 'Conv')}: {ix},{iy}  RGB: {r},{g},{b}  HEX: {hx}"
            except Exception:
                txt = f"{('Orig' if which=='orig' else 'Conv')}: {ix},{iy}"
        else:
            txt = f"{('Orig' if which=='orig' else 'Conv')}: -, -  RGB: -  HEX: -"
        if which == "orig":
            self.status_left.config(text=txt)
        else:
            self.status_right.config(text=txt)

    def _on_wheel(self, which: str, e, delta=None):
        canvas = self.canvas_orig if which == "orig" else self.canvas_conv
        img = self.original_image if which == "orig" else (self.converted_image if self.show_after_on_right else self.original_image)
        if img is None:
            return
        d = (e.delta if delta is None else delta)
        if d == 0:
            return
        factor = 1.1 if d > 0 else (1/1.1)
        # Compute pre-zoom ratios
        iw, ih = img.size
        cw = max(canvas.winfo_width(), 1)
        ch = max(canvas.winfo_height(), 1)
        base = min(1.0, cw / iw, ch / ih)
        scale = self.scale_orig if which == "orig" else self.scale_conv
        eff_before = base * max(0.01, float(scale))
        total_w_before = iw * eff_before
        total_h_before = ih * eff_before
        cx = canvas.canvasx(e.x)
        cy = canvas.canvasy(e.y)
        rx = 0.0 if total_w_before <= 0 else cx / total_w_before
        ry = 0.0 if total_h_before <= 0 else cy / total_h_before
        # Apply zoom and re-render
        if which == "orig":
            self.scale_orig = max(0.1, min(8.0, self.scale_orig * factor))
        else:
            self.scale_conv = max(0.1, min(8.0, self.scale_conv * factor))
        self._render_image()
        # Adjust view to keep cursor point stable
        scale_after = self.scale_orig if which == "orig" else self.scale_conv
        eff_after = base * max(0.01, float(scale_after))
        total_w_after = iw * eff_after
        total_h_after = ih * eff_after
        target_x = rx * total_w_after
        target_y = ry * total_h_after
        left = max(0.0, target_x - e.x)
        top = max(0.0, target_y - e.y)
        fx = 0.0 if total_w_after <= 0 else left / total_w_after
        fy = 0.0 if total_h_after <= 0 else top / total_h_after
        try:
            canvas.xview_moveto(max(0.0, min(1.0, fx)))
            canvas.yview_moveto(max(0.0, min(1.0, fy)))
        except Exception:
            pass

    def _zoom_both(self, factor: float):
        # Zoom around canvas centers
        for which in ("orig", "conv"):
            canvas = self.canvas_orig if which == "orig" else self.canvas_conv
            e = type("_E", (), {"x": canvas.winfo_width() // 2, "y": canvas.winfo_height() // 2, "delta": 120 if factor > 1 else -120})
            self._on_wheel(which, e)

    def _pan_both(self, dx_frac: float, dy_frac: float):
        try:
            self.canvas_orig.xview_scroll(int(dx_frac * 10), 'units')
            self.canvas_conv.xview_scroll(int(dx_frac * 10), 'units')
            self.canvas_orig.yview_scroll(int(dy_frac * 10), 'units')
            self.canvas_conv.yview_scroll(int(dy_frac * 10), 'units')
        except Exception:
            pass

    def _toggle_right_image(self):
        self.show_after_on_right = not self.show_after_on_right
        self._render_image()

    def _build_menu(self):
        menubar = tk.Menu(self)
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open...", command=self.open_image, accelerator="Ctrl+O")
        file_menu.add_command(label="Save", command=self.save_image, accelerator="Ctrl+S")
        file_menu.add_command(label="Save As...", command=self.save_image_as, accelerator="Ctrl+Shift+S")
        file_menu.add_separator()
        # Ensure we close popups when exiting
        file_menu.add_command(label="Exit", command=self._on_close_main)
        menubar.add_cascade(label="File", menu=file_menu)

        # Options menu opens a settings dialog
        options_menu = tk.Menu(menubar, tearoff=0)
        options_menu.add_command(label="Options...", command=self.open_options_dialog)
        menubar.add_cascade(label="Options", menu=options_menu)

        self.config(menu=menubar)

    def _on_close_main(self):
        # signal cancel if running
        try:
            _cancel_event.set()
        except Exception:
            pass
        # Close any open dialogs first
        for dlg in list(self._open_dialogs):
            try:
                dlg.destroy()
            except Exception:
                pass
        # then close main window
        try:
            self.destroy()
        except Exception:
            pass

    def open_options_dialog(self):
        dlg = tk.Toplevel(self)
        dlg.title("Palette Optimizer - Options")
        dlg.resizable(False, False)
        self._open_dialogs.append(dlg)
        # Make dialog modal/focused so Enter only affects this window
        try:
            dlg.transient(self)
            dlg.grab_set()
            dlg.focus_force()
            # center after the window has computed its requested size
            dlg.after(0, lambda: self._center_over(self, dlg))
        except Exception:
            pass

        def _close_and_remove():
            try:
                dlg.grab_release()
            except Exception:
                pass
            try:
                dlg.destroy()
            except Exception:
                pass
            try:
                self._open_dialogs.remove(dlg)
            except ValueError:
                pass

        dlg.protocol("WM_DELETE_WINDOW", _close_and_remove)

        # Root container with padding and grid expansion
        root = ttk.Frame(dlg, padding=10)
        root.grid(row=0, column=0, sticky="nsew")
        try:
            dlg.columnconfigure(0, weight=1)
            dlg.rowconfigure(0, weight=1)
            root.columnconfigure(0, weight=1)
        except Exception:
            pass

        # =========== Palette selection group ===========
        pal_group = ttk.LabelFrame(root, text="Palette")
        pal_group.grid(row=0, column=0, sticky="ew", padx=0, pady=(0, 8))
        for i in range(0, 6):
            try:
                pal_group.columnconfigure(i, weight=(1 if i == 1 else 0))
            except Exception:
                pass

        ttk.Label(pal_group, text="Palette:").grid(row=0, column=0, sticky="w", padx=(8, 6), pady=8)
        pal_combo = ttk.Combobox(pal_group, textvariable=self.pal_choice, values=tuple(DEFAULT_PALETTE_OPTIONS), state="readonly", width=28)
        pal_combo.grid(row=0, column=1, sticky="ew", padx=(0, 6), pady=8)

        # New palette name + create/import moved below selector
        ttk.Label(pal_group, text="New name:").grid(row=1, column=0, sticky="w", padx=(8, 6), pady=(0, 8))
        new_pal_entry = ttk.Entry(pal_group, width=24)
        new_pal_entry.grid(row=1, column=1, sticky="ew", padx=(0, 6), pady=(0, 8))
        
        def rebuild_palette_menu():
            try:
                pal_combo["values"] = tuple(DEFAULT_PALETTE_OPTIONS)
            except Exception:
                pass

        def create_palette():
            name = new_pal_entry.get().strip()
            if not name:
                messagebox.showwarning("Invalid name", "Please enter a palette name.", parent=dlg)
                return
            exists = (name in pallettes) or (name in DEFAULT_PALETTE_OPTIONS)
            if exists:
                res = messagebox.askyesno("Overwrite palette?", f"A palette named '{name}' already exists. Overwrite it?", parent=dlg)
                if not res:
                    return
                # Overwrite: ensure palettes dict has an empty list ready, and menu contains a single entry
                pallettes[name] = []
                if name not in DEFAULT_PALETTE_OPTIONS:
                    DEFAULT_PALETTE_OPTIONS.append(name)
            else:
                pallettes[name] = []
                DEFAULT_PALETTE_OPTIONS.append(name)
            rebuild_palette_menu()
            self.pal_choice.set(name)
            refresh_colors()
            try:
                save_palettes(); save_config()
            except Exception:
                pass

        def import_palette():
            path = filedialog.askopenfilename(parent=dlg, title="Import palette file",
                                              filetypes=[("Palette files", "*.json;*.txt;*.csv"), ("All files", "*.*")])
            if not path:
                return
            cols = _parse_palette_file(path)
            if not cols:
                messagebox.showerror("Import failed", "Failed to parse the selected palette file.", parent=dlg)
                return
            base = os.path.splitext(os.path.basename(path))[0]
            name = base.replace('_', ' ')
            if name in pallettes or name in DEFAULT_PALETTE_OPTIONS:
                res = messagebox.askyesno("Overwrite palette?", f"A palette named '{name}' already exists. Overwrite it?", parent=dlg)
                if not res:
                    # keep old behavior: select a unique name by suffixing
                    i = 1
                    newname = f"{name} {i}"
                    while newname in pallettes or newname in DEFAULT_PALETTE_OPTIONS:
                        i += 1
                        newname = f"{name} {i}"
                    name = newname
            pallettes[name] = cols
            try:
                pallettes[name] = _sort_palette_colors(pallettes[name])
            except Exception:
                pass
            if name not in DEFAULT_PALETTE_OPTIONS:
                DEFAULT_PALETTE_OPTIONS.append(name)
            rebuild_palette_menu()
            try:
                save_palettes(); save_config()
            except Exception:
                pass
            self.pal_choice.set(name)
            refresh_colors()
            messagebox.showinfo("Imported", f"Palette imported as: {name}", parent=dlg)

        ttk.Button(pal_group, text="Create", command=create_palette).grid(row=1, column=2, padx=(0, 6), pady=(0, 8))
        ttk.Button(pal_group, text="Import...", command=import_palette).grid(row=1, column=3, padx=(0, 8), pady=(0, 8))

        # =========== Colors group ===========
        colors_group = ttk.LabelFrame(root, text="Colors")
        colors_group.grid(row=1, column=0, sticky="w", padx=0, pady=(0, 8))
        try:
            # prevent expansion so the box sizes to content
            colors_group.columnconfigure(0, weight=0)
        except Exception:
            pass

        # Header with sort controls
        colors_header = ttk.Frame(colors_group)
        # Span only the tree (col 0) and its scrollbar (col 1) so buttons align over the color box
        colors_header.grid(row=0, column=0, columnspan=2, sticky="ew")
        try:
            # Label column expands, sort buttons column stays tight to the right edge of the list area
            colors_header.columnconfigure(0, weight=1)
            colors_header.columnconfigure(1, weight=0)
        except Exception:
            pass
        # Show color count inline without changing layout
        list_label_var = tk.StringVar(value="List:")
        ttk.Label(colors_header, textvariable=list_label_var).grid(row=0, column=0, sticky="w", padx=(8, 6), pady=(8, 4))

        # Sort handlers
        def sort_luma():
            name = self.pal_choice.get()
            try:
                pallettes[name] = _sort_palette_colors(pallettes.get(name, []))
                refresh_colors()
                save_palettes()
            except Exception:
                pass

        def sort_hsv():
            name = self.pal_choice.get()
            try:
                pallettes[name] = _sort_palette_colors_hsv(pallettes.get(name, []))
                refresh_colors()
                save_palettes()
            except Exception:
                pass

        # Right-align the sort buttons so they sit just above the color list (tree + scrollbar)
        mid = ttk.Frame(colors_header)
        mid.grid(row=0, column=1, sticky="e", pady=(8, 4), padx=(0, 8))
        ttk.Button(mid, text="Sort Luma", command=sort_luma).pack(side="left", padx=(0, 6))
        ttk.Button(mid, text="Sort Hue", command=sort_hsv).pack(side="left")

        # treeview with scrollbar (row 1)
        image_cache = {}  # keep PhotoImage references
        tree = ttk.Treeview(colors_group, columns=("hex",), show='tree', height=6)
        tree.column('#0', width=160)
        tree.grid(row=1, column=0, sticky="nw", padx=(8, 0), pady=(0, 8))
        vsb = ttk.Scrollbar(colors_group, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        vsb.grid(row=1, column=1, sticky="ns", padx=(0, 8), pady=(0, 8))

        # Right-side vertical button stack: Add, Remove, Move Up/Down, Edit
        right_btns = ttk.Frame(colors_group)
        right_btns.grid(row=1, column=2, sticky="n", padx=(0, 8), pady=(0, 8))

        def open_hex_color_dialog(initial_hex=None, on_update_index=None):
            cd = tk.Toplevel(dlg)
            cd.title("Pick color")
            cd.resizable(False, False)
            self._open_dialogs.append(cd)
            try:
                cd.transient(dlg)
                cd.grab_set()
                cd.focus_force()
                cd.after(0, lambda: self._center_over(dlg, cd))
            except Exception:
                pass

            def _close_cd():
                try:
                    cd.grab_release(); cd.destroy(); self._open_dialogs.remove(cd)
                except Exception:
                    pass

            cd.protocol("WM_DELETE_WINDOW", _close_cd)

            ttk.Label(cd, text="Hex (#RRGGBB):").grid(row=0, column=0, padx=8, pady=8)
            hex_var = tk.StringVar(value=(initial_hex or "#ffffff"))
            hex_entry = ttk.Entry(cd, textvariable=hex_var, width=12)
            hex_entry.grid(row=0, column=1, padx=8, pady=8)

            preview = tk.Label(cd, text="    ", bg=hex_var.get(), relief="sunken")
            preview.grid(row=0, column=2, padx=8, pady=8)

            validity_lbl = ttk.Label(cd, text="", foreground="red")
            validity_lbl.grid(row=1, column=0, columnspan=3)

            def pick_colorchooser():
                res = colorchooser.askcolor(parent=cd, title="Choose color")
                if not res:
                    return
                rgb, hx = res
                if hx:
                    hex_var.set(hx)
                    preview.config(bg=hx)
                    validity_lbl.config(text="")

            def on_hex_change(*_):
                h = hex_var.get().strip()
                if not h:
                    validity_lbl.config(text="")
                    return
                if not h.startswith('#'):
                    h = '#' + h
                try:
                    if len(h) == 4:
                        h = '#' + ''.join(ch*2 for ch in h[1:])
                    int(h[1:], 16)
                    preview.config(bg=h)
                    validity_lbl.config(text="")
                except Exception:
                    validity_lbl.config(text="Invalid hex")

            hex_var.trace_add('write', on_hex_change)

            def add_from_dialog():
                name = self.pal_choice.get()
                if name not in pallettes:
                    messagebox.showwarning("No palette", "Select or create a palette to add colors to.", parent=cd)
                    try:
                        cd.lift(); cd.focus_force(); hex_entry.focus_set()
                    except Exception:
                        pass
                    return
                h = hex_var.get().strip()
                if not h.startswith('#'):
                    h = '#' + h
                if len(h) == 4:
                    h = '#' + ''.join(ch*2 for ch in h[1:])
                try:
                    v = int(h[1:], 16)
                    r = (v >> 16) & 0xFF
                    g = (v >> 8) & 0xFF
                    b = v & 0xFF
                except Exception:
                    messagebox.showerror("Invalid hex", "Enter a valid hex color like #ffa07a", parent=cd)
                    try:
                        cd.lift(); cd.focus_force(); hex_entry.focus_set()
                    except Exception:
                        pass
                    return
                rgb = (r, g, b)
                # duplicate check
                if rgb in pallettes[name]:
                    messagebox.showinfo("Duplicate", "This color already exists in the palette.", parent=cd)
                    try:
                        cd.lift(); cd.focus_force(); hex_entry.focus_set()
                    except Exception:
                        pass
                    return
                if on_update_index is not None:
                    pallettes[name][on_update_index] = rgb
                else:
                    pallettes[name].append(rgb)
                refresh_colors()
                save_palettes()
                _close_cd()

            bar = ttk.Frame(cd)
            bar.grid(row=2, column=0, columnspan=3, pady=(0,8))
            ttk.Button(bar, text="Pick...", command=pick_colorchooser).pack(side="left", padx=6)
            ttk.Button(bar, text="Add", command=add_from_dialog).pack(side="left", padx=6)
            ttk.Button(bar, text="Cancel", command=_close_cd).pack(side="left", padx=6)

            def _on_return_cd(event):
                add_from_dialog()
                return "break"
            cd.bind("<Return>", _on_return_cd)
            hex_entry.focus_set()

        def add_color():
            open_hex_color_dialog()

        def remove_color():
            name = self.pal_choice.get()
            sel = tree.selection()
            if not sel:
                messagebox.showwarning("No selection", "Select a color to remove.", parent=dlg)
                return
            iid = sel[0]
            idx = tree.index(iid)
            try:
                pallettes[name].pop(idx)
                refresh_colors()
                save_palettes()
            except Exception:
                pass

        def edit_color():
            name = self.pal_choice.get()
            sel = tree.selection()
            if not sel:
                messagebox.showwarning("No selection", "Select a color to edit.", parent=dlg)
                return
            iid = sel[0]
            idx = tree.index(iid)
            hexval = '#{:02x}{:02x}{:02x}'.format(*pallettes[name][idx])
            open_hex_color_dialog(initial_hex=hexval, on_update_index=idx)

        # Treeview UX shortcuts and context menu
        try:
            tree.bind("<Double-1>", lambda e: (edit_color(), "break"))
            tree.bind("<Delete>", lambda e: (remove_color(), "break"))
        except Exception:
            pass
        # Reorder with Ctrl+Up/Down
        def _bind_move_shortcuts():
            try:
                tree.bind("<Control-Up>", lambda e: (move_up(), "break"))
                tree.bind("<Control-Down>", lambda e: (move_down(), "break"))
            except Exception:
                pass
        _bind_move_shortcuts()
        # Copy selected HEX to clipboard
        def copy_selected_hex():
            try:
                sel = tree.selection()
                if not sel:
                    return
                idx = tree.index(sel[0])
                name = self.pal_choice.get()
                hx = '#{:02x}{:02x}{:02x}'.format(*pallettes.get(name, [])[idx])
                self.clipboard_clear(); self.clipboard_append(hx)
            except Exception:
                pass
        try:
            tree.bind("<Control-c>", lambda e: (copy_selected_hex(), "break"))
        except Exception:
            pass
        # Context menu
        try:
            menu = tk.Menu(tree, tearoff=0)
            menu.add_command(label="Add Color", command=add_color)
            menu.add_command(label="Edit Color", command=edit_color)
            menu.add_command(label="Remove Color", command=remove_color)
            menu.add_separator()
            menu.add_command(label="Move Up", command=lambda: move_up())
            menu.add_command(label="Move Down", command=lambda: move_down())
            menu.add_separator()
            menu.add_command(label="Sort Luma", command=sort_luma)
            menu.add_command(label="Sort Hue", command=sort_hsv)
            def _popup(evt):
                try:
                    row = tree.identify_row(evt.y)
                    if row:
                        tree.focus(row); tree.selection_set(row)
                    menu.tk_popup(evt.x_root, evt.y_root)
                finally:
                    try:
                        menu.grab_release()
                    except Exception:
                        pass
            tree.bind("<Button-3>", _popup)
        except Exception:
            pass

        ttk.Button(right_btns, text="Add Color", command=add_color).pack(side="top", fill="x")
        ttk.Button(right_btns, text="Remove Color", command=remove_color).pack(side="top", fill="x", pady=(4, 0))
        ttk.Separator(right_btns, orient="horizontal").pack(fill="x", pady=6)

        def move_up():
            name = self.pal_choice.get()
            sel = tree.selection()
            if not sel:
                return
            iid = sel[0]
            idx = tree.index(iid)
            if idx <= 0:
                return
            lst = pallettes.get(name, [])
            try:
                lst[idx-1], lst[idx] = lst[idx], lst[idx-1]
                refresh_colors()
                try:
                    tgt = tree.get_children()[idx-1]
                    tree.selection_set(tgt)
                    tree.see(tgt)
                except Exception:
                    pass
                save_palettes()
            except Exception:
                pass

        def move_down():
            name = self.pal_choice.get()
            sel = tree.selection()
            if not sel:
                return
            iid = sel[0]
            idx = tree.index(iid)
            lst = pallettes.get(name, [])
            if idx >= len(lst) - 1:
                return
            try:
                lst[idx+1], lst[idx] = lst[idx], lst[idx+1]
                refresh_colors()
                try:
                    tgt = tree.get_children()[idx+1]
                    tree.selection_set(tgt)
                    tree.see(tgt)
                except Exception:
                    pass
                save_palettes()
            except Exception:
                pass

        ttk.Button(right_btns, text="Move Up", command=move_up).pack(side="top", fill="x")
        ttk.Button(right_btns, text="Move Down", command=move_down).pack(side="top", fill="x", pady=(4, 0))
        ttk.Separator(right_btns, orient="horizontal").pack(fill="x", pady=6)
        ttk.Button(right_btns, text="Edit Color", command=edit_color).pack(side="top", fill="x")

        def make_swatch(hexcol):
            if hexcol in image_cache:
                return image_cache[hexcol]
            try:
                img = tk.PhotoImage(width=16, height=12)
                img.put(hexcol, to=(0,0,16,12))
                image_cache[hexcol] = img
                return img
            except Exception:
                return None

        def refresh_colors():
            # preserve current selection index
            try:
                sel = tree.selection()
                sel_idx = tree.index(sel[0]) if sel else None
            except Exception:
                sel_idx = None
            # clear and repopulate
            try:
                for iid in tree.get_children():
                    tree.delete(iid)
            except Exception:
                pass
            name = self.pal_choice.get()
            vals = pallettes.get(name, [])
            for col in vals:
                try:
                    hx = '#{:02x}{:02x}{:02x}'.format(*col)
                    img = make_swatch(hx)
                    tree.insert('', 'end', text=hx, image=img)
                except Exception:
                    pass
            # adjust visible rows to content (+1 buffer), min 3, max 12
            try:
                count = len(vals)
                list_label_var.set(f"List: ({count})")
                desired = min(max(count + 1, 3), 12)
                tree.configure(height=desired)
            except Exception:
                pass
            # restore selection if possible
            try:
                if sel_idx is not None and tree.get_children():
                    sel_idx = min(sel_idx, len(tree.get_children()) - 1)
                    tgt = tree.get_children()[sel_idx]
                    tree.selection_set(tgt)
                    tree.see(tgt)
            except Exception:
                pass

        # Toolbar under the list (row 2)
        btnbar = ttk.Frame(colors_group)
        btnbar.grid(row=2, column=0, columnspan=3, sticky="w", padx=8, pady=(0, 8))

        # =========== Simplify settings group ===========
        simplify_group = ttk.LabelFrame(root, text="Simplify settings")
        simplify_group.grid(row=2, column=0, sticky="ew", padx=0, pady=(0, 8))
        ttk.Label(simplify_group, text="Similarity threshold (%):").grid(row=0, column=0, sticky="w", padx=(8, 6), pady=8)
        tk.Spinbox(simplify_group, from_=0, to=100, textvariable=self.similarity_threshold_var, width=6).grid(row=0, column=1, sticky="w", padx=(0, 8), pady=8)

        # Apply threshold changes immediately to keep runs in sync
        def _on_thresh_changed(*_):
            global similarity_threshold
            try:
                similarity_threshold = int(self.similarity_threshold_var.get())
                save_config()
            except Exception:
                pass
        try:
            self.similarity_threshold_var.trace_add('write', _on_thresh_changed)
        except Exception:
            pass

        # Toggle groups based on selection (keep color list always visible)
        def on_palette_change(value):
            is_simple = (value == "Simplify Pallette")
            if is_simple:
                simplify_group.grid()
            else:
                simplify_group.grid_remove()
            colors_group.grid()
            refresh_colors()

        pal_combo.bind('<<ComboboxSelected>>', lambda e: on_palette_change(self.pal_choice.get()))

        # Save/export current palette helper and actions
        def save_current_palette():
            name = self.pal_choice.get()
            if not name or name not in pallettes:
                messagebox.showwarning("No palette", "Select or create a palette to save.", parent=dlg)
                return
            try:
                os.makedirs(_PALETTES_DIR, exist_ok=True)
            except Exception:
                pass
            suggested = _slugify(name) + '.json'
            path = filedialog.asksaveasfilename(parent=dlg, title="Save palette as",
                                                initialdir=_PALETTES_DIR,
                                                initialfile=suggested,
                                                defaultextension='.json',
                                                filetypes=[('JSON', '*.json'), ('All files', '*.*')])
            if not path:
                return
            try:
                data = ['#{:02x}{:02x}{:02x}'.format(*c) for c in pallettes[name]]
                with open(path, 'w', encoding='utf-8') as f:
                    json.dump(data, f, indent=2)
                try:
                    save_palettes(); save_config()
                except Exception:
                    pass
                messagebox.showinfo("Saved", f"Palette saved to:\n{path}", parent=dlg)
            except Exception as ex:
                messagebox.showerror("Save failed", f"Failed to save palette:\n{ex}", parent=dlg)

        def apply_and_close():
            # Threshold already syncs via trace; still persist
            try:
                save_palettes(); save_config()
            except Exception:
                pass
            _close_and_remove()

        actions = ttk.Frame(root)
        actions.grid(row=3, column=0, sticky="e", pady=(0, 0))
        ttk.Button(actions, text="Save", command=save_current_palette).pack(side="right")
        ttk.Button(actions, text="Close", command=_close_and_remove).pack(side="right", padx=(6, 0))
        ttk.Button(actions, text="Apply and Close", command=apply_and_close).pack(side="right", padx=(6, 0))

        # Dialog-level shortcuts
        try:
            dlg.bind("<Control-s>", lambda e: (save_current_palette(), "break"))
            dlg.bind("<Control-Return>", lambda e: (apply_and_close(), "break"))
            dlg.bind("<Control-w>", lambda e: (_close_and_remove(), "break"))
            dlg.bind("<Escape>", lambda e: (_close_and_remove(), "break"))
        except Exception:
            pass

        # initialize list
        refresh_colors()
        on_palette_change(self.pal_choice.get())

    def _on_return_main(self, event):
        # Trigger Run only when no dialogs are open (active window is main)
        if self._open_dialogs:
            return
        try:
            if str(self.run_btn['state']) == 'normal':
                self.start_analyze_thread()
        except Exception:
            pass
        return "break"

    def _on_palette_select(self, value):
        # Keep selection available for later processing
        print(f"Palette selected: {value}")

    def open_image(self):
        self.converted_image = None
        self.scale_orig = 1.0
        self.scale_conv = 1.0
        self._init_view_done_orig = False
        self._init_view_done_conv = False
        path = filedialog.askopenfilename(
            title="Select image",
            filetypes=[("Image files", ("*.png", "*.jpg", "*.jpeg", "*.bmp", "*.gif", "*.tiff")), ("All files", "*.*")]
        )
        if not path:
            return

        try:
            img = Image.open(path).convert("RGB")
        except Exception as ex:
            messagebox.showerror("Error", f"Unable to open image:\n{ex}")
            return

        self.file_path = path
        self.save_path = path
        self.original_image = img
        self.path_label.config(text=os.path.abspath(path))
        self._render_image()

    def save_image(self):
        """Save the current converted image (if exists) or original to the current save_path.
        If no save_path is known, delegate to Save As."""


        if self.converted_image is not None:
            img = self.converted_image
        else:
            img = self.original_image

        if img is None:
            messagebox.showwarning("No image", "No image to save.")
            return

        if not self.save_path:
            return self.save_image_as()

        try:
            img.save(self.save_path)
            messagebox.showinfo("Saved", f"Image saved to:\n{self.save_path}")
        except Exception as ex:
            messagebox.showerror("Save error", f"Failed to save image:\n{ex}")

    def save_image_as(self):
        """Ask user for file path and save image there."""
        if self.converted_image is not None:
            img = self.converted_image
        else:
            img = self.original_image

        if img is None:
            messagebox.showwarning("No image", "No image to save.")
            return

        path = filedialog.asksaveasfilename(
            title="Save image as",
            defaultextension=".png",
            filetypes=[("PNG", "*.png"), ("JPEG", "*.jpg;*.jpeg"), ("BMP", "*.bmp"), ("All files", "*.*")]
        )
        if not path:
            return

        try:
            img.save(path)
            self.save_path = path
            messagebox.showinfo("Saved", f"Image saved to:\n{path}")
        except Exception as ex:
            messagebox.showerror("Save error", f"Failed to save image:\n{ex}")

    def _render_image(self):
        # Render original image on left (origin at 0,0; use scrollregion for panning)
        if self.original_image:
            canvas = self.canvas_orig
            cw = max(canvas.winfo_width(), 1)
            ch = max(canvas.winfo_height(), 1)
            iw, ih = self.original_image.size
            base = min(1.0, cw / iw, ch / ih)
            eff = base * max(0.01, float(self.scale_orig))
            new_size = (max(1, int(iw * eff)), max(1, int(ih * eff)))
            rendered = self.original_image if eff == 1.0 else self.original_image.resize(new_size, Image.LANCZOS)
            self._img_tk_orig = ImageTk.PhotoImage(rendered)
            canvas.delete("IMG")
            canvas.create_image(0, 0, image=self._img_tk_orig, anchor="nw", tags="IMG")
            canvas.config(scrollregion=(0, 0, rendered.width, rendered.height))
            if not self._init_view_done_orig:
                try:
                    if rendered.width > cw:
                        canvas.xview_moveto((rendered.width - cw) / rendered.width / 2)
                    if rendered.height > ch:
                        canvas.yview_moveto((rendered.height - ch) / rendered.height / 2)
                except Exception:
                    pass
                self._init_view_done_orig = True
        # Render right image (converted or original based on toggle)
        img_right = None
        if self.converted_image and self.show_after_on_right:
            img_right = self.converted_image
        elif self.original_image and not self.show_after_on_right:
            img_right = self.original_image
        if img_right:
            canvas = self.canvas_conv
            cw = max(canvas.winfo_width(), 1)
            ch = max(canvas.winfo_height(), 1)
            iw, ih = img_right.size
            base = min(1.0, cw / iw, ch / ih)
            eff = base * max(0.01, float(self.scale_conv))
            new_size = (max(1, int(iw * eff)), max(1, int(ih * eff)))
            rendered = img_right if eff == 1.0 else img_right.resize(new_size, Image.LANCZOS)
            self._img_tk_conv = ImageTk.PhotoImage(rendered)
            canvas.delete("IMG")
            canvas.create_image(0, 0, image=self._img_tk_conv, anchor="nw", tags="IMG")
            canvas.config(scrollregion=(0, 0, rendered.width, rendered.height))
            if not self._init_view_done_conv:
                try:
                    if rendered.width > cw:
                        canvas.xview_moveto((rendered.width - cw) / rendered.width / 2)
                    if rendered.height > ch:
                        canvas.yview_moveto((rendered.height - ch) / rendered.height / 2)
                except Exception:
                    pass
                self._init_view_done_conv = True
        else:
            # Clear right canvas if no image
            self.canvas_conv.delete("IMG")
            self.canvas_conv.config(scrollregion=(0, 0, 0, 0))

    def get_pallette(self):
        return self.pal_choice.get()

    def _poll_progress(self):
        """Poll the module-level progress variable and update the UI."""
        global progress, processed_pixels, total_pixels
        with _progress_lock:
            val = float(progress)
            proc = int(processed_pixels)
            tot = int(total_pixels)
        # clamp and set
        if val < 0.0:
            val = 0.0
        if val > 100.0:
            val = 100.0
        self.progress_var.set(val)
        self._progress_label.config(text=f"{int(val)}%")
        if tot > 0:
            self.status_prog.config(text=f"{proc:,}/{tot:,} px")
        else:
            self.status_prog.config(text="")
        # schedule next poll (100ms)
        self.after(100, self._poll_progress)

    def update_progress(self, value: float):
        """Update progress immediately from main thread."""
        self.progress_var.set(max(0.0, min(100.0, float(value))))
        self._progress_label.config(text=f"{int(self.progress_var.get())}%")

    def start_analyze_thread(self):
        """Start image analysis on a background thread to keep UI responsive."""
        if getattr(self, "_analyzing", False):
            return
        if self.original_image is None:
            messagebox.showwarning("No image", "Please open an image first.")
            return
        self._analyzing = True
        self.run_btn.configure(state="disabled")
        self.cancel_btn.configure(state="normal")
        if getattr(self, "open_btn", None):
            try:
                self.open_btn.configure(state="disabled")
            except Exception:
                pass
        # reset progress
        set_progress(0.0)
        with _progress_lock:
            global processed_pixels, total_pixels
            processed_pixels = 0
            total_pixels = (self.original_image.size[0] * self.original_image.size[1])
        try:
            _cancel_event.clear()
        except Exception:
            pass
        t = threading.Thread(target=analyze_image_worker, daemon=True)
        t.start()

    def analyze_canceled(self):
        # Reset UI after cancel
        self._analyzing = False
        try:
            self.run_btn.configure(state="normal")
            self.cancel_btn.configure(state="disabled")
        except Exception:
            pass
        if getattr(self, "open_btn", None):
            try:
                self.open_btn.configure(state="normal")
            except Exception:
                pass

    def analyze_done(self, new_image):
        """Called on main thread when worker finishes."""


        # If Simplify Pallette was selected, ask whether to save the collected colors as a new palette
        try:
            if new_image is not None and self.get_pallette() == "Simplify Pallette" and saved_colors:
                # derive a base name from the image file name if available
                try:
                    base = os.path.splitext(os.path.basename(self.file_path or ""))[0] or "Image"
                except Exception:
                    base = "Image"
                pal_name = f"{base} (simplified)"
                # ensure a suggested unique name (do not create yet)
                i = 1
                suggested_name = pal_name
                while suggested_name in pallettes or suggested_name in DEFAULT_PALETTE_OPTIONS:
                    i += 1
                    suggested_name = f"{pal_name} {i}"

                # Prompt dialog to let the user choose the palette name and Save/Cancel
                dlg = tk.Toplevel(self)
                dlg.title("Palette Optimizer - Save Simplified Palette")
                dlg.resizable(False, False)
                self._open_dialogs.append(dlg)
                try:
                    dlg.transient(self)
                    dlg.grab_set()
                    dlg.focus_force()
                    dlg.after(0, lambda: self._center_over(self, dlg))
                except Exception:
                    pass

                def _close_prompt():
                    try:
                        dlg.grab_release()
                    except Exception:
                        pass
                    try:
                        dlg.destroy()
                    except Exception:
                        pass
                    try:
                        self._open_dialogs.remove(dlg)
                    except ValueError:
                        pass

                dlg.protocol("WM_DELETE_WINDOW", _close_prompt)

                tk.Label(dlg, text="Palette name:").grid(row=0, column=0, padx=10, pady=10, sticky="w")
                name_var = tk.StringVar(value=suggested_name)
                name_entry = tk.Entry(dlg, textvariable=name_var, width=32)
                name_entry.grid(row=0, column=1, padx=(0,10), pady=10)

                btns = tk.Frame(dlg)
                btns.grid(row=1, column=0, columnspan=2, pady=(0,10))

                def _do_save():
                    name = name_var.get().strip()
                    if not name:
                        messagebox.showwarning("Invalid name", "Please enter a palette name.", parent=dlg)
                        try:
                            dlg.lift(); dlg.focus_force(); name_entry.focus_set()
                        except Exception:
                            pass
                        return
                    if name in pallettes or name in DEFAULT_PALETTE_OPTIONS:
                        res = messagebox.askyesno("Overwrite palette?", f"A palette named '{name}' already exists. Overwrite it?", parent=dlg)
                        if not res:
                            try:
                                name_entry.select_range(0, 'end'); name_entry.focus_set()
                            except Exception:
                                pass
                            return
                    # Save/overwrite palette under chosen name
                    pallettes[name] = [tuple(int(c) for c in col) for col in saved_colors]
                    if name not in DEFAULT_PALETTE_OPTIONS:
                        DEFAULT_PALETTE_OPTIONS.append(name)
                    try:
                        self.pal_choice.set(name)
                    except Exception:
                        pass
                    try:
                        save_palettes(); save_config()
                    except Exception:
                        pass
                    try:
                        messagebox.showinfo("Palette saved", f"Saved simplified palette as: {name}", parent=self)
                    except Exception:
                        pass
                    _close_prompt()

                tk.Button(btns, text="Save", command=_do_save).pack(side="left", padx=6)
                tk.Button(btns, text="Cancel", command=_close_prompt).pack(side="left", padx=6)

                # Enter -> Save in this prompt only
                def _on_return_prompt(event):
                    _do_save()
                    return "break"
                dlg.bind("<Return>", _on_return_prompt)
                try:
                    name_entry.focus_set()
                except Exception:
                    pass
        except Exception:
            # don't let saving interfere with rendering; log silently
            try:
                tb = traceback.format_exc()
                log_path = os.path.join(BASE_DIR, "palette_optimizer_error.log")
                with open(log_path, "a", encoding="utf-8") as f:
                    f.write(f"\n\nException showing save simplified palette prompt:\n{tb}\n")
            except Exception:
                pass

        if new_image is not None:
            self.converted_image = new_image
            try:
                self._render_image()
            except Exception:
                tb = traceback.format_exc()
                messagebox.showerror("Render error", f"Failed to render image:\n{tb}")
        self._analyzing = False
        self.run_btn.configure(state="normal")
        self.cancel_btn.configure(state="disabled")
        if getattr(self, "open_btn", None):
            try:
                self.open_btn.configure(state="normal")
            except Exception:
                pass
        set_progress(100.0)


def color_distance_sq(rgb1, rgb2):
    """Return squared Euclidean distance between two RGB colors (avoids sqrt)."""
    r1, g1, b1 = rgb1
    r2, g2, b2 = rgb2
    return (r1 - r2) ** 2 + (g1 - g2) ** 2 + (b1 - b2) ** 2


def analyze_image_worker():
    """Background worker that performs analysis and calls set_progress().
       At the end it schedules update on the main thread via app.after(...).
       All exceptions are caught and reported to the user on the main thread.
    """
    try:
        # Basic validation
        if app is None or app.original_image is None:
            raise RuntimeError("No application instance or no image loaded in app.")

        # Work on a copy so GUI image isn't modified mid-render
        new_image = app.original_image.copy()
        # PIL size is (width, height)
        width, height = new_image.size

        saved_colors.clear()
        set_progress(0.0)
        with _progress_lock:
            global total_pixels, processed_pixels
            total_pixels = width * height
            processed_pixels = 0

        # Precompute allowed squared distance for similarity threshold check
        allowed_distance = (1.0 - (similarity_threshold / 100.0)) * max_distance
        allowed_sq = allowed_distance * allowed_distance

        # Use a cache to avoid recomputing nearest color for the same input color
        nearest_cache = {}

        # Fast pixel access
        px = new_image.load()
        rng = random.Random(time.time_ns())
        canceled = False
        
        if app.get_pallette() == "Simplify Pallette":
            total = width * height
            processed = 0
            tile = 300

            for y0 in range(0, height, tile):
                if _cancel_event.is_set():
                    canceled = True
                    break
                y1 = min(y0 + tile, height)
                for x0 in range(0, width, tile):
                    if _cancel_event.is_set():
                        canceled = True
                        break
                    x1 = min(x0 + tile, width)

                    # Build random order of all pixels inside this tile
                    coords = [(x, y) for y in range(y0, y1) for x in range(x0, x1)]
                    rng.shuffle(coords)

                    for (x, y) in coords:
                        if _cancel_event.is_set():
                            canceled = True
                            break
                        pixel_color = px[x, y]
                        # ensure tuple
                        if not isinstance(pixel_color, tuple):
                            pixel_color = tuple(pixel_color)

                        if pixel_color not in saved_colors:
                            if saved_colors:
                                nearest = nearest_cache.get(pixel_color)
                                if nearest is None:
                                    # find nearest saved color by squared distance
                                    best = saved_colors[0]
                                    best_dist = color_distance_sq(pixel_color, best)
                                    for color in saved_colors[1:]:
                                        d = color_distance_sq(pixel_color, color)
                                        if d < best_dist:
                                            best = color
                                            best_dist = d
                                    nearest = best
                                    nearest_cache[pixel_color] = nearest

                                # If nearest is too far, add this pixel color as a new saved color
                                if color_distance_sq(nearest, pixel_color) > allowed_sq:
                                    saved_colors.append(pixel_color)
                                    # remove from cache to avoid stale mapping
                                    nearest_cache.pop(pixel_color, None)
                                else:
                                    # replace pixel with nearest saved color
                                    px[x, y] = nearest
                            else:
                                saved_colors.append(pixel_color)

                        processed += 1
                        if processed % 5000 == 0:
                            set_progress((processed / total) * 100.0)
                            with _progress_lock:
                                processed_pixels = processed
                    if canceled:
                        break
                if canceled:
                    break
        else:
            pallette = pallettes.get(app.get_pallette(), [])
            total = width * height if pallette else 1
            processed = 0
            for y in range(height):
                if _cancel_event.is_set():
                    canceled = True
                    break
                for x in range(width):
                    if _cancel_event.is_set():
                        canceled = True
                        break
                    pixel_color = px[x, y]
                    if not isinstance(pixel_color, tuple):
                        pixel_color = tuple(pixel_color)
                    if pallette:
                        nearest = nearest_cache.get(pixel_color)
                        if nearest is None:
                            best = pallette[0]
                            best_dist = color_distance_sq(pixel_color, best)
                            for color in pallette[1:]:
                                d = color_distance_sq(pixel_color, color)
                                if d < best_dist:
                                    best = color
                                    best_dist = d
                            nearest = best
                            nearest_cache[pixel_color] = nearest
                        px[x, y] = nearest
                    processed += 1
                    if processed % 5000 == 0:
                        set_progress((processed / total) * 100.0)
                        with _progress_lock:
                            processed_pixels = processed
                if canceled:
                    break

        if canceled:
            # Reset progress details but keep current progress value
            try:
                app.after(0, app.analyze_canceled)
            except Exception:
                pass
            return

        # final update and render on main thread
        set_progress(100.0)
        with _progress_lock:
            processed_pixels = total_pixels
        try:
            app.after(0, lambda: app.analyze_done(new_image))
        except Exception:
            raise
    except Exception as ex:
        tb = traceback.format_exc()
        try:
            log_path = os.path.join(BASE_DIR, "palette_optimizer_error.log")
            with open(log_path, "a", encoding="utf-8") as f:
                f.write(f"\n\nException in analyze_image_worker:\n{tb}\n")
        except Exception:
            pass

        def _report():
            messagebox.showerror("Processing error", f"{ex}\n\nSee log for details.")
            try:
                app.analyze_done(None)
            except Exception:
                try:
                    app._analyzing = False
                    app.run_btn.configure(state="normal")
                    app.cancel_btn.configure(state="disabled")
                    if getattr(app, "open_btn", None):
                        try:
                            app.open_btn.configure(state="normal")
                        except Exception:
                            pass
                except Exception:
                    pass

        try:
            app.after(0, _report)
        except Exception:
            print(tb, file=sys.stderr)
            try:
                app._analyzing = False
                app.run_btn.configure(state="normal")
                app.cancel_btn.configure(state="disabled")
                if getattr(app, "open_btn", None):
                    try:
                        app.open_btn.configure(state="normal")
                    except Exception:
                        pass
            except Exception:
                pass


def set_progress(value: float):
    """Thread-safe API other code can call to update the progress variable."""
    global progress
    with _progress_lock:
        progress = max(0.0, min(100.0, float(value)))
    # do NOT call Tk API from worker threads; GUI polls and will reflect the change


def color_similarity(rgb1, rgb2):
    """Return similarity percentage between two RGB colors."""
    r1, g1, b1 = rgb1
    r2, g2, b2 = rgb2

    # Euclidean distance between two colors
    distance = math.sqrt((r1 - r2)**2 + (g1 - g2)**2 + (b1 - b2)**2)

    # Convert distance to similarity percentage
    similarity = (1 - (distance / max_distance)) * 100
    return round(similarity, 2)


# create app instance
app = ImageViewer()


if __name__ == "__main__":
    app.mainloop()