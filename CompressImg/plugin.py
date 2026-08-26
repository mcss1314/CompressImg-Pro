#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import sys
import math
import time
import queue
import traceback
import json
import re
import posixpath
import tempfile
import atexit
from io import BytesIO
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from collections import deque
from urllib.parse import unquote, quote

_PLUGIN_DIR = Path(__file__).resolve().parent
_VENDOR_DIR = _PLUGIN_DIR / "vendor"
MAX_PIXELS = 100_000_000  # 100 Megapixels 上限阈值

def setup_environment():
    """初始化运行环境与 vendor 依赖包路径"""
    if not _VENDOR_DIR.exists():
        _VENDOR_DIR.mkdir(parents=True, exist_ok=True)
        
    vendor_path = str(_VENDOR_DIR)
    if vendor_path not in sys.path:
        sys.path.insert(0, vendor_path)
            
    if sys.platform == 'win32' and hasattr(os, 'add_dll_directory'):
        try:
            os.add_dll_directory(vendor_path)
            for item in _VENDOR_DIR.iterdir():
                if item.is_dir() and (item.name.endswith('.libs') or item.name == 'imagequant'):
                    os.add_dll_directory(str(item))
        except Exception:
            pass

setup_environment()

import tkinter as tk
from tkinter import ttk, messagebox, font as tkfont

# 正则匹配表达式（已加入 \b 单词边界防误匹配 data-src / data-href）
_RE_COVER_META_1 = re.compile(r'<meta\s+[^>]*?name=["\']cover["\']\s+content=["\']([^"\']+)["\']', re.IGNORECASE | re.DOTALL)
_RE_COVER_META_2 = re.compile(r'<meta\s+[^>]*?content=["\']([^"\']+)["\']\s+name=["\']cover["\']', re.IGNORECASE | re.DOTALL)
_RE_IMG_REF = re.compile(
    r'(?:<(?:img|image|source)[^>]*?\b(?:src|xlink:href|href)\s*=\s*[\'"]([^\'"]+)[\'"]|url\(\s*[\'"]?([^\'"]+?)[\'"]?\s*\))',
    re.IGNORECASE | re.DOTALL
)
_RE_SRCSET = re.compile(
    r'srcset\s*=\s*(?:(["\'])(.*?)(?:\1)|([^\s>]+))',
    re.IGNORECASE | re.DOTALL
)
_RE_HTML_IMG = re.compile(
    r'(<(?:img|image|source)[^>]*?\b(?:src|xlink:href|href)\s*=\s*)([\'"])(.*?)([\'"])([^>]*?>)', 
    re.IGNORECASE | re.DOTALL
)
_RE_HTML_SRCSET = re.compile(
    r'(<(?:img|image|source)[^>]*?srcset\s*=\s*)(?:([\'"])(.*?)([\'"])|([^\s>]+))([^>]*?>)',
    re.IGNORECASE | re.DOTALL
)
_RE_CSS_URL = re.compile(r'(\burl\s*\(\s*)([\'"]?)(.*?)([\'"]?\s*\))', re.IGNORECASE | re.DOTALL)
_RE_CSS_IMPORT = re.compile(r'(@import\s+)([\'"])(.*?)([\'"])', re.IGNORECASE | re.DOTALL)
_RE_TAG_BLOCK = re.compile(r'<[a-zA-Z0-9:]+\b[^>]*?>', re.IGNORECASE | re.DOTALL)

IMAGE_EXTENSIONS = ('.png', '.jpg', '.jpeg', '.webp', '.gif', '.bmp', '.svg', '.tif', '.tiff', '.ico')

class _DummyUnidentifiedImageError(Exception):
    pass

try:
    import PIL
    from PIL import Image, ImageTk, UnidentifiedImageError, ImageOps
    Image.MAX_IMAGE_PIXELS = MAX_PIXELS
except ImportError:
    Image = None
    ImageTk = None
    UnidentifiedImageError = _DummyUnidentifiedImageError
    ImageOps = None

HAS_IMAGEQUANT = False
try:
    import imagequant
    if hasattr(imagequant, 'quantize_pil_image'):
        HAS_IMAGEQUANT = True
except Exception:
    HAS_IMAGEQUANT = False

def get_image_mime(filename_or_ext):
    """根据文件扩展名推论 EPUB / W3C 标准 MIME 类型"""
    ext = posixpath.splitext(filename_or_ext)[1].lower().lstrip('.')
    mime_map = {
        'jpg': 'image/jpeg',
        'jpeg': 'image/jpeg',
        'png': 'image/png',
        'webp': 'image/webp',
        'gif': 'image/gif',
        'svg': 'image/svg+xml',
        'bmp': 'image/bmp',
        'tif': 'image/tiff',
        'tiff': 'image/tiff',
        'ico': 'image/x-icon'
    }
    return mime_map.get(ext, 'image/jpeg')

def split_url_suffix(url_str):
    """拆分 URL 路径与 Query / Hash 后缀"""
    q_idx = url_str.find('?')
    h_idx = url_str.find('#')
    
    split_idx = -1
    if q_idx != -1 and h_idx != -1:
        split_idx = min(q_idx, h_idx)
    elif q_idx != -1:
        split_idx = q_idx
    elif h_idx != -1:
        split_idx = h_idx
        
    if split_idx != -1:
        return url_str[:split_idx], url_str[split_idx:]
    return url_str, ""

def canonical_epub_path(href):
    """
    统一 EPUB 容器绝对标准路径归一化。
    彻底清理首部斜杠 /、连续斜杠与路径游标 ../，防止生成 OEBPS/Images/Images/... 等嵌套误判。
    """
    if not href:
        return ""
    clean, _ = split_url_suffix(href)
    unquoted = unquote(clean).replace('\\', '/').strip()
    norm = posixpath.normpath(unquoted).lstrip('/')
    while norm.startswith('../'):
        norm = norm[3:]
    return posixpath.normpath(norm).lstrip('/')

def normalize_epub_path(base_file_href, rel_url):
    """
    统一 EPUB 规范化路径计算。
    支持相对路径与根绝对路径解析，并规约计算出 EPUB 根规范路径。
    """
    if not rel_url:
        return "", ""
        
    clean_url, extra_suffix = split_url_suffix(rel_url)
    unquoted = unquote(clean_url).replace('\\', '/').strip()
    
    if not unquoted or unquoted.startswith(('data:', 'http:', 'https:', 'mailto:', 'javascript:', 'ftp:', '#')):
        return "", ""
        
    if unquoted.startswith('/'):
        norm_path = posixpath.normpath(unquoted.lstrip('/')).lstrip('/')
    elif base_file_href:
        base_dir = posixpath.dirname(canonical_epub_path(base_file_href))
        norm_path = posixpath.normpath(posixpath.join(base_dir, unquoted)).lstrip('/')
    else:
        norm_path = posixpath.normpath(unquoted).lstrip('/')
        
    while norm_path.startswith('../'):
        norm_path = norm_path[3:]
    norm_path = posixpath.normpath(norm_path).lstrip('/')
        
    return norm_path, extra_suffix

def get_relative_epub_path(from_file_href, target_book_path):
    """计算从 from_file_href 所在地到 target_book_path 的 POSIX 相对路径"""
    from_dir = posixpath.dirname(canonical_epub_path(from_file_href))
    target_norm = canonical_epub_path(target_book_path)
    try:
        rel = posixpath.relpath(target_norm, from_dir)
    except Exception:
        rel = target_norm
    return rel.replace('\\', '/')

def safe_decode_text(data):
    """安全解析 XML/SVG/HTML 文本编码，返回 (decoded_text, is_bytes)"""
    if isinstance(data, str):
        return data, False
    if not isinstance(data, bytes):
        return str(data), False
        
    match = re.search(rb'^\s*<\?xml[^>]*encoding=["\']([^"\']+)["\']', data, re.IGNORECASE)
    if match:
        enc = match.group(1).decode('ascii', errors='ignore')
        try:
            return data.decode(enc), True
        except (UnicodeDecodeError, LookupError):
            pass
            
    try:
        return data.decode('utf-8'), True
    except UnicodeDecodeError:
        pass
        
    return data.decode('utf-8', errors='replace'), True

def update_xml_encoding_header(text, new_enc="utf-8"):
    """更新 XML 头部的 encoding 声明为 new_enc，确保物理编码与 XML 头一致"""
    return re.sub(
        r'(^\s*<\?xml[^>]*?\bencoding=["\'])([^"\']+)(["\'])',
        rf'\g<1>{new_enc}\g<3>',
        text,
        count=1,
        flags=re.IGNORECASE
    )

def get_resample_filter(cur_w, cur_h, new_w, new_h):
    """根据缩放比例动态选择重采样滤波器"""
    if Image is None:
        return None

    res_obj = getattr(Image, 'Resampling', Image)
    filter_box = getattr(res_obj, 'BOX', getattr(Image, 'BOX', getattr(Image, 'BILINEAR', 2)))
    filter_bicubic = getattr(res_obj, 'BICUBIC', getattr(Image, 'BICUBIC', 3))
    filter_lanczos = getattr(res_obj, 'LANCZOS', getattr(Image, 'LANCZOS', 1))

    if cur_w <= 0 or cur_h <= 0 or new_w <= 0 or new_h <= 0:
        return filter_lanczos

    scale_ratio = (new_w * new_h) / float(cur_w * cur_h)
    if scale_ratio < 0.25:
        return filter_box
    elif scale_ratio < 0.6:
        return filter_bicubic
    
    return filter_lanczos

def convert_cmyk_to_rgb(img):
    """转换 CMYK 印刷色彩空间为 RGB"""
    if img is None or img.mode != 'CMYK':
        return img

    try:
        from PIL import ImageCms
        if 'icc_profile' in img.info and img.info['icc_profile']:
            in_profile = ImageCms.ImageCmsProfile(BytesIO(img.info['icc_profile']))
            srgb_profile = ImageCms.createProfile('sRGB')
            return ImageCms.profileToProfile(img, in_profile, srgb_profile, outputMode='RGB')
    except Exception:
        pass
    
    try:
        return img.convert('RGB')
    except Exception:
        return img

def should_reencode_image(img_info, opts, img_obj):
    """判定图片是否需要重新编码"""
    orig_fmt = img_obj.format if img_obj.format else img_info['format']
    if orig_fmt.upper() == 'JPG': orig_fmt = 'JPEG'
    
    target_fmt = opts['conv_target'] if opts.get('do_conv') else orig_fmt
    if target_fmt.upper() == 'JPG': target_fmt = 'JPEG'
    
    exif_rot_needed = False
    if hasattr(img_obj, 'getexif'):
        try:
            exif = img_obj.getexif()
            if exif and exif.get(0x0112, 1) not in (1, 0, None):
                exif_rot_needed = True
        except Exception:
            pass

    if img_obj.mode == 'CMYK':
        return True, target_fmt

    rot = img_info.get('rotate', 0)
    if rot != 0 or exif_rot_needed:
        return True, target_fmt
        
    if opts.get('do_conv') and target_fmt != orig_fmt:
        return True, target_fmt
        
    if opts.get('do_scale'):
        stype = opts.get('scale_type')
        cur_w, cur_h = img_obj.size
        if rot % 360 in (90, 270):
            cur_w, cur_h = cur_h, cur_w
            
        if stype == "percent" and opts.get('scale_percent') != 100:
            return True, target_fmt
        elif stype == "width" and opts.get('scale_width') != cur_w:
            return True, target_fmt
        elif stype == "height" and opts.get('scale_height') != cur_h:
            return True, target_fmt

    if opts.get('do_depth') and target_fmt == 'PNG':
        if img_obj.mode != 'P':
            return True, target_fmt

    is_lossless_mode = opts.get('do_lossless') or (opts.get('do_conv') and opts.get('conv_type') == 'lossless')
    if target_fmt == 'JPEG' and is_lossless_mode and orig_fmt == 'JPEG':
        if not opts.get('strip_meta'):
            return False, target_fmt

    if opts.get('do_qlty') or (opts.get('do_conv') and opts.get('conv_type') == 'quality'):
        if target_fmt in ('JPEG', 'WEBP'):
            return True, target_fmt

    if is_lossless_mode:
        return True, target_fmt

    if opts.get('strip_meta'):
        if hasattr(img_obj, 'getexif') and img_obj.getexif():
            return True, target_fmt
        if 'icc_profile' in img_obj.info or 'exif' in img_obj.info:
            return True, target_fmt

    return False, target_fmt

def check_dependencies():
    """检查依赖库 Pillow 是否符合运行条件"""
    errors = []
    try:
        import PIL
        from PIL import Image
        
        def _parse_version(v_str):
            match = re.search(r'^(\d+\.\d+(\.\d+)?)', str(v_str))
            return tuple(map(int, match.group(1).split('.'))) if match else (0, 0, 0)
            
        if hasattr(PIL, '__version__') and _parse_version(PIL.__version__) < (8, 0):
            errors.append(f"Pillow 版本过低 (当前 {PIL.__version__}，需 >= 8.0.0)")
    except Exception as e:
        errors.append(f"Pillow 库未安装或加载异常: {e}")

    if errors:
        return "；".join(errors)
    return None

class CompressApp:
    def __init__(self, root, bk):
        self.root = root
        self.bk = bk
        self.images = []
        self.error_details = []
        self._ui_disabled = False
        self._is_cancelled = False
        self.temp_dir = None
        self.executor = None
        
        self._check_queue_job = None
        self._scroll_job = None
        self._resize_job = None
        
        self._existing_ids = set()
        self._existing_bookpaths = set()
        
        self.prefs = self.load_prefs()
        
        self.root.title("CompressImg-Pro V1.1.3")
        self.root.geometry("1100x800")
        self.root.minsize(1050, 750)
        self.root.eval('tk::PlaceWindow . center')
        
        self.style = ttk.Style()
        if 'clam' in self.style.theme_names():
            self.style.theme_use('clam')
            
        self.os_font = "微软雅黑" if sys.platform == "win32" else "Helvetica Neue"
        
        bg_color = "#f4f6f9"
        self.bg_color = bg_color
        fg_color = "#2c3e50"
        accent_color = "#3498db"
        accent_active = "#2980b9"
        
        self.panel_states = self.prefs.get('panel_states', {})
        self.root.configure(background=bg_color)

        self.style.configure(".", font=(self.os_font, 10), background=bg_color, foreground=fg_color)
        self.style.configure("TCheckbutton", focuscolor=bg_color)
        self.style.configure("TRadiobutton", focuscolor=bg_color)
        
        self.style.map("TRadiobutton", foreground=[('disabled', fg_color)])
        self.style.map("TCheckbutton", foreground=[('disabled', fg_color)])
        
        self.style.map('TCombobox', 
                       fieldbackground=[('focus', accent_color), ('readonly', 'white'), ('disabled', 'white'), ('!disabled', 'white')],
                       selectbackground=[('focus', accent_color), ('!focus', 'white')],
                       selectforeground=[('focus', 'white'), ('!focus', fg_color)],
                       foreground=[('focus', 'white')])
        self.style.map('TSpinbox', 
                       fieldbackground=[('focus', accent_color), ('readonly', 'white'), ('disabled', 'white'), ('!disabled', 'white')],
                       selectbackground=[('focus', accent_color), ('!focus', 'white')],
                       selectforeground=[('focus', 'white'), ('!focus', fg_color)],
                       foreground=[('focus', 'white')])
        
        self.style.configure("TFrame", background=bg_color)
        self.style.configure("TLabelframe", background=bg_color, borderwidth=1, bordercolor="#dcdde1")
        self.style.configure("TLabelframe.Label", font=(self.os_font, 11, "bold"), foreground="#34495e", background=bg_color)
        
        self.style.configure("TButton", font=(self.os_font, 10), padding=6, relief="flat", background="#e0e6ed", foreground=fg_color)
        self.style.map("TButton", background=[('active', '#d1d8e0')])
        
        self.style.configure("Accent.TButton", font=(self.os_font, 10, "bold"), padding=6, relief="flat", background=accent_color, foreground="white")
        self.style.map("Accent.TButton", 
                       background=[('active', accent_active), ('disabled', '#e0e6ed')],
                       foreground=[('disabled', '#95a5a6')])
                       
        processing_color = "#154360"
        self.style.configure("Processing.TButton", font=(self.os_font, 10, "bold"), padding=6, relief="flat", background=processing_color, foreground="white")
        self.style.map("Processing.TButton", 
                       background=[('disabled', processing_color)], 
                       foreground=[('disabled', 'white')])
                       
        error_color = "#e74c3c"
        self.style.configure("Error.TButton", font=(self.os_font, 10, "bold"), padding=6, relief="flat", background=error_color, foreground="white")
        self.style.map("Error.TButton", 
                       background=[('disabled', error_color)], 
                       foreground=[('disabled', 'white')])
        
        self.style.configure("Treeview", rowheight=30, borderwidth=0, fieldbackground="#ffffff", font=(self.os_font, 10))
        self.style.configure("Treeview.Heading", font=(self.os_font, 10, "bold"), background="#e0e6ed", foreground=fg_color, relief="flat", padding=5)
        self.style.map('Treeview', background=[('selected', accent_color)], foreground=[('selected', 'white')])
        
        self.init_data()
        self.build_ui()
        atexit.register(self._cleanup_temp_dir)

    def close_app(self):
        """关闭程序时释放资源并清除异步调度任务"""
        self._is_cancelled = True
        try:
            atexit.unregister(self._cleanup_temp_dir)
        except Exception:
            pass
        
        for job_attr in ('_check_queue_job', '_scroll_job', '_resize_job'):
            job_id = getattr(self, job_attr, None)
            if job_id and hasattr(self, 'root') and self.root:
                try:
                    self.root.after_cancel(job_id)
                except Exception:
                    pass
                setattr(self, job_attr, None)

        if hasattr(self, 'executor') and self.executor:
            try:
                self.executor.shutdown(wait=False, cancel_futures=True)
            except TypeError:
                self.executor.shutdown(wait=False)
            except Exception:
                pass
        
        self._cleanup_temp_dir()
        self.save_prefs()
        
        try:
            self.root.destroy()
        except Exception:
            pass

    def load_prefs(self):
        path = os.path.join(str(_PLUGIN_DIR), ".sigil_compress_plugin_prefs.json")
        if os.path.exists(path):
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except Exception:
                pass
        return {}

    def save_prefs(self):
        path = os.path.join(str(_PLUGIN_DIR), ".sigil_compress_plugin_prefs.json")
        
        def _to_int(val, default):
            try:
                if isinstance(val, str):
                    val = val.replace("级", "").strip()
                return int(val)
            except Exception:
                return default

        prefs = {
            'format_conv': self.var_format_conv.get(),
            'combo_conv': self.combo_conv.get(),
            'conv_type': self.var_conv_type.get(),
            'conv_lossless_lvl': f"{_to_int(self.combo_conv_lossless_level.get(), 2)}级",
            'conv_qlty': _to_int(self.sp_conv_qlty.get(), 80),
            'qlty_cmp': self.var_qlty_cmp.get(),
            'jpeg_qlty': _to_int(self.sp_jpeg_qlty.get(), 80),
            'webp_qlty': _to_int(self.sp_webp_qlty.get(), 80),
            'scale_img': self.var_scale_img.get(),
            'scale_type': self.var_scale_type.get(),
            'scale_percent': _to_int(self.sp_scale_percent.get(), 50),
            'scale_width': _to_int(self.sp_scale_width.get(), 800),
            'scale_height': _to_int(self.sp_scale_height.get(), 800),
            'depth_cmp': self.var_colordepth_cmp.get() if HAS_IMAGEQUANT else False,
            'lossless_cmp': self.var_lossless_cmp.get(),
            'lossless_lvl': f"{_to_int(self.combo_adv_lossless.get(), 2)}级",
            'strip_meta': self.var_strip_meta.get(),
            'batch_rename': self.var_batch_rename.get(),
            'panel_states': getattr(self, 'panel_states', {})
        }
        try:
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(prefs, f)
        except Exception as e:
            print(f"保存配置失败: {e}")

    def init_data(self):
        """遍历电子书图片库并规范化其标准绝对路径"""
        if self.bk is None:
            return
            
        self.images.clear()
        try:
            for img_info in self.bk.image_iter():
                try:
                    img_id = img_info[0]
                    href = canonical_epub_path(img_info[1])
                    
                    data = self.bk.readfile(img_id)
                    size = len(data) if data else 0
                    filename = posixpath.basename(href)
                    ext = filename.rsplit('.', 1)[-1].upper() if '.' in filename else 'UNKNOWN'
                    
                    w, h = 0, 0
                    if data:
                        try:
                            with Image.open(BytesIO(data)) as tmp_img:
                                tmp_img = ImageOps.exif_transpose(tmp_img)
                                w, h = tmp_img.size
                        except Exception:
                            pass
                    
                    self.images.append({
                        'id': img_id,
                        'href': href,
                        'filename': filename,
                        'size': size,
                        'format': ext,
                        'width': w,
                        'height': h,
                        'selected': False,
                        'rotate': 0
                    })
                except Exception as e:
                    print(f"读取图片 {img_info} 失败: {e}")
        except Exception as iter_err:
            print(f"遍历电子书图片失败: {iter_err}")

    def build_ui(self):
        self._managed_widgets = []
        
        self.main_wrapper = ttk.Frame(self.root)
        self.main_wrapper.pack(fill=tk.BOTH, expand=True)
        
        self.main_wrapper.columnconfigure(0, weight=1)
        self.main_wrapper.columnconfigure(1, weight=0)
        self.main_wrapper.rowconfigure(0, weight=1)
        
        self.left_frame = ttk.Frame(self.main_wrapper)
        self.right_frame = ttk.Frame(self.main_wrapper)
        
        self.left_frame.grid(row=0, column=0, sticky='nsew', padx=(15, 7.5), pady=15)
        self.right_frame.grid(row=0, column=1, sticky='nsew', padx=(7.5, 15), pady=15)
        
        self.build_left_panel(self.left_frame)
        self.build_right_panel(self.right_frame)
        
        self.update_states()
        
        self.root.bind('<Control-a>', lambda e: self.select_all())
        self.root.bind('<Control-A>', lambda e: self.select_all())
        self.root.bind('<Return>', lambda e: self.run_process())

    def build_left_panel(self, parent):
        filter_frame = ttk.LabelFrame(parent, text=" 快速筛选 ")
        filter_frame.pack(fill=tk.X, side=tk.TOP, pady=5)
        
        inner_filter = ttk.Frame(filter_frame, padding=8)
        inner_filter.pack(fill=tk.X)
        
        self.var_bmp = tk.BooleanVar(value=True)
        self.var_jpg = tk.BooleanVar(value=True)
        self.var_png = tk.BooleanVar(value=True)
        self.var_webp = tk.BooleanVar(value=True)
        
        cb_bmp = ttk.Checkbutton(inner_filter, text="BMP", variable=self.var_bmp, command=self.apply_filter)
        cb_bmp.pack(side=tk.LEFT, padx=5)
        cb_jpg = ttk.Checkbutton(inner_filter, text="JPEG", variable=self.var_jpg, command=self.apply_filter)
        cb_jpg.pack(side=tk.LEFT, padx=5)
        cb_png = ttk.Checkbutton(inner_filter, text="PNG", variable=self.var_png, command=self.apply_filter)
        cb_png.pack(side=tk.LEFT, padx=5)
        cb_webp = ttk.Checkbutton(inner_filter, text="WEBP", variable=self.var_webp, command=self.apply_filter)
        cb_webp.pack(side=tk.LEFT, padx=5)
        
        btn_rev = ttk.Button(inner_filter, text="反 选", command=self.select_reverse, width=6)
        btn_rev.pack(side=tk.RIGHT, padx=5)
        btn_all = ttk.Button(inner_filter, text="全 选", command=self.select_all, width=6)
        btn_all.pack(side=tk.RIGHT, padx=5)

        self._managed_widgets.extend([cb_bmp, cb_jpg, cb_png, cb_webp, btn_rev, btn_all])

        ctrl_top = ttk.Frame(parent)
        ctrl_top.pack(fill=tk.X, side=tk.TOP, pady=5)
        
        rot_frame = ttk.LabelFrame(ctrl_top, text=" 图片旋转 ")
        rot_frame.pack(fill=tk.X, side=tk.TOP, pady=5)
        
        inner_rot = ttk.Frame(rot_frame, padding=8)
        inner_rot.pack(fill=tk.X)
        
        btn_rot_cw = ttk.Button(inner_rot, text="↻ 顺时针 90°", command=lambda: self.rotate_selected(90))
        btn_rot_cw.pack(side=tk.LEFT, padx=5)
        btn_rot_ccw = ttk.Button(inner_rot, text="↺ 逆时针 90°", command=lambda: self.rotate_selected(-90))
        btn_rot_ccw.pack(side=tk.LEFT, padx=5)
        btn_rot_reset = ttk.Button(inner_rot, text="✖ 重置旋转", command=lambda: self.rotate_selected(0))
        btn_rot_reset.pack(side=tk.LEFT, padx=5)

        self._managed_widgets.extend([btn_rot_cw, btn_rot_ccw, btn_rot_reset])

        tree_frame = ttk.Frame(parent)
        tree_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)
        
        self.tree = ttk.Treeview(tree_frame, columns=('Name', 'Format', 'Size', 'Rotate'), show='headings', selectmode="extended")
        self.tree.heading('Name', text='文件名称')
        self.tree.column('Name', minwidth=150, anchor='w')
        self.tree.heading('Format', text='格式')
        self.tree.column('Format', minwidth=60, anchor='center')
        self.tree.heading('Size', text='体积')
        self.tree.column('Size', minwidth=60, anchor='e')
        self.tree.heading('Rotate', text='旋转状态')
        self.tree.column('Rotate', minwidth=60, anchor='center')
        
        def _on_tree_resize(event):
            w = event.width
            if getattr(self.tree, '_last_width', None) != w and w > 100:
                self.tree._last_width = w
                name_w = int(w * 0.50)
                rem = w - name_w
                col_w = int(rem / 3)
                rot_w = rem - (col_w * 2)
                
                self.tree.column('Name', width=name_w)
                self.tree.column('Format', width=col_w)
                self.tree.column('Size', width=col_w)
                self.tree.column('Rotate', width=rot_w)
                
        self.tree.bind('<Configure>', _on_tree_resize)
        
        self.tree.tag_configure('even', background='#fafbfc')
        self.tree.tag_configure('odd', background='#ffffff')
        
        yscrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=yscrollbar.set)
        
        self.tree.grid(row=0, column=0, sticky='nsew')
        yscrollbar.grid(row=0, column=1, sticky='ns')
        
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        self.tree.bind('<Double-1>', self.on_tree_double_click)
        
        self.refresh_tree()

    def _create_collapsible(self, parent, title, key):
        card = ttk.Frame(parent)
        card.pack(fill=tk.X, padx=5, pady=4)
        
        header = ttk.Frame(card, cursor="hand2")
        header.pack(fill=tk.X, expand=True)
        
        is_open = self.panel_states.get(key, True)
        self.panel_states[key] = is_open
        
        lbl_icon = tk.Label(
            header, 
            text="▼" if is_open else "▶", 
            font=(self.os_font, 9, "bold"), 
            foreground="#34495e", 
            background=self.bg_color, 
            cursor="hand2", 
            width=2
        )
        lbl_icon.pack(side=tk.LEFT, padx=(2, 0))
        
        lbl_title = tk.Label(
            header, 
            text=f" {title}", 
            font=(self.os_font, 10, "bold"), 
            foreground="#34495e", 
            background=self.bg_color, 
            cursor="hand2",
            anchor='w'
        )
        lbl_title.pack(side=tk.LEFT, fill=tk.X, expand=True, pady=4)
        
        inner = ttk.Frame(card, padding=(10, 5, 10, 5))
        
        def toggle(event=None):
            if getattr(self, '_ui_disabled', False):
                return
            self.panel_states[key] = not self.panel_states[key]
            if self.panel_states[key]:
                inner.pack(fill=tk.X, expand=True, pady=(2, 5))
                lbl_icon.config(text="▼")
            else:
                inner.pack_forget()
                lbl_icon.config(text="▶")
                
        header.bind("<Button-1>", toggle)
        lbl_icon.bind("<Button-1>", toggle)
        lbl_title.bind("<Button-1>", toggle)
        
        if is_open:
            inner.pack(fill=tk.X, expand=True, pady=(2, 5))
        else:
            inner.pack_forget()
            
        return inner

    def build_right_panel(self, parent):
        self.action_frame = ttk.Frame(parent)
        self.action_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=5)
        
        self.btn_run = ttk.Button(self.action_frame, text="🚀 执 行 处 理", command=self.run_process, style="Accent.TButton")
        self.btn_run.pack(fill=tk.X, expand=True, ipady=8)

        scroll_container = ttk.Frame(parent)
        scroll_container.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        canvas = tk.Canvas(scroll_container, bg=self.bg_color, highlightthickness=0, borderwidth=0, width=340)
        
        options_frame = ttk.Frame(canvas)
        options_frame.columnconfigure(0, weight=1)
        canvas_window = canvas.create_window((0, 0), window=options_frame, anchor="nw")
        
        def _update_scroll_region():
            if canvas.winfo_exists():
                bbox = canvas.bbox("all")
                canvas.configure(scrollregion=bbox)
                if bbox:
                    content_height = bbox[3] - bbox[1]
                    canvas_height = canvas.winfo_height()
                    if content_height <= canvas_height:
                        canvas.yview_moveto(0)

        def _on_frame_configure(event):
            if self._scroll_job and self.root:
                try:
                    self.root.after_cancel(self._scroll_job)
                except Exception:
                    pass
                self._scroll_job = None
            if not getattr(self, '_is_cancelled', False):
                self._scroll_job = self.root.after(15, _update_scroll_region)
            
        def _update_canvas_width(w):
            if canvas.winfo_exists():
                canvas.itemconfig(canvas_window, width=w)

        def _on_canvas_configure(event):
            w = event.width
            if getattr(canvas, '_last_width', None) != w:
                canvas._last_width = w
                if self._resize_job and self.root:
                    try:
                        self.root.after_cancel(self._resize_job)
                    except Exception:
                        pass
                    self._resize_job = None
                if not getattr(self, '_is_cancelled', False):
                    self._resize_job = self.root.after(15, lambda: _update_canvas_width(w))
            _update_scroll_region()
                
        options_frame.bind("<Configure>", _on_frame_configure)
        canvas.bind("<Configure>", _on_canvas_configure)
        
        def _on_mousewheel(event):
            bbox = canvas.bbox("all")
            if not bbox:
                return
            content_height = bbox[3] - bbox[1]
            canvas_height = canvas.winfo_height()
            
            if content_height <= canvas_height:
                canvas.yview_moveto(0)
                return
                
            if event.delta:
                canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            elif event.num == 4:
                canvas.yview_scroll(-1, "units")
            elif event.num == 5:
                canvas.yview_scroll(1, "units")
                
        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _on_mousewheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))
        
        canvas.pack(fill=tk.BOTH, expand=True)

        # 1. 格式转化
        self.var_format_conv = tk.BooleanVar(value=self.prefs.get('format_conv', False))
        inner_conv = self._create_collapsible(options_frame, "格式转化", "panel_conv")
        inner_conv.columnconfigure(0, weight=1)
        inner_conv.columnconfigure(1, weight=0)
        
        chk_format_conv = ttk.Checkbutton(inner_conv, text="启用格式转化", variable=self.var_format_conv, command=lambda: self.on_mode_change('format'))
        chk_format_conv.grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        ttk.Label(inner_conv, text="目标图片格式:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.combo_conv = ttk.Combobox(inner_conv, values=["JPEG", "PNG", "WEBP"], state="readonly", width=10)
        self.combo_conv.set(self.prefs.get('combo_conv', 'JPEG'))
        self.combo_conv.grid(row=1, column=1, sticky=tk.E, pady=5, padx=(5, 0))
        self.combo_conv.bind('<<ComboboxSelected>>', lambda e: self.update_states())
        
        self.var_conv_type = tk.StringVar(value=self.prefs.get('conv_type', 'quality'))
        self.rb_conv_lossless = ttk.Radiobutton(inner_conv, text="无损转换", variable=self.var_conv_type, value="lossless", command=self.update_states)
        self.rb_conv_lossless.grid(row=2, column=0, sticky=tk.W, pady=5)
        
        self.combo_conv_lossless_level = ttk.Combobox(inner_conv, values=[f"{i}级" for i in range(10)], state="readonly", width=10)
        self.combo_conv_lossless_level.set(self.prefs.get('conv_lossless_lvl', '2级'))
        self.combo_conv_lossless_level.grid(row=2, column=1, sticky=tk.E, pady=5, padx=(5, 0))
        
        self.rb_conv_qlty = ttk.Radiobutton(inner_conv, text="质量压缩", variable=self.var_conv_type, value="quality", command=self.update_states)
        self.rb_conv_qlty.grid(row=3, column=0, sticky=tk.W, pady=5)
        
        self.sp_conv_qlty = ttk.Spinbox(inner_conv, from_=5, to=100, width=10)
        self.sp_conv_qlty.set(self.prefs.get('conv_qlty', 80))
        self.sp_conv_qlty.grid(row=3, column=1, sticky=tk.E, pady=5, padx=(5, 0))

        # 2. 质量压缩与尺寸缩放
        self.var_qlty_cmp = tk.BooleanVar(value=self.prefs.get('qlty_cmp', False))
        inner_qlty = self._create_collapsible(options_frame, "质量压缩与缩放", "panel_qlty")
        inner_qlty.columnconfigure(0, weight=1)
        inner_qlty.columnconfigure(1, weight=0)
        
        chk_qlty_cmp = ttk.Checkbutton(inner_qlty, text="启用质量压缩", variable=self.var_qlty_cmp, command=lambda: self.on_mode_change('quality'))
        chk_qlty_cmp.grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        ttk.Label(inner_qlty, text="JPEG 输出质量:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.sp_jpeg_qlty = ttk.Spinbox(inner_qlty, from_=5, to=95, width=10)
        self.sp_jpeg_qlty.set(self.prefs.get('jpeg_qlty', 80))
        self.sp_jpeg_qlty.grid(row=1, column=1, sticky=tk.E, pady=5, padx=(5, 0))
        
        ttk.Label(inner_qlty, text="WEBP 输出质量:").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.sp_webp_qlty = ttk.Spinbox(inner_qlty, from_=5, to=100, width=10)
        self.sp_webp_qlty.set(self.prefs.get('webp_qlty', 80))
        self.sp_webp_qlty.grid(row=2, column=1, sticky=tk.E, pady=5, padx=(5, 0))
        
        self.var_scale_img = tk.BooleanVar(value=self.prefs.get('scale_img', False))
        chk_scale_img = ttk.Checkbutton(inner_qlty, text="启用图片缩放", variable=self.var_scale_img, command=lambda: self.on_mode_change('quality'))
        chk_scale_img.grid(row=3, column=0, columnspan=2, sticky=tk.W, pady=(5, 5))
        
        self.var_scale_type = tk.StringVar(value=self.prefs.get('scale_type', 'percent'))
        
        self.rb_scale_percent = ttk.Radiobutton(inner_qlty, text="按百分比缩放", variable=self.var_scale_type, value="percent", command=self.update_states)
        self.rb_scale_percent.grid(row=4, column=0, sticky=tk.W, pady=5)
        
        self.sp_scale_percent = ttk.Spinbox(inner_qlty, from_=1, to=500, width=10)
        self.sp_scale_percent.set(self.prefs.get('scale_percent', 50))
        self.sp_scale_percent.grid(row=4, column=1, sticky=tk.E, pady=5, padx=(5, 0))
        
        self.rb_scale_width = ttk.Radiobutton(inner_qlty, text="按指定宽度缩放", variable=self.var_scale_type, value="width", command=self.update_states)
        self.rb_scale_width.grid(row=5, column=0, sticky=tk.W, pady=5)
        
        self.sp_scale_width = ttk.Spinbox(inner_qlty, from_=1, to=10000, width=10)
        self.sp_scale_width.set(self.prefs.get('scale_width', 800))
        self.sp_scale_width.grid(row=5, column=1, sticky=tk.E, pady=5, padx=(5, 0))
        
        self.rb_scale_height = ttk.Radiobutton(inner_qlty, text="按指定高度缩放", variable=self.var_scale_type, value="height", command=self.update_states)
        self.rb_scale_height.grid(row=6, column=0, sticky=tk.W, pady=5)
        
        self.sp_scale_height = ttk.Spinbox(inner_qlty, from_=1, to=10000, width=10)
        self.sp_scale_height.set(self.prefs.get('scale_height', 800))
        self.sp_scale_height.grid(row=6, column=1, sticky=tk.E, pady=5, padx=(5, 0))

        # 3. 位深与高级无损压缩
        inner_adv = self._create_collapsible(options_frame, "高级压缩", "panel_adv")
        inner_adv.columnconfigure(0, weight=1)
        inner_adv.columnconfigure(1, weight=0)
        
        initial_depth_val = self.prefs.get('depth_cmp', False) if HAS_IMAGEQUANT else False
        self.var_colordepth_cmp = tk.BooleanVar(value=initial_depth_val)
        
        self.chk_depth_cmp = ttk.Checkbutton(
            inner_adv, 
            text="启用位深压缩 (PNG转8位)", 
            variable=self.var_colordepth_cmp, 
            command=lambda: self.on_mode_change('advanced')
        )
        self.chk_depth_cmp.grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        if not HAS_IMAGEQUANT:
            strike_font = tkfont.Font(family=self.os_font, size=10, overstrike=1)
            self.style.configure("Strikethrough.TCheckbutton", font=strike_font)
            self.style.map("Strikethrough.TCheckbutton", 
                           font=[('disabled', strike_font), ('!disabled', strike_font)],
                           foreground=[('disabled', '#888888'), ('!disabled', '#888888')])
            self.chk_depth_cmp.config(style="Strikethrough.TCheckbutton", state=tk.DISABLED)
            self.var_colordepth_cmp.set(False)
        
        self.var_lossless_cmp = tk.BooleanVar(value=self.prefs.get('lossless_cmp', False))
        chk_lossless_cmp = ttk.Checkbutton(inner_adv, text="启用无损压缩 (JPEG高质量)", variable=self.var_lossless_cmp, command=lambda: self.on_mode_change('advanced'))
        chk_lossless_cmp.grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        ttk.Label(inner_adv, text="无损压缩级别:").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.combo_adv_lossless = ttk.Combobox(inner_adv, values=[f"{i}级" for i in range(10)], state="readonly", width=10)
        self.combo_adv_lossless.set(self.prefs.get('lossless_lvl', '2级'))
        self.combo_adv_lossless.grid(row=2, column=1, sticky=tk.E, padx=(5, 0))

        # 4. 元数据清理与批量重命名
        inner_meta = self._create_collapsible(options_frame, "隐私与清理", "panel_meta")
        inner_meta.columnconfigure(0, weight=1)
        
        self.var_strip_meta = tk.BooleanVar(value=self.prefs.get('strip_meta', False))
        chk_strip_meta = ttk.Checkbutton(inner_meta, text="清除图片元数据 (EXIF等)", variable=self.var_strip_meta, command=self.check_run_state)
        chk_strip_meta.grid(row=0, column=0, sticky=tk.W)

        self.var_batch_rename = tk.BooleanVar(value=self.prefs.get('batch_rename', False))
        chk_batch_rename = ttk.Checkbutton(inner_meta, text="按HTML调用顺序批量重命名", variable=self.var_batch_rename, command=self.check_run_state)
        chk_batch_rename.grid(row=1, column=0, sticky=tk.W, pady=(6, 0))

        self._managed_widgets.extend([
            chk_format_conv, self.combo_conv, self.rb_conv_lossless, self.combo_conv_lossless_level,
            self.rb_conv_qlty, self.sp_conv_qlty, chk_qlty_cmp, self.sp_jpeg_qlty, self.sp_webp_qlty,
            chk_scale_img, self.rb_scale_percent, self.sp_scale_percent, self.rb_scale_width, self.sp_scale_width,
            self.rb_scale_height, self.sp_scale_height, self.chk_depth_cmp, chk_lossless_cmp, self.combo_adv_lossless,
            chk_strip_meta, chk_batch_rename
        ])

    def _set_ui_enabled(self, enabled=True):
        self._ui_disabled = not enabled
        tk_state = tk.NORMAL if enabled else tk.DISABLED
        
        for widget in getattr(self, '_managed_widgets', []):
            try:
                if widget == getattr(self, 'chk_depth_cmp', None) and not HAS_IMAGEQUANT:
                    widget.config(state=tk.DISABLED)
                    continue
                if isinstance(widget, ttk.Combobox):
                    widget.config(state="readonly" if enabled else "disabled")
                elif isinstance(widget, ttk.Spinbox):
                    widget.config(state="normal" if enabled else "disabled")
                elif hasattr(widget, 'config'):
                    widget.config(state=tk_state)
            except Exception:
                pass
                
        if not enabled:
            self.btn_run.config(state=tk.DISABLED)
        else:
            self.check_run_state()

    def on_mode_change(self, active_mode):
        if getattr(self, '_ui_disabled', False):
            return
            
        if active_mode == 'format' and self.var_format_conv.get():
            self.var_qlty_cmp.set(False)
            self.var_scale_img.set(False)
            self.var_colordepth_cmp.set(False)
            self.var_lossless_cmp.set(False)
        elif active_mode == 'quality' and (self.var_qlty_cmp.get() or self.var_scale_img.get()):
            self.var_format_conv.set(False)
            self.var_colordepth_cmp.set(False)
            self.var_lossless_cmp.set(False)
        elif active_mode == 'advanced':
            if not HAS_IMAGEQUANT:
                self.var_colordepth_cmp.set(False)
            if self.var_colordepth_cmp.get() or self.var_lossless_cmp.get():
                self.var_format_conv.set(False)
                self.var_qlty_cmp.set(False)
                self.var_scale_img.set(False)
        self.update_states()

    def update_states(self):
        if getattr(self, '_ui_disabled', False):
            return

        is_conv = self.var_format_conv.get()
        
        if is_conv:
            target = self.combo_conv.get()
            if target == "JPEG":
                self.var_conv_type.set("quality")
                self.rb_conv_lossless.state(['disabled'])
                self.rb_conv_qlty.state(['!disabled'])
            elif target == "PNG":
                self.var_conv_type.set("lossless")
                self.rb_conv_lossless.state(['!disabled'])
                self.rb_conv_qlty.state(['disabled'])
            else:  # WEBP
                self.rb_conv_lossless.state(['!disabled'])
                self.rb_conv_qlty.state(['!disabled'])
        else:
            self.rb_conv_lossless.state(['disabled'])
            self.rb_conv_qlty.state(['disabled'])
            
        if self.var_scale_img.get():
            self.rb_scale_percent.state(['!disabled'])
            self.rb_scale_width.state(['!disabled'])
            self.rb_scale_height.state(['!disabled'])
        else:
            self.rb_scale_percent.state(['disabled'])
            self.rb_scale_width.state(['disabled'])
            self.rb_scale_height.state(['disabled'])

        if not HAS_IMAGEQUANT:
            self.var_colordepth_cmp.set(False)
            if hasattr(self, 'chk_depth_cmp'):
                self.chk_depth_cmp.config(state=tk.DISABLED)
            
        self.check_run_state()

    def check_run_state(self):
        if not hasattr(self, 'btn_run') or getattr(self, '_ui_disabled', False):
            return
            
        has_selected_imgs = any(img['selected'] for img in self.images)
        has_features = (
            self.var_format_conv.get() or
            self.var_qlty_cmp.get() or
            self.var_scale_img.get() or
            (self.var_colordepth_cmp.get() if HAS_IMAGEQUANT else False) or
            self.var_lossless_cmp.get() or
            self.var_strip_meta.get() or
            self.var_batch_rename.get() or
            any(img['rotate'] != 0 for img in self.images if img['selected'])
        )
        
        if has_selected_imgs and has_features:
            self.btn_run.config(state=tk.NORMAL)
        else:
            self.btn_run.config(state=tk.DISABLED)

    def refresh_tree(self):
        self._is_refreshing = True
        for item in self.tree.get_children():
            self.tree.delete(item)
            
        allowed_exts = []
        if self.var_bmp.get(): allowed_exts.append('BMP')
        if self.var_jpg.get(): allowed_exts.extend(['JPG', 'JPEG'])
        if self.var_png.get(): allowed_exts.append('PNG')
        if self.var_webp.get(): allowed_exts.append('WEBP')
            
        display_idx = 0
        for idx, img in enumerate(self.images):
            if img['format'] not in allowed_exts:
                continue
            
            size_str = f"{img['size']/1024:.1f} KB"
            
            rot = img['rotate'] % 360
            if rot == 0:
                rot_str = ""
            elif rot == 90:
                rot_str = "↻ 90°"
            elif rot == 180:
                rot_str = "180°"
            elif rot == 270:
                rot_str = "↺ 90°"
            else:
                rot_str = f"↻ {rot}°"
            
            stripe_tag = 'even' if display_idx % 2 == 0 else 'odd'
            item = self.tree.insert('', tk.END, values=(img['filename'], img['format'], size_str, rot_str), tags=(str(idx), stripe_tag))
            
            if img['selected']:
                self.tree.selection_add(item)
                
            display_idx += 1
            
        self._is_refreshing = False
        self.check_run_state()

    def on_tree_select(self, event):
        if getattr(self, '_is_refreshing', False) or getattr(self, '_ui_disabled', False):
            return
            
        selected_items = self.tree.selection()
        for item in self.tree.get_children():
            idx = int(self.tree.item(item, 'tags')[0])
            self.images[idx]['selected'] = (item in selected_items)
            
        selected_imgs = [img for img in self.images if img['selected']]
        if len(selected_imgs) == 1:
            w = selected_imgs[0].get('width', 0)
            h = selected_imgs[0].get('height', 0)
            if w and h:
                if hasattr(self, 'sp_scale_width'): self.sp_scale_width.set(w)
                if hasattr(self, 'sp_scale_height'): self.sp_scale_height.set(h)
            
        self.check_run_state()
                    
    def select_all(self):
        if getattr(self, '_ui_disabled', False):
            return
        for item in self.tree.get_children():
            self.tree.selection_add(item)
        self.on_tree_select(None)
        
    def select_reverse(self):
        if getattr(self, '_ui_disabled', False):
            return
        selected = self.tree.selection()
        for item in self.tree.get_children():
            if item in selected:
                self.tree.selection_remove(item)
            else:
                self.tree.selection_add(item)
        self.on_tree_select(None)
        
    def apply_filter(self):
        if getattr(self, '_ui_disabled', False):
            return
        self.refresh_tree()

    def rotate_selected(self, angle):
        if getattr(self, '_ui_disabled', False):
            return
        for item in self.tree.selection():
            idx = int(self.tree.item(item, 'tags')[0])
            if angle == 0:
                self.images[idx]['rotate'] = 0
            else:
                self.images[idx]['rotate'] = (self.images[idx]['rotate'] + angle) % 360
        self.refresh_tree()

    def on_tree_double_click(self, event):
        if getattr(self, '_ui_disabled', False):
            return
        item = self.tree.identify_row(event.y)
        if not item:
            return
        tags = self.tree.item(item, 'tags')
        if tags:
            idx = int(tags[0])
            if 0 <= idx < len(self.images):
                self.preview_image(self.images[idx])

    def preview_image(self, img_info):
        if self.bk is None:
            return
            
        try:
            raw_data = self.bk.readfile(img_info['id'])
            if not raw_data:
                return
            
            with Image.open(BytesIO(raw_data)) as orig_img:
                img = ImageOps.exif_transpose(orig_img)
                img = convert_cmyk_to_rgb(img)
                
            if img_info.get('rotate', 0):
                img = img.rotate(-img_info['rotate'], expand=True)
                
            orig_w, orig_h = img.size
            size_kb = img_info['size'] / 1024.0
            
            win = tk.Toplevel(self.root)
            win.title(f"图片预览 - {img_info['filename']}")
            win.transient(self.root)
            win.grab_set()
            
            max_w, max_h = 800, 600
            scale = min(1.0, max_w / float(orig_w) if orig_w > 0 else 1.0, max_h / float(orig_h) if orig_h > 0 else 1.0)
            preview_w = max(1, int(orig_w * scale))
            preview_h = max(1, int(orig_h * scale))
            
            resample_filter = get_resample_filter(orig_w, orig_h, preview_w, preview_h)
            disp_img = img.resize((preview_w, preview_h), resample_filter) if (preview_w, preview_h) != (orig_w, orig_h) else img
            
            photo = ImageTk.PhotoImage(disp_img)
            
            main_f = ttk.Frame(win, padding=15)
            main_f.pack(fill=tk.BOTH, expand=True)
            
            img_lbl = ttk.Label(main_f, image=photo)
            img_lbl.image = photo
            img_lbl.pack(pady=(0, 10))
            
            info_str = f"文件名: {img_info['filename']}   |   分辨率: {orig_w} × {orig_h} px   |   体积: {size_kb:.1f} KB   |   格式: {img_info['format']}"
            ttk.Label(main_f, text=info_str, font=(self.os_font, 9), foreground="#555555").pack(pady=(0, 12))
            
            ttk.Button(main_f, text="关 闭", command=win.destroy, width=10).pack()
            
            win.bind('<Escape>', lambda e: win.destroy())
            
            win.update_idletasks()
            win_w = win.winfo_width()
            win_h = win.winfo_height()
            root_x = self.root.winfo_x()
            root_y = self.root.winfo_y()
            root_w = self.root.winfo_width()
            root_h = self.root.winfo_height()
            
            center_x = root_x + (root_w - win_w) // 2
            center_y = root_y + (root_h - win_h) // 2
            win.geometry(f"+{center_x}+{center_y}")
            
        except Exception as e:
            messagebox.showerror("预览失败", f"无法加载并预览图片: {e}", parent=self.root)

    def _get_cover_hrefs_and_ids(self):
        cover_hrefs = set()
        cover_ids = set()
        cover_html_hrefs = set()
        cover_html_ids = set()
        
        if self.bk is None:
            return cover_hrefs, cover_ids, cover_html_hrefs, cover_html_ids
        
        try:
            meta_xml = self.bk.getmetadataxml()
            if meta_xml:
                matches = _RE_COVER_META_1.findall(meta_xml) + _RE_COVER_META_2.findall(meta_xml)
                for cid in matches:
                    cover_ids.add(cid)
                    try:
                        href = self.bk.id_to_href(cid)
                        if href:
                            cover_hrefs.add(canonical_epub_path(href))
                    except Exception:
                        pass
        except Exception:
            pass
            
        try:
            for item in self.bk.manifest_iter():
                item_id = item[0]
                item_href = canonical_epub_path(item[1])
                props = str(item[3]) if len(item) >= 4 and item[3] else ""
                
                if 'cover-image' in props:
                    cover_ids.add(item_id)
                    cover_hrefs.add(item_href)
                if 'cover' in props and ('html' in item_href.lower() or 'xhtml' in item_href.lower()):
                    cover_html_ids.add(item_id)
                    cover_html_hrefs.add(item_href)
                if item_id.lower() in ('cover', 'cover-image', 'cover_image'):
                    if any(item_href.lower().endswith(ext) for ext in IMAGE_EXTENSIONS):
                        cover_ids.add(item_id)
                        cover_hrefs.add(item_href)
        except Exception:
            pass
                
        return cover_hrefs, cover_ids, cover_html_hrefs, cover_html_ids

    def _get_html_file_contents(self):
        if self.bk is None:
            return []

        text_files = []
        if hasattr(self.bk, 'spine_iter'):
            try:
                for item in self.bk.spine_iter():
                    text_files.append((item[0], canonical_epub_path(item[1])))
            except Exception:
                pass
        if not text_files:
            if hasattr(self.bk, 'text_iter'):
                try:
                    for item in self.bk.text_iter():
                        text_files.append((item[0], canonical_epub_path(item[1])))
                except Exception:
                    pass

        if hasattr(self.bk, 'manifest_iter'):
            try:
                for item in self.bk.manifest_iter():
                    item_id = item[0]
                    item_href = canonical_epub_path(item[1])
                    if item_href.lower().endswith('.svg') and (item_id, item_href) not in text_files:
                        text_files.append((item_id, item_href))
            except Exception:
                pass

        contents = []
        for html_id, html_href in text_files:
            try:
                data = self.bk.readfile(html_id)
                text, _ = safe_decode_text(data)
                contents.append((html_id, html_href, text))
            except Exception as e:
                print(f"读取文本/SVG文件 {html_href} 内容失败: {e}")
        return contents

    def _compute_rename_stems(self, selected_imgs, cover_info, html_contents):
        cover_hrefs, cover_ids, cover_html_hrefs, cover_html_ids = cover_info
        
        href_to_imgid = {canonical_epub_path(img['href']): img['id'] for img in self.images}
        img_call_positions = {img['id']: [] for img in self.images}
        call_counter = 0
        
        for html_id, html_href, html_text in html_contents:
            if html_id in cover_html_ids or html_href in cover_html_hrefs:
                continue
                
            try:
                for tag_match in _RE_TAG_BLOCK.finditer(html_text):
                    tag_text = tag_match.group(0)
                    tag_urls = []
                    
                    for m in _RE_IMG_REF.finditer(tag_text):
                        url = m.group(1) or m.group(2)
                        if url:
                            tag_urls.append(url)
                            
                    for m in _RE_SRCSET.finditer(tag_text):
                        srcset_val = m.group(2) if m.group(1) else m.group(3)
                        if srcset_val:
                            candidates = re.split(r',\s+(?=[^\s,]+)', srcset_val.strip())
                            for cand in candidates:
                                tokens = cand.strip().split()
                                if tokens:
                                    tag_urls.append(tokens[0])
                                    
                    matched_ids_in_tag = []
                    for raw_url in tag_urls:
                        book_path, _ = normalize_epub_path(html_href, raw_url)
                        if not book_path:
                            continue
                        matched_img_id = href_to_imgid.get(canonical_epub_path(book_path))
                        if matched_img_id and matched_img_id in img_call_positions and matched_img_id not in cover_ids:
                            if matched_img_id not in matched_ids_in_tag:
                                matched_ids_in_tag.append(matched_img_id)
                                
                    for matched_img_id in matched_ids_in_tag:
                        call_counter += 1
                        if call_counter not in img_call_positions[matched_img_id]:
                            img_call_positions[matched_img_id].append(call_counter)

            except Exception as e:
                print(f"解析 HTML {html_href} 中的图片引用失败: {e}")
                
        digits = max(3, len(str(call_counter)))
        fmt_str = f"p{{:0{digits}d}}"
        
        final_stems = {}
        for img in selected_imgs:
            img_id = img['id']
            img_href = canonical_epub_path(img['href'])
            
            if img_id in cover_ids or img_href in cover_hrefs:
                continue
                
            positions = img_call_positions.get(img_id, [])
            if not positions:
                continue
                
            if len(positions) > 3:
                stem_parts = [fmt_str.format(pos) for pos in positions[:3]]
                final_stems[img_id] = "_".join(stem_parts) + "__"
            else:
                stem_parts = [fmt_str.format(pos) for pos in positions]
                final_stems[img_id] = "_".join(stem_parts)
            
        return final_stems

    def _fill_executor(self, opts):
        if self.bk is None or getattr(self, '_is_cancelled', False) or not hasattr(self, 'executor') or self.executor is None:
            return
            
        target_active = self.threads * 2
        while len(self.active_futures) < target_active and self.process_queue and not self._is_cancelled:
            img_info = self.process_queue.popleft()
            try:
                raw_data = self.bk.readfile(img_info['id'])
                if raw_data is None:
                    raise ValueError("读取得到空字节数据")
                future = self.executor.submit(self.process_single_image, img_info, opts, raw_data)
                self.active_futures[future] = img_info['id']
            except Exception as e:
                err_msg = f"读取图片 {img_info['filename']} 失败: {e}"
                print(err_msg)
                try:
                    self.q.put_nowait((False, img_info['id'], err_msg, None))
                except queue.Full:
                    self.q.put((False, img_info['id'], err_msg, None))

    def _write_binary_file(self, file_id, data):
        if data is None:
            return
        if isinstance(data, str):
            data = data.encode('utf-8')
        if not isinstance(data, bytes):
            raise TypeError(f"写入文件 {file_id} 需要 bytes 字节类型数据，当前为: {type(data)}")
        self.bk.writefile(file_id, data)

    def _cleanup_temp_dir(self):
        if getattr(self, 'temp_dir', None) is not None:
            try:
                self.temp_dir.cleanup()
            except Exception as e:
                print(f"清理临时目录失败: {e}")
            self.temp_dir = None

    def _get_staged_data(self, item):
        temp_path = item.get('temp_path')
        if temp_path and os.path.exists(temp_path):
            try:
                with open(temp_path, 'rb') as f:
                    return f.read()
            except Exception as e:
                print(f"读取临时文件 {temp_path} 失败: {e}")
                return None
        return item.get('data')

    def run_process(self):
        if getattr(self, '_ui_disabled', False) or self.bk is None:
            return
            
        self._is_cancelled = False
            
        def sanitize_sp(widget, min_v, max_v, default_v):
            try:
                val = int(widget.get().strip())
                if not (min_v <= val <= max_v):
                    val = max(min_v, min(val, max_v))
                    widget.set(val)
                return val
            except Exception:
                widget.set(default_v)
                return default_v

        conv_qlty = sanitize_sp(self.sp_conv_qlty, 5, 100, 80)
        jpg_qlty = sanitize_sp(self.sp_jpeg_qlty, 5, 95, 80)
        webp_qlty = sanitize_sp(self.sp_webp_qlty, 5, 100, 80)
        scale_percent = sanitize_sp(self.sp_scale_percent, 1, 500, 50)
        scale_width = sanitize_sp(self.sp_scale_width, 1, 10000, 800)
        scale_height = sanitize_sp(self.sp_scale_height, 1, 10000, 800)
        
        try:
            adv_lossless_lvl = int(self.combo_adv_lossless.get().replace("级", ""))
        except ValueError:
            adv_lossless_lvl = 2
            
        try:
            conv_lossless_lvl = int(self.combo_conv_lossless_level.get().replace("级", ""))
        except ValueError:
            conv_lossless_lvl = 2
            
        self.save_prefs()
        
        selected_imgs = [img for img in self.images if img['selected']]
        if not selected_imgs:
            return

        self._set_ui_enabled(False)
        
        self._cleanup_temp_dir()
        try:
            self.temp_dir = tempfile.TemporaryDirectory(prefix="sigil_compress_")
        except Exception as e:
            print(f"创建临时缓存目录失败: {e}")
            self.temp_dir = None
            
        opts = {
            'do_conv': self.var_format_conv.get(),
            'conv_target': self.combo_conv.get() if self.var_format_conv.get() else None,
            'conv_type': self.var_conv_type.get(),
            'conv_qlty': conv_qlty,
            'conv_lossless_level': conv_lossless_lvl,
            
            'do_qlty': self.var_qlty_cmp.get(),
            'jpg_qlty': jpg_qlty,
            'webp_qlty': webp_qlty,
            
            'do_scale': self.var_scale_img.get(),
            'scale_type': self.var_scale_type.get(),
            'scale_percent': scale_percent,
            'scale_width': scale_width,
            'scale_height': scale_height,
            
            'do_depth': self.var_colordepth_cmp.get() if HAS_IMAGEQUANT else False,
            'do_lossless': self.var_lossless_cmp.get(),
            'lossless_level': adv_lossless_lvl,
            
            'strip_meta': self.var_strip_meta.get(),
            'batch_rename': self.var_batch_rename.get()
        }
        
        try:
            cover_info = self._get_cover_hrefs_and_ids() if opts.get('batch_rename') else None
            html_contents = self._get_html_file_contents() if opts.get('batch_rename') else None
            
            self.btn_run.config(style="Processing.TButton", state=tk.DISABLED, text="⚙ 准备处理...")
            
            self.success_count = 0
            self.error_count = 0
            self.processed_count = 0
            self.error_details.clear()
            
            self.staged_images = []
            self.staged_id_map = {}
            self.staged_href_map = {}
            
            self.prep_q = queue.Queue()
            self._prep_status = 'pending'
            
            try:
                self._existing_ids = {info[0] for info in self.bk.manifest_iter()}
                self._existing_bookpaths = set()
                for info in self.bk.manifest_iter():
                    bp = self.bk.id_to_bookpath(info[0]) if hasattr(self.bk, 'id_to_bookpath') else self.bk.id_to_href(info[0])
                    if bp:
                        self._existing_bookpaths.add(canonical_epub_path(bp).lower())
            except Exception:
                self._existing_ids = set()
                self._existing_bookpaths = set()
            
            self.threads = os.cpu_count() or 4
            self.executor = ThreadPoolExecutor(max_workers=self.threads)
            
            self.q = queue.Queue()
            self.process_queue = deque(selected_imgs)
            self.active_futures = {}
            
            self.executor.submit(self._async_prepare, selected_imgs, opts, cover_info, html_contents)
            self._fill_executor(opts)
            if not getattr(self, '_is_cancelled', False):
                self._check_queue_job = self.root.after(100, lambda: self.check_queue(len(selected_imgs), opts))

        except Exception as setup_err:
            err_msg = f"初始化处理任务失败: {setup_err}\n{traceback.format_exc()}"
            print(err_msg)
            self.error_details.append(err_msg)
            self._show_error_summary()
            self._cleanup_temp_dir()
            self._set_ui_enabled(True)

    def _async_prepare(self, selected_imgs, opts, cover_info=None, html_contents=None):
        if getattr(self, '_is_cancelled', False):
            return
        try:
            if opts.get('batch_rename') and cover_info and html_contents:
                opts['rename_stems'] = self._compute_rename_stems(selected_imgs, cover_info, html_contents)
            if not getattr(self, '_is_cancelled', False):
                self.prep_q.put((True, None))
        except Exception as e:
            err_msg = f"计算重命名索引异常: {e}\n{traceback.format_exc()}"
            print(err_msg)
            if not getattr(self, '_is_cancelled', False):
                self.prep_q.put((False, err_msg))

    def process_single_image(self, img_info, opts, raw_data):
        if getattr(self, '_is_cancelled', False):
            return

        try:
            with Image.open(BytesIO(raw_data)) as img:
                is_animated = getattr(img, 'is_animated', False) and getattr(img, 'n_frames', 1) > 1
                if is_animated:
                    if not getattr(self, '_is_cancelled', False):
                        self.q.put((True, img_info['id'], None, img_info['format']))
                    return

                img = ImageOps.exif_transpose(img)
                img = convert_cmyk_to_rgb(img)

                needs_reencode, target_fmt = should_reencode_image(img_info, opts, img)
                if not needs_reencode:
                    if not getattr(self, '_is_cancelled', False):
                        self.q.put((True, img_info['id'], None, target_fmt))
                    return

                rot_angle = img_info.get('rotate', 0)
                if rot_angle != 0:
                    img = img.rotate(-rot_angle, expand=True)

                cur_w, cur_h = img.size
                if cur_w * cur_h > MAX_PIXELS:
                    raise ValueError(f"原始图片尺寸超出安全上限 ({cur_w}×{cur_h} > {MAX_PIXELS} 像素)")

                if opts.get('do_scale'):
                    stype = opts.get('scale_type')
                    new_w, new_h = cur_w, cur_h
                    
                    if stype == "percent":
                        factor = opts.get('scale_percent') / 100.0
                        new_w = max(1, int(cur_w * factor))
                        new_h = max(1, int(cur_h * factor))
                    elif stype == "width":
                        val = opts.get('scale_width')
                        if cur_w > 0:
                            new_w = val
                            new_h = max(1, int(cur_h * (val / cur_w)))
                    elif stype == "height":
                        val = opts.get('scale_height')
                        if cur_h > 0:
                            new_h = val
                            new_w = max(1, int(cur_w * (val / cur_h)))
                                
                    if new_w * new_h > MAX_PIXELS:
                        raise ValueError(f"缩放后尺寸超出安全上限 ({new_w}×{new_h} > {MAX_PIXELS} 像素)")

                    if (new_w, new_h) != (cur_w, cur_h):
                        resample_filter = get_resample_filter(cur_w, cur_h, new_w, new_h)
                        img = img.resize((new_w, new_h), resample_filter)

                save_kwargs = {}
                
                if opts.get('strip_meta'):
                    clean_info = {}
                    for key in ('duration', 'loop'):
                        if key in img.info:
                            clean_info[key] = img.info[key]
                    img.info = clean_info
                    
                    if hasattr(img, 'getexif'):
                        try:
                            exif = img.getexif()
                            if exif is not None:
                                exif.clear()
                        except Exception:
                            pass
                    
                    if target_fmt in ('JPEG', 'WEBP', 'TIFF'):
                        save_kwargs['exif'] = b""
                    if target_fmt in ('JPEG', 'WEBP'):
                        save_kwargs['icc_profile'] = None

                if target_fmt == 'JPEG':
                    if img.mode in ('RGBA', 'LA') or (img.mode == 'P' and 'transparency' in img.info):
                        bg = Image.new('RGB', img.size, (255, 255, 255))
                        rgba_img = img.convert('RGBA')
                        bg.paste(rgba_img, mask=rgba_img.split()[3])
                        img = bg
                    elif img.mode != 'RGB':
                        img = img.convert('RGB')
                else:
                    if img.mode not in ('RGB', 'RGBA', 'P'):
                        img = img.convert('RGBA')
                
                if opts['do_depth'] and target_fmt == 'PNG':
                    if HAS_IMAGEQUANT:
                        try:
                            import imagequant
                            if img.mode != 'RGBA':
                                img = img.convert('RGBA')
                            img = imagequant.quantize_pil_image(img, max_quality=100)
                        except Exception:
                            img = img.convert('P', palette=Image.ADAPTIVE, colors=256)
                    else:
                        img = img.convert('P', palette=Image.ADAPTIVE, colors=256)
                    
                save_kwargs['format'] = target_fmt
                
                if opts['do_conv'] and opts['conv_type'] == 'quality':
                    if target_fmt in ('JPEG', 'WEBP'):
                        save_kwargs['quality'] = opts['conv_qlty']
                elif opts['do_qlty']:
                    if target_fmt == 'JPEG':
                        save_kwargs['quality'] = opts['jpg_qlty']
                    elif target_fmt == 'WEBP':
                        save_kwargs['quality'] = opts['webp_qlty']
                        
                is_conv_lossless = opts['do_conv'] and opts['conv_type'] == 'lossless'
                if is_conv_lossless or opts['do_lossless']:
                    if target_fmt in ('PNG', 'JPEG', 'WEBP'):
                        save_kwargs['optimize'] = True
                        
                    lvl = opts['conv_lossless_level'] if is_conv_lossless else opts['lossless_level']
                    
                    if target_fmt == 'JPEG':
                        save_kwargs['quality'] = 95
                        save_kwargs['subsampling'] = 0
                    elif target_fmt == 'PNG':
                        save_kwargs['compress_level'] = min(9, lvl)
                    elif target_fmt == 'WEBP':
                        save_kwargs['lossless'] = True
                        save_kwargs['method'] = min(6, lvl)
                        
                out_io = BytesIO()
                img.save(out_io, **save_kwargs)
                new_data = out_io.getvalue()
                
                if not getattr(self, '_is_cancelled', False):
                    self.q.put((True, img_info['id'], new_data, target_fmt))
            
        except UnidentifiedImageError:
            err_msg = "无法识别的图像格式或图片文件已损坏 (UnidentifiedImageError)"
            if not getattr(self, '_is_cancelled', False):
                self.q.put((False, img_info['id'], err_msg, None))
        except MemoryError:
            err_msg = "图像处理失败：内存不足 (MemoryError)"
            if not getattr(self, '_is_cancelled', False):
                self.q.put((False, img_info['id'], err_msg, None))
        except (OSError, IOError) as os_err:
            err_msg = f"图像解码/读取失败，数据可能损坏或不完整: {os_err}"
            if not getattr(self, '_is_cancelled', False):
                self.q.put((False, img_info['id'], err_msg, None))
        except ValueError as val_err:
            err_msg = f"图像参数校验失败: {val_err}"
            if not getattr(self, '_is_cancelled', False):
                self.q.put((False, img_info['id'], err_msg, None))
        except Exception as e:
            err_tb = traceback.format_exc()
            if not getattr(self, '_is_cancelled', False):
                self.q.put((False, img_info['id'], f"未知处理异常: {e}\n{err_tb}", None))

    def check_queue(self, total, opts):
        self._check_queue_job = None
        
        if getattr(self, '_is_cancelled', False):
            return

        if self.bk is None:
            self._set_ui_enabled(True)
            return

        if getattr(self, '_prep_status', 'pending') == 'pending':
            try:
                prep_ok, prep_err = self.prep_q.get_nowait()
                if prep_ok:
                    self._prep_status = 'done'
                else:
                    self._prep_status = 'failed'
                    if prep_err:
                        self.error_details.append(prep_err)
            except queue.Empty:
                if not getattr(self, '_is_cancelled', False):
                    self.btn_run.config(text="⚙ 正在计算重命名...")
                    self._check_queue_job = self.root.after(100, lambda: self.check_queue(total, opts))
                return

        if self._prep_status == 'failed':
            if self.executor:
                try:
                    self.executor.shutdown(wait=False, cancel_futures=True)
                except TypeError:
                    self.executor.shutdown(wait=False)
            self.btn_run.config(style="Error.TButton", text="❌ 准备失败")
            self._show_error_summary()
            self._cleanup_temp_dir()
            self._set_ui_enabled(True)
            return

        try:
            while not getattr(self, '_is_cancelled', False):
                success, img_id, result, target_fmt = self.q.get_nowait()
                self.processed_count += 1
                
                if success:
                    try:
                        temp_path = None
                        if result is not None and getattr(self, 'temp_dir', None) is not None:
                            try:
                                tmp_filename = f"tmp_{re.sub(r'[^\w\-]', '_', img_id)}.bin"
                                temp_path = os.path.join(self.temp_dir.name, tmp_filename)
                                with open(temp_path, 'wb') as tf:
                                    tf.write(result)
                                result = None
                            except Exception as e:
                                print(f"写入临时文件失败: {e}")

                        # 区分 Manifest href (OPF 相对路径) 与 Zip Root bookpath (容器绝对路径)
                        old_href = canonical_epub_path(self.bk.id_to_href(img_id))
                        old_bookpath = canonical_epub_path(self.bk.id_to_bookpath(img_id)) if hasattr(self.bk, 'id_to_bookpath') else old_href
                        
                        old_basename = posixpath.basename(old_bookpath)
                        old_bookpath_dir = posixpath.dirname(old_bookpath)
                        old_href_dir = posixpath.dirname(old_href)
                        
                        old_ext = old_basename.rsplit('.', 1)[-1].upper() if '.' in old_basename else 'PNG'
                        if old_ext == 'JPG': old_ext = 'JPEG'
                        
                        new_ext = target_fmt.lower() if target_fmt else old_ext.lower()
                        if new_ext == 'jpeg': new_ext = 'jpg'
                        
                        rename_stems = opts.get('rename_stems', {})
                        is_batch_renamed = opts.get('batch_rename') and img_id in rename_stems
                        
                        if is_batch_renamed:
                            name_part = rename_stems[img_id]
                        else:
                            name_part = old_basename.rsplit('.', 1)[0]
                            
                        candidate_basename = f"{name_part}.{new_ext}"
                        candidate_bookpath = canonical_epub_path(posixpath.join(old_bookpath_dir, candidate_basename)) if old_bookpath_dir else candidate_basename
                        candidate_href = canonical_epub_path(posixpath.join(old_href_dir, candidate_basename)) if old_href_dir else candidate_basename
                        
                        if candidate_bookpath.lower() != old_bookpath.lower() or is_batch_renamed:
                            self._existing_ids.discard(img_id)
                            self._existing_bookpaths.discard(old_bookpath.lower())
                            
                            clean_stem = re.sub(r'[^\w\-]', '_', name_part)
                            base_new_id = f"img_{clean_stem}_{new_ext}"
                            new_id = base_new_id
                            
                            # P1 修复解耦 1：独立解决 Manifest ID 命名空间冲突
                            id_counter = 1
                            while new_id in self._existing_ids:
                                new_id = f"{base_new_id}_{id_counter}"
                                id_counter += 1
                            self._existing_ids.add(new_id)
                            
                            # P1 修复解耦 2：独立解决 EPUB 物理 Bookpath 冲突（精准保留 OEBPS/Images/ 架构，按小写比对检查大小写不敏感冲突）
                            new_basename = candidate_basename
                            new_bookpath = candidate_bookpath
                            new_href = candidate_href
                            href_counter = 1
                            while new_bookpath.lower() in self._existing_bookpaths:
                                new_basename = f"{name_part}_{href_counter}.{new_ext}"
                                new_bookpath = canonical_epub_path(posixpath.join(old_bookpath_dir, new_basename)) if old_bookpath_dir else new_basename
                                new_href = canonical_epub_path(posixpath.join(old_href_dir, new_basename)) if old_href_dir else new_basename
                                href_counter += 1
                            self._existing_bookpaths.add(new_bookpath.lower())
                            
                            self.staged_id_map[img_id] = new_id
                            self.staged_href_map[old_href] = new_href
                            
                            self.staged_images.append({
                                'id': img_id,
                                'new_id': new_id,
                                'new_basename': new_basename,
                                'old_href': old_href,
                                'new_href': new_href,
                                'old_bookpath': old_bookpath,
                                'new_bookpath': new_bookpath,
                                'temp_path': temp_path,
                                'data': result,
                                'action': 'add_delete'
                            })
                        else:
                            self.staged_images.append({
                                'id': img_id,
                                'new_id': img_id,
                                'new_basename': old_basename,
                                'old_href': old_href,
                                'new_href': old_href,
                                'old_bookpath': old_bookpath,
                                'new_bookpath': old_bookpath,
                                'temp_path': temp_path,
                                'data': result,
                                'action': 'write' if (temp_path or result is not None) else 'none'
                            })
                            
                    except Exception as stage_err:
                        err_msg = f"暂存图片 {img_id} 处理失败: {stage_err}\n{traceback.format_exc()}"
                        print(err_msg)
                        self.error_details.append(err_msg)
                        self.error_count += 1
                else:
                    self.error_count += 1
                    err_msg = f"处理图片 {img_id} 失败: {result}"
                    print(err_msg)
                    self.error_details.append(err_msg)
                    
        except queue.Empty:
            pass

        if getattr(self, '_is_cancelled', False):
            return

        # P0 修复：在 Future 轮询中捕获 Worker 线程崩溃，防止 processed_count 死锁
        done_futures = [f for f in self.active_futures if f.done()]
        for f in done_futures:
            img_id = self.active_futures.pop(f)
            try:
                exc = f.exception()
                if exc is not None:
                    err_msg = f"Worker 线程处理图片 ({img_id}) 发生未捕获致命崩溃: {exc}"
                    print(err_msg)
                    self.q.put((False, img_id, err_msg, None))
            except Exception:
                pass
            
        progress_percent = int((self.processed_count / total) * 100) if total > 0 else 0
        self.btn_run.config(text=f"⚙ 处理进度 {progress_percent}%")
            
        self._fill_executor(opts)
            
        if self.processed_count >= total:
            if self.executor:
                try:
                    self.executor.shutdown(wait=False, cancel_futures=True)
                except TypeError:
                    self.executor.shutdown(wait=False)
            
            staged_writes, staged_metadata, ref_ok = self._stage_all_references()
            
            if ref_ok and self.error_count == 0:
                try:
                    self._commit_all_changes(staged_writes, staged_metadata)
                except Exception as commit_exc:
                    err_msg = f"提交物理变更发生未预期异常: {commit_exc}"
                    print(err_msg)
                    self.error_count += 1
                    if err_msg not in self.error_details:
                        self.error_details.append(err_msg)
            else:
                abort_msg = "由于处理过程中存在错误，已取消提交物理修改，EPUB 文件保持原样。"
                print(abort_msg)
                self.error_details.append(abort_msg)

            self._cleanup_temp_dir()

            if not getattr(self, '_is_cancelled', False):
                self.btn_run.config(style="Accent.TButton", text="🚀 执 行 处 理")
                
                if self.error_details:
                    self._show_error_summary()
                else:
                    messagebox.showinfo(
                        "处理完成", 
                        "图片处理完成并已成功刷入 Sigil 缓冲区！\n\n提示：根据 Sigil 插件工作机制，请关闭本插件窗口，Sigil 主界面将自动刷新并呈现最新更改。", 
                        parent=self.root
                    )
                
                self.images = []
                self.init_data()
                self._set_ui_enabled(True)
                self.refresh_tree()
                self.update_states()
        else:
            if not getattr(self, '_is_cancelled', False):
                self._check_queue_job = self.root.after(100, lambda: self.check_queue(total, opts))

    def _stage_all_references(self):
        """Phase 1: 内存计算全书 HTML/CSS/SVG 引用更新"""
        if self.bk is None or not self.staged_href_map:
            return {}, None, True

        staged_writes = {}
        staged_metadata = None

        def _url_replacer(match, current_file_href):
            groups = match.groups()
            if len(groups) == 5:
                prefix, quote1, href, quote2, suffix = groups
            elif len(groups) == 4:
                prefix, quote1, href, suffix = groups
                quote2 = ""
            else:
                return match.group(0)

            book_path, extra_suffix = normalize_epub_path(current_file_href, href)
            if not book_path:
                return match.group(0)

            raw_ext = posixpath.splitext(book_path.lower())[1]
            if raw_ext and raw_ext not in IMAGE_EXTENSIONS:
                return match.group(0)

            norm_book_path = canonical_epub_path(book_path)
            if norm_book_path in self.staged_href_map:
                new_book_path = self.staged_href_map[norm_book_path]
                new_rel_path = get_relative_epub_path(current_file_href, new_book_path)
                encoded_rel_path = quote(new_rel_path, safe='/')
                new_href = encoded_rel_path + extra_suffix
            else:
                new_href = href

            return f"{prefix}{quote1}{new_href}{quote2}{suffix}" if len(groups) == 5 else f"{prefix}{quote1}{new_href}{suffix}"

        def _srcset_replacer(match, current_file_href):
            """P3 修复：基于候选地址规范分割 srcset，防转义逗号及 Data URI 截断"""
            groups = match.groups()
            prefix = groups[0]
            if groups[1] is not None:
                quote1 = groups[1]
                srcset_val = groups[2]
                quote2 = groups[3]
            else:
                quote1 = ""
                srcset_val = groups[4]
                quote2 = ""
            suffix = groups[5]

            if not srcset_val:
                return match.group(0)

            candidates = re.split(r',\s+(?=[^\s,]+)', srcset_val.strip())
            new_candidates = []

            for cand in candidates:
                cand_str = cand.strip()
                if not cand_str:
                    continue

                parts = cand_str.split(None, 1)
                raw_url = parts[0]
                descriptor = f" {parts[1]}" if len(parts) > 1 else ""

                book_path, extra_suffix = normalize_epub_path(current_file_href, raw_url)
                if not book_path:
                    new_candidates.append(cand_str)
                    continue

                raw_ext = posixpath.splitext(book_path.lower())[1]
                if raw_ext and raw_ext not in IMAGE_EXTENSIONS:
                    new_candidates.append(cand_str)
                    continue

                norm_book_path = canonical_epub_path(book_path)
                if norm_book_path in self.staged_href_map:
                    new_book_path = self.staged_href_map[norm_book_path]
                    new_rel_path = get_relative_epub_path(current_file_href, new_book_path)
                    encoded_rel_path = quote(new_rel_path, safe='/')
                    raw_url = encoded_rel_path + extra_suffix

                new_candidates.append(raw_url + descriptor)

            new_srcset = ", ".join(new_candidates)
            return f"{prefix}{quote1}{new_srcset}{quote2}{suffix}"

        try:
            if hasattr(self.bk, 'text_iter'):
                for html_id, raw_html_href in self.bk.text_iter():
                    html_href = canonical_epub_path(raw_html_href)
                    html_data = self.bk.readfile(html_id)
                    text, is_bytes = safe_decode_text(html_data)

                    new_text = _RE_HTML_IMG.sub(lambda m, h=html_href: _url_replacer(m, h), text)
                    new_text = _RE_HTML_SRCSET.sub(lambda m, h=html_href: _srcset_replacer(m, h), new_text)
                    new_text = _RE_CSS_URL.sub(lambda m, h=html_href: _url_replacer(m, h), new_text)

                    if text != new_text:
                        new_text = update_xml_encoding_header(new_text, "utf-8")
                        staged_writes[html_id] = new_text.encode('utf-8') if is_bytes else new_text

            if hasattr(self.bk, 'css_iter'):
                for css_id, raw_css_href in self.bk.css_iter():
                    css_href = canonical_epub_path(raw_css_href)
                    css_data = self.bk.readfile(css_id)
                    text, is_bytes = safe_decode_text(css_data)

                    new_text = _RE_CSS_URL.sub(lambda m, h=css_href: _url_replacer(m, h), text)
                    new_text = _RE_CSS_IMPORT.sub(lambda m, h=css_href: _url_replacer(m, h), new_text)

                    if text != new_text:
                        staged_writes[css_id] = new_text.encode('utf-8') if is_bytes else new_text

            if hasattr(self.bk, 'manifest_iter'):
                for item in self.bk.manifest_iter():
                    svg_id = item[0]
                    svg_href = canonical_epub_path(item[1])
                    if svg_href.lower().endswith('.svg'):
                        svg_data = self.bk.readfile(svg_id)
                        if not svg_data:
                            continue
                        text, is_bytes = safe_decode_text(svg_data)

                        new_text = _RE_HTML_IMG.sub(lambda m, h=svg_href: _url_replacer(m, h), text)
                        new_text = _RE_HTML_SRCSET.sub(lambda m, h=svg_href: _srcset_replacer(m, h), new_text)
                        new_text = _RE_CSS_URL.sub(lambda m, h=svg_href: _url_replacer(m, h), new_text)

                        if text != new_text:
                            new_text = update_xml_encoding_header(new_text, "utf-8")
                            staged_writes[svg_id] = new_text.encode('utf-8') if is_bytes else new_text

            if self.staged_id_map:
                metadata = self.bk.getmetadataxml()
                if metadata:
                    def _meta_replacer(m):
                        tag = m.group(0)
                        c_match = re.search(r'(content\s*=\s*[\'"])(.*?)([\'"])', tag, re.IGNORECASE)
                        if c_match:
                            old_id = c_match.group(2)
                            if old_id in self.staged_id_map:
                                return tag[:c_match.start(2)] + self.staged_id_map[old_id] + tag[c_match.end(2):]
                        return tag

                    new_metadata = re.sub(r'<[a-zA-Z0-9:]*?meta\s+[^>]*?name\s*=\s*[\'"]cover[\'"][^>]*?>', _meta_replacer, metadata, flags=re.IGNORECASE)
                    if new_metadata == metadata:
                        new_metadata = re.sub(r'<[a-zA-Z0-9:]*?meta\s+[^>]*?content\s*=\s*[\'"][^\'"]*[\'"][^>]*?name\s*=\s*[\'"]cover[\'"][^>]*?>', _meta_replacer, metadata, flags=re.IGNORECASE)

                    if new_metadata != metadata:
                        staged_metadata = new_metadata

            return staged_writes, staged_metadata, True

        except Exception as e:
            err_msg = f"计算全书引用更新异常: {e}\n{traceback.format_exc()}"
            print(err_msg)
            self.error_details.append(err_msg)
            return {}, None, False

    def _commit_all_changes(self, staged_writes, staged_metadata):
        """Phase 2: 提交变更到 Sigil EPUB 容器，具备原子备份与还原回滚策略"""
        added_ids = []
        written_backups = {}   # {img_id: original_raw_bytes}
        deleted_backups = {}   # {img_id: (old_bookpath, original_raw_bytes, original_mime)}
        text_backups = {}      # {file_id: original_raw_content}
        original_metadata = None
        resolved_data_map = {} # {img_id: raw_bytes}
        
        try:
            # 1. 备份原数据并在执行任何物理修改前预先解析待写入的二进制数据
            for item in self.staged_images:
                img_id = item['id']
                orig_data = self.bk.readfile(img_id)
                if orig_data is not None:
                    if item['action'] == 'write':
                        written_backups[img_id] = orig_data
                    elif item['action'] == 'add_delete':
                        orig_mime = get_image_mime(item['old_bookpath'])
                        deleted_backups[img_id] = (item['old_bookpath'], orig_data, orig_mime)
                
                # 预解析数据：优先读取暂存的处理结果，若无（如仅重命名未重编码）则使用备份的原数据
                staged_data = self._get_staged_data(item)
                if staged_data is not None:
                    resolved_data_map[img_id] = staged_data
                else:
                    resolved_data_map[img_id] = orig_data

            # 2. 备份文本与元数据
            for file_id in staged_writes.keys():
                orig_text = self.bk.readfile(file_id)
                if orig_text is not None:
                    text_backups[file_id] = orig_text

            if staged_metadata:
                original_metadata = self.bk.getmetadataxml()

            # 步骤一：物理删除将被替换或重命名的旧图片（必须先删后加以释放 ID 与 Bookpath 占位）
            for item in self.staged_images:
                if item['action'] == 'add_delete':
                    try:
                        self.bk.deletefile(item['id'])
                    except Exception as del_err:
                        raise RuntimeError(f"清除原旧图片 '{item['id']}' 物理文件失败: {del_err}")

            # 步骤二：添加新图片（直接从 resolved_data_map 读取，不再调用已被删除的 ID 的 readfile）
            for item in self.staged_images:
                if item['action'] == 'add_delete':
                    data = resolved_data_map.get(item['id'])
                    if data is None:
                        raise RuntimeError(f"未找到待添加新图片 '{item['id']}' 的有效二进制数据")
                    
                    if isinstance(data, str):
                        data = data.encode('utf-8')
                    
                    mime_type = get_image_mime(item['new_basename'])
                    try:
                        self.bk.addbookpath(item['new_id'], item['new_bookpath'], data, mime=mime_type)
                        added_ids.append(item['new_id'])
                        self.success_count += 1
                    except Exception as add_err:
                        raise RuntimeError(f"添加新图片 '{item['new_basename']}' (ID: {item['new_id']}) 失败: {add_err}")

            # 步骤三：覆写图片
            for item in self.staged_images:
                if item['action'] == 'write':
                    data = resolved_data_map.get(item['id'])
                    if data is not None:
                        try:
                            self._write_binary_file(item['id'], data)
                            self.success_count += 1
                        except Exception as write_err:
                            raise RuntimeError(f"覆写图片 '{item['id']}' 内容失败: {write_err}")

            # 步骤四：更新文本引用
            for file_id, content in staged_writes.items():
                try:
                    self.bk.writefile(file_id, content)
                except TypeError:
                    if isinstance(content, str):
                        self.bk.writefile(file_id, content.encode('utf-8'))
                    elif isinstance(content, bytes):
                        self.bk.writefile(file_id, content.decode('utf-8', errors='ignore'))
                except Exception as ref_err:
                    raise RuntimeError(f"更新 HTML/CSS/SVG 引用文件 '{file_id}' 失败: {ref_err}")

            # 步骤五：写入元数据 XML
            if staged_metadata:
                try:
                    self.bk.setmetadataxml(staged_metadata)
                except Exception as meta_err:
                    raise RuntimeError(f"更新元数据 (OPF) 失败: {meta_err}")

        except Exception as commit_err:
            print(f"物理提交过程捕获致命异常，正在启动完整原子回滚策略: {commit_err}")
            
            # 回滚 1：删除已添加的新图片
            for rollback_id in list(added_ids):
                try:
                    self.bk.deletefile(rollback_id)
                except Exception as rb_e:
                    print(f"回滚删除已添加图片 '{rollback_id}' 失败: {rb_e}")
            added_ids.clear()

            # 回滚 2：精准按 Bookpath 还原已被删除的原图片（显式传递 orig_mime）
            for del_id, (old_bookpath, orig_bytes, orig_mime) in deleted_backups.items():
                try:
                    self.bk.addbookpath(del_id, old_bookpath, orig_bytes, mime=orig_mime)
                except Exception as rb_d:
                    print(f"回滚恢复已被删除图片 '{del_id}' 失败: {rb_d}")
            deleted_backups.clear()

            # 回滚 3：还原覆写的图片
            for write_id, orig_bytes in written_backups.items():
                try:
                    self._write_binary_file(write_id, orig_bytes)
                except Exception as rb_w:
                    print(f"回滚还原已覆盖图片 '{write_id}' 失败: {rb_w}")
            written_backups.clear()

            # 回滚 4：还原 HTML/CSS/SVG 文本
            for file_id, orig_content in text_backups.items():
                try:
                    self.bk.writefile(file_id, orig_content)
                except Exception as rb_t:
                    print(f"回滚还原文本文件 '{file_id}' 失败: {rb_t}")
            text_backups.clear()

            # 回滚 5：还原 OPF 元数据
            if original_metadata:
                try:
                    self.bk.setmetadataxml(original_metadata)
                except Exception as rb_m:
                    print(f"回滚还原 OPF 元数据失败: {rb_m}")

            err_msg = f"物理提交到 Sigil 时发生错误 (已完整回滚图片、文本及 OPF 元数据，保持 EPUB 原样): {commit_err}\n{traceback.format_exc()}"
            print(err_msg)
            if err_msg not in self.error_details:
                self.error_details.append(err_msg)
            raise

    def _show_error_summary(self):
        if not self.error_details or getattr(self, '_is_cancelled', False):
            return

        err_win = tk.Toplevel(self.root)
        err_win.title("⚠️ 插件处理异常汇总")
        err_win.geometry("680x440")
        err_win.minsize(550, 320)
        err_win.transient(self.root)
        err_win.grab_set()
        
        main_f = ttk.Frame(err_win, padding=15)
        main_f.pack(fill=tk.BOTH, expand=True)
        
        header_text = f"执行过程中共发现 {len(self.error_details)} 项异常或警告："
        lbl_head = ttk.Label(main_f, text=header_text, font=(self.os_font, 10, "bold"), foreground="#e74c3c")
        lbl_head.pack(anchor=tk.W, pady=(0, 10))
        
        text_frame = ttk.Frame(main_f)
        text_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 12))
        
        txt = tk.Text(text_frame, bg="#fafafa", fg="#2c3e50", font=(self.os_font, 9), relief=tk.SOLID, bd=1, wrap=tk.WORD)
        txt.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        sb = ttk.Scrollbar(text_frame, orient=tk.VERTICAL, command=txt.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        txt.configure(yscrollcommand=sb.set)
        
        for idx, item in enumerate(self.error_details, 1):
            txt.insert(tk.END, f"【异常记录 {idx}】\n{item.strip()}\n\n")
        txt.config(state=tk.DISABLED)
        
        btn_bar = ttk.Frame(main_f)
        btn_bar.pack(fill=tk.X, side=tk.BOTTOM)
        
        def copy_log():
            log_content = "\n".join([f"【异常记录 {i+1}】\n{err}" for i, err in enumerate(self.error_details)])
            err_win.clipboard_clear()
            err_win.clipboard_append(log_content)
            messagebox.showinfo("提示", "异常日志已成功复制到剪贴板！", parent=err_win)
            
        btn_copy = ttk.Button(btn_bar, text="📋 复制错误日志", command=copy_log, width=15)
        btn_copy.pack(side=tk.LEFT, padx=(0, 10))
        
        btn_close = ttk.Button(btn_bar, text="关 闭", command=err_win.destroy, width=12)
        btn_close.pack(side=tk.RIGHT)
        
        err_win.bind('<Escape>', lambda e: err_win.destroy())
        
        err_win.update_idletasks()
        win_x = self.root.winfo_x() + (self.root.winfo_width() - 680) // 2
        win_y = self.root.winfo_y() + (self.root.winfo_height() - 440) // 2
        err_win.geometry(f"+{max(0, win_x)}+{max(0, win_y)}")

def run(bk):
    """Sigil 插件标准入口函数"""
    if sys.platform == 'win32':
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

    err_msg = check_dependencies()
    if err_msg:
        err_root = tk.Tk()
        err_root.withdraw()
        
        guide_win = tk.Toplevel()
        guide_win.title("⚠️ 插件环境异常")
        guide_win.geometry("600x360")
        
        ui_font = ("微软雅黑" if sys.platform == "win32" else "Helvetica Neue" if sys.platform == "darwin" else "sans-serif", 10)
        code_font = ("Consolas" if sys.platform == "win32" else "Menlo" if sys.platform == "darwin" else "sans-serif", 10)
        
        guide_win.update_idletasks()
        win_x = (guide_win.winfo_screenwidth() // 2) - (600 // 2)
        win_y = (guide_win.winfo_screenheight() // 2) - (320 // 2)
        guide_win.geometry(f'+{win_x}+{win_y}')
        
        top_frame = tk.Frame(guide_win, padx=25, pady=20)
        top_frame.pack(fill=tk.BOTH, expand=True)

        tk.Label(top_frame, text="由于缺失必要的核心组件，插件无法启动。", font=(ui_font[0], 12, "bold"), fg="#d9534f").pack(anchor=tk.W, pady=(0, 10))
        
        info_text = (
            f"具体拦截原因: {err_msg}\n\n"
            f"请按下 Win+R 打开 [cmd] 命令行 (macOS 请使用终端)，\n"
            f"复制并执行下方的自动修复指令将依赖装入插件目录中："
        )
        tk.Label(top_frame, text=info_text, justify=tk.LEFT, font=ui_font).pack(anchor=tk.W)
        
        cmd_str = f'pip install Pillow --target="{str(_VENDOR_DIR)}"'
        
        text_box = tk.Text(top_frame, height=3, width=70, bg="#f5f6f7", font=code_font, relief=tk.FLAT)
        text_box.insert(tk.END, cmd_str)
        text_box.config(state=tk.DISABLED)
        text_box.pack(pady=15, fill=tk.X)
        
        def copy_cmd():
            guide_win.clipboard_clear()
            guide_win.clipboard_append(cmd_str)
            messagebox.showinfo("已复制", "命令已复制到剪贴板！\n\n请打开命令行界面右键粘贴并回车执行。\n安装完毕后重新启动本插件即可。", parent=guide_win)
            
        ttk.Button(top_frame, text="📋 一键复制修复指令", command=copy_cmd, padding=5).pack(pady=(5,0))
        
        guide_win.wait_window()
        err_root.destroy()
        return -1

    try:
        root = tk.Tk()
        app = CompressApp(root, bk)
        root.protocol("WM_DELETE_WINDOW", app.close_app)
        root.mainloop()
    except Exception as e:
        print(traceback.format_exc())
        return -1

    return 0

if __name__ == "__main__":
    print("此脚本作为 Sigil 插件设计。请在 Sigil 环境中将其作为插件运行。")