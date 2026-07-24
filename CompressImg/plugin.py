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
from io import BytesIO
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from collections import deque

# ==========================================
# 1. 插件路径与第三方依赖加载
# ==========================================
_PLUGIN_DIR = Path(__file__).resolve().parent
_VENDOR_DIR = _PLUGIN_DIR / "vendor"

def setup_environment():
    if not _VENDOR_DIR.exists():
        _VENDOR_DIR.mkdir(parents=True, exist_ok=True)
        
    vendor_path = str(_VENDOR_DIR)
    if vendor_path not in sys.path:
        sys.path.insert(0, vendor_path)
            
    if sys.platform == 'win32' and hasattr(os, 'add_dll_directory'):
        try:
            os.add_dll_directory(vendor_path)
            for item in _VENDOR_DIR.iterdir():
                # 兼容包含动态链接库的包
                if item.is_dir() and (item.name.endswith('.libs') or item.name == 'imagequant'):
                    os.add_dll_directory(str(item))
        except Exception:
            pass

setup_environment()

import tkinter as tk
from tkinter import ttk, messagebox

# Check for Pillow library, handled securely in run() if missing
try:
    import PIL
    from PIL import Image, UnidentifiedImageError
except ImportError:
    pass

# ==========================================
# 2. 依赖检查机制
# ==========================================
def check_dependencies():
    try:
        import PIL
        from PIL import Image
        
        # 版本检查逻辑
        def _parse_version(v_str):
            match = re.search(r'^(\d+\.\d+(\.\d+)?)', str(v_str))
            return tuple(map(int, match.group(1).split('.'))) if match else (0, 0, 0)
            
        if hasattr(PIL, '__version__') and _parse_version(PIL.__version__) < (8, 0):
            return f"Pillow 版本过低 (当前 {PIL.__version__}，需 >= 8.0.0)"
            
        return None
    except Exception as e:
        return str(e)


class CompressApp:
    def __init__(self, root, bk):
        self.root = root
        self.bk = bk
        self.images = []  # To store metadata of images extracted from the ebook
        
        # 读取用户之前的设置
        self.prefs = self.load_prefs()
        
        # Configure overall style and layout
        self.root.title("图片压缩插件 V1.1")
        self.root.geometry("1050x800")
        self.root.minsize(1000, 750)
        self.root.eval('tk::PlaceWindow . center')
        
        self.style = ttk.Style()
        # Use 'clam' theme for a flatter, more modern cross-platform look
        if 'clam' in self.style.theme_names():
            self.style.theme_use('clam')
            
        self.os_font = "微软雅黑" if sys.platform == "win32" else "Helvetica Neue"
        
        # Modern Color Palette
        bg_color = "#f4f6f9"
        fg_color = "#2c3e50"
        accent_color = "#3498db"
        accent_active = "#2980b9"
        
        self.root.configure(background=bg_color)
        
        # Configure standard widgets
        self.style.configure(".", font=(self.os_font, 10), background=bg_color, foreground=fg_color)
        
        # 移除单选框和复选框点击时的焦点虚线框
        self.style.configure("TCheckbutton", focuscolor=bg_color)
        self.style.configure("TRadiobutton", focuscolor=bg_color)
        
        # 使【无损转换】【质量压缩】等在禁用(灰底)状态下仍保持深色字体
        self.style.map("TRadiobutton", foreground=[('disabled', fg_color)])
        self.style.map("TCheckbutton", foreground=[('disabled', fg_color)])
        
        # 强制所有下拉框和调节框为白底，并且正在调节的框变为强调色(蓝色)，消除默认的灰底文本选中色
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
        
        # Configure Labelframes
        self.style.configure("TLabelframe", background=bg_color, borderwidth=1, bordercolor="#dcdde1")
        self.style.configure("TLabelframe.Label", font=(self.os_font, 11, "bold"), foreground="#34495e", background=bg_color)
        
        # Configure Buttons
        self.style.configure("TButton", font=(self.os_font, 10), padding=6, relief="flat", background="#e0e6ed", foreground=fg_color)
        self.style.map("TButton", background=[('active', '#d1d8e0')])
        
        # Accent Button (Primary Action)
        self.style.configure("Accent.TButton", font=(self.os_font, 10, "bold"), padding=6, relief="flat", background=accent_color, foreground="white")
        self.style.map("Accent.TButton", 
                       background=[('active', accent_active), ('disabled', '#e0e6ed')],
                       foreground=[('disabled', '#95a5a6')])
                       
        # Processing Button (Darker shade for running state)
        processing_color = "#154360" # 颜色比悬停更深
        self.style.configure("Processing.TButton", font=(self.os_font, 10, "bold"), padding=6, relief="flat", background=processing_color, foreground="white")
        self.style.map("Processing.TButton", 
                       background=[('disabled', processing_color)], 
                       foreground=[('disabled', 'white')])
                       
        # Error Button (Red for validation failure)
        error_color = "#e74c3c"
        self.style.configure("Error.TButton", font=(self.os_font, 10, "bold"), padding=6, relief="flat", background=error_color, foreground="white")
        self.style.map("Error.TButton", 
                       background=[('disabled', error_color)], 
                       foreground=[('disabled', 'white')])
        
        # Configure Treeview (Data Table)
        self.style.configure("Treeview", rowheight=30, borderwidth=0, fieldbackground="#ffffff", font=(self.os_font, 10))
        self.style.configure("Treeview.Heading", font=(self.os_font, 10, "bold"), background="#e0e6ed", foreground=fg_color, relief="flat", padding=5)
        self.style.map('Treeview', background=[('selected', accent_color)], foreground=[('selected', 'white')])
        
        self.init_data()
        self.build_ui()

    def load_prefs(self):
        """从用户目录加载历史配置"""
        path = os.path.join(os.path.expanduser("~"), ".sigil_compress_plugin_prefs.json")
        if os.path.exists(path):
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except:
                pass
        return {}

    def save_prefs(self):
        """保存当前配置到用户目录"""
        path = os.path.join(os.path.expanduser("~"), ".sigil_compress_plugin_prefs.json")
        prefs = {
            'format_conv': self.var_format_conv.get(),
            'combo_conv': self.combo_conv.get(),
            'conv_type': self.var_conv_type.get(),
            'conv_lossless_lvl': self.combo_conv_lossless_level.get(),
            'conv_qlty': self.sp_conv_qlty.get(),
            'qlty_cmp': self.var_qlty_cmp.get(),
            'jpeg_qlty': self.sp_jpeg_qlty.get(),
            'webp_qlty': self.sp_webp_qlty.get(),
            'depth_cmp': self.var_colordepth_cmp.get(),
            'lossless_cmp': self.var_lossless_cmp.get(),
            'lossless_lvl': self.combo_adv_lossless.get(),
        }
        try:
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(prefs, f)
        except:
            pass

    def init_data(self):
        """Iterate through all images in the Sigil ebook and collect their metadata."""
        if self.bk is None:
            # For testing mode without Sigil
            return
            
        for img_info in self.bk.image_iter():
            try:
                img_id = img_info[0]
                href = img_info[1]
                
                data = self.bk.readfile(img_id)
                size = len(data)
                filename = href.split('/')[-1]
                ext = filename.split('.')[-1].upper()
                
                self.images.append({
                    'id': img_id,
                    'href': href,
                    'filename': filename,
                    'size': size,
                    'format': ext,
                    'selected': False,  # 默认全不选
                    'rotate': 0        # Default rotation angle
                })
            except Exception as e:
                print(f"读取图片 {href} 失败: {e}")

    def build_ui(self):
        """Constructs the main wrappers and left/right panels."""
        # Main wrapper to hold the content
        self.main_wrapper = ttk.Frame(self.root)
        self.main_wrapper.pack(fill=tk.BOTH, expand=True)
        
        # Main split pane
        self.main_pane = ttk.PanedWindow(self.main_wrapper, orient=tk.HORIZONTAL)
        self.main_pane.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        self.left_frame = ttk.Frame(self.main_pane)
        self.right_frame = ttk.Frame(self.main_pane)
        
        # 严格分配 80% 和 20% 空间 (4:1)
        self.main_pane.add(self.left_frame, weight=4)
        self.main_pane.add(self.right_frame, weight=1)
        
        # Build panels
        self.build_left_panel(self.left_frame)
        self.build_right_panel(self.right_frame)
        
        self.update_states()
        
        # 绑定快捷键
        self.root.bind('<Control-a>', lambda e: self.select_all())
        self.root.bind('<Control-A>', lambda e: self.select_all())
        self.root.bind('<Return>', lambda e: self.run_process())

    def build_left_panel(self, parent):
        # 1. 快速筛选面板
        filter_frame = ttk.LabelFrame(parent, text=" 快速筛选 ")
        filter_frame.pack(fill=tk.X, side=tk.TOP, pady=5)
        
        inner_filter = ttk.Frame(filter_frame, padding=8)
        inner_filter.pack(fill=tk.X)
        
        self.var_bmp = tk.BooleanVar(value=True)
        self.var_jpg = tk.BooleanVar(value=True)
        self.var_png = tk.BooleanVar(value=True)
        self.var_webp = tk.BooleanVar(value=True)
        
        ttk.Checkbutton(inner_filter, text="BMP", variable=self.var_bmp, command=self.apply_filter).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(inner_filter, text="JPEG", variable=self.var_jpg, command=self.apply_filter).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(inner_filter, text="PNG", variable=self.var_png, command=self.apply_filter).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(inner_filter, text="WEBP", variable=self.var_webp, command=self.apply_filter).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(inner_filter, text="反 选", command=self.select_reverse, width=6).pack(side=tk.RIGHT, padx=5)
        ttk.Button(inner_filter, text="全 选", command=self.select_all, width=6).pack(side=tk.RIGHT, padx=5)

        # 3. 旋转控制面板
        ctrl_top = ttk.Frame(parent)
        ctrl_top.pack(fill=tk.X, side=tk.TOP, pady=5)
        
        rot_frame = ttk.LabelFrame(ctrl_top, text=" 图片旋转 ")
        rot_frame.pack(fill=tk.X, side=tk.TOP, pady=5)
        
        inner_rot = ttk.Frame(rot_frame, padding=8)
        inner_rot.pack(fill=tk.X)
        
        ttk.Button(inner_rot, text="↻ 顺时针 90°", command=lambda: self.rotate_selected(-90)).pack(side=tk.LEFT, padx=5)
        ttk.Button(inner_rot, text="↺ 逆时针 90°", command=lambda: self.rotate_selected(90)).pack(side=tk.LEFT, padx=5)
        ttk.Button(inner_rot, text="✖ 重置旋转", command=lambda: self.rotate_selected(0)).pack(side=tk.LEFT, padx=5)

        # 2. Treeview for image list
        tree_frame = ttk.Frame(parent)
        tree_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)
        
        self.tree = ttk.Treeview(tree_frame, columns=('Name', 'Format', 'Size', 'Rotate'), show='headings', selectmode="extended")
        self.tree.heading('Name', text='文件名称')
        self.tree.column('Name', minwidth=150, width=265, stretch=tk.YES)
        self.tree.heading('Format', text='格式')
        self.tree.column('Format', width=105, anchor='center', stretch=tk.NO)
        self.tree.heading('Size', text='体积')
        self.tree.column('Size', width=105, anchor='e', stretch=tk.NO)
        self.tree.heading('Rotate', text='旋转状态')
        self.tree.column('Rotate', width=105, anchor='center', stretch=tk.NO)
        
        # Tags for zebra striping
        self.tree.tag_configure('even', background='#fafbfc')
        self.tree.tag_configure('odd', background='#ffffff')
        
        yscrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=yscrollbar.set)
        
        self.tree.grid(row=0, column=0, sticky='nsew')
        yscrollbar.grid(row=0, column=1, sticky='ns')
        
        # 绑定原生选择事件，替代原本拦截鼠标左键的逻辑，从而支持 Shift/Ctrl 多选
        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        
        self.refresh_tree()

    def build_right_panel(self, parent):
        padding_opts = {'fill': tk.X, 'padx': 5, 'pady': 5}
        
        # 1. 格式转化 (Format Conversion)
        self.var_format_conv = tk.BooleanVar(value=self.prefs.get('format_conv', False))
        lf_conv = ttk.LabelFrame(parent, text=" 格式转化 ")
        lf_conv.pack(**padding_opts)
        
        inner_conv = ttk.Frame(lf_conv, padding=10)
        inner_conv.pack(fill=tk.BOTH, expand=True)
        
        ttk.Checkbutton(inner_conv, text="启用格式转化", variable=self.var_format_conv, command=lambda: self.on_mode_change('format')).grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        ttk.Label(inner_conv, text="目标图片格式:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.combo_conv = ttk.Combobox(inner_conv, values=["JPEG", "PNG", "WEBP"], state="readonly", width=12)
        self.combo_conv.set(self.prefs.get('combo_conv', 'JPEG'))
        self.combo_conv.grid(row=1, column=1, sticky=tk.W, pady=5, padx=10)
        self.combo_conv.bind('<<ComboboxSelected>>', lambda e: self.update_states())
        
        self.var_conv_type = tk.StringVar(value=self.prefs.get('conv_type', 'quality'))
        self.rb_conv_lossless = ttk.Radiobutton(inner_conv, text="无损转换", variable=self.var_conv_type, value="lossless", command=self.update_states)
        self.rb_conv_lossless.grid(row=2, column=0, sticky=tk.W, pady=5)
        
        self.combo_conv_lossless_level = ttk.Combobox(inner_conv, values=[f"{i}级" for i in range(8)], state="readonly", width=12)
        self.combo_conv_lossless_level.set(self.prefs.get('conv_lossless_lvl', '2级'))
        self.combo_conv_lossless_level.grid(row=2, column=1, sticky=tk.W, pady=5, padx=10)
        
        self.rb_conv_qlty = ttk.Radiobutton(inner_conv, text="质量压缩", variable=self.var_conv_type, value="quality", command=self.update_states)
        self.rb_conv_qlty.grid(row=3, column=0, sticky=tk.W, pady=5)
        
        self.sp_conv_qlty = ttk.Spinbox(inner_conv, from_=5, to=100, width=12)
        self.sp_conv_qlty.set(self.prefs.get('conv_qlty', 80))
        self.sp_conv_qlty.grid(row=3, column=1, sticky=tk.W, pady=5, padx=10)

        # 2. 质量压缩 (Quality Compression)
        self.var_qlty_cmp = tk.BooleanVar(value=self.prefs.get('qlty_cmp', False))
        lf_qlty = ttk.LabelFrame(parent, text=" 质量压缩 (限 JPEG、WEBP) ")
        lf_qlty.pack(**padding_opts)
        
        inner_qlty = ttk.Frame(lf_qlty, padding=10)
        inner_qlty.pack(fill=tk.BOTH, expand=True)
        
        ttk.Checkbutton(inner_qlty, text="启用质量压缩", variable=self.var_qlty_cmp, command=lambda: self.on_mode_change('quality')).grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        ttk.Label(inner_qlty, text="JPEG 输出质量:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.sp_jpeg_qlty = ttk.Spinbox(inner_qlty, from_=5, to=95, width=12)
        self.sp_jpeg_qlty.set(self.prefs.get('jpeg_qlty', 80))
        self.sp_jpeg_qlty.grid(row=1, column=1, sticky=tk.W, pady=5, padx=10)
        
        ttk.Label(inner_qlty, text="WEBP 输出质量:").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.sp_webp_qlty = ttk.Spinbox(inner_qlty, from_=5, to=100, width=12)
        self.sp_webp_qlty.set(self.prefs.get('webp_qlty', 80))
        self.sp_webp_qlty.grid(row=2, column=1, sticky=tk.W, pady=5, padx=10)

        # 3. 位深与无损压缩
        lf_adv = ttk.LabelFrame(parent, text=" 高级压缩 ")
        lf_adv.pack(**padding_opts)
        
        inner_adv = ttk.Frame(lf_adv, padding=10)
        inner_adv.pack(fill=tk.BOTH, expand=True)
        
        self.var_colordepth_cmp = tk.BooleanVar(value=self.prefs.get('depth_cmp', False))
        ttk.Checkbutton(inner_adv, text="启用位深压缩 (PNG转8位)", variable=self.var_colordepth_cmp, command=lambda: self.on_mode_change('advanced')).grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        self.var_lossless_cmp = tk.BooleanVar(value=self.prefs.get('lossless_cmp', False))
        ttk.Checkbutton(inner_adv, text="启用无损压缩", variable=self.var_lossless_cmp, command=lambda: self.on_mode_change('advanced')).grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        
        ttk.Label(inner_adv, text="无损压缩级别:").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.combo_adv_lossless = ttk.Combobox(inner_adv, values=[f"{i}级" for i in range(8)], state="readonly", width=12)
        self.combo_adv_lossless.set(self.prefs.get('lossless_lvl', '2级'))
        self.combo_adv_lossless.grid(row=2, column=1, sticky=tk.W, padx=10)

        # Spacer 占位符
        spacer = ttk.Frame(parent)
        spacer.pack(fill=tk.BOTH, expand=True)

        # 底部执行按钮容器
        self.action_frame = ttk.Frame(parent)
        self.action_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=(0, 0))
        
        self.btn_run = ttk.Button(self.action_frame, text="🚀 执 行 处 理", command=self.run_process, style="Accent.TButton")
        # 加大内边距使主按钮更显眼
        self.btn_run.pack(fill=tk.X, expand=True, ipady=8)

    def on_mode_change(self, active_mode):
        """处理三大压缩类别的互斥逻辑，选取一项时自动取消另外两项的选择状态"""
        if active_mode == 'format' and self.var_format_conv.get():
            self.var_qlty_cmp.set(False)
            self.var_colordepth_cmp.set(False)
            self.var_lossless_cmp.set(False)
        elif active_mode == 'quality' and self.var_qlty_cmp.get():
            self.var_format_conv.set(False)
            self.var_colordepth_cmp.set(False)
            self.var_lossless_cmp.set(False)
        elif active_mode == 'advanced':
            if self.var_colordepth_cmp.get() or self.var_lossless_cmp.get():
                self.var_format_conv.set(False)
                self.var_qlty_cmp.set(False)
        self.update_states()

    def update_states(self):
        """Enable or disable option widgets based on checkbox selections."""
        # 1. Format Conversion Logic (仅处理单选框的互斥与锁定，不再锁定任何数值调节框)
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
            
        self.check_run_state()

    def check_run_state(self):
        """Enable or disable the Run button based on selections."""
        if not hasattr(self, 'btn_run'):
            return
            
        has_selected_imgs = any(img['selected'] for img in self.images)
        has_features = (
            self.var_format_conv.get() or
            self.var_qlty_cmp.get() or
            self.var_colordepth_cmp.get() or
            self.var_lossless_cmp.get() or
            any(img['rotate'] != 0 for img in self.images if img['selected'])
        )
        
        # 必须同时有选中的图片和激活的功能，才能启用执行按钮
        if has_selected_imgs and has_features:
            self.btn_run.config(state=tk.NORMAL)
        else:
            self.btn_run.config(state=tk.DISABLED)

    def refresh_tree(self):
        """Redraws the image list based on current data and filters."""
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
            
            # Format rotation string nicely
            rot = img['rotate']
            if rot == 0: rot_str = ""
            elif rot == -90: rot_str = "↻ 90°"
            elif rot == 90: rot_str = "↺ 90°"
            elif rot == 180: rot_str = "180°"
            else: rot_str = f"{rot}°"
            
            stripe_tag = 'even' if display_idx % 2 == 0 else 'odd'
            # Tag holds the original index in self.images and the stripe styling
            item = self.tree.insert('', tk.END, values=(img['filename'], img['format'], size_str, rot_str), tags=(str(idx), stripe_tag))
            
            # 恢复视觉选中状态
            if img['selected']:
                self.tree.selection_add(item)
                
            display_idx += 1
            
        self._is_refreshing = False
        self.check_run_state()
            
    def on_tree_select(self, event):
        """Syncs native Treeview selection (including Shift/Ctrl multi-select) back to the data model."""
        if getattr(self, '_is_refreshing', False):
            return
            
        selected_items = self.tree.selection()
        # 仅同步当前可见项的选择状态，隐藏(被过滤)的项保持原状态不变
        for item in self.tree.get_children():
            idx = int(self.tree.item(item, 'tags')[0])
            self.images[idx]['selected'] = (item in selected_items)
            
        self.check_run_state()
                    
    def select_all(self):
        """选中当前列表中可见的所有项"""
        for item in self.tree.get_children():
            self.tree.selection_add(item)
        self.on_tree_select(None)
        
    def select_reverse(self):
        """反转当前列表中可见项的选中状态"""
        selected = self.tree.selection()
        for item in self.tree.get_children():
            if item in selected:
                self.tree.selection_remove(item)
            else:
                self.tree.selection_add(item)
        self.on_tree_select(None)
        
    def apply_filter(self):
        self.refresh_tree()

    def rotate_selected(self, angle):
        """Adjust rotation for the currently highlighted Treeview items."""
        for item in self.tree.selection():
            idx = int(self.tree.item(item, 'tags')[0])
            if angle == 0:
                self.images[idx]['rotate'] = 0
            else:
                self.images[idx]['rotate'] = (self.images[idx]['rotate'] + angle) % 360
        self.refresh_tree()

    def _fill_executor(self, opts):
        """流式分块读取核心机制：保持活动任务数量不超过线程数的 2 倍，防止电子书过大撑爆内存"""
        target_active = self.threads * 2
        while len(self.active_futures) < target_active and self.process_queue:
            img_info = self.process_queue.popleft()
            try:
                # 必须在主线程触发宿主的 readfile（避免多线程调用 Sigil API 导致崩溃）
                raw_data = self.bk.readfile(img_info['id'])
                future = self.executor.submit(self.process_single_image, img_info, opts, raw_data)
                self.active_futures[future] = img_info['id']
            except Exception as e:
                print(f"读取图片失败 {img_info['id']}: {e}")
                self.q.put((False, img_info['id'], str(e), None))

    def run_process(self):
        """Prepares options and spawns background threads for image processing."""
        # 如果按钮处于禁用状态（如通过回车快捷键触发时不满足条件），则直接返回
        if str(self.btn_run['state']) == tk.DISABLED:
            return
            
        # --- 数据校验 ---
        invalid = False
        
        def validate_sp(widget, min_v, max_v, default_v):
            try:
                val = int(widget.get())
                if not (min_v <= val <= max_v):
                    raise ValueError
                return val
            except ValueError:
                widget.set(default_v)
                return None

        conv_qlty = validate_sp(self.sp_conv_qlty, 5, 100, 80)
        jpg_qlty = validate_sp(self.sp_jpeg_qlty, 5, 95, 80)
        webp_qlty = validate_sp(self.sp_webp_qlty, 5, 100, 80)
        
        # 提取高级压缩的无损级别下拉框的值
        try:
            adv_lossless_lvl = int(self.combo_adv_lossless.get().replace("级", ""))
        except ValueError:
            adv_lossless_lvl = 2
            
        # 提取格式转换功能专属的无损级别下拉框的值
        try:
            conv_lossless_lvl = int(self.combo_conv_lossless_level.get().replace("级", ""))
        except ValueError:
            conv_lossless_lvl = 2
        
        if None in (conv_qlty, jpg_qlty, webp_qlty):
            # 校验失败，变红提示
            self.btn_run.config(style="Error.TButton", state=tk.DISABLED, text="❌ 执 行 失 败")
            self.root.after(1500, lambda: (
                self.btn_run.config(style="Accent.TButton", text="🚀 执 行 处 理"),
                self.check_run_state()
            ))
            return
            
        # 每次执行前保存配置
        self.save_prefs()
        
        selected_imgs = [img for img in self.images if img['selected']]
        if not selected_imgs:
            return
            
        # Collect configuration parameters
        opts = {
            'do_conv': self.var_format_conv.get(),
            'conv_target': self.combo_conv.get() if self.var_format_conv.get() else None,
            'conv_type': self.var_conv_type.get(),
            'conv_qlty': conv_qlty,
            'conv_lossless_level': conv_lossless_lvl,
            
            'do_qlty': self.var_qlty_cmp.get(),
            'jpg_qlty': jpg_qlty,
            'webp_qlty': webp_qlty,
            
            'do_depth': self.var_colordepth_cmp.get(),
            'do_lossless': self.var_lossless_cmp.get(),
            'lossless_level': adv_lossless_lvl
        }
        
        # Update UI for processing state (更换状态和按钮颜色)
        self.btn_run.config(style="Processing.TButton", state=tk.DISABLED, text="⚙ 正在处理...")
        
        self.success_count = 0
        self.error_count = 0
        self.processed_count = 0
        self.rename_map = {}  # 记录格式转换时的旧文件名与新文件名映射
        self.id_map = {}      # 记录格式转换时的旧ID与新ID映射 (用于 metadata 更新)
        self.href_map = {}    # 记录旧 bookpath 与新 bookpath 映射
        
        # 缓存 EPUB 现有资源清单，用于新文件查重，绝对避免文件 ID 和文件名称冲突
        self._existing_ids = {info[0] for info in self.bk.manifest_iter()}
        self._existing_basenames = {info[1].split('/')[-1] for info in self.bk.manifest_iter()}
        
        # 配置多核并发 (提前初始化以便给 Queue 设置 maxsize)
        self.threads = os.cpu_count() or 4
        self.executor = ThreadPoolExecutor(max_workers=self.threads)
        
        # Communication queue & Thread pool
        self.q = queue.Queue(maxsize=self.threads*4)
        
        self.process_queue = deque(selected_imgs)
        self.active_futures = {}
        
        # 首次注水填满线程池
        self._fill_executor(opts)
            
        # Start checking the queue without freezing UI
        self.root.after(50, lambda: self.check_queue(len(selected_imgs), opts))

    def process_single_image(self, img_info, opts, raw_data):
        """Worker thread function to process a single image strictly using PIL."""
        try:
            img = Image.open(BytesIO(raw_data))
            
            # 1. Rotate Application
            if img_info['rotate']:
                # Expand=True preserves edges for non-square rotations
                img = img.rotate(img_info['rotate'], expand=True)
                
            orig_fmt = img.format if img.format else img_info['format']
            if orig_fmt.upper() == 'JPG': orig_fmt = 'JPEG'
            
            target_fmt = opts['conv_target'] if opts['do_conv'] else orig_fmt
            if target_fmt.upper() == 'JPG': target_fmt = 'JPEG'
            
            # 位深压缩自动跳过非 PNG 格式 (且无其他合并操作时直接跳过处理以避免冗余的编码解码)
            if opts['do_depth'] and not opts['do_lossless']:
                if target_fmt != 'PNG' and not img_info['rotate']:
                    self.q.put((True, img_info['id'], None, target_fmt))
                    return
            
            # Safely handle transparency when converting to JPEG
            if target_fmt == 'JPEG' and img.mode in ('RGBA', 'P', 'LA'):
                bg = Image.new('RGB', img.size, (255, 255, 255))
                if img.mode in ('RGBA', 'LA'):
                    bg.paste(img, mask=img.split()[-1])
                else:
                    bg.paste(img)
                img = bg
                
            # Convert WebP from RGBA to RGB if alpha is empty/unneeded (Optional optimization)
            if target_fmt != 'JPEG' and img.mode not in ('RGB', 'RGBA', 'P'):
                img = img.convert('RGBA')
            
            # 2. Color Depth (8-bit P mode)
            if opts['do_depth'] and target_fmt == 'PNG':
                try:
                    # Attempt imagequant if available in Sigil env
                    import imagequant
                    img = imagequant.quantize_pil_image(img, max_quality=100)
                except ImportError:
                    # Native PIL fallback
                    img = img.convert('P', palette=Image.ADAPTIVE, colors=256)
                
            save_kwargs = {'format': target_fmt}
            
            # 3. Quality configuration
            if opts['do_conv'] and opts['conv_type'] == 'quality':
                if target_fmt in ('JPEG', 'WEBP'):
                    save_kwargs['quality'] = opts['conv_qlty']
            elif opts['do_qlty']:
                if target_fmt == 'JPEG':
                    save_kwargs['quality'] = opts['jpg_qlty']
                elif target_fmt == 'WEBP':
                    save_kwargs['quality'] = opts['webp_qlty']
                    
            # 4. Lossless configuration 
            is_conv_lossless = opts['do_conv'] and opts['conv_type'] == 'lossless'
            if is_conv_lossless or opts['do_lossless']:
                if target_fmt in ('PNG', 'JPEG', 'WEBP'):
                    save_kwargs['optimize'] = True
                    
                # 根据是“格式转换”还是“高级压缩”选用对应的级别值
                lvl = opts['conv_lossless_level'] if is_conv_lossless else opts['lossless_level']
                
                if target_fmt == 'PNG':
                    # PNG 允许的 zlib 压缩范围是 0-9
                    save_kwargs['compress_level'] = min(9, lvl)
                if target_fmt == 'WEBP':
                    save_kwargs['lossless'] = True
                    # WEBP 无损模式下 method 决定压缩耗时和体积（范围 0-6）
                    save_kwargs['method'] = min(6, max(0, lvl - 1))
                    
            # Write compressed output to memory
            out_io = BytesIO()
            img.save(out_io, **save_kwargs)
            new_data = out_io.getvalue()
            
            # 将目标格式 target_fmt 也传递回主线程
            self.q.put((True, img_info['id'], new_data, target_fmt))
            
        except Exception as e:
            self.q.put((False, img_info['id'], str(e), None))

    def check_queue(self, total, opts):
        """Periodic UI-loop function to collect completed tasks and update Sigil."""
        try:
            while True:
                success, img_id, result, target_fmt = self.q.get_nowait()
                self.processed_count += 1
                
                if success:
                    self.success_count += 1
                    
                    if result is None:
                        # 文件被自动跳过（例如非 PNG 格式的位深压缩），无需写入新文件或更改引用
                        pass
                    else:
                        try:
                            # 遵循 Sigil 官方规范：更改格式需新建文件并修改 HTML 引用
                            old_href = self.bk.id_to_href(img_id)
                            old_basename = old_href.split('/')[-1]
                            old_ext = old_basename.rsplit('.', 1)[-1].upper()
                            if old_ext == 'JPG': old_ext = 'JPEG'
                            
                            # 判断是否需要更改后缀名
                            if target_fmt.upper() != old_ext:
                                new_ext = target_fmt.lower()
                                if new_ext == 'jpeg': new_ext = 'jpg'
                                
                                name_part = old_basename.rsplit('.', 1)[0]
                                new_basename = f"{name_part}.{new_ext}"
                                new_id = f"{img_id}_{new_ext}"
                                
                                # ID和文件名去重算法：确保新生成的标识符在整个 EPUB 中绝对唯一
                                counter = 1
                                while new_id in self._existing_ids or new_basename in self._existing_basenames:
                                    new_id = f"{img_id}_{new_ext}_{counter}"
                                    new_basename = f"{name_part}_{counter}.{new_ext}"
                                    counter += 1
                                    
                                self._existing_ids.add(new_id)
                                self._existing_basenames.add(new_basename)
                                
                                # 1. 添加新格式文件  2. 删除旧格式文件  3. 记录映射关系
                                self.bk.addfile(new_id, new_basename, result)
                                self.bk.deletefile(img_id)
                                self.rename_map[old_basename] = new_basename
                                self.id_map[img_id] = new_id
                                
                                # 记录包含文件层次的完整引用路径映射关系
                                if '/' in old_href:
                                    new_href = old_href.rsplit('/', 1)[0] + '/' + new_basename
                                else:
                                    new_href = new_basename
                                self.href_map[old_href] = new_href
                            else:
                                # 格式未变，原地覆盖原有数据即可
                                self.bk.writefile(img_id, result)
                        except Exception as op_err:
                            print(f"Error saving {img_id}: {op_err}")
                            self.error_count += 1
                else:
                    self.error_count += 1
                    print(f"Error processing {img_id}: {result}")
                    
        except queue.Empty:
            pass
            
        # 剥离已完成的任务池引用
        done_futures = [f for f in self.active_futures if f.done()]
        for f in done_futures:
            del self.active_futures[f]
            
        # 及时补充分块读取的任务
        self._fill_executor(opts)
            
        # Completion check
        if self.processed_count >= total:
            self.executor.shutdown(wait=False)
            
            # --- 统一更新受格式转换影响的 HTML 和 CSS 引用 ---
            if hasattr(self, 'rename_map') and self.rename_map:
                self._update_all_references()
                self.rename_map = {}
                self.id_map = {}
                self.href_map = {}
            
            # Reset button state
            self.btn_run.config(style="Accent.TButton", text="🚀 执 行 处 理")
            
            # Refresh internal lists
            self.images = []
            self.init_data()
            self.refresh_tree()
            self.update_states()
        else:
            self.root.after(50, lambda: self.check_queue(total, opts))

    def _update_all_references(self):
        """Updates all HTML and CSS files if image filenames were changed due to format conversion."""
        if not hasattr(self, 'rename_map') or not self.rename_map:
            return
            
        import re
        import posixpath
        from urllib.parse import unquote
        
        def get_bookpath(base_href, rel_path):
            """引入 get_bookpath 用于将相对路径解析为书籍根目录下的绝对 bookpath"""
            return posixpath.normpath(posixpath.join(posixpath.dirname(base_href), rel_path))
        
        # 精确锚定包含引用的标签结构，提取 URL (参考官方 plugin_2.py 做法)
        # 支持匹配： src="...", href="...", xlink:href="..." (添加了 source 标签的支持)
        html_img_pattern = re.compile(r'(<(?:img|image|source)[^>]*?(?:src|xlink:href|href)\s*=\s*)([\'"])(.*?)([\'"])([^>]*?>)', re.IGNORECASE)
        # 支持匹配 srcset="..."
        html_srcset_pattern = re.compile(r'(<(?:img|image|source)[^>]*?srcset\s*=\s*)([\'"])(.*?)([\'"])([^>]*?>)', re.IGNORECASE)
        # 支持匹配 css / html inline style 中的 url(...)
        css_url_pattern = re.compile(r'(\burl\s*\(\s*)([\'"]?)(.*?)([\'"]?\s*\))', re.IGNORECASE)

        def _url_replacer(match, current_file_href, is_html_tag=False):
            if is_html_tag:
                prefix, quote1, href, quote2, suffix = match.groups()
            else:
                prefix, quote1, href, suffix = match.groups()
                quote2 = ""
                
            # 提取 basename (兼容 / # ? 等锚点)
            raw_url = href.split('#')[0].split('?')[0]
            unquoted_url = unquote(raw_url) # 处理 %20 空格等转义字符
            
            # 跳过数据 URL 与外部链接
            if not unquoted_url or unquoted_url.startswith('data:') or unquoted_url.startswith('http'):
                return match.group(0)
                
            book_path = get_bookpath(current_file_href, unquoted_url)
            
            if hasattr(self, 'href_map') and book_path in self.href_map:
                new_book_path = self.href_map[book_path]
                
                # 引入 bk.get_relativepath 对处理逻辑进一步优化，基于目标文件与当前宿主文件间的相对层级还原相对路径
                try:
                    new_rel_path = self.bk.get_relativepath(current_file_href, new_book_path)
                except AttributeError:
                    # Fallback 处理：兼容可能没有暴露此原生 API 的早期版本 Sigil
                    new_rel_path = posixpath.relpath(new_book_path, posixpath.dirname(current_file_href))
                    
                # 还原锚点和查询参数
                suffix_idx = len(raw_url)
                remainder = href[suffix_idx:]
                href = new_rel_path + remainder
                
            else:
                # Fallback: 保留原有的按文件名末尾匹配的逻辑（作为在某些极端情况下路径未能精确计算时的备份措施）
                raw_basename = raw_url.split('/')[-1]
                if raw_basename in self.rename_map:
                    new_basename = self.rename_map[raw_basename]
                    href = href[:href.rfind(raw_basename)] + new_basename
                
            return f"{prefix}{quote1}{href}{quote2}{suffix}" if is_html_tag else f"{prefix}{quote1}{href}{suffix}"

        def _srcset_replacer(match, current_file_href):
            prefix, quote1, srcset_val, quote2, suffix = match.groups()
            
            parts = srcset_val.split(',')
            new_parts = []
            for part in parts:
                stripped_part = part.strip()
                if not stripped_part:
                    continue
                
                # srcset 的每一项可能包含 URL 和 尺寸描述符 (如 "image.jpg 2x")
                tokens = stripped_part.split()
                if not tokens:
                    new_parts.append(part)
                    continue
                    
                raw_url = tokens[0]
                unquoted_url = unquote(raw_url.split('#')[0].split('?')[0])
                
                if not unquoted_url or unquoted_url.startswith('data:') or unquoted_url.startswith('http'):
                    new_parts.append(part)
                    continue
                    
                book_path = get_bookpath(current_file_href, unquoted_url)
                new_url = raw_url
                
                if hasattr(self, 'href_map') and book_path in self.href_map:
                    new_book_path = self.href_map[book_path]
                    
                    try:
                        new_rel_path = self.bk.get_relativepath(current_file_href, new_book_path)
                    except AttributeError:
                        new_rel_path = posixpath.relpath(new_book_path, posixpath.dirname(current_file_href))
                        
                    suffix_idx = len(raw_url.split('#')[0].split('?')[0])
                    new_url = new_rel_path + raw_url[suffix_idx:]
                else:
                    # Fallback 处理
                    raw_basename = unquoted_url.split('/')[-1]
                    if raw_basename in self.rename_map:
                        new_basename = self.rename_map[raw_basename]
                        new_url = raw_url[:raw_url.rfind(raw_basename)] + new_basename
                        
                tokens[0] = new_url
                new_parts.append(" ".join(tokens))
                
            new_srcset = ", ".join(new_parts)
            return f"{prefix}{quote1}{new_srcset}{quote2}{suffix}"

        # 遍历更新所有 HTML 文件
        for html_id, html_href in self.bk.text_iter():
            try:
                html_data = self.bk.readfile(html_id)
                is_bytes = isinstance(html_data, bytes)
                text = html_data.decode('utf-8') if is_bytes else html_data
                
                # 更新 <img> / <image> / <source> 标签的普通引用
                new_text = html_img_pattern.sub(lambda m: _url_replacer(m, html_href, is_html_tag=True), text)
                # 更新 srcset 属性
                new_text = html_srcset_pattern.sub(lambda m: _srcset_replacer(m, html_href), new_text)
                # 更新内联 style url()
                new_text = css_url_pattern.sub(lambda m: _url_replacer(m, html_href, is_html_tag=False), new_text)
                
                if text != new_text:
                    self.bk.writefile(html_id, new_text.encode('utf-8') if is_bytes else new_text)
            except Exception as e:
                print(f"Failed to update HTML references in {html_href}: {e}")

        # 遍历更新所有 CSS 文件
        if hasattr(self.bk, 'css_iter'):
            for css_id, css_href in self.bk.css_iter():
                try:
                    css_data = self.bk.readfile(css_id)
                    is_bytes = isinstance(css_data, bytes)
                    text = css_data.decode('utf-8') if is_bytes else css_data
                    
                    # 注入当前所在的 CSS href 
                    new_text = css_url_pattern.sub(lambda m: _url_replacer(m, css_href, is_html_tag=False), text)
                    
                    if text != new_text:
                        self.bk.writefile(css_id, new_text.encode('utf-8') if is_bytes else new_text)
                except Exception as e:
                    print(f"Failed to update CSS references in {css_href}: {e}")
                    
        # --- 核心新增：同步更新 OPF Metadata 中的封面引用 ---
        if hasattr(self, 'id_map') and self.id_map:
            try:
                metadata = self.bk.getmetadataxml()
                if metadata:
                    def _meta_replacer(m):
                        tag = m.group(0)
                        # 查找 content="..." 提取关联的 ID
                        c_match = re.search(r'(content\s*=\s*[\'"])(.*?)([\'"])', tag, re.IGNORECASE)
                        if c_match:
                            old_id = c_match.group(2)
                            if old_id in self.id_map:
                                return tag[:c_match.start(2)] + self.id_map[old_id] + tag[c_match.end(2):]
                        return tag
                        
                    # 正反两套顺序兼容匹配（匹配 name="cover" 或者先 content="..." 后 name="cover"）
                    new_metadata = re.sub(r'<[a-zA-Z0-9:]*?meta\s+[^>]*?name\s*=\s*[\'"]cover[\'"][^>]*?>', _meta_replacer, metadata, flags=re.IGNORECASE)
                    if new_metadata == metadata:
                        new_metadata = re.sub(r'<[a-zA-Z0-9:]*?meta\s+[^>]*?content\s*=\s*[\'"][^\'"]*[\'"][^>]*?name\s*=\s*[\'"]cover[\'"][^>]*?>', _meta_replacer, metadata, flags=re.IGNORECASE)
                        
                    if new_metadata != metadata:
                        self.bk.setmetadataxml(new_metadata)
            except Exception as e:
                print(f"Failed to update metadata cover ID: {e}")

def run(bk):
    """
    Standard Sigil Plugin Entry Function.
    This replaces PyQt references with an isolated Tkinter app suitable for single-file deployment.
    """
    # 增强跨平台 UI 兼容性：主动设置 Windows 高 DPI 缩放感知
    if sys.platform == 'win32':
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

    # 环境与依赖完整性检查
    err_msg = check_dependencies()
    if err_msg:
        # 将错误弹窗逻辑嵌入到入口处，防止阻塞加载并给出对应的修复指令
        err_root = tk.Tk()
        err_root.withdraw()
        
        guide_win = tk.Toplevel()
        guide_win.title("⚠️ 插件环境异常")
        guide_win.geometry("600x360")
        
        # 跨平台字体回退机制
        ui_font = ("微软雅黑" if sys.platform == "win32" else "Helvetica Neue" if sys.platform == "darwin" else "sans-serif", 10)
        code_font = ("Consolas" if sys.platform == "win32" else "Menlo" if sys.platform == "darwin" else "monospace", 10)
        
        # 窗口居中
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
        
        # 生成对应的 pip 安装命令
        cmd_str = f'pip install Pillow imagequant --target="{str(_VENDOR_DIR)}"'
        
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

    # Boot Application
    try:
        root = tk.Tk()
        app = CompressApp(root, bk)
        # 绑定窗口关闭事件，在退出时自动保存一次配置
        root.protocol("WM_DELETE_WINDOW", lambda: (app.save_prefs(), root.destroy()))
        root.mainloop()
    except Exception as e:
        print(traceback.format_exc())
        return -1

    return 0

# For localized testing outside of Sigil
if __name__ == "__main__":
    print("此脚本作为 Sigil 插件设计。请在 Sigil 环境中将其作为插件运行。")
    # Uncomment to test UI locally without e-book context (Will load empty list)
    # root = tk.Tk()
    # app = CompressApp(root, None)
    # root.mainloop()