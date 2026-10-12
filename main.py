import asyncio
import contextlib
import io
import os
import re
import tempfile
import time
from functools import lru_cache
from pathlib import Path

import aiohttp
from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageFont

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.message_components import File as FileComponent
from astrbot.api.star import Context, Star, register

API = "https://jiezhi.xyz/mini"
MAP_API = "https://jiezhi.xyz/mini/map"
COVER_API = "https://jiezhi.xyz/mini/cover"
DOWNLOAD_API = "https://jiezhi.xyz/mini/download"
SITE_DOWNLOAD = "https://sjy1218.com/api/mapdownload/download"
BG_URL = "https://api.yppp.net/pc.php"
BG_OPACITY = 0.20          # 背景照片可见度，即 80% 透明度
GLASS_BLUR = 26            # 毛玻璃模糊半径
GLASS_LIFT = 1.22          # 玻璃面板对背景的提亮系数
MAX_CARDS = 30             # /map 作品卡片最多渲染的张数

USAGE_MAP = "❌错误 用法/map 迷你号或地图id"
USAGE_MAPS = "❌错误 用法/maps 迷你号或地图id"
USAGE_DOWN = "❌错误 用法/down 地图id"

_cover_cache = {}

FONT_CANDIDATES = [
    str(Path(__file__).resolve().parent / "LXGWBright-Medium.ttf"),
    "/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc",
    "/usr/share/fonts/truetype/wqy/wqy-microhei.ttc",
    "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    "C:/Windows/Fonts/msyh.ttc",
]

RENDER_NOTICE_DELAY = 5    # 渲染超过该秒数仍未完成则提醒用户等待

W = 1600
MARGIN = 40
PAD = 34
GAP = 24
RADIUS = 24
C_TITLE = (248, 251, 255)
C_SEC = (120, 226, 205)
C_TEXT = (232, 240, 250)
C_MUTED = (154, 174, 198)
C_ACCENT = (255, 190, 105)

_last_bg = None


@lru_cache(maxsize=24)
def _font(size):
    for path in FONT_CANDIDATES:
        if Path(path).is_file():
            return ImageFont.truetype(path, size)
    raise RuntimeError("系统中找不到可用的中文字体")


def _wrap(meas, text, font, max_w):
    text = "" if text is None else str(text)
    out = []
    for raw in text.split("\n"):
        raw = raw.rstrip()
        if not raw:
            out.append("")
            continue
        line = ""
        for ch in raw:
            if meas.textlength(line + ch, font=font) <= max_w:
                line += ch
            else:
                out.append(line)
                line = ch
        out.append(line)
    return out


def _fmt(value):
    if value is None:
        return "未知"
    if isinstance(value, bool):
        return "是" if value else "否"
    return str(value)


def _fit_text(meas, text, font, max_w):
    """超出宽度则截断并加省略号。"""
    text = _fmt(text)
    if meas.textlength(text, font=font) <= max_w:
        return text
    while text and meas.textlength(text + "…", font=font) > max_w:
        text = text[:-1]
    return text + "…"


def _rounded_mask(size, radius):
    mask = Image.new("L", size, 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, size[0] - 1, size[1] - 1), radius=radius, fill=255)
    return mask


def _cover_fit(img, w, h):
    """等比缩放并居中裁剪到指定尺寸。"""
    img = img.convert("RGB")
    scale = max(w / img.width, h / img.height)
    nw, nh = max(w, int(img.width * scale + 0.5)), max(h, int(img.height * scale + 0.5))
    img = img.resize((nw, nh), Image.LANCZOS)
    left, top = (nw - w) // 2, (nh - h) // 2
    return img.crop((left, top, left + w, top + h))


def _rounded_image(img, radius):
    img = img.convert("RGBA")
    img.putalpha(_rounded_mask(img.size, radius))
    return img


def _placeholder_cover(w, h, name=""):
    """封面缺失或 404 时的兜底图：主题色渐变 + 「暂无封面」。尺寸与真实封面一致。"""
    w, h = max(2, int(w)), max(2, int(h))
    img = Image.new("RGB", (w, h))
    d = ImageDraw.Draw(img)
    top, bottom = (30, 40, 58), (17, 24, 38)
    for y in range(h):
        t = y / (h - 1)
        d.line((0, y, w, y), fill=(
            int(top[0] + (bottom[0] - top[0]) * t),
            int(top[1] + (bottom[1] - top[1]) * t),
            int(top[2] + (bottom[2] - top[2]) * t),
        ))
    # 右侧柔和光斑，避免整块死板
    glow = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((int(w * 0.55), int(-h * 0.35), int(w * 1.35), int(h * 0.75)),
               fill=(86, 214, 190, 26))
    img = Image.alpha_composite(img.convert("RGBA"), glow).convert("RGB")
    ImageDraw.Draw(img).text(
        (w / 2, h / 2), "暂无封面",
        font=_font(max(18, min(26, int(h * 0.1)))), fill=(126, 146, 170), anchor="mm")
    return img


class Canvas:
    """先量高后绘制；面板以毛玻璃方式呈现。"""

    def __init__(self):
        self.boxes = []
        self.fg = []
        self.y = MARGIN
        self.f_title = _font(56)
        self.f_sec = _font(36)
        self.f_name = _font(30)
        self.f_text = _font(26)
        self.f_small = _font(22)
        self.meas = ImageDraw.Draw(Image.new("RGB", (8, 8)))
        self.inner = W - 2 * MARGIN - 2 * PAD

    def add_box(self, box, cmds):
        self.boxes.append(box)
        for kind, args in cmds:
            if kind == "text":
                x, dy, text, font, fill = args
                self.fg.append(("text", (box[0] + x, box[1] + dy, text, font, fill)))
            elif kind == "image":
                img, x, dy = args
                self.fg.append(("image", (img, box[0] + x, box[1] + dy)))

    def panel(self, height, cmds):
        box = (MARGIN, self.y, W - MARGIN, self.y + height)
        self.add_box(box, cmds)
        self.y += height + GAP

    def sec_header(self, lines, note=""):
        """标题面板：lines 为 [(文本, 字体, 颜色), ...]。"""
        cmds = []
        y = PAD
        for text, font, color in lines:
            cmds.append(("text", (PAD, y, text, font, color)))
            y += 70 if font is self.f_title else 44
        if note:
            cmds.append(("text", (PAD, y, note, self.f_small, C_MUTED)))
            y += 34
        self.panel(y + 6, cmds)

    def sec_card_grid(self, cards, cols=3, gap=24):
        """卡片网格：每张卡独立成一块毛玻璃，上方封面，下方信息。"""
        if not cards:
            return
        card_w = (W - 2 * MARGIN - gap * (cols - 1)) // cols
        pad = 20
        cover_w = card_w - 2 * pad
        cover_h = int(cover_w * 9 / 16)
        text_top = pad + cover_h + 16
        card_h = text_top + 40 * 2 + 34 + 32
        rows = [cards[i:i + cols] for i in range(0, len(cards), cols)]
        for row in rows:
            for idx, card in enumerate(row):
                x0 = MARGIN + idx * (card_w + gap)
                box = (x0, self.y, x0 + card_w, self.y + card_h)
                cmds = []
                cov = card.get("cover")
                if cov is None:
                    cov = _placeholder_cover(cover_w, cover_h, card.get("name"))
                cmds.append(("image", (_rounded_image(
                    _cover_fit(cov, cover_w, cover_h), 14), pad, pad)))
                name_lines = _wrap(self.meas, _fmt(card.get("name")), self.f_name, cover_w)
                if len(name_lines) > 2:
                    name_lines = name_lines[:2]
                    tail = name_lines[1]
                    while tail and self.meas.textlength(tail + "…", font=self.f_name) > cover_w:
                        tail = tail[:-1]
                    name_lines[1] = tail + "…"
                y = text_top
                for ln in name_lines:
                    cmds.append(("text", (pad, y, ln, self.f_name, C_TITLE)))
                    y += 40
                y = text_top + 80
                for ln in card.get("lines", []):
                    cmds.append(("text", (pad, y, ln, self.f_small, C_MUTED)))
                    y += 32
                self.add_box(box, cmds)
            self.y += card_h + gap

    def sec_table(self, title, headers, rows, widths, aligns, extra=""):
        """无框线表格：仅按列对齐文字，不画任何格线。"""
        cmds = []
        top = self.title(cmds, title, extra)
        y = top
        x = 0
        for head, wide in zip(headers, widths):
            cmds.append(("text", (PAD + x, y, head, self.f_small, C_SEC)))
            x += wide
        y += 44
        for row in rows:
            x = 0
            for cell, wide, align in zip(row, widths, aligns):
                txt = _fit_text(self.meas, cell, self.f_small, wide - 14)
                tx = PAD + x
                if align == "r":
                    tx = PAD + x + wide - 14 - int(self.meas.textlength(txt, font=self.f_small))
                cmds.append(("text", (tx, y, txt, self.f_small, C_TEXT)))
                x += wide
            y += 44
        self.panel(y + 4, cmds)

    def title(self, cmds, text, extra=""):
        cmds.append(("text", (PAD, PAD - 4, text, self.f_sec, C_SEC)))
        if extra:
            tw = self.meas.textlength(text, font=self.f_sec)
            cmds.append(("text", (PAD + tw + 16, PAD + 6, extra, self.f_small, C_MUTED)))
        return PAD + 56

    def chip(self, label, value):
        return [(f"{label} ", self.f_small, C_MUTED), (_fmt(value), self.f_text, C_TEXT)]

    def flow(self, cmds, items, top, line_h=48, gap=36):
        x, y = 0, top
        for segs in items:
            width = sum(self.meas.textlength(t, font=f) for t, f, _ in segs)
            if x > 0 and x + width > self.inner:
                x, y = 0, y + line_h
            for t, f, c in segs:
                cmds.append(("text", (PAD + int(x), int(y), t, f, c)))
                x += self.meas.textlength(t, font=f)
            x += gap
        return (y - top) + line_h

    def sec_flow(self, title, items, extra=""):
        if not items:
            return
        cmds = []
        top = self.title(cmds, title, extra or f"共 {len(items)} 项")
        used = self.flow(cmds, items, top)
        self.panel(top + used + 8, cmds)

    def sec_text(self, title, text, extra=""):
        if not text:
            return
        cmds = []
        top = self.title(cmds, title, extra)
        y = top
        for ln in _wrap(self.meas, _fmt(text), self.f_text, self.inner - 8):
            cmds.append(("text", (PAD + 8, y, ln, self.f_text, C_TEXT)))
            y += 38
        self.panel(y + 8, cmds)

    def sec_map_header(self, info, cover_img):
        cmds = []
        y = PAD
        img_h = max(340, min(int(self.inner * 9 / 16), 660))
        if cover_img is None:
            cover_img = _placeholder_cover(self.inner, img_h, _fmt(info.get("name")))
        cmds.append(("image", (_rounded_image(
            _cover_fit(cover_img, self.inner, img_h), 18), PAD, y)))
        y += img_h + 26
        for ln in _wrap(self.meas, _fmt(info.get("name")), self.f_title, self.inner):
            cmds.append(("text", (PAD, y, ln, self.f_title, C_TITLE)))
            y += 66
        y += 6
        cmds.append(("text", (PAD, y, f"作者 {_fmt(info.get('author'))} · 地图ID {_fmt(info.get('wid'))}",
                              self.f_name, C_ACCENT)))
        y += 46
        self.panel(y + 8, cmds)

    def sec_works(self, title, works):
        if not works:
            return
        cmds = []
        top = self.title(cmds, title, f"共 {len(works)} 项")
        y = top
        for w in works:
            row = [
                (_fmt(w.get("name")), self.f_name, C_TITLE),
                (f"  [{_fmt(w.get('type'))}]", self.f_small, C_ACCENT),
                (f"  下载 {_fmt(w.get('download'))} · 点赞 {_fmt(w.get('like'))} · {_fmt(w.get('create_time'))}", self.f_small, C_MUTED),
            ]
            if sum(self.meas.textlength(t, font=f) for t, f, _ in row) > self.inner:
                row = row[:2]
            x = 0
            for t, f, c in row:
                cmds.append(("text", (PAD + int(x), int(y), t, f, c)))
                x += self.meas.textlength(t, font=f)
            y += 46
            intro = _fmt(w.get("intro"))
            if intro not in ("暂无详细简介", "未知", "None", ""):
                for ln in _wrap(self.meas, intro, self.f_small, self.inner - 8):
                    cmds.append(("text", (PAD + 8, y, ln, self.f_small, C_TEXT)))
                    y += 32
            y += 14
        self.panel(y + 8, cmds)

    def sec_posts(self, title, posts):
        if not posts:
            return
        cmds = []
        top = self.title(cmds, title, f"共 {len(posts)} 条")
        y = top
        for p in posts:
            for ln in _wrap(self.meas, _fmt(p.get("content")), self.f_text, self.inner - 8):
                cmds.append(("text", (PAD + 8, y, ln, self.f_text, C_TEXT)))
                y += 38
            meta = f"{_fmt(p.get('location'))} · 点赞 {_fmt(p.get('likes'))} · 评论 {_fmt(p.get('comments'))} · {_fmt(p.get('create_time'))}"
            cmds.append(("text", (PAD + 8, y, meta, self.f_small, C_MUTED)))
            y += 40
        self.panel(y + 8, cmds)

    def header(self, user, avatar_img):
        sig = _wrap(self.meas, _fmt(user.get("signature")), self.f_text, self.inner - 230)
        height = PAD * 2 + max(184, 104 + len(sig) * 36)
        cmds = []
        if avatar_img is not None:
            cmds.append(("image", (avatar_img, PAD, PAD)))
        x = PAD + 208
        name = _fmt(user.get("nickname"))
        while self.meas.textlength(name, font=self.f_title) > self.inner - 240 and len(name) > 4:
            name = name[:-2]
        cmds.append(("text", (x, PAD + 2, name, self.f_title, C_TITLE)))
        cmds.append(("text", (x, PAD + 76, f"迷你号 {_fmt(user.get('uid'))}", self.f_name, C_ACCENT)))
        for j, ln in enumerate(sig):
            cmds.append(("text", (x, PAD + 120 + j * 36, ln, self.f_text, C_MUTED)))
        self.panel(height, cmds)

    def finish(self):
        return max(self.y - GAP + MARGIN, 600), self.boxes, self.fg


def _circle(img, size):
    img = img.convert("RGBA")
    side = min(img.size)
    left = (img.width - side) // 2
    top = (img.height - side) // 2
    img = img.crop((left, top, left + side, top + side)).resize((size, size), Image.LANCZOS)
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size - 1, size - 1), fill=255)
    base = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    base.paste(img, (0, 0), mask)
    ImageDraw.Draw(base).ellipse((1, 1, size - 2, size - 2), outline=(255, 255, 255, 110), width=3)
    return base


def _compose(c, bg_bytes):
    """按毛玻璃方案合成整图。"""
    height, boxes, fg = c.finish()
    base = Image.new("RGB", (W, height), (10, 14, 24))
    if bg_bytes:
        try:
            photo = Image.open(io.BytesIO(bg_bytes)).convert("RGB")
            target_ratio = W / height
            if photo.width / photo.height > target_ratio:
                cw = max(1, int(photo.height * target_ratio))
                left = (photo.width - cw) // 2
                photo = photo.crop((left, 0, left + cw, photo.height))
            else:
                ch = max(1, int(photo.width / target_ratio))
                top = (photo.height - ch) // 2
                photo = photo.crop((0, top, photo.width, top + ch))
            photo = photo.resize((W, height), Image.LANCZOS)
            base = Image.blend(base, photo, BG_OPACITY)
        except Exception as exc:
            logger.warning("背景图处理失败，使用纯色底: %s", type(exc).__name__)

    blurred = base.filter(ImageFilter.GaussianBlur(GLASS_BLUR))
    lifted = ImageEnhance.Brightness(blurred).enhance(GLASS_LIFT)
    for box in boxes:
        base.paste(lifted.crop(box), (box[0], box[1]),
                   _rounded_mask((box[2] - box[0], box[3] - box[1]), RADIUS))

    glass = Image.new("RGBA", (W, height), (0, 0, 0, 0))
    gd = ImageDraw.Draw(glass)
    for box in boxes:
        gd.rounded_rectangle(box, radius=RADIUS, fill=(255, 255, 255, 22))
        gd.rounded_rectangle(box, radius=RADIUS, outline=(255, 255, 255, 58), width=2)
        gd.line((box[0] + RADIUS, box[1] + 1, box[2] - RADIUS, box[1] + 1), fill=(255, 255, 255, 92), width=2)
    base = Image.alpha_composite(base.convert("RGBA"), glass).convert("RGB")

    draw = ImageDraw.Draw(base)
    for kind, args in fg:
        if kind == "text":
            x, y, text, font, fill = args
            draw.text((x, y), text, font=font, fill=fill)
        elif kind == "image":
            img, x, y = args
            base.paste(img, (x, y), img)

    draw.text((MARGIN + PAD, height - 46), "数据来源 sjy1218.com · 仅供参考，禁止商用",
              font=c.f_small, fill=(150, 168, 190))
    return base


def _save(img):
    fd, path = tempfile.mkstemp(prefix="astrbot-mini-", suffix=".jpg")
    os.close(fd)
    try:
        img.save(path, "JPEG", quality=86, optimize=True)
        if os.path.getsize(path) > 8 * 1024 * 1024:
            img.save(path, "JPEG", quality=72, optimize=True)
    except Exception:
        if os.path.isfile(path):
            os.unlink(path)
        raise
    return path


def render(user, bg_bytes=None, avatar_bytes=None):
    c = Canvas()

    avatar_img = None
    if avatar_bytes:
        try:
            avatar_img = _circle(Image.open(io.BytesIO(avatar_bytes)), 176)
        except Exception:
            avatar_img = None

    c.header(user, avatar_img)

    medal = user.get("current_medal") or {}
    info = []
    for label, value in [
        ("等级", f"Lv.{_fmt(user.get('player_level'))}"),
        ("信用分", user.get("credit_score")),
        ("粉丝", user.get("fans")),
        ("关注", user.get("following")),
        ("好友", user.get("mutuals")),
        ("成就点", user.get("achieve_points")),
        ("魅力值", user.get("charm_value")),
        ("人气值", user.get("popularity")),
        ("创作者", f"Lv.{_fmt(user.get('creator_level'))}"),
        ("累计下载", user.get("total_downloads")),
        ("地图", user.get("map_count")),
        ("模组", user.get("module_count")),
        ("已认证模组", user.get("certified_module_count")),
        ("模组获赞", user.get("module_likes")),
        ("注册", user.get("reg_time")),
        ("最近登录", user.get("last_login_time")),
        ("段位", user.get("match_level")),
        ("对局", user.get("match_count")),
        ("胜利", user.get("victory_count")),
        ("对局积分", user.get("match_score")),
        ("胜率", (f"{float(user.get('victory_count', 0)) / float(user.get('match_count', 1)) * 100:.1f}%"
                 if user.get("match_count") else "暂无")),
    ]:
        info.append(c.chip(label, value))
    c.sec_flow("个人资料", info, extra=f"共 {len(info)} 项")

    dress = []
    for label, value in [
        ("皮肤", user.get("current_skin")),
        ("坐骑", user.get("current_mount")),
        ("武器", user.get("current_weapon")),
        ("头像框", user.get("current_head_frame")),
        ("称号", user.get("current_title")),
        ("佩戴徽章", medal.get("title_id")),
        ("徽章等级", f"Lv.{_fmt(medal.get('level'))}"),
    ]:
        dress.append(c.chip(label, value))
    c.sec_flow("当前装扮", dress)

    works = [w for w in (user.get("works") or []) if isinstance(w, dict)]
    c.sec_works("作品", works)

    posts = [p for p in (user.get("posts") or []) if isinstance(p, dict)]
    c.sec_posts("动态", posts)

    c.sec_flow("最佳拍档", [
        [(_fmt(p.get("nickname")), c.f_text, C_TITLE),
         (f" UID {_fmt(p.get('uin'))} · 默契 {_fmt(p.get('tacitnum'))} · {_fmt(p.get('create_time'))}", c.f_small, C_MUTED)]
        for p in (user.get("partners") or []) if isinstance(p, dict)
    ])

    c.sec_flow("称号", [
        [(_fmt(t.get("name")), c.f_text, C_TITLE), (f" {_fmt(t.get('get_time'))}", c.f_small, C_MUTED)]
        for t in (user.get("all_titles") or []) if isinstance(t, dict)
    ])

    c.sec_flow("勋章", [
        [(f"徽章{_fmt(m.get('title_id'))}", c.f_text, C_TITLE),
         (f" Lv.{_fmt(m.get('max_level'))} · {_fmt(m.get('finished'))}", c.f_small, C_MUTED)]
        for m in (user.get("medals") or []) if isinstance(m, dict)
    ])

    c.sec_flow("头像框", [
        [(_fmt(h.get("name")), c.f_text, C_TITLE), (f" {_fmt(h.get('get_time'))}", c.f_small, C_MUTED)]
        for h in (user.get("head_frames") or []) if isinstance(h, dict)
    ])

    c.sec_flow("皮肤", [
        [(_fmt(s.get("name")), c.f_text, C_TITLE), (f" {_fmt(s.get('id'))}", c.f_small, C_MUTED)]
        for s in (user.get("skins") or []) if isinstance(s, dict)
    ])

    c.sec_flow("坐骑", [
        [(f"{_fmt(m.get('name'))} Lv.{_fmt(m.get('level'))}", c.f_text, C_TITLE), (f" {_fmt(m.get('id'))}", c.f_small, C_MUTED)]
        for m in (user.get("mounts") or []) if isinstance(m, dict)
    ])

    c.sec_flow("武器", [
        [(_fmt(w.get("name")), c.f_text, C_TITLE), (f" {_fmt(w.get('id'))}/{_fmt(w.get('item_id'))}", c.f_small, C_MUTED)]
        for w in (user.get("weapons") or []) if isinstance(w, dict)
    ])

    handled = {
        "uid", "nickname", "signature", "avatar_url", "fans", "following", "mutuals",
        "achieve_points", "charm_value", "popularity", "player_level", "credit_score",
        "creator_level", "total_downloads", "map_count", "module_count",
        "certified_module_count", "module_likes", "match_level", "match_count",
        "victory_count", "match_score", "current_skin", "current_mount", "current_weapon",
        "current_head_frame", "current_medal", "current_title", "reg_time",
        "last_login_time", "works", "posts", "partners", "all_titles", "medals",
        "head_frames", "skins", "mounts", "weapons", "post_count",
    }
    extras = [k for k, v in user.items()
              if k not in handled and not isinstance(v, (list, dict)) and v not in (None, "")]
    if extras:
        c.sec_flow("其他数据", [c.chip(k, user[k]) for k in extras])

    return _save(_compose(c, bg_bytes))


def render_map(info, bg_bytes=None, cover_bytes=None):
    c = Canvas()

    cover_img = None
    if cover_bytes:
        try:
            cover_img = Image.open(io.BytesIO(cover_bytes))
        except Exception:
            cover_img = None

    c.sec_map_header(info, cover_img)

    c.sec_flow("数据表现", [
        c.chip("游玩次数", info.get("play_count")),
        c.chip("下载次数", info.get("download_count")),
        c.chip("本周下载", info.get("week_download")),
        c.chip("点赞", info.get("like")),
        c.chip("收藏", info.get("collect")),
        c.chip("分享", info.get("share")),
        c.chip("点踩", info.get("dislike")),
        c.chip("评分", f"{_fmt(info.get('rating'))} 分（{_fmt(info.get('rating_num'))} 人）"),
    ])

    c.sec_flow("地图信息", [
        c.chip("作者", info.get("author")),
        c.chip("作者ID", info.get("author_uin")),
        c.chip("地图ID", info.get("wid")),
        c.chip("大小", f"{_fmt(info.get('size_mb'))} MB"),
        c.chip("分类标签", info.get("label")),
        c.chip("标签ID", info.get("tags")),
        c.chip("含模组", "是" if info.get("has_mod") else "否"),
        c.chip("云服", "是" if info.get("cloud") else "否"),
        c.chip("创建时间", info.get("create_time")),
        c.chip("更新时间", info.get("update_time")),
        c.chip("节点", info.get("node")),
    ])

    c.sec_text("地图简介", info.get("desc"))

    handled = {
        "wid", "name", "author", "author_uin", "desc", "cover", "size", "size_mb",
        "node", "label", "tags", "has_mod", "cloud", "create_time", "update_time",
        "play_count", "download_count", "week_download", "like", "collect", "share",
        "dislike", "rating", "rating_num", "download_url",
    }
    extras = [k for k, v in info.items()
              if k not in handled and not isinstance(v, (list, dict)) and v not in (None, "")]
    if extras:
        c.sec_flow("其他数据", [c.chip(k, info[k]) for k in extras])

    return _save(_compose(c, bg_bytes))


def _cover_url(work):
    if work.get("cover"):
        return work["cover"]
    day, md5 = work.get("cover_dir"), work.get("cover_md5")
    if day and md5:
        return f"{COVER_API}/{day}/{md5}.png"
    return None


def _work_from_player(work):
    return {
        "name": _fmt(work.get("name")),
        "type": _fmt(work.get("type")),
        "download": work.get("download"),
        "like": work.get("like"),
        "create_time": _fmt(work.get("create_time")),
        "intro": _fmt(work.get("intro")),
        "cover_url": _cover_url(work),
        "is_mod": work.get("is_mod"),
    }


def _work_from_map(info):
    return {
        "name": _fmt(info.get("name")),
        "type": "地图",
        "download": info.get("download_count"),
        "like": info.get("like"),
        "create_time": _fmt(info.get("create_time")),
        "intro": _fmt(info.get("desc")),
        "cover_url": info.get("cover"),
        "is_mod": bool(info.get("has_mod")),
    }


async def _load_ident(session, ident):
    """智能区分迷你号与地图ID：先按位数猜测，失败再试另一种。

    两种都失败时，抛出**主路径**的错误（与输入类型相符），避免用地图的错误
    去回答一个迷你号查询。
    """
    order = ("map", "player") if len(ident) >= 12 else ("player", "map")
    errors = []
    for kind in order:
        try:
            if kind == "player":
                async with session.get(API, params={"uid": ident}) as r:
                    data = await r.json()
                    if r.status != 200:
                        raise ValueError(str(data.get("error", "查询失败"))[:200])
                    user = data.get("user")
                    if not isinstance(user, dict):
                        raise ValueError("接口未返回玩家资料")
                    return "player", user
            async with session.get(MAP_API, params={"wid": ident}) as r:
                data = await r.json()
                if r.status != 200:
                    raise ValueError(str(data.get("error", "查询失败"))[:200])
                info = data.get("map")
                if not isinstance(info, dict):
                    raise ValueError("接口未返回地图资料")
                return "map", info
        except Exception as exc:
            errors.append(str(exc) if isinstance(exc, ValueError) else "查询服务暂不可用")
    main_kind, main_msg = order[0], errors[0]
    if main_kind == "player":
        raise ValueError(f"{main_msg}（已按迷你号查询；若这是地图ID，请确认后重试）")
    raise ValueError(f"{main_msg}（已按地图ID查询；若这是迷你号，请确认后重试）")


async def _fetch_covers(session, works):
    """并发抓取作品封面，带内存缓存与并发上限。

    单张超时收紧到 10 秒：部分小地图本就没有封面（404）或封面直链已过期，
    不能让个别慢请求拖住整张图。
    """
    sem = asyncio.Semaphore(8)

    async def one(work):
        url = work.get("cover_url")
        if not url:
            return None
        if url in _cover_cache:
            return _cover_cache[url]
        async with sem:
            data = await _fetch_image(session, url, timeout=10)
        if data:
            if len(_cover_cache) > 300:
                _cover_cache.clear()
            _cover_cache[url] = data
        return data

    return await asyncio.gather(*(one(w) for w in works))


def _to_pil(data):
    if not data:
        return None
    try:
        return Image.open(io.BytesIO(data))
    except Exception:
        return None


def _cleanup_stale_maps(max_age=3600):
    """清理超过 max_age 秒的临时地图包，避免 /tmp 堆积。"""
    try:
        now = time.time()
        with os.scandir(tempfile.gettempdir()) as it:
            for entry in it:
                if not entry.name.startswith("astrbot-map-"):
                    continue
                try:
                    if entry.is_file() and now - entry.stat().st_mtime > max_age:
                        os.unlink(entry.path)
                except OSError:
                    continue
    except Exception:
        pass


def render_works_cards(title, subtitle, note, works, covers, bg_bytes):
    """作品卡片：每个作品一张卡片，合成一张总图。"""
    c = Canvas()
    lines = [(title, c.f_title, C_TITLE)]
    if subtitle:
        lines.append((subtitle, c.f_name, C_ACCENT))
    c.sec_header(lines, note)

    cards = []
    for work, raw in zip(works, covers):
        cards.append({
            "cover": _to_pil(raw),
            "name": work["name"],
            "lines": [
                f"[{work['type']}] 下载 {_fmt(work['download'])} · 点赞 {_fmt(work['like'])}",
                f"发布 {work['create_time']}",
            ],
        })
    c.sec_card_grid(cards)
    return _save(_compose(c, bg_bytes))


def render_works_table(title, subtitle, works, bg_bytes):
    """maps：无框线表格，按下载量从高到低。"""
    c = Canvas()
    lines = [(title, c.f_title, C_TITLE)]
    if subtitle:
        lines.append((subtitle, c.f_name, C_ACCENT))
    c.sec_header(lines, f"共 {len(works)} 个作品 · 按下载量从高到低")

    widths = [90, 700, 160, 130, 160, 212]
    headers = ["#", "作品名称", "下载量", "点赞", "类型", "发布时间"]
    aligns = ["l", "l", "r", "r", "l", "l"]
    rows = [
        [str(i), w["name"], _fmt(w["download"]), _fmt(w["like"]), w["type"], w["create_time"]]
        for i, w in enumerate(works, 1)
    ]
    c.sec_table("作品列表", headers, rows, widths, aligns, extra=f"共 {len(rows)} 项")
    return _save(_compose(c, bg_bytes))


def map_summary(info):
    return "\n".join([
        f"迷你世界地图 · {_fmt(info.get('name'))}",
        f"地图ID：{_fmt(info.get('wid'))}",
        f"作者：{_fmt(info.get('author'))}（{_fmt(info.get('author_uin'))}）",
        f"游玩 {_fmt(info.get('play_count'))} · 下载 {_fmt(info.get('download_count'))} · 本周下载 {_fmt(info.get('week_download'))}",
        f"点赞 {_fmt(info.get('like'))} · 收藏 {_fmt(info.get('collect'))} · 分享 {_fmt(info.get('share'))} · 点踩 {_fmt(info.get('dislike'))}",
        f"评分 {_fmt(info.get('rating'))} 分（{_fmt(info.get('rating_num'))} 人）",
        f"大小 {_fmt(info.get('size_mb'))} MB · 含模组 {'是' if info.get('has_mod') else '否'} · 云服 {'是' if info.get('cloud') else '否'}",
        f"创建 {_fmt(info.get('create_time'))} · 更新 {_fmt(info.get('update_time'))}",
        f"简介：{_fmt(info.get('desc'))}",
        "数据来源 sjy1218.com · 仅供参考，禁止商用",
    ])


def summary(user):
    def v(key):
        return _fmt(user.get(key))
    lines = [
        f"迷你世界 · {v('nickname')}（迷你号 {v('uid')}）",
        f"签名：{v('signature')}",
        f"等级 {v('player_level')} · 信用分 {v('credit_score')} · 粉丝 {v('fans')} · 关注 {v('following')} · 好友 {v('mutuals')}",
        f"成就 {v('achieve_points')} · 魅力 {v('charm_value')} · 人气 {v('popularity')} · 创作者 Lv.{v('creator_level')}",
        f"累计下载 {v('total_downloads')} · 地图 {v('map_count')} · 模组 {v('module_count')} · 已认证 {v('certified_module_count')}",
        f"段位 {v('match_level')} · 对局 {v('match_count')} · 胜利 {v('victory_count')} · 积分 {v('match_score')}",
        f"皮肤 {v('current_skin')} · 坐骑 {v('current_mount')} · 武器 {v('current_weapon')} · 头像框 {v('current_head_frame')}",
        f"注册 {v('reg_time')} · 最近登录 {v('last_login_time')}",
        f"称号 {len(user.get('all_titles') or [])} · 勋章 {len(user.get('medals') or [])} · 头像框 {len(user.get('head_frames') or [])}",
        f"皮肤 {len(user.get('skins') or [])} · 坐骑 {len(user.get('mounts') or [])} · 武器 {len(user.get('weapons') or [])}",
        f"作品 {len(user.get('works') or [])} · 动态 {len(user.get('posts') or [])} · 拍档 {len(user.get('partners') or [])}",
        "数据来源 sjy1218.com · 仅供参考，禁止商用",
    ]
    return "\n".join(lines)


async def _fetch(session, url, limit=8 * 1024 * 1024, timeout=20):
    if not url:
        return None
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            if r.status != 200:
                return None
            buf = bytearray()
            async for chunk in r.content.iter_chunked(65536):
                buf.extend(chunk)
                if len(buf) > limit:
                    return None
            return bytes(buf) if buf else None
    except Exception:
        return None


async def _fetch_image(session, url, timeout=20):
    """优先 https，失败再退回原始 http。"""
    if not url:
        return None
    if url.startswith("http://"):
        data = await _fetch(session, "https://" + url[7:], timeout=timeout)
        if data:
            return data
    return await _fetch(session, url, timeout=timeout)


async def _notice_after(event, text, delay=None):
    """delay 秒后若任务仍未被取消，则发送提醒。delay 为 None 时读模块常量。"""
    if delay is None:
        delay = RENDER_NOTICE_DELAY
    try:
        await asyncio.sleep(delay)
        await event.send(event.plain_result(text))
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        logger.warning("提示发送失败: %s", type(exc).__name__)


async def _render_notice(event):
    """渲染超过 RENDER_NOTICE_DELAY 秒仍未完成时提醒用户等待。"""
    await _notice_after(event, "⚠️：图片仍在渲染中 请等待！", RENDER_NOTICE_DELAY)


async def _background(session):
    global _last_bg
    bg = await _fetch(session, BG_URL)
    if bg:
        _last_bg = bg
    return bg or _last_bg


@register("astrbot_plugin_mini", "小白", "迷你世界玩家与地图查询：毛玻璃长图优先，文字回退", "1.8.0")
class MiniPlugin(Star):
    def __init__(self, context: Context):
        super().__init__(context)
        self.semaphore = asyncio.Semaphore(2)

    @filter.command("mini")
    async def mini(self, event: AstrMessageEvent, uid: str = ""):
        uid = (uid or "").strip()
        if not re.fullmatch(r"[0-9]{1,20}", uid):
            yield event.plain_result("用法：/mini 迷你号\n例如：/mini 1531249328")
            return

        try:
            async with asyncio.timeout(70):
                async with self.semaphore:
                    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=60)) as session:
                        async with session.get(API, params={"uid": uid}) as r:
                            data = await r.json()
                            if r.status != 200:
                                raise ValueError(str(data.get("error", "查询失败"))[:200])
                            user = data.get("user")
                            if not isinstance(user, dict):
                                raise ValueError("接口未返回玩家资料")
                        bg, avatar = await asyncio.gather(
                            _background(session),
                            _fetch_image(session, user.get("avatar_url")),
                        )
        except TimeoutError:
            yield event.plain_result("查询超时，请稍后再试。")
            return
        except Exception as exc:
            logger.warning("Mini query failed: %s", type(exc).__name__)
            yield event.plain_result(str(exc) if isinstance(exc, ValueError) else "查询服务暂不可用，请稍后再试")
            return

        path = None
        notice = asyncio.create_task(_render_notice(event))
        try:
            path = await asyncio.to_thread(render, user, bg, avatar)
            await event.send(event.image_result(path))
        except Exception as exc:
            logger.warning("Mini image failed, using text: %s", type(exc).__name__)
            yield event.plain_result(summary(user))
        finally:
            notice.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await notice
            if path and os.path.isfile(path):
                os.unlink(path)

    @filter.command("map")
    async def map_query(self, event: AstrMessageEvent, ident: str = ""):
        """地图ID → 单图详情；迷你号 → 该玩家全部作品卡片。"""
        ident = (ident or "").strip()
        if not re.fullmatch(r"[0-9]{1,25}", ident):
            yield event.plain_result("用法：/map 地图ID 或 迷你号\n例如：/map 45557796758440 或 /map 198379")
            return

        try:
            async with asyncio.timeout(70):
                async with self.semaphore:
                    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=60)) as session:
                        kind, payload = await _load_ident(session, ident)
                        if kind == "player":
                            info = None
                        else:
                            info = payload
                            bg, cover = await asyncio.gather(
                                _background(session),
                                _fetch_image(session, info.get("cover")),
                            )
        except TimeoutError:
            yield event.plain_result("查询超时，请稍后再试。")
            return
        except Exception as exc:
            logger.warning("Map query failed: %s", type(exc).__name__)
            yield event.plain_result(str(exc) if isinstance(exc, ValueError) else "查询服务暂不可用，请稍后再试")
            return

        if info is None:
            # 输入是迷你号：走作品卡片渲染
            async for result in self._player_cards(event, ident):
                yield result
            return

        path = None
        notice = asyncio.create_task(_render_notice(event))
        try:
            path = await asyncio.to_thread(render_map, info, bg, cover)
            await event.send(event.image_result(path))
        except Exception as exc:
            logger.warning("Map image failed, using text: %s", type(exc).__name__)
            yield event.plain_result(map_summary(info))
        finally:
            notice.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await notice
            if path and os.path.isfile(path):
                os.unlink(path)

    async def _player_cards(self, event: AstrMessageEvent, ident: str = ""):
        """渲染迷你号下的全部作品，每张卡片一块（由 /map 识别为迷你号时调用）。"""
        ident = (ident or "").strip()
        if not re.fullmatch(r"[0-9]{1,25}", ident):
            yield event.plain_result(USAGE_MAP)
            return

        try:
            async with asyncio.timeout(120):
                async with self.semaphore:
                    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=110)) as session:
                        kind, payload = await _load_ident(session, ident)
                        if kind == "player":
                            works = [_work_from_player(w) for w in (payload.get("works") or [])
                                     if isinstance(w, dict)]
                            title = _fmt(payload.get("nickname"))
                            subtitle = f"迷你号 {_fmt(payload.get('uid'))}"
                        else:
                            works = [_work_from_map(payload)]
                            title = _fmt(payload.get("name"))
                            subtitle = f"地图ID {_fmt(payload.get('wid'))}"
                        total = len(works)
                        works = works[:MAX_CARDS]
                        note = f"共 {total} 个作品"
                        if total > MAX_CARDS:
                            note += f"，仅显示前 {MAX_CARDS} 个"
                        covers = await _fetch_covers(session, works)
                        bg = await _background(session)
        except TimeoutError:
            yield event.plain_result(f"查询超时，请稍后再试\n{USAGE_MAP}")
            return
        except Exception as exc:
            logger.warning("map card query failed: %s", type(exc).__name__)
            msg = str(exc) if isinstance(exc, ValueError) else "查询服务暂不可用，请稍后再试"
            yield event.plain_result(f"{msg}\n{USAGE_MAP}")
            return

        if not works:
            yield event.plain_result(f"该迷你号没有公开作品\n{USAGE_MAP}")
            return

        path = None
        notice = asyncio.create_task(_render_notice(event))
        try:
            path = await asyncio.to_thread(render_works_cards, title, subtitle, note, works, covers, bg)
            await event.send(event.image_result(path))
        except Exception as exc:
            logger.warning("map card render failed: %s", type(exc).__name__)
            yield event.plain_result(f"图片渲染失败，请稍后再试\n{USAGE_MAP}")
        finally:
            notice.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await notice
            if path and os.path.isfile(path):
                os.unlink(path)

    @filter.command("maps")
    async def maps_list(self, event: AstrMessageEvent, ident: str = ""):
        """按下载量从高到低列出作品，无框线表格。"""
        ident = (ident or "").strip()
        if not re.fullmatch(r"[0-9]{1,25}", ident):
            yield event.plain_result(USAGE_MAPS)
            return

        try:
            async with asyncio.timeout(90):
                async with self.semaphore:
                    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=80)) as session:
                        kind, payload = await _load_ident(session, ident)
                        if kind == "player":
                            works = [_work_from_player(w) for w in (payload.get("works") or [])
                                     if isinstance(w, dict)]
                            title = _fmt(payload.get("nickname"))
                            subtitle = f"迷你号 {_fmt(payload.get('uid'))}"
                        else:
                            works = [_work_from_map(payload)]
                            title = _fmt(payload.get("name"))
                            subtitle = f"地图ID {_fmt(payload.get('wid'))}"
                        works.sort(key=lambda w: w.get("download") or 0, reverse=True)
                        bg = await _background(session)
        except TimeoutError:
            yield event.plain_result(f"查询超时，请稍后再试\n{USAGE_MAPS}")
            return
        except Exception as exc:
            logger.warning("maps query failed: %s", type(exc).__name__)
            msg = str(exc) if isinstance(exc, ValueError) else "查询服务暂不可用，请稍后再试"
            yield event.plain_result(f"{msg}\n{USAGE_MAPS}")
            return

        if not works:
            yield event.plain_result(f"该迷你号没有公开作品\n{USAGE_MAPS}")
            return

        path = None
        notice = asyncio.create_task(_render_notice(event))
        try:
            path = await asyncio.to_thread(render_works_table, title, subtitle, works, bg)
            await event.send(event.image_result(path))
        except Exception as exc:
            logger.warning("maps render failed: %s", type(exc).__name__)
            yield event.plain_result(f"图片渲染失败，请稍后再试\n{USAGE_MAPS}")
        finally:
            notice.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await notice
            if path and os.path.isfile(path):
                os.unlink(path)

    @filter.command("down")
    async def down(self, event: AstrMessageEvent, wid: str = ""):
        """发送地图包文件；下载或发送失败则回退为下载链接。"""
        wid = (wid or "").strip()
        if not re.fullmatch(r"[0-9]{1,25}", wid):
            yield event.plain_result(USAGE_DOWN)
            return

        _cleanup_stale_maps()
        info, link, path, fname = None, None, None, None
        # 地图包约 10MB，下载期间给一次提醒，避免看起来像“没反应”
        notice = asyncio.create_task(_notice_after(event, "⚠️：地图文件正在下载中 请等待！"))
        try:
            try:
                async with asyncio.timeout(300):
                    async with self.semaphore:
                        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=280)) as session:
                            try:
                                async with session.get(MAP_API, params={"wid": wid}) as r:
                                    data = await r.json()
                                    if r.status == 200 and isinstance(data.get("map"), dict):
                                        info = data["map"]
                            except Exception:
                                info = None
                            name = (info or {}).get("name") or f"map-{wid}"
                            link = (info or {}).get("download_url") or f"{SITE_DOWNLOAD}?wid={wid}"
                            fd, path = tempfile.mkstemp(prefix="astrbot-map-", suffix=".zip")
                            os.close(fd)
                            async with session.get(DOWNLOAD_API, params={"wid": wid}) as r:
                                if r.status != 200:
                                    try:
                                        err = (await r.json()).get("error")
                                    except Exception:
                                        err = None
                                    raise ValueError(err or "地图文件下载失败")
                                with open(path, "wb") as fh:
                                    async for chunk in r.content.iter_chunked(65536):
                                        fh.write(chunk)
                            if os.path.getsize(path) == 0:
                                raise ValueError("地图文件为空")
                            fname = f"{name}-{wid}.zip"
            except TimeoutError:
                if path and os.path.isfile(path):
                    os.unlink(path)
                yield event.plain_result(
                    f"❌ 地图文件获取超时，请使用下载链接：\n{link or f'{SITE_DOWNLOAD}?wid={wid}'}")
                return
            except Exception as exc:
                if path and os.path.isfile(path):
                    os.unlink(path)
                logger.warning("down fetch failed: %s", type(exc).__name__)
                reason = str(exc) if isinstance(exc, ValueError) else "查询服务暂不可用"
                yield event.plain_result(
                    f"❌ 地图文件获取失败：{reason}\n请使用下载链接：\n{link or f'{SITE_DOWNLOAD}?wid={wid}'}")
                return

            try:
                await event.send(event.chain_result([FileComponent(name=fname, file=path)]))
            except Exception as exc:
                logger.warning("down send failed: %s", type(exc).__name__)
                if os.path.isfile(path):
                    os.unlink(path)
                yield event.plain_result(f"❌ 地图文件发送失败，请使用下载链接：\n{link}")
                return
        finally:
            notice.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await notice

