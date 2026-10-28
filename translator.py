# -*- coding: utf-8 -*-
"""
Экранный переводчик EN -> RU.

Зажми Shift и наведи мышь на английское слово в ЛЮБОМ окне (браузер, игра, Discord...).
Рядом с курсором появится карточка: перевод, предложение целиком, короткие примеры.
Отпусти Shift и в течение 5 секунд нажми ☆ Сохранить, чтобы слово попало в my_words.tsv.

  run.bat    - запуск
  check.bat  - проверка всех компонентов (запусти, если что-то не работает)
"""
from __future__ import annotations

import argparse
import atexit
import ctypes
import dataclasses
import functools
import http.client
import json
import os
import queue
import re
import sys
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime

# ============================ НАСТРОЙКИ ============================
SOURCE_LANG = "en"
TARGET_LANG = "ru"
OCR_LANG = "en"             # язык для Windows OCR
HOTKEY = "shift"            # shift | ctrl | alt
REGION_W = 800              # ширина области вокруг курсора (px): из неё берётся предложение
REGION_H = 160              # высота области (px): несколько строк текста
SCALE = 3                   # во сколько раз увеличивать картинку перед OCR
MAX_OCR_SIDE = 2400         # у Windows OCR есть предел размера картинки
SETTLE_SECONDS = 0.15       # сколько секунд мышь должна стоять, прежде чем искать слово
MOVE_TOLERANCE_PX = 4       # дрожание мыши, которое не считается движением
POLL_MS = 40                # как часто проверять клавишу и мышь
LINGER_SECONDS = 5.0        # сколько окошко остаётся после отпускания Shift (чтобы нажать кнопку)
OVERLAY_OFFSET = REGION_H // 2 + 14   # расстояние от курсора до окошка (больше половины высоты области)
MY_WORDS_FILE = "my_words.tsv"        # сюда попадают слова, сохранённые кнопкой ★
FAST_SETTLE_SECONDS = 0.05  # пауза мыши, если слово можно взять из кэша (без OCR)
CACHE_ENTRIES = 6           # сколько последних распознанных областей помнить
CACHE_MARGIN = (60, 30)     # отступ от края области (px): ближе к краю кэшу не доверяем
CACHE_DIFF_THRESHOLD = 24   # на сколько должен измениться пиксель, чтобы считаться изменённым
CACHE_DIFF_RATIO = 0.002    # доля изменённых пикселей, при которой экран ещё считается прежним
PREFETCH_WORDS = 4          # сколько соседних слов переводить заранее (0 = выключить)
PREFETCH_DELAY = 0.4        # пауза между такими запросами (бережём лимит Google)
HTTP_TIMEOUT = 3            # секунд на ответ сервера перевода
WARM_URL = "https://translate.googleapis.com/"
# ==================================================================

# --- Rust-ускоритель (необязательный). Если не собран - работает Python-версия. ---
try:
    import fast_core as _fast  # type: ignore
except Exception:  # noqa: BLE001
    _fast = None


# ----------------------------- данные -----------------------------
@dataclass
class Word:
    text: str
    x: float
    y: float
    w: float
    h: float


@dataclass
class Shot:
    left: int
    top: int
    width: int
    height: int
    bgra: bytes


@dataclass
class Entry:
    """Всё, что мы знаем о слове под курсором. Заполняется в два этапа."""
    word: str
    translation: str
    box: tuple                                   # (x0, y0, x1, y1) в координатах экрана
    ok: bool = True
    alts: list = field(default_factory=list)     # [[«сущ.», ["банк", "берег"]], ...]
    sentence: str = ""                           # предложение вокруг слова
    sentence_ru: str = ""                        # его перевод
    hit: str = ""                                # вариант слова, найденный в переводе предложения
    examples: list = field(default_factory=list) # [(англ., рус.), ...]
    ipa: str = ""                                # транскрипция
    lemma: str = ""                              # начальная форма (для неправильных глаголов)
    name_hint: bool = False                      # слово похоже на имя собственное
    phrase: str = ""                             # фразовый глагол в тексте: «gave up»
    phrase_base: str = ""                        # его начальная форма: «give up»
    phrase_ru: str = ""                          # перевод фразового глагола
    src: str = ""                                # откуда слова: "ocr" или "cache"
    ms: float = 0.0                              # сколько заняло поиск (мс)


# ------------------------- работа с текстом -------------------------
TOKEN_RE = re.compile(r"[^\W\d_]+(?:['’\-][^\W\d_]+)*")


def clean_token(text):
    """Достаёт из строки OCR чистое слово: 'Dragon,' -> 'Dragon', "king's" -> 'king'."""
    m = TOKEN_RE.search(text or "")
    if not m:
        return None
    tok = m.group(0)
    for suf in ("'s", "’s"):
        if tok.lower().endswith(suf) and len(tok) > 3:
            tok = tok[:-2]
    return tok


def pick_word(words, px, py):
    """Выбирает слово, ближайшее к точке (px, py). Возвращает (Word, чистое_слово) или None."""
    best, best_d = None, None
    for wd in words:
        tok = clean_token(wd.text)
        if not tok:
            continue
        dx = max(wd.x - px, 0, px - (wd.x + wd.w))
        dy = max(wd.y - py, 0, py - (wd.y + wd.h))
        d = (dx * dx + dy * dy) ** 0.5
        if best is None or d < best_d:
            best, best_d = (wd, tok), d
    if best is None:
        return None
    wd, tok = best
    if best_d > wd.h * 0.6:  # курсор слишком далеко от любого слова
        return None
    return wd, tok


# ------------------------- предложение вокруг слова -------------------------
ABBREV = {"mr.", "mrs.", "ms.", "dr.", "st.", "vs.", "etc.", "e.g.", "i.e.", "jr.", "sr.",
          "no.", "prof.", "sir.", "mt."}
_CLOSERS = "\"”’')]»*_"


def ends_sentence(tok):
    t = tok.rstrip(_CLOSERS)
    if not t or t[-1] not in ".!?…":
        return False
    if t.lower() in ABBREV or re.fullmatch(r"[A-Z]\.", t):  # «Mr.», «J.»
        return False
    return True


def group_lines(words):
    """Раскладывает слова OCR по строкам: (список строк, номера строк после которых абзац кончается)."""
    toks = [w for w in words if re.search(r"\w", w.text or "")]
    if not toks:
        return [], set()
    toks.sort(key=lambda w: w.y + w.h / 2)
    med_h = sorted(w.h for w in toks)[len(toks) // 2] or 1
    lines, cur, cur_cy = [], [], None
    for w in toks:
        cy = w.y + w.h / 2
        if cur and abs(cy - cur_cy) > 0.6 * med_h:
            lines.append(cur)
            cur = []
        cur.append(w)
        cur_cy = sum(t.y + t.h / 2 for t in cur) / len(cur)
    lines.append(cur)
    lines = [sorted(l, key=lambda w: w.x) for l in lines]
    centers = [sum(t.y + t.h / 2 for t in l) / len(l) for l in lines]
    pitches = [centers[i + 1] - centers[i] for i in range(len(lines) - 1)]
    breaks = set()
    for i, p in enumerate(pitches):
        # Абзац = зазор заметно больше обычного межстрочного шага (самого маленького из видимых).
        # Если строк мало и шаг сравнить не с чем, берём запас по высоте слов.
        if (len(pitches) >= 2 and p > 1.6 * min(pitches)) or p > 3.0 * med_h:
            breaks.add(i)
    return lines, breaks


def sentence_context(words, target, max_side=35):
    """Предложение, в котором стоит слово `target` (объект Word из списка `words`).
    Читает строки сверху вниз, переходит со строки на строку. «…» ставится там, где
    предложение продолжается за пределами снятой области. Если предложение короче
    трёх слов, возвращает '' (это не контекст)."""
    lines, breaks = group_lines(words)
    flat = [(w, li) for li, line in enumerate(lines) for w in line]
    idx = next((i for i, (w, _) in enumerate(flat) if w is target), None)
    if idx is None:
        return ""

    start, left_cut, i = idx, True, idx - 1
    while i >= 0 and idx - i <= max_side:
        prev, cur = flat[i], flat[i + 1]
        if ends_sentence(prev[0].text) or (prev[1] != cur[1] and prev[1] in breaks):
            left_cut = False          # нашли начало предложения
            break
        start = i
        i -= 1

    end, right_cut, j = idx, True, idx
    while j < len(flat) and j - idx <= max_side:
        end = j
        cur = flat[j]
        nxt = flat[j + 1] if j + 1 < len(flat) else None
        if ends_sentence(cur[0].text) or (nxt and nxt[1] != cur[1] and cur[1] in breaks):
            right_cut = False         # нашли конец предложения
            break
        j += 1

    span = [w.text for w, _ in flat[start:end + 1]]
    if len(span) < 3:
        return ""
    return ("… " if left_cut else "") + " ".join(span) + (" …" if right_cut else "")


def _ru_words(text):
    return re.findall(r"[^\W\d_]+", (text or "").lower())


def stem_match(term, ru_words):
    """Совпадает ли вариант перевода с каким-то словом предложения (с учётом окончаний)."""
    for t in _ru_words(term):
        if len(t) < 3:
            continue
        for w in ru_words:
            if len(w) < 3:
                continue
            n = 0
            for a, b in zip(t, w):
                if a != b:
                    break
                n += 1
            if n >= max(3, min(len(t), len(w)) - 2):
                return True
    return False


def find_context_hit(alts, translation, sentence_ru):
    """Какой из вариантов перевода слова встретился в переводе предложения.
    Пустая строка, если не нашли или это и есть основной перевод."""
    if not sentence_ru:
        return ""
    rw = _ru_words(sentence_ru)
    for _pos, terms in alts:
        for term in terms:
            if stem_match(term, rw):
                return "" if term.lower() == (translation or "").lower() else term
    return ""


# ------------------------- умные подсказки: имена, формы глаголов, фразовые глаголы -------------------------
_IRREGULAR = """
be: was were been am is are
have: had has
do: did done does
go: went gone
say: said
make: made
take: took taken
come: came
see: saw seen
know: knew known
get: got gotten
give: gave given
find: found
think: thought
tell: told
become: became
leave: left
feel: felt
bring: brought
begin: began begun
keep: kept
hold: held
write: wrote written
stand: stood
hear: heard
mean: meant
meet: met
run: ran
pay: paid
sit: sat
speak: spoke spoken
lead: led
grow: grew grown
lose: lost
fall: fell fallen
send: sent
build: built
understand: understood
draw: drew drawn
break: broke broken
spend: spent
rise: rose risen
drive: drove driven
buy: bought
wear: wore worn
choose: chose chosen
throw: threw thrown
catch: caught
win: won
forget: forgot forgotten
sell: sold
fight: fought
hide: hid hidden
eat: ate eaten
fly: flew flown
sing: sang sung
sleep: slept
teach: taught
shake: shook shaken
steal: stole stolen
wake: woke woken
bite: bit bitten
blow: blew blown
dig: dug
feed: fed
forgive: forgave forgiven
freeze: froze frozen
hang: hung
lend: lent
ride: rode ridden
ring: rang rung
shoot: shot
slide: slid
spin: spun
strike: struck
swear: swore sworn
swing: swung
tear: tore torn
swim: swam swum
sink: sank sunk
drink: drank drunk
"""
IRREGULAR_FORMS = {}
for _line in _IRREGULAR.strip().splitlines():
    _base, _forms = _line.split(":")
    for _f in _forms.split():
        IRREGULAR_FORMS[_f] = _base.strip()

PHRASAL_BASES = set("""give take look get go come put turn set run make break bring pick hold carry call cut
fall find keep let pass pull push show stand work wake throw sit check clean close fill figure hang hand knock
lay lead leave log move open pay point roll rush sell send settle shut sign sort speak start stay step stop
switch talk tear tell think try wait walk watch wear wipe write drop eat end catch chase cheer clear count
cool dress drag fight fix follow grow hurry join jump kick lie lift line lock mix pack play pop pour print rip
rub save scroll seal see shake share shout sleep slow smash sneak snap spread stick sum tidy tie touch trip
wash wind wrap zoom""".split())
# «in», «by», «after» сюда не входят: слишком много ложных срабатываний («the man in the cloak»)
PARTICLES = {"up", "out", "off", "on", "down", "over", "away", "back", "into", "around", "apart",
             "aside", "forward", "ahead", "together", "along", "behind"}
PREP_AFTER = {"to", "with", "of", "for", "on"}       # look forward TO, put up WITH, run out OF
DETERMINERS = {"the", "a", "an", "his", "her", "their", "my", "your", "our", "its", "this", "that",
               "these", "those", "some", "no", "any", "every", "each", "another"}


def _verb_forms(base):
    f = {base, base + "s", base + "ed", base + "ing", base + base[-1] + "ed", base + base[-1] + "ing"}
    if base.endswith("e"):
        f |= {base + "d", base[:-1] + "ing"}
    if base.endswith("y"):
        f |= {base[:-1] + "ies", base[:-1] + "ied"}
    if base.endswith(("s", "sh", "ch", "x", "z", "o")):
        f.add(base + "es")
    return f


VERB_FORMS = {}
for _b in PHRASAL_BASES:
    for _f in _verb_forms(_b):
        VERB_FORMS.setdefault(_f, _b)
for _f, _b in IRREGULAR_FORMS.items():
    if _b in PHRASAL_BASES:
        VERB_FORMS[_f] = _b

STOPWORDS = set("""the a an and or but if so as of at by for from in into on onto to with without about over under
after before between through during is are was were be been being am do does did done have has had having will
would shall should can could may might must i you he she it we they me him her us them my your his its our
their this that these those there here not no nor too very just only also then than when where while what
which who whom whose why how all any some each every both few more most other such own same again once up
down out off said say says""".split())


def irregular_base(word):
    """«went» -> «go». Только неправильные формы (их нельзя угадать), иначе ''."""
    w = (word or "").lower()
    base = IRREGULAR_FORMS.get(w, "")
    return base if base and base != w else ""


def _reading_order(words):
    lines, _ = group_lines(words)
    return [w for line in lines for w in line]


def looks_like_name(words, target):
    """Слово с заглавной буквы в середине предложения: скорее всего имя или название."""
    flat = _reading_order(words)
    idx = next((i for i, w in enumerate(flat) if w is target), None)
    if idx is None or idx == 0:
        return False
    raw = target.text or ""
    tok = clean_token(raw) or ""
    if len(tok) < 2 or not (tok[0].isupper() and tok[1:].islower()):
        return False                                   # «KIRITO» (крик) и «I» не считаем
    if raw[:1] in "\"“‘'«(" or tok.startswith(("I'", "I’")):
        return False                                   # реплика после кавычки, «I'm»
    return not ends_sentence(flat[idx - 1].text)       # слово не открывает предложение


def find_phrase(words, target):
    """Фразовый глагол вокруг слова. Возвращает ('gave up', 'give up') или ('', '')."""
    flat = _reading_order(words)
    idx = next((i for i, w in enumerate(flat) if w is target), None)
    if idx is None:
        return "", ""

    def tok(i):
        t = clean_token(flat[i].text) if 0 <= i < len(flat) else None
        return t.lower() if t else None

    me = tok(idx)
    if me is None:
        return "", ""
    start = idx - 1 if me in PARTICLES else idx       # наведены на частицу -> глагол стоит перед ней
    base = VERB_FORMS.get(tok(start) or "")
    if not base or ends_sentence(flat[start].text) or tok(start + 1) not in PARTICLES:
        return "", ""
    if start > 0 and not ends_sentence(flat[start - 1].text) and tok(start - 1) in DETERMINERS:
        return "", ""                                  # «the run up»: это существительное
    text, parts = [clean_token(flat[start].text), clean_token(flat[start + 1].text)], [base, tok(start + 1)]
    if not ends_sentence(flat[start + 1].text) and tok(start + 2) in PREP_AFTER:
        text.append(clean_token(flat[start + 2].text))
        parts.append(tok(start + 2))
    return " ".join(text), " ".join(parts)


# ------------------------- подготовка картинки -------------------------
def _resample():
    from PIL import Image
    return getattr(Image, "Resampling", Image).BICUBIC


def best_gray(img):
    """Серая версия картинки. Обычно это стандартная яркость, но для цветного текста на
    тёмном фоне (красные/синие/зелёные буквы на чёрном, как в манхве) яркость почти
    сливается с фоном. Тогда берём самый яркий из каналов R/G/B: цветной текст остаётся
    светлым и хорошо читается. Выбираем тот вариант, где контраст выше."""
    from PIL import ImageChops, ImageStat
    luma = img.convert("L")
    r, g, b = img.split()
    peak = ImageChops.lighter(ImageChops.lighter(r, g), b)
    if ImageStat.Stat(peak).stddev[0] > ImageStat.Stat(luma).stddev[0] * 1.05:
        return peak
    return luma


def preprocess_python(bgra, w, h, scale):
    """Серый + светлый фон + контраст + увеличение. Возвращает PIL-картинку 'L'."""
    from PIL import Image, ImageOps, ImageStat
    img = Image.frombytes("RGB", (w, h), bytes(bgra), "raw", "BGRX")
    gray = best_gray(img)
    if ImageStat.Stat(gray).mean[0] < 110:  # тёмный фон (игры, Discord) -> инвертируем
        gray = ImageOps.invert(gray)
    gray = ImageOps.autocontrast(gray, cutoff=1)
    return gray.resize((w * scale, h * scale), _resample())


def preprocess(bgra, w, h, scale):
    """Использует Rust (fast_core), если он собран, иначе Python."""
    global _fast
    if _fast is not None:
        try:
            from PIL import Image
            img = Image.frombytes("RGB", (w, h), bytes(bgra), "raw", "BGRX")
            gray = best_gray(img)
            # Rust ждёт BGRA; отдаём ему серый кадр (три одинаковых канала), результат тот же.
            fake = Image.merge("RGBA", (gray, gray, gray, Image.new("L", gray.size, 255))).tobytes()
            data = _fast.preprocess(fake, w, h, scale)
            return Image.frombytes("L", (w * scale, h * scale), data)
        except Exception as e:  # noqa: BLE001
            print(f"[!] Rust-модуль не сработал ({e}). Перехожу на Python-версию.")
            _fast = None
    return preprocess_python(bgra, w, h, scale)


_fast_diff_ok = True


def frame_diff(a, b, w, h, thr=CACHE_DIFF_THRESHOLD):
    """Доля пикселей двух BGRA-кадров, отличающихся больше чем на thr (0.0 - 1.0)."""
    global _fast_diff_ok
    if _fast is not None and _fast_diff_ok and hasattr(_fast, "diff_ratio"):
        try:
            return float(_fast.diff_ratio(bytes(a), bytes(b), thr))
        except Exception as e:  # noqa: BLE001
            print(f"[!] Rust-сравнение кадров не сработало ({e}). Использую Python.")
            _fast_diff_ok = False
    return frame_diff_python(a, b, w, h, thr)


def frame_diff_python(a, b, w, h, thr=CACHE_DIFF_THRESHOLD):
    from PIL import Image, ImageChops
    ia = Image.frombytes("RGB", (w, h), bytes(a), "raw", "BGRX")
    ib = Image.frombytes("RGB", (w, h), bytes(b), "raw", "BGRX")
    r, g, bl = ImageChops.difference(ia, ib).split()
    mx = ImageChops.lighter(ImageChops.lighter(r, g), bl)
    return sum(mx.histogram()[thr + 1:]) / float(w * h)


# ----------------------------- захват экрана -----------------------------
class Capturer:
    """Снимок кусочка экрана. У mss свой экземпляр на каждый поток."""

    def __init__(self):
        self._local = threading.local()

    def _sct(self):
        sct = getattr(self._local, "sct", None)
        if sct is None:
            import mss
            factory = getattr(mss, "MSS", None) or mss.mss  # новое имя, со старым как запасным
            sct = factory()
            self._local.sct = sct
        return sct

    def grab(self, left, top, width, height):
        sct = self._sct()
        mon = sct.monitors[0]  # весь виртуальный экран (все мониторы)
        left = int(max(mon["left"], min(left, mon["left"] + mon["width"] - width)))
        top = int(max(mon["top"], min(top, mon["top"] + mon["height"] - height)))
        shot = sct.grab({"left": left, "top": top, "width": width, "height": height})
        return Shot(left, top, shot.width, shot.height, bytes(shot.bgra))


# ----------------------------- распознавание текста -----------------------------
def _get(obj, name, default=None):
    """Достаёт поле и из словаря, и из объекта."""
    if obj is None:
        return default
    if isinstance(obj, dict):
        return obj.get(name, default)
    return getattr(obj, name, default)


class WinOCR:
    """Встроенный в Windows 10/11 OCR (через пакет winocr)."""
    name = "Windows OCR"

    def __init__(self, lang):
        import winocr  # noqa: F401
        self.winocr = winocr
        self.lang = lang

    def recognize(self, img):
        rgb = img.convert("RGB")
        fn = getattr(self.winocr, "recognize_pil_sync", None)
        if fn is not None:
            res = fn(rgb, self.lang)
        else:
            import asyncio
            res = asyncio.run(self.winocr.recognize_pil(rgb, self.lang))
        words = []
        for line in _get(res, "lines", []) or []:
            for w in _get(line, "words", []) or []:
                r = _get(w, "bounding_rect")
                text = _get(w, "text", "")
                if r is None or not text:
                    continue
                words.append(Word(text, float(_get(r, "x", 0)), float(_get(r, "y", 0)),
                                  float(_get(r, "width", 0)), float(_get(r, "height", 0))))
        return words


class TessOCR:
    """Запасной вариант: Tesseract (нужно установить отдельно)."""
    name = "Tesseract"

    def __init__(self, lang="eng"):
        import pytesseract
        for p in (r"C:\Program Files\Tesseract-OCR\tesseract.exe",
                  r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe"):
            if os.path.exists(p):
                pytesseract.pytesseract.tesseract_cmd = p
                break
        pytesseract.get_tesseract_version()  # бросит ошибку, если Tesseract не установлен
        self.pt = pytesseract
        self.lang = lang

    def recognize(self, img):
        d = self.pt.image_to_data(img, lang=self.lang, config="--psm 11",
                                  output_type=self.pt.Output.DICT)
        words = []
        for i, text in enumerate(d["text"]):
            if not text or not text.strip():
                continue
            try:
                if float(d["conf"][i]) < 0:
                    continue
            except (ValueError, TypeError):
                pass
            words.append(Word(text, d["left"][i], d["top"][i], d["width"][i], d["height"][i]))
        return words


class PaddleOCR_Wrapper:
    """Альтернативный OCR: PaddleOCR."""
    name = "PaddleOCR"

    def __init__(self, lang="en"):
        from paddleocr import PaddleOCR
        # По умолчанию инициализируется 'en'
        self.ocr = PaddleOCR(use_angle_cls=True, lang=lang, show_log=False)

    def recognize(self, img):
        import numpy as np
        results = self.ocr.ocr(np.array(img), cls=True)
        words = []
        if results is None:
            return words
        for line in results:
            if line is None:
                continue
            for word_info in line:
                # word_info: [box, (text, confidence)]
                box = word_info[0]
                text = word_info[1][0]
                xs = [p[0] for p in box]
                ys = [p[1] for p in box]
                words.append(Word(text, float(min(xs)), float(min(ys)),
                                  float(max(xs) - min(xs)), float(max(ys) - min(ys))))
        return words


def load_font(size):
    from PIL import ImageFont
    for name in ("segoeui.ttf", "arial.ttf", "DejaVuSans.ttf",
                 "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"):
        try:
            return ImageFont.truetype(name, size)
        except Exception:  # noqa: BLE001
            continue
    return ImageFont.load_default(size)


def render_sentence(sentence, size=22, fg=(20, 20, 20), bg=(245, 245, 245),
                    width=900, height=220, origin=(40, 50), line_gap=1.5):
    """Рисует текст (можно в несколько строк через \\n).
    Возвращает (картинка, [(слово, центр_x, центр_y), ...])."""
    from PIL import Image, ImageDraw
    img = Image.new("RGB", (width, height), bg)
    draw = ImageDraw.Draw(img)
    font = load_font(size)
    asc, desc = font.getmetrics()
    positions = []
    for li, line in enumerate(sentence.split("\n")):
        oy = origin[1] + int(li * (asc + desc) * line_gap)
        draw.text((origin[0], oy), line, font=font, fill=fg)
        prefix = ""
        for word in line.split(" "):
            x0 = origin[0] + font.getlength(prefix)
            x1 = x0 + font.getlength(word)
            positions.append((word, int((x0 + x1) / 2), int(oy + (asc + desc) / 2)))
            prefix += word + " "
    return img, positions


class FakeScreen:
    """Подменяет экран картинкой (для самопроверки и тестов). Работает как Capturer."""

    def __init__(self, img):
        self.img = img

    def grab(self, left, top, width, height):
        left = max(0, min(left, self.img.width - width))
        top = max(0, min(top, self.img.height - height))
        crop = self.img.crop((left, top, left + width, top + height)).convert("RGB")
        r, g, b = crop.split()
        from PIL import Image
        bgrx = Image.merge("RGBA", (b, g, r, Image.new("L", crop.size, 255)))
        return Shot(left, top, width, height, bgrx.tobytes())


def make_ocr(log=print):
    """Пробует OCR-движки по очереди и берёт первый, который реально читает текст."""
    candidates = []
    if sys.platform == "win32":
        candidates.append(("Windows OCR", lambda: WinOCR(OCR_LANG)))
    candidates.append(("PaddleOCR", lambda: PaddleOCR_Wrapper(lang=OCR_LANG)))
    candidates.append(("Tesseract", lambda: TessOCR()))
    errors = []
    for name, factory in candidates:
        try:
            ocr = factory()
            img, _ = render_sentence("Hello world", size=24, height=64, origin=(20, 14))
            sample = img.convert("L").resize((img.width * 2, img.height * 2))
            words = ocr.recognize(sample)
            if any("hello" in w.text.lower() for w in words):
                ocr.extra_factories = [f for n, f in candidates if n != name]
                return ocr
            errors.append(f"{name}: движок запустился, но тестовый текст не распознал")
        except Exception as e:  # noqa: BLE001
            errors.append(f"{name}: {type(e).__name__}: {e}")
    hint = ""
    if sys.platform == "win32":
        hint = ("\n\nЧаще всего не хватает английского языка для распознавания текста:\n"
                "Параметры Windows -> Время и язык -> Язык и регион -> Добавить язык -> "
                "English (United States) -> при установке оставьте галочку "
                "«Распознавание текста».")
    raise RuntimeError("Не удалось запустить распознавание текста:\n  " + "\n  ".join(errors) + hint)


# ----------------------------- перевод и примеры -----------------------------
CACHE_FILE = "translations_cache.json"
_HERE = os.path.dirname(os.path.abspath(__file__))
POS_RU = {"noun": "сущ.", "verb": "гл.", "adjective": "прил.", "adverb": "нареч.",
          "preposition": "предл.", "pronoun": "мест.", "conjunction": "союз",
          "interjection": "межд.", "exclamation": "межд.", "article": "арт.",
          "determiner": "опред.", "particle": "частица", "abbreviation": "сокр.",
          "numeral": "числ."}


class _Http:
    """GET-запросы с JSON-ответом. Соединение с сервером переиспользуется (keep-alive):
    не тратим 100-300 мс на новое TLS-рукопожатие при каждом слове."""

    def __init__(self):
        self._local = threading.local()

    def _conns(self):
        d = getattr(self._local, "conns", None)
        if d is None:
            d = self._local.conns = {}
        return d

    @staticmethod
    def _connect(scheme, netloc, timeout):
        cls = http.client.HTTPSConnection if scheme == "https" else http.client.HTTPConnection
        return cls(netloc, timeout=timeout)

    def warm(self, url, timeout=HTTP_TIMEOUT):
        """Заранее открывает соединение (DNS + TLS), чтобы первый перевод не ждал."""
        u = urllib.parse.urlsplit(url)
        key, conns = (u.scheme, u.netloc), self._conns()
        if key not in conns:
            c = self._connect(u.scheme, u.netloc, timeout)
            c.connect()
            conns[key] = c

    def get_json(self, url, timeout=HTTP_TIMEOUT, _redirects=3):
        u = urllib.parse.urlsplit(url)
        key, conns = (u.scheme, u.netloc), self._conns()
        path = (u.path or "/") + ("?" + u.query if u.query else "")
        for attempt in (0, 1):
            conn = conns.get(key)
            reused = conn is not None
            if conn is None:
                conn = conns[key] = self._connect(u.scheme, u.netloc, timeout)
            try:
                conn.request("GET", path, headers={"User-Agent": "Mozilla/5.0 (screen-translator)",
                                                   "Accept": "application/json",
                                                   "Accept-Encoding": "identity"})
                resp = conn.getresponse()
                body = resp.read()
            except (http.client.HTTPException, OSError):
                conn.close()
                conns.pop(key, None)
                if reused and attempt == 0:
                    continue          # старое соединение могло закрыться: одна попытка на новом
                raise
            if resp.will_close:
                conn.close()
                conns.pop(key, None)
            loc = resp.getheader("Location")
            if resp.status in (301, 302, 303, 307, 308) and loc and _redirects > 0:
                return self.get_json(urllib.parse.urljoin(url, loc), timeout, _redirects - 1)
            if resp.status >= 400:
                raise urllib.error.HTTPError(url, resp.status, resp.reason, resp.msg, None)
            return json.loads(body.decode("utf-8"))


_HTTP = _Http()


def _http_json(url, timeout=HTTP_TIMEOUT):
    return _HTTP.get_json(url, timeout)


def _gtx_url(text, extra=""):
    return ("https://translate.googleapis.com/translate_a/single?client=gtx"
            f"&sl={SOURCE_LANG}&tl={TARGET_LANG}&dt=t{extra}&q=" + urllib.parse.quote(text))


def parse_gtx(data):
    """Ответ Google -> (перевод, [[часть речи, [варианты]], ...]). Варианты необязательны."""
    text = "".join(p[0] for p in data[0] if p and p[0]).strip()
    alts = []
    try:
        for e in (data[1] or [])[:3]:
            pos = POS_RU.get(str(e[0]).lower(), str(e[0]))
            terms = [t for t in e[1] if isinstance(t, str)][:4]
            if terms:
                alts.append([pos, terms])
    except Exception:  # noqa: BLE001
        alts = []
    return text, alts


def _google_gtx(text):
    """Источник 1: публичный адрес Google, которым пользуются расширения браузеров."""
    return parse_gtx(_http_json(_gtx_url(text)))[0]


def _google_gtx_full(word):
    """Тот же адрес, но с вариантами перевода по частям речи."""
    return parse_gtx(_http_json(_gtx_url(word, "&dt=bd")))


def _google_deep(text):
    """Источник 2: Google через библиотеку deep-translator."""
    from deep_translator import GoogleTranslator
    return GoogleTranslator(source=SOURCE_LANG, target=TARGET_LANG).translate(text)


def _mymemory(text):
    """Источник 3: MyMemory (бесплатный, независим от Google)."""
    from deep_translator import MyMemoryTranslator
    return MyMemoryTranslator(source="english", target="russian").translate(text)


def _has_word(text, word):
    return re.search(r"(?<!\w)" + re.escape(word) + r"(?!\w)", text, re.I) is not None


def parse_tatoeba(data, word, max_len=90):
    """Ответ Tatoeba -> [(английское предложение, русский перевод)], короткие вперёд."""
    out = []
    for r in (data or {}).get("results", []) or []:
        en = (r.get("text") or "").strip()
        ru = ""
        for grp in r.get("translations", []) or []:
            for t in (grp if isinstance(grp, list) else [grp]):
                if isinstance(t, dict) and t.get("lang") == "rus" and t.get("text"):
                    ru = t["text"].strip()
                    break
            if ru:
                break
        if en and ru and len(en) <= max_len and _has_word(en, word):
            out.append((en, ru))
    out.sort(key=lambda p: len(p[0]))
    return out[:3]


def _tatoeba(word):
    url = ("https://tatoeba.org/en/api_v0/search?from=eng&to=rus&orphans=no&unapproved=no&query="
           + urllib.parse.quote(word))
    return parse_tatoeba(_http_json(url), word)


def parse_dictapi(data, word, max_len=100):
    """Ответ Free Dictionary API -> [английские примеры]."""
    out = []
    if isinstance(data, list):
        for entry in data:
            for m in entry.get("meanings", []) or []:
                for d in m.get("definitions", []) or []:
                    ex = (d.get("example") or "").strip()
                    if ex and len(ex) <= max_len and ex not in out and _has_word(ex, word):
                        out.append(ex)
    return out[:3]


@functools.lru_cache(maxsize=256)
def _dict_json(word):
    """Ответ Free Dictionary API. Один запрос обслуживает и примеры, и транскрипцию."""
    try:
        return _http_json("https://api.dictionaryapi.dev/v2/entries/en/" + urllib.parse.quote(word))
    except urllib.error.HTTPError as e:
        if e.code == 404:  # слова нет в словаре, это не ошибка сети
            return []
        raise


def _dictapi(word):
    return parse_dictapi(_dict_json(word), word)


def parse_ipa(data):
    """Транскрипция из ответа Free Dictionary API или ''."""
    if isinstance(data, list):
        for entry in data:
            t = (entry.get("phonetic") or "").strip()
            if t:
                return t
            for ph in entry.get("phonetics", []) or []:
                t = (ph.get("text") or "").strip()
                if t:
                    return t
    return ""


def _dictapi_ipa(word):
    return parse_ipa(_dict_json(word))


class Translator:
    """Переводы слов и предложений. Пробует несколько источников по очереди, помнит ответы
    (в памяти и в файле), поэтому повторные слова не требуют интернета."""

    def __init__(self, providers=None, word_fn=None, cache_path=None, clock=time.monotonic):
        self.providers = providers or [("Google", _google_gtx), ("Google (deep)", _google_deep),
                                       ("MyMemory", _mymemory)]
        self.word_fn = word_fn or _google_gtx_full
        self.cache_path = cache_path or os.path.join(_HERE, CACHE_FILE)
        self.clock = clock
        self.blocked_until = {}
        self._lock = threading.RLock()
        self._dirty = False
        self._last_save = 0.0
        try:
            with open(self.cache_path, encoding="utf-8") as f:
                self.cache = json.load(f)
        except Exception:  # noqa: BLE001
            self.cache = {}

    # --- кэш ---
    def _save(self):
        with self._lock:
            try:
                with open(self.cache_path, "w", encoding="utf-8") as f:
                    json.dump(self.cache, f, ensure_ascii=False)
                self._dirty = False
            except OSError:
                pass
            self._last_save = self.clock()

    def flush(self):
        if self._dirty:
            self._save()

    def _remember(self, key, value):
        with self._lock:
            self.cache[key] = value
            self._dirty = True
            if self.clock() - self._last_save > 3:
                self._save()

    def _penalize(self, name, exc):
        msg = f"{type(exc).__name__}: {exc}"
        limited = "429" in msg or "too many" in msg.lower()
        self.blocked_until[name] = self.clock() + (300 if limited else 30)
        return msg

    # --- переводы ---
    def _text_chain(self, text, key):
        cached = self.cache.get(key)
        if isinstance(cached, str) and cached:
            return cached
        now = self.clock()
        order = sorted(self.providers, key=lambda p: self.blocked_until.get(p[0], 0) > now)
        errors = []
        for name, fn in order:
            try:
                out = (fn(text) or "").strip()
                if not out:
                    raise RuntimeError("пустой ответ")
                self._remember(key, out)
                return out
            except Exception as e:  # noqa: BLE001
                errors.append(f"{name}: {self._penalize(name, e)[:80]}")
        raise RuntimeError("; ".join(errors))

    def __call__(self, word):
        w = word.lower()
        return self._text_chain(w, w)

    def text(self, sentence):
        return self._text_chain(sentence, "s:" + sentence.lower())

    def word_info(self, word):
        """(перевод, варианты по частям речи). Если Google с вариантами недоступен,
        возвращает просто перевод из запасных источников."""
        w = word.lower()
        key = "w:" + w
        c = self.cache.get(key)
        if isinstance(c, dict) and c.get("t"):
            return c["t"], [list(a) for a in c.get("alts", [])]
        if self.blocked_until.get("Google", 0) <= self.clock():
            try:
                text, alts = self.word_fn(w)
                if text:
                    self._remember(key, {"t": text, "alts": alts})
                    return text, alts
            except Exception as e:  # noqa: BLE001
                self._penalize("Google", e)
        return self(word), []


class EchoTranslator:
    """Заглушка без интернета: для самопроверки и тестов."""
    cache = {}

    def word_info(self, w):
        return f"<{w}>", []

    def text(self, s):
        return f"<{s}>"

    def __call__(self, w):
        return f"<{w}>"

    def flush(self):
        pass

    def _remember(self, key, value):
        self.cache[key] = value


def fetch_examples(word, translator, sources=None, max_n=2):
    """До двух коротких примеров [(англ., рус.)]. Сначала Tatoeba (там сразу есть русский
    перевод), потом Free Dictionary (перевод делаем сами). Результат кэшируется."""
    key = "x:" + word.lower()
    c = translator.cache.get(key)
    if isinstance(c, list):
        return [tuple(p) for p in c]
    tatoeba, dictapi = sources or (_tatoeba, _dictapi)
    pairs, failed = [], False
    try:
        pairs = list(tatoeba(word.lower()))
    except Exception:  # noqa: BLE001
        failed = True
    if len(pairs) < max_n:
        try:
            seen = {p[0].lower() for p in pairs}
            for en in dictapi(word.lower()):
                if en.lower() in seen:
                    continue
                try:
                    ru = translator.text(en)
                except Exception:  # noqa: BLE001
                    ru, failed = "", True
                pairs.append((en, ru))
                if len(pairs) >= max_n:
                    break
        except Exception:  # noqa: BLE001
            failed = True
    pairs = pairs[:max_n]
    if not failed:  # ошибки сети в кэш не пишем
        translator._remember(key, [list(p) for p in pairs])
    return pairs


def fetch_ipa(word, translator, source=None):
    """Транскрипция слова ('' если не нашли). Успешный ответ запоминается."""
    key = "p:" + word.lower()
    c = translator.cache.get(key)
    if isinstance(c, str):
        return c
    try:
        ipa = (source or _dictapi_ipa)(word.lower())
    except Exception:  # noqa: BLE001
        return ""        # ошибки сети в кэш не пишем
    translator._remember(key, ipa)
    return ipa


class MyWords:
    """Слова, сохранённые кнопкой. Файл my_words.tsv: слово, перевод, предложение,
    перевод предложения, дата (через Tab). Открывается в Excel и импортируется в Anki."""

    def __init__(self, path=None):
        self.path = path or os.path.join(_HERE, MY_WORDS_FILE)
        self.rows = {}
        if os.path.exists(self.path):
            with open(self.path, encoding="utf-8") as f:
                for line in f:
                    parts = line.rstrip("\r\n").split("\t")
                    if parts and parts[0]:
                        parts += [""] * (5 - len(parts))
                        self.rows[parts[0].lower()] = tuple(parts[:5])

    @staticmethod
    def _c(s):
        return " ".join(str(s or "").split())  # убирает Tab и переносы строк

    def has(self, word):
        return word.lower() in self.rows

    def items(self):
        return list(self.rows.values())

    def add(self, e):
        old = self.rows.get(e.word.lower())
        date = old[4] if old else datetime.now().strftime("%Y-%m-%d")
        self.rows[e.word.lower()] = (self._c(e.word), self._c(e.translation), self._c(e.sentence),
                                     self._c(e.sentence_ru), date)
        self._write()

    def remove(self, word):
        if self.rows.pop(word.lower(), None) is not None:
            self._write()

    def _write(self):
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8", newline="\n") as f:
            for row in self.rows.values():
                f.write("\t".join(row) + "\n")
        os.replace(tmp, self.path)


# ----------------------------- кэш распознавания -----------------------------
@dataclass
class CachedScan:
    rect: tuple      # (left, top, width, height) в пикселях экрана
    bgra: bytes      # как выглядела эта область, когда её распознали
    words: list      # слова OCR в координатах экрана


class OcrCache:
    """Помнит последние распознанные области. Пока пиксели области не изменились, повторное
    наведение на соседние слова обходится без OCR (самый медленный этап)."""

    def __init__(self, max_entries=None):
        self.max_entries = max_entries or CACHE_ENTRIES
        self.items = []
        self.hits = 0
        self.misses = 0
        self._lock = threading.Lock()

    @staticmethod
    def _inside(e, x, y):
        l, t, w, h = e.rect
        mx, my = CACHE_MARGIN
        return l + mx <= x <= l + w - mx and t + my <= y <= t + h - my

    def covers(self, x, y):
        """Быстрая проверка без снимка экрана: есть ли запись, в зоне которой курсор."""
        with self._lock:
            return any(self._inside(e, x, y) for e in self.items)

    def find(self, x, y, capturer):
        """Запись, чьи слова можно использовать, или None. Проверка: снимаем ту же область
        заново и сравниваем с запомненной (Rust, если собран)."""
        with self._lock:
            candidates = [e for e in self.items if self._inside(e, x, y)]
        for e in candidates:
            l, t, w, h = e.rect
            fresh = capturer.grab(l, t, w, h)
            same = ((fresh.left, fresh.top, fresh.width, fresh.height) == e.rect and
                    frame_diff(e.bgra, fresh.bgra, w, h, CACHE_DIFF_THRESHOLD) <= CACHE_DIFF_RATIO)
            with self._lock:
                if e in self.items:
                    self.items.remove(e)
                if same:                       # устаревшую запись просто выбрасываем
                    self.items.insert(0, e)
            if same:
                self.hits += 1
                return e
        self.misses += 1
        return None

    def add(self, scan):
        with self._lock:
            self.items.insert(0, scan)
            del self.items[self.max_entries:]


# ----------------------------- главный конвейер -----------------------------
# ------------- запасные способы подготовки картинки и запасные OCR -------------
DEBUG_DIR = os.path.join(_HERE, "debug_ocr")


def _otsu(gray):
    """Порог, лучше всего разделяющий светлое и тёмное (метод Оцу)."""
    hist = gray.histogram()
    total = sum(hist)
    sum_all = sum(i * h for i, h in enumerate(hist))
    wb = sb = 0
    best, thr = -1.0, 127
    for t in range(256):
        wb += hist[t]
        if wb == 0:
            continue
        wf = total - wb
        if wf == 0:
            break
        sb += t * hist[t]
        var = wb * wf * (sb / wb - (sum_all - sb) / wf) ** 2
        if var > best:
            best, thr = var, t
    return thr


def preprocess_variant(bgra, w, h, scale, mode, cx, cy):
    """Запасная подготовка. Смотрит на участок вокруг курсора (cx, cy), где точно текст:
    по нему решает, где фон, а где буквы, и делает буквы чёрными на белом.
    mode 'bin' - строго чёрно-белая картинка, 'soft' - с плавными оттенками.
    Возвращает (картинка, отступ_в_пикселях_уже_после_увеличения)."""
    from PIL import Image, ImageOps, ImageStat
    img = Image.frombytes("RGB", (w, h), bytes(bgra), "raw", "BGRX")
    gray = ImageOps.autocontrast(best_gray(img), cutoff=1)
    box = (max(0, int(cx) - 200), max(0, int(cy) - 45), min(w, int(cx) + 200), min(h, int(cy) + 45))
    if box[2] - box[0] < 8 or box[3] - box[1] < 8:
        box = (0, 0, w, h)
    local = gray.crop(box)
    if mode in ("diff", "diffbin"):
        # Буквы = всё, что заметно отличается от цвета фона у курсора (любого цвета).
        from PIL import ImageChops
        med = tuple(int(v) for v in ImageStat.Stat(img.crop(box)).median)
        dr, dg, db = ImageChops.difference(img, Image.new("RGB", img.size, med)).split()
        d = ImageChops.lighter(ImageChops.lighter(dr, dg), db)
        d = ImageOps.autocontrast(d, cutoff=1)
        if mode == "diffbin":
            thr = max(40, _otsu(d.crop(box)))
            d = d.point(lambda v: 255 if v > thr else 0)
        gray = ImageOps.invert(d)  # буквы чёрные, фон белый
    elif mode == "bin":
        thr = _otsu(local)
        bw = gray.point(lambda v: 255 if v > thr else 0)
        bright = ImageStat.Stat(local.point(lambda v: 255 if v > thr else 0)).mean[0] / 255.0
        gray = bw if bright > 0.5 else ImageOps.invert(bw)  # букв меньше, чем фона
    else:
        if ImageStat.Stat(local).mean[0] < 110:
            gray = ImageOps.invert(gray)
    if scale != 1:
        gray = gray.resize((w * scale, h * scale), _resample())
    pad = 24
    gray = ImageOps.expand(gray, border=pad, fill=255)
    return gray, pad


# (режим, увеличение): пробуем по очереди, пока рядом с курсором не найдётся слово
VARIANTS = (("diffbin", 2), ("diff", 2), ("diffbin", 1), ("diff", 3), ("bin", 2), ("soft", 2))


def _engines(ocr):
    yield ocr
    extra = getattr(ocr, "_extra_inst", None)
    if extra is None:
        extra = []
        for factory in getattr(ocr, "extra_factories", []):
            try:
                extra.append(factory())
            except Exception:  # noqa: BLE001
                pass
        ocr._extra_inst = extra
    for e in extra:
        yield e


def recognize_region(shot, x, y, ocr):
    """OCR области с запасными вариантами. Возвращает слова в координатах экрана."""
    scale = max(1, min(SCALE, MAX_OCR_SIDE // max(shot.width, shot.height)))

    def to_screen(ws, sc, pad):
        return [Word(w.text, shot.left + (w.x - pad) / sc, shot.top + (w.y - pad) / sc,
                     w.w / sc, w.h / sc) for w in ws]

    img = preprocess(shot.bgra, shot.width, shot.height, scale)
    words = to_screen(ocr.recognize(img), scale, 0)
    if pick_word(words, x, y) is not None:
        return words
    cx, cy = x - shot.left, y - shot.top
    best = words
    tried = []
    for mode, sc in VARIANTS:
        sc = max(1, min(sc, MAX_OCR_SIDE // max(shot.width, shot.height)))
        try:
            vimg, pad = preprocess_variant(shot.bgra, shot.width, shot.height, sc, mode, cx, cy)
        except Exception:  # noqa: BLE001
            continue
        tried.append((f"{mode}{sc}", vimg))
        for eng in _engines(ocr):
            try:
                ws = to_screen(eng.recognize(vimg), sc, pad)
            except Exception:  # noqa: BLE001
                continue
            if pick_word(ws, x, y) is not None:
                return ws
            if len(ws) > len(best):
                best = ws
    try:  # ничего не нашли: сохраняем, что видела программа (для разбора проблемы)
        os.makedirs(DEBUG_DIR, exist_ok=True)
        from PIL import Image
        Image.frombytes("RGB", (shot.width, shot.height), bytes(shot.bgra), "raw", "BGRX").save(
            os.path.join(DEBUG_DIR, "region.png"))
        img.save(os.path.join(DEBUG_DIR, "std.png"))
        for name, vimg in tried:
            vimg.save(os.path.join(DEBUG_DIR, f"{name}.png"))
        print(f"[debug] слово у курсора не найдено; картинки сохранены в {DEBUG_DIR}")
    except Exception:  # noqa: BLE001
        pass
    return best


def lookup_at(x, y, capturer, ocr, translator, cache=None, on_words=None):
    """Этап 1 (быстрый): экран -> (кэш или OCR) -> слово под (x, y) -> перевод,
    предложение вокруг, форма глагола, фразовый глагол, подсказка про имя.
    Возвращает Entry или None. on_words(words, слово) вызывается после свежего OCR."""
    t0 = time.perf_counter()
    scan = cache.find(x, y, capturer) if cache is not None else None
    src = "cache"
    if scan is None:
        src = "ocr"
        shot = capturer.grab(x - REGION_W // 2, y - REGION_H // 2, REGION_W, REGION_H)
        words = recognize_region(shot, x, y, ocr)
        scan = CachedScan((shot.left, shot.top, shot.width, shot.height), shot.bgra, words)
        if cache is not None:
            cache.add(scan)
    words = scan.words
    picked = pick_word(words, x, y)
    if picked is None:
        return None
    wd, tok = picked
    box = (wd.x, wd.y, wd.x + wd.w, wd.y + wd.h)
    try:
        tr, alts = translator.word_info(tok)
    except Exception:  # noqa: BLE001
        return Entry(tok, "⚠ перевод недоступен (лимит запросов или нет интернета). Попробуйте позже.",
                     box, ok=False, src=src, ms=(time.perf_counter() - t0) * 1000)
    phrase, phrase_base = find_phrase(words, wd)
    entry = Entry(tok, tr, box, alts=alts, sentence=sentence_context(words, wd),
                  lemma=irregular_base(tok), name_hint=looks_like_name(words, wd),
                  phrase=phrase, phrase_base=phrase_base, src=src,
                  ms=(time.perf_counter() - t0) * 1000)
    if src == "ocr" and on_words is not None:
        on_words(words, wd)
    return entry


def enrich_text(entry, translator, is_current=lambda: True, emit=lambda patch: None):
    """Этап 2а (фон): перевод предложения, вариант «по контексту», перевод фразового глагола.
    Каждый результат сразу отдаётся как патч (словарь полей карточки)."""
    patch = {}
    if entry.sentence and is_current():
        core = entry.sentence.strip("… ").strip()
        try:
            ru = translator.text(core)
            patch["sentence_ru"] = ("… " if entry.sentence.startswith("…") else "") + ru + \
                                   (" …" if entry.sentence.endswith("…") else "")
            patch["hit"] = find_context_hit(entry.alts, entry.translation, ru)
        except Exception:  # noqa: BLE001
            patch = {}
        if patch and is_current():
            emit(dict(patch))
    if entry.phrase_base and is_current():
        try:
            ru = translator.text(entry.phrase_base)
        except Exception:  # noqa: BLE001
            ru = ""
        if ru and is_current():
            patch["phrase_ru"] = ru
            emit({"phrase_ru": ru})
    return patch


def enrich_extras(entry, translator, examples_fn, ipa_fn=None, is_current=lambda: True,
                  emit=lambda patch: None):
    """Этап 2б (фон, параллельно с 2а): транскрипция и примеры."""
    patch = {}
    if ipa_fn is not None and is_current():
        try:
            ipa = ipa_fn(entry.word, translator) or ""
        except Exception:  # noqa: BLE001
            ipa = ""
        if ipa and is_current():
            patch["ipa"] = ipa
            emit({"ipa": ipa})
    if is_current():
        try:
            ex = examples_fn(entry.word, translator)
        except Exception:  # noqa: BLE001
            ex = []
        if ex and is_current():
            patch["examples"] = ex
            emit({"examples": ex})
    return patch


def enrich(entry, translator, examples_fn, ipa_fn=None, is_current=lambda: True,
           emit=lambda patch: None):
    """Оба этапа подряд (для проверок и скриптов). Возвращает дополненную копию карточки."""
    patch = enrich_text(entry, translator, is_current, emit)
    patch.update(enrich_extras(entry, translator, examples_fn, ipa_fn, is_current, emit))
    return dataclasses.replace(entry, **patch)


def prefetch_words(words, target, translator, limit, is_current, delay=None, sleep=time.sleep):
    """Заранее переводит ближайшие слова, чтобы следующее наведение было мгновенным.
    Осторожно: останавливается, как только пользователь ушёл или Google «в штрафе»."""
    if limit <= 0:
        return 0
    delay = PREFETCH_DELAY if delay is None else delay
    cx, cy = target.x + target.w / 2, target.y + target.h / 2
    cands = []
    for w in words:
        tok = clean_token(w.text)
        if w is target or not tok or len(tok) < 4 or tok[0].isupper() or tok.lower() in STOPWORDS:
            continue
        cands.append((abs(w.x + w.w / 2 - cx) + 3 * abs(w.y + w.h / 2 - cy), tok))
    cands.sort(key=lambda c: c[0])
    cache = getattr(translator, "cache", {})
    done, seen = 0, set()
    for _, tok in cands:
        low = tok.lower()
        if low in seen or ("w:" + low) in cache:
            continue
        seen.add(low)
        if done >= limit or not is_current():
            break
        blocked = getattr(translator, "blocked_until", {}).get("Google", 0)
        if blocked > getattr(translator, "clock", time.monotonic)():
            break                                   # не дразним сервер, который уже отказал
        try:
            translator.word_info(tok)
        except Exception:  # noqa: BLE001
            break
        done += 1
        sleep(delay)
    return done


# ----------------------------- логика наведения -----------------------------
def box_contains(box, pos, pad=3):
    return box[0] - pad <= pos[0] <= box[2] + pad and box[1] - pad <= pos[1] <= box[3] + pad


class HoverLogic:
    """Решает, когда запускать поиск слова. Без GUI, поэтому легко проверяется."""

    def __init__(self, settle=SETTLE_SECONDS, tol=MOVE_TOLERANCE_PX):
        self.settle, self.tol = settle, tol
        self.was_down = False
        self.reset()

    def reset(self):
        self.last_pos = None
        self.still_since = 0.0
        self.last_lookup_pos = None
        self.box = None
        self.busy = False

    def _moved(self, a, b):
        return abs(a[0] - b[0]) > self.tol or abs(a[1] - b[1]) > self.tol

    def update(self, key_down, pos, now, fast=False):
        """Возвращает 'lookup' (искать слово), 'hide' (мышь ушла со слова), 'release' (отпустили клавишу) или None."""
        if not key_down:
            if self.was_down:
                self.was_down = False
                self.reset()
                return "release"
            return None
        self.was_down = True
        if self.last_pos is None or self._moved(pos, self.last_pos):
            self.last_pos = pos
            self.still_since = now
            if self.box and not box_contains(self.box, pos):
                self.box = None
                return "hide"
            return None
        wait = FAST_SETTLE_SECONDS if fast else self.settle
        if self.busy or now - self.still_since < wait:
            return None
        if self.box and box_contains(self.box, pos):
            return None
        if self.last_lookup_pos and not self._moved(pos, self.last_lookup_pos):
            return None
        self.busy = True
        self.last_lookup_pos = pos
        return "lookup"

    def finish(self, box):
        self.busy = False
        self.box = box


# ----------------------------- Windows: клавиша, мышь, DPI -----------------------------
class POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class WinInput:
    VK = {"shift": 0x10, "ctrl": 0x11, "alt": 0x12}

    def __init__(self, key):
        if key not in self.VK:
            raise ValueError(f"HOTKEY должен быть одним из: {', '.join(self.VK)}")
        self.vk = self.VK[key]
        self.user32 = ctypes.windll.user32
        self.user32.GetAsyncKeyState.restype = ctypes.c_short

    def key_down(self):
        return bool(self.user32.GetAsyncKeyState(self.vk) & 0x8000)

    def mouse_pos(self):
        pt = POINT()
        self.user32.GetCursorPos(ctypes.byref(pt))
        return pt.x, pt.y


def enable_dpi_awareness():
    """Чтобы координаты мыши и экрана совпадали при масштабе Windows 125%/150%."""
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:  # noqa: BLE001
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:  # noqa: BLE001
            pass


# ----------------------------- карточка с переводом -----------------------------
class Overlay:
    """Окно-карточка: слово, перевод, подсказки, предложение, примеры и кнопки.
    Не забирает фокус у игры/браузера."""
    BG, ACCENT, FG, DIM, GOOD, LINE, NOTE = ("#1e1e2e", "#89b4fa", "#cdd6f4", "#9399b2",
                                             "#a6e3a1", "#45475a", "#f9e2af")
    WRAP = 440

    def __init__(self, root, on_save, on_close):
        import tkinter as tk
        self.tk, self.on_save, self.on_close = tk, on_save, on_close
        self.visible, self.rect, self.anchor = False, None, (0, 0)
        self.win = tk.Toplevel(root)
        self.win.withdraw()
        self.win.overrideredirect(True)
        self.win.attributes("-topmost", True)
        try:
            self.win.attributes("-alpha", 0.97)
        except Exception:  # noqa: BLE001
            pass
        f = tk.Frame(self.win, bg=self.BG, highlightbackground=self.ACCENT, highlightthickness=1)
        f.pack()
        f.columnconfigure(0, weight=1)

        head = tk.Frame(f, bg=self.BG)
        head.grid(row=0, column=0, sticky="we", padx=10, pady=(8, 0))
        self.word = tk.Label(head, bg=self.BG, fg=self.ACCENT, font=("Segoe UI", 11, "bold"))
        self.word.pack(side="left")
        self.ipa = tk.Label(head, bg=self.BG, fg=self.DIM, font=("Segoe UI", 10))
        self.ipa.pack(side="left", padx=(8, 0))
        btn = dict(relief="flat", bd=0, cursor="hand2", font=("Segoe UI", 9), padx=8, pady=2,
                   bg="#313244", fg=self.FG, activebackground=self.LINE, activeforeground=self.FG)
        self.btn_close = tk.Button(head, text="✕", command=lambda: self.on_close(), **btn)
        self.btn_close.pack(side="right")
        self.btn_save = tk.Button(head, text="☆ Сохранить", command=lambda: self.on_save(), **btn)
        self.btn_save.pack(side="right", padx=(0, 6))

        def label(row, fg, size, **kw):
            lb = tk.Label(f, bg=self.BG, fg=fg, font=("Segoe UI", size), anchor="w", justify="left",
                          wraplength=self.WRAP, **kw)
            lb.grid(row=row, column=0, sticky="we", padx=10, pady=(2, 0))
            lb.grid_remove()
            return lb
        self.tr = label(1, self.FG, 15)
        self.hint = label(2, self.GOOD, 10)        # вариант перевода «по контексту»
        self.note = label(3, self.NOTE, 10)        # форма глагола / похоже на имя
        self.phrase = label(4, self.ACCENT, 10)    # фразовый глагол
        self.alts = label(5, self.DIM, 10)
        self.sep = tk.Frame(f, bg=self.LINE, height=1)
        self.sep.grid(row=6, column=0, sticky="we", padx=10, pady=(8, 4))
        self.sep.grid_remove()
        self.sent = label(7, self.FG, 10)
        self.sent_ru = label(8, self.DIM, 10)
        self.ex = label(9, self.DIM, 10)
        tk.Frame(f, bg=self.BG, height=6).grid(row=10, column=0)
        self._no_activate()

    def _no_activate(self):
        """Клик по карточке не должен переключать фокус из игры/браузера."""
        try:
            from ctypes import wintypes
            self.win.update_idletasks()
            u = ctypes.windll.user32
            u.GetParent.argtypes = [wintypes.HWND]
            u.GetParent.restype = wintypes.HWND
            u.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
            u.GetWindowLongW.restype = ctypes.c_long
            u.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
            hwnd = u.GetParent(self.win.winfo_id()) or self.win.winfo_id()
            style = u.GetWindowLongW(hwnd, -20)
            u.SetWindowLongW(hwnd, -20, style | 0x08000000 | 0x80)  # NOACTIVATE | TOOLWINDOW
        except Exception:  # noqa: BLE001
            pass

    @staticmethod
    def _put(widget, text):
        if text:
            widget.config(text=text)
            widget.grid()
        else:
            widget.grid_remove()

    def set_saved(self, saved):
        self.btn_save.config(text="★ Сохранено" if saved else "☆ Сохранить",
                             fg=self.GOOD if saved else self.FG)

    @staticmethod
    def notes_text(e):
        notes = []
        if e.lemma:
            notes.append(f"форма глагола: {e.lemma}")
        if e.name_hint:
            notes.append("похоже на имя или название")
        return " · ".join(notes)

    @staticmethod
    def phrase_text(e):
        if not e.phrase_base:
            return ""
        return f"фразовый глагол: {e.phrase_base}" + (f" — {e.phrase_ru}" if e.phrase_ru else "")

    def _render(self, e, saved):
        self.word.config(text=e.word)
        self.ipa.config(text=e.ipa)
        if e.ok:
            self.btn_save.pack(side="right", padx=(0, 6))
            self.set_saved(saved)
        else:
            self.btn_save.pack_forget()
        self._put(self.tr, e.translation)
        self._put(self.hint, f"в этом предложении, вероятно: {e.hit}" if e.hit else "")
        self._put(self.note, self.notes_text(e))
        self._put(self.phrase, self.phrase_text(e))
        self._put(self.alts, "\n".join(f"{pos}: {', '.join(terms)}" for pos, terms in e.alts))
        if e.sentence or e.examples:
            self.sep.grid()
        else:
            self.sep.grid_remove()
        self._put(self.sent, e.sentence)
        self._put(self.sent_ru, e.sentence_ru)
        self._put(self.ex, "\n".join(f"• {en}" + (f"\n   {ru}" if ru else "") for en, ru in e.examples))

    def _place(self):
        self.win.update_idletasks()
        w, h = self.win.winfo_reqwidth(), self.win.winfo_reqheight()
        sw, sh = self.win.winfo_screenwidth(), self.win.winfo_screenheight()
        x, y = self.anchor
        px = max(0, min(x + 12, sw - w - 4))
        py = y + OVERLAY_OFFSET
        if py + h > sh:
            py = y - OVERLAY_OFFSET - h
        py = max(0, py)
        self.win.geometry(f"+{int(px)}+{int(py)}")
        self.rect = (px, py, px + w, py + h)

    def show(self, entry, saved, x, y):
        self.anchor = (x, y)
        self._render(entry, saved)
        self._place()
        self.win.deiconify()
        self.win.lift()
        self.visible = True

    def update(self, entry, saved):
        if self.visible:
            self._render(entry, saved)
            self._place()

    def contains(self, pos, pad=4):
        r = self.rect
        return bool(self.visible and r and r[0] - pad <= pos[0] <= r[2] + pad
                    and r[1] - pad <= pos[1] <= r[3] + pad)

    def hide(self):
        self.win.withdraw()
        self.visible, self.rect = False, None


class WordsWindow:
    """Список сохранённых слов с удалением и открытием файла."""

    def __init__(self, root, words, on_change):
        import tkinter as tk
        self.words, self.on_change, self.keys = words, on_change, []
        self.win = tk.Toplevel(root)
        self.win.title("Мои слова")
        self.win.geometry("480x380")
        self.list = tk.Listbox(self.win, font=("Segoe UI", 11), activestyle="none")
        self.list.pack(fill="both", expand=True, padx=8, pady=8)
        bar = tk.Frame(self.win)
        bar.pack(fill="x", padx=8, pady=(0, 8))
        tk.Button(bar, text="Удалить выбранное", command=self.delete).pack(side="left")
        tk.Button(bar, text="Открыть файл", command=self.open_file).pack(side="right")
        self.refresh()

    def refresh(self):
        self.list.delete(0, "end")
        self.keys = []
        for row in reversed(self.words.items()):
            self.list.insert("end", f"{row[0]} — {row[1]}")
            self.keys.append(row[0])

    def delete(self):
        for idx in self.list.curselection():
            self.words.remove(self.keys[idx])
        self.refresh()
        self.on_change()

    def open_file(self):
        try:
            os.startfile(self.words.path)  # type: ignore[attr-defined]
        except Exception:  # noqa: BLE001
            pass


# ----------------------------- приложение -----------------------------
class App:
    def __init__(self):
        import tkinter as tk
        enable_dpi_awareness()
        self.tk = tk
        self.root = tk.Tk()
        self.root.title("Экранный переводчик")
        self.root.geometry("420x190")
        self.root.protocol("WM_DELETE_WINDOW", self.quit)
        self.status = tk.StringVar(value="Загружаю распознавание текста...")
        self.count = tk.StringVar()
        self.perf = tk.StringVar(value="")
        tk.Label(self.root, textvariable=self.status, wraplength=400, justify="left").pack(
            padx=10, pady=(12, 4), anchor="w")
        tk.Label(self.root, textvariable=self.count, fg="#555").pack(padx=10, anchor="w")
        tk.Label(self.root, textvariable=self.perf, fg="#555").pack(padx=10, anchor="w")
        bar = tk.Frame(self.root)
        bar.pack(pady=10)
        tk.Button(bar, text="Мои слова", width=12, command=self.open_words).pack(side="left", padx=4)
        tk.Button(bar, text="Выход", width=12, command=self.quit).pack(side="left", padx=4)

        self.words = MyWords()
        self.translator = Translator()
        self.cache = OcrCache()
        atexit.register(self.translator.flush)
        self._update_count()
        self.overlay = Overlay(self.root, self.toggle_save, self._hide_popup)
        self.inp = WinInput(HOTKEY)
        self.logic = HoverLogic()
        self.jobs, self.results = queue.Queue(), queue.Queue()
        self.pool = ThreadPoolExecutor(max_workers=3)           # этап 2: две части + прогрев
        self.prefetch_pool = ThreadPoolExecutor(max_workers=1)  # упреждающий перевод соседей
        self.prefetch_gen = 0
        self.job_id = 0
        self.shown_job = None
        self.current_entry = None
        self.linger_until = 0.0
        threading.Thread(target=self._worker, daemon=True).start()
        for _ in range(2):   # прогреваем соединения потоков этапа 2 (DNS + TLS заранее)
            self.pool.submit(self._warm)
        self.root.after(POLL_MS, self._tick)

    def quit(self):
        self.translator.flush()
        self.pool.shutdown(wait=False, cancel_futures=True)
        self.prefetch_pool.shutdown(wait=False, cancel_futures=True)
        self.root.destroy()

    def run(self):
        self.root.mainloop()

    @staticmethod
    def _warm():
        try:
            _HTTP.warm(WARM_URL)
        except Exception:  # noqa: BLE001
            pass           # не страшно: первый перевод просто откроет соединение сам

    def _update_count(self):
        self.count.set(f"Сохранено слов: {len(self.words.items())}")

    def open_words(self):
        WordsWindow(self.root, self.words, self._update_count)

    # --- сохранение слова кнопкой ☆ ---
    def toggle_save(self):
        e = self.current_entry
        if e is None or not e.ok:
            return
        try:
            if self.words.has(e.word):
                self.words.remove(e.word)
                saved = False
            else:
                self.words.add(e)
                saved = True
        except OSError as ex:
            self.status.set(f"Не удалось сохранить слово: {ex}")
            return
        self.overlay.set_saved(saved)
        self._update_count()
        self.linger_until = time.monotonic() + LINGER_SECONDS

    # --- фоновый поток: снимок экрана, кэш, OCR ---
    def _worker(self):
        try:
            capturer = Capturer()
            ocr = make_ocr()
        except Exception as e:  # noqa: BLE001
            traceback.print_exc()
            self.results.put(("fatal", str(e)))
            return
        rust = ", Rust-ускорение" if _fast is not None else ""
        self.results.put(("status", f"Готово ({ocr.name}{rust}).\n"
                                    f"Зажми {HOTKEY.upper()} и наведи мышь на слово. "
                                    f"Отпусти и нажми ☆, чтобы сохранить. Окно можно свернуть."))
        self._warm()   # соединение этого потока
        while True:
            jid, pos = self.jobs.get()
            try:
                res = lookup_at(pos[0], pos[1], capturer, ocr, self.translator, self.cache, self._on_words)
            except Exception as e:  # noqa: BLE001
                traceback.print_exc()
                box = (pos[0] - 20, pos[1] - 20, pos[0] + 20, pos[1] + 20)
                res = Entry("Ошибка", f"{type(e).__name__}: {e}"[:150], box, ok=False)
            self.results.put(("result", jid, pos, res))

    def _on_words(self, words, wd):
        """После свежего OCR: заранее переводим соседние слова (в отдельном потоке)."""
        if PREFETCH_WORDS <= 0:
            return
        self.prefetch_gen += 1
        gen = self.prefetch_gen
        self.prefetch_pool.submit(prefetch_words, words, wd, self.translator, PREFETCH_WORDS,
                                  lambda: gen == self.prefetch_gen and self.logic.was_down)

    def _run_job(self, fn, *args):
        try:
            fn(*args)
        except Exception:  # noqa: BLE001
            traceback.print_exc()

    def _start_enrich(self, jid, entry):
        """Этап 2: две независимые части параллельно, каждая присылает патчи карточки."""
        cur = lambda: self.shown_job == jid                       # noqa: E731
        emit = lambda patch: self.results.put(("update", jid, patch))  # noqa: E731
        self.pool.submit(self._run_job, enrich_text, entry, self.translator, cur, emit)
        self.pool.submit(self._run_job, enrich_extras, entry, self.translator,
                         fetch_examples, fetch_ipa, cur, emit)

    # --- главный поток ---
    def _hide_popup(self):
        self.job_id += 1
        self.overlay.hide()
        self.shown_job = None
        self.current_entry = None
        self.logic.box = None
        self.logic.last_lookup_pos = None

    def _tick(self):
        try:
            self._drain_results()
            pos = self.inp.mouse_pos()
            down = self.inp.key_down()
            now = time.monotonic()
            if self.overlay.contains(pos):
                self.linger_until = now + LINGER_SECONDS   # мышь над карточкой: не закрываем
            else:
                fast = down and self.cache.covers(*pos)    # ответ можно взять из кэша: пауза короче
                action = self.logic.update(down, pos, now, fast)
                if action == "release":
                    if self.overlay.visible:
                        self.linger_until = now + LINGER_SECONDS
                elif action == "hide":
                    self._hide_popup()
                elif action == "lookup":
                    self.job_id += 1
                    self.jobs.put((self.job_id, pos))
                if self.overlay.visible and not down and now >= self.linger_until:
                    self._hide_popup()
        except Exception:  # noqa: BLE001
            traceback.print_exc()
        finally:
            self.root.after(POLL_MS, self._tick)

    def _saved(self, entry):
        return entry.ok and self.words.has(entry.word)

    def _drain_results(self):
        while True:
            try:
                msg = self.results.get_nowait()
            except queue.Empty:
                return
            kind = msg[0]
            if kind == "status":
                self.status.set(msg[1])
            elif kind == "fatal":
                self.status.set("Ошибка запуска, подробности в окне сообщения.")
                from tkinter import messagebox
                messagebox.showerror("Экранный переводчик", msg[1])
            elif kind == "result":
                _, jid, pos, res = msg
                if jid != self.job_id or not self.logic.was_down:
                    continue  # результат устарел
                cur = self.inp.mouse_pos()
                if abs(cur[0] - pos[0]) > 25 or abs(cur[1] - pos[1]) > 25:
                    self.logic.finish(None)  # мышь уже ушла
                    self.logic.last_lookup_pos = None
                    continue
                if res is None:
                    self.logic.finish(None)
                    self._hide_popup()
                else:
                    self.logic.finish(res.box)
                    self.shown_job, self.current_entry = jid, res
                    self.overlay.show(res, self._saved(res), pos[0], pos[1])
                    if res.src:
                        total = self.cache.hits + self.cache.misses
                        self.perf.set(f"Последний поиск: {res.ms:.0f} мс "
                                      f"({'из кэша' if res.src == 'cache' else 'распознавание'}); "
                                      f"из кэша: {self.cache.hits} из {total}")
                    if res.ok:
                        self._start_enrich(jid, res)
            elif kind == "update":
                _, jid, patch = msg
                if jid != self.shown_job or not self.overlay.visible or self.current_entry is None:
                    continue
                entry = dataclasses.replace(self.current_entry, **patch)
                self.current_entry = entry
                if self._saved(entry):
                    try:
                        self.words.add(entry)   # дополняем уже сохранённую запись контекстом
                    except OSError:
                        pass
                self.overlay.update(entry, self._saved(entry))


# ----------------------------- самопроверка -----------------------------
def run_check():
    ok_all = True

    def line(ok, text, required=True):
        nonlocal ok_all
        if required:
            ok_all = ok_all and ok
        print(("[ OK ] " if ok else ("[FAIL] " if required else "[ !! ] ")) + text)

    print(f"Python {sys.version.split()[0]}, платформа: {sys.platform}\n")
    for mod, need in (("mss", True), ("PIL", True), ("deep_translator", True),
                      ("tkinter", True), ("winocr", sys.platform == "win32"),
                      ("pytesseract", False)):
        try:
            __import__(mod)
            line(True, f"модуль {mod}")
        except Exception as e:  # noqa: BLE001
            line(not need, f"модуль {mod}: {type(e).__name__}: {e}" + ("" if need else "  (необязательный)"))
    if _fast is None:
        print("[ -- ] Rust-модуль не собран (это нормально, работает Python-версия)")
    else:
        has_diff = hasattr(_fast, "diff_ratio")
        line(has_diff, f"Rust-модуль fast_core подключён (версия API {getattr(_fast, 'api_version', lambda: 1)()}"
                       + ("" if has_diff else ", старая сборка без сравнения кадров: запустите build_rust.bat") + ")",
             required=False)

    try:
        shot = Capturer().grab(0, 0, 100, 100)
        line(len(shot.bgra) >= 100 * 100 * 4, f"снимок экрана {shot.width}x{shot.height}")
    except Exception as e:  # noqa: BLE001
        line(False, f"снимок экрана: {type(e).__name__}: {e}")

    ocr = None
    try:
        ocr = make_ocr()
        line(True, f"распознавание текста: {ocr.name}")
    except Exception as e:  # noqa: BLE001
        line(False, str(e))

    tr = Translator(cache_path=os.path.join(_HERE, "check_cache.tmp"))
    try:
        text, alts = tr.word_info("bank")
        extra = "; ".join(f"{p}: {', '.join(t)}" for p, t in alts)
        line(True, f"перевод слова: bank -> {text}" + (f"  [{extra}]" if extra else "  [вариантов по частям речи нет]"))
    except Exception as e:  # noqa: BLE001
        line(False, f"перевод слова (нужен интернет): {type(e).__name__}: {e}")
    try:
        ru = tr.text("We sat on the bank of the river.")
        line(True, f"перевод предложения: {ru}")
        hit = find_context_hit(tr.word_info("bank")[1], tr.word_info("bank")[0], ru)
        line(True, f"вариант по контексту: {hit or '(основной перевод подходит или не определён)'}", required=False)
    except Exception as e:  # noqa: BLE001
        line(False, f"перевод предложения: {type(e).__name__}: {e}")
    try:
        ex = fetch_examples("dragon", tr)
        line(bool(ex), "примеры: " + (" | ".join(f"{a} / {b}" for a, b in ex) if ex else
                                     "не найдены (карточка просто будет без примеров)"), required=False)
    except Exception as e:  # noqa: BLE001
        line(False, f"примеры: {type(e).__name__}: {e}", required=False)
    try:
        os.remove(tr.cache_path)
    except OSError:
        pass

    if ocr is not None:
        text = ("The old merchant leaned across the counter and whispered a secret.\n"
                "Nobody in the tavern heard what the stranger said before he left.")
        for style, fg, bg in (("тёмный текст на светлом", (20, 20, 20), (245, 245, 245)),
                              ("светлый текст на тёмном", (235, 235, 235), (25, 25, 35))):
            img, pos = render_sentence(text, size=20, fg=fg, bg=bg, width=900, height=260)
            screen = FakeScreen(img)
            for word, cx, cy in pos:
                if word != "stranger":
                    continue
                try:
                    res = lookup_at(cx, cy, screen, ocr, EchoTranslator())
                    got = res.word if res else None
                    line(got == word, f"поиск слова ({style}): ждали «{word}», получили «{got}»")
                    # Достаточно, чтобы предложение целиком дошло до точки; одна неверная
                    # буква в начале (особенность OCR) не считается ошибкой.
                    want = "the stranger said before he left."
                    line(bool(res) and res.sentence.strip().endswith(want),
                         f"предложение ({style}): «{res.sentence if res else None}»")
                    cache = OcrCache()
                    lookup_at(cx, cy, screen, ocr, EchoTranslator(), cache)
                    near = next(p for p in pos if p[0] == "tavern")
                    res2 = lookup_at(near[1], near[2], screen, ocr, EchoTranslator(), cache)
                    line(bool(res2) and res2.word == "tavern" and res2.src == "cache",
                         f"кэш распознавания ({style}): соседнее слово взято без OCR "
                         f"({res2.src if res2 else None}, {res2.ms:.0f} мс)" if res2 else "кэш: слово не найдено")
                except Exception as e:  # noqa: BLE001
                    line(False, f"поиск слова ({style}): {type(e).__name__}: {e}")
    print("\n" + ("ВСЁ В ПОРЯДКЕ, можно запускать run.bat" if ok_all else
                  "Есть проблемы (см. строки [FAIL] выше). Пришлите этот текст мне."))
    return 0 if ok_all else 1


def run_bench():
    """Замеры: сколько занимает каждый этап поиска слова на этом компьютере."""
    text = ("The old merchant leaned across the counter and whispered a secret.\n"
            "Nobody in the tavern heard what the stranger said before he left\n"
            "the town. Outside, the ancient dragon slept quietly on the hill.")
    img, pos = render_sentence(text, size=20, width=1000, height=300)
    screen = FakeScreen(img)
    shot = screen.grab(100, 40, REGION_W, REGION_H)
    w, h = shot.width, shot.height

    def avg_ms(fn, n=15):
        fn()
        t0 = time.perf_counter()
        for _ in range(n):
            fn()
        return (time.perf_counter() - t0) * 1000 / n

    print(f"Область {w}x{h}, увеличение x{SCALE}\n")
    py_ms = avg_ms(lambda: preprocess_python(shot.bgra, w, h, SCALE))
    print(f"подготовка картинки, Python (Pillow): {py_ms:7.2f} мс")
    other = FakeScreen(img).grab(100, 40, REGION_W, REGION_H)
    d_py = avg_ms(lambda: frame_diff_python(shot.bgra, other.bgra, w, h))
    print(f"сравнение двух кадров, Python:        {d_py:7.2f} мс")
    if _fast is None:
        print("Rust-модуль не собран: запустите build_rust.bat, чтобы увидеть его цифры.")
    else:
        rs = avg_ms(lambda: _fast.preprocess(shot.bgra, w, h, SCALE))
        print(f"подготовка картинки, Rust:            {rs:7.2f} мс  (быстрее в {py_ms / rs:.1f} раза)")
        if hasattr(_fast, "diff_ratio"):
            dr = avg_ms(lambda: _fast.diff_ratio(shot.bgra, other.bgra, CACHE_DIFF_THRESHOLD))
            print(f"сравнение двух кадров, Rust:          {dr:7.2f} мс  (быстрее в {d_py / dr:.1f} раза)")
    try:
        cap = Capturer()
        print(f"снимок экрана (mss):                  {avg_ms(lambda: cap.grab(0, 0, REGION_W, REGION_H)):7.2f} мс")
    except Exception as e:  # noqa: BLE001
        print(f"снимок экрана недоступен: {type(e).__name__}: {e}")
    try:
        ocr = make_ocr()
    except Exception as e:  # noqa: BLE001
        print(f"\nOCR недоступен: {e}")
        return 1
    prepared = preprocess(shot.bgra, w, h, SCALE)
    ocr_ms = avg_ms(lambda: ocr.recognize(prepared), n=3)
    print(f"распознавание текста ({ocr.name}):".ljust(38) + f"{ocr_ms:7.1f} мс")

    cache = OcrCache()
    a = next(p for p in pos if p[0] == "stranger")
    b = next(p for p in pos if p[0] == "tavern")
    t0 = time.perf_counter()
    r1 = lookup_at(a[1], a[2], screen, ocr, EchoTranslator(), cache)
    cold = (time.perf_counter() - t0) * 1000
    t0 = time.perf_counter()
    r2 = lookup_at(b[1], b[2], screen, ocr, EchoTranslator(), cache)
    warm = (time.perf_counter() - t0) * 1000
    print(f"\nпервое слово (с распознаванием):      {cold:7.1f} мс  [{r1.src if r1 else None}]")
    print(f"соседнее слово (из кэша):             {warm:7.1f} мс  [{r2.src if r2 else None}]"
          + (f"  (быстрее в {cold / warm:.0f} раз)" if warm > 0 else ""))
    print("\nК этому добавляется перевод по сети: для нового слова обычно 0.1-0.4 с, для слова из кэша "
          "переводов (translations_cache.json) 0 мс.")
    return 0


def main():
    global HOTKEY
    ap = argparse.ArgumentParser(description="Экранный переводчик EN->RU")
    ap.add_argument("--check", action="store_true", help="проверить все компоненты")
    ap.add_argument("--bench", action="store_true", help="замерить скорость этапов")
    ap.add_argument("--key", choices=["shift", "ctrl", "alt"], default=HOTKEY,
                    help="клавиша-активатор")
    args = ap.parse_args()
    HOTKEY = args.key
    if args.check:
        sys.exit(run_check())
    if args.bench:
        sys.exit(run_bench())
    if sys.platform != "win32":
        print("Эта программа рассчитана на Windows.")
        sys.exit(1)
    App().run()


if __name__ == "__main__":
    main()
