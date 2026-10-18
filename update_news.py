#!/usr/bin/env python3
"""Świat w Minutę — generator newsów v2 (Gemini + Pexels).

Zapisuje: news.json, raw_feed.json, archive.json
Sekrety (zmienne środowiskowe): GEMINI_API_KEY, PEXELS_API_KEY
"""
import hashlib
import html as html_lib
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta
from time import mktime
from urllib.parse import parse_qs, urlparse
from zoneinfo import ZoneInfo

import feedparser
from google import genai
from google.genai import types

# ───────────────────────── KONFIGURACJA ─────────────────────────
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "")
PEXELS_API_KEY = os.environ.get("PEXELS_API_KEY", "")  # bez wartości domyślnej!
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-3.6-flash")
USE_SOURCE_IMAGES = os.environ.get("USE_SOURCE_IMAGES", "0") == "1"  # 0 = tylko Pexels

FALLBACK_IMG = "https://images.unsplash.com/photo-1451187580459-43490279c0fa?q=80&w=800&auto=format&fit=crop"
PL_TZ = ZoneInfo("Europe/Warsaw")
MAX_AGE_HOURS = 24
TARGET_ITEMS = 14
MIN_ITEMS = 8               # lepiej mniej pozycji niż powtórki
MAX_POOL = 50               # tyle artykułów próbujemy pobrać w całości
MAX_CANDIDATES = 40
MAX_PER_SOURCE = 4
MAX_UNGROUNDED_CAND = 8     # kandydaci bez pełnego tekstu (Google News, paywalle)
MAX_UNGROUNDED_ITEMS = 2    # tyle takich pozycji może trafić do wydania
GROUNDED_MIN_CHARS = 400
ARCHIVE_MAX_SESSIONS = 60
DEDUPE_TITLE_SESSIONS = 8   # ~4 dni wstecz

# (url, język, domyślna kategoria, nazwa źródła)
FEEDS = [
    ("https://www.money.pl/rss/", "pl", "GOSPODARKA", "Money.pl"),
    ("https://businessinsider.com.pl/.rss", "pl", "BIZNES", "Business Insider Polska"),
    ("https://www.bankier.pl/rss/wiadomosci.xml", "pl", "GOSPODARKA", "Bankier.pl"),
    ("https://www.wnp.pl/rss/artykuly.xml", "pl", "GOSPODARKA", "WNP.pl"),
    ("https://archiwum.rp.pl/rss/ekonomia", "pl", "GOSPODARKA", "Rzeczpospolita"),
    ("https://defence24.pl/rss", "pl", "OBRONNOŚĆ", "Defence24"),
    ("https://feeds.bloomberg.com/markets/news.rss", "en", "GOSPODARKA", "Bloomberg"),
    ("https://search.cnbc.com/rs/search/view.html?partnerId=2000&keywords=markets&sort=date", "en", "GOSPODARKA", "CNBC"),
    ("https://feeds.bbci.co.uk/news/world/rss.xml", "en", "ŚWIAT", "BBC News"),
    ("https://feeds.bbci.co.uk/news/world/us_and_canada/rss.xml", "en", "ŚWIAT", "BBC News"),
    ("https://news.google.com/rss?hl=pl&gl=PL&ceid=PL:pl", "pl", "POLSKA", "Google News"),
    ("https://news.google.com/rss/search?q=world+news+geopolitics&hl=en-US&gl=US&ceid=US:en", "en", "GEOPOLITYKA", "Google News"),
]

POLISH_MONTHS = {1: "stycznia", 2: "lutego", 3: "marca", 4: "kwietnia", 5: "maja", 6: "czerwca",
                 7: "lipca", 8: "sierpnia", 9: "września", 10: "października", 11: "listopada", 12: "grudnia"}
STOP_WORDS = {"polsce", "polski", "polaków", "nowy", "nowa", "nowe", "roku", "swiat", "przez", "tylko",
              "rzad", "rząd", "beda", "będą", "moze", "może", "oraz", "jest", "jego", "bardzo", "nawet",
              "teraz", "after", "with", "from", "that", "this", "more"}
GENERIC_QUERY = {"POLSKA": "Poland city street", "GOSPODARKA": "economy finance charts", "BIZNES": "business office",
                 "GEOPOLITYKA": "world map globe", "OBRONNOŚĆ": "military equipment", "TECHNOLOGIE": "technology circuit",
                 "ŚWIAT": "city skyline"}
DEFAULT_EMOJI = {"POLSKA": "🇵🇱", "GOSPODARKA": "📊", "BIZNES": "💼", "GEOPOLITYKA": "🌍",
                 "OBRONNOŚĆ": "🛡️", "TECHNOLOGIE": "💻", "ŚWIAT": "🌍"}
ALLOWED_EMOJI = set("🚨📉📈💥🔥⚠⚖🏛🛡🪖💰🛢⚡🤖💻🏥🌍🚀🏗📊⏰🏢🌉🏭💵🏦🛒🚗✈🚢🌾⚓🧬🔋📡🗳📰💼🔒🧊🌡⛽")
GENERIC_WORDS = {"view", "sign", "signs", "street", "night", "scene", "modern", "aerial", "system", "line",
                 "tracks", "landscape", "area", "concept", "background", "city"}
# zdjęcia sugerujące INNE wydarzenie (np. huragan przy zamieszkach) — zawsze odrzucane
BAD_ALT_RE = re.compile(r"hurricane|tornado|flood|earthquake|tsunami|cemetery|grave|funeral|coffin|abandoned|ruins|corpse", re.I)
PEOPLE_RE = re.compile(r"\b(man|men|woman|women|people|person|child|children|kid|boy|girl|patient|soldier|"
                       r"soldiers|crowd|couple|family|doctor|nurse|police|policeman|policemen|prosthetic)\b", re.I)
HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                         "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
           "Accept": "text/html,application/xhtml+xml", "Accept-Language": "en-US,en;q=0.9,pl;q=0.8"}


# ───────────────────────── NARZĘDZIA ─────────────────────────
def clean_link(url: str) -> str:
    if not url or url == "#":
        return "#"
    try:
        tracking = {"utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
                    "at_medium", "at_campaign", "fbclid", "gclid", "mc_cid", "mc_eid"}
        p = urlparse(url)
        if p.scheme not in ("http", "https"):
            return "#"
        if p.query:
            qs = {k: v[0] for k, v in parse_qs(p.query).items() if k not in tracking}
            q = urllib.parse.urlencode(qs)
            return f"{p.scheme}://{p.netloc}{p.path}" + (f"?{q}" if q else "")
        return url
    except Exception:
        return url


def norm_link(url: str) -> str:
    """Klucz porównawczy linków (bez schematu, www, końcowego /, parametrów poza Google News)."""
    try:
        p = urlparse(str(url).strip().lower())
        host = p.netloc.removeprefix("www.")
        path = p.path.rstrip("/")
        return f"{host}{path}" + (f"?{p.query}" if "news.google.com" in host and p.query else "")
    except Exception:
        return str(url)


def is_recent(entry) -> bool:
    pub = getattr(entry, "published_parsed", None) or getattr(entry, "updated_parsed", None)
    if not pub:
        return True
    try:
        dt = datetime.fromtimestamp(mktime(pub), tz=PL_TZ)
        return datetime.now(PL_TZ) - dt <= timedelta(hours=MAX_AGE_HOURS)
    except Exception:
        return True


def normalize_category(cat: str) -> str:
    c = str(cat or "").upper().strip()
    if "POLSK" in c:
        return "POLSKA"
    if "OBRON" in c or "WOJSK" in c:
        return "OBRONNOŚĆ"
    if "TECH" in c or c == "AI":
        return "TECHNOLOGIE"
    if "GEOPOLITYK" in c:
        return "GEOPOLITYKA"
    if "ŚWIAT" in c or "SWIAT" in c:
        return "ŚWIAT"
    if "BIZNES" in c or "SPÓŁK" in c or "FIRM" in c:
        return "BIZNES"
    return "GOSPODARKA"


def format_title(title: str, category: str = "ŚWIAT") -> str:
    """Emoji z listy dozwolonych + reszta WIELKIMI LITERAMI; naprawia spację przed U+FE0F."""
    s = re.sub(r"\s+\ufe0f", "\ufe0f", str(title or "").strip())
    s = re.sub(r"\s+", " ", s)
    if not s:
        return ""
    m = re.match(r"^([^\w]+)(.*)$", s)
    prefix, rest = (m.group(1).strip(), m.group(2).strip()) if m else ("", s)
    chars = [c for c in prefix if c not in "\ufe0f\u200d "]
    if not chars or not all(c in ALLOWED_EMOJI for c in chars):
        prefix = DEFAULT_EMOJI.get(category, "📰")
    return f"{prefix} {rest.upper()}".strip() if rest else ""


def extract_keywords(text: str) -> set:
    words = re.findall(r"[a-zA-ZąćęłńóśźżĄĆĘŁŃÓŚŹŻ]{4,}", text.lower())
    return {w for w in words if w not in STOP_WORDS}


def are_topics_duplicate(a: str, b: str, threshold: float = 0.40) -> bool:
    w1, w2 = extract_keywords(a), extract_keywords(b)
    if not w1 or not w2:
        return False
    common = w1 & w2
    if len(common) >= 3:
        return True
    return len(common) >= 2 and len(common) / min(len(w1), len(w2)) >= threshold


def write_json(path: str, data) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def short_id(link: str) -> str:
    return hashlib.sha1(link.encode("utf-8")).hexdigest()[:10]


def numbers_in(text: str) -> set:
    """Liczby z normalizacją separatorów tysięcy: '1,800' / '1 800' / '1.800' → '1800'."""
    out = set()
    for n in re.findall(r"\d{1,3}(?:[ \u00a0,.]\d{3})+|\d+", text or ""):
        d = re.sub(r"\D", "", n)
        if len(d) > 1:
            out.add(d)
    return out


def interleave(items: list, per_source: int, limit: int) -> list:
    by_src = defaultdict(list)
    for a in items:
        by_src[a["source_name"]].append(a)
    queues = [v[:per_source] for v in by_src.values()]
    out = []
    while queues and len(out) < limit:
        for q in queues:
            if q and len(out) < limit:
                out.append(q.pop(0))
        queues = [q for q in queues if q]
    return out


# ───────────────────────── POBIERANIE ─────────────────────────
def fetch_feeds() -> list:
    articles = []
    for url, lang, cat, default_name in FEEDS:
        try:
            feed = feedparser.parse(url)
            n = 0
            for e in feed.entries[:12]:
                if not is_recent(e):
                    continue
                title = getattr(e, "title", "").strip()
                link = clean_link(getattr(e, "link", "#"))
                if len(title) <= 15 or link == "#":
                    continue
                src = default_name
                try:
                    src = (e.get("source", {}) or {}).get("title") or default_name
                except Exception:
                    pass
                if src and title.endswith(f" - {src}"):
                    title = title[: -len(src) - 3].strip()
                snippet = re.sub(r"<[^>]+>", "", getattr(e, "summary", "")).strip()
                snippet = html_lib.unescape(re.sub(r"\s+", " ", snippet))[:280]
                articles.append({"title": title, "snippet": snippet, "link": link, "source_name": src,
                                 "lang": lang, "feed_category": cat})
                n += 1
            print(f"  RSS {default_name:<24} {n:>2} art.")
            if n == 0:
                print(f"    ⚠ pusty feed: {url}")
        except Exception as ex:
            print(f"  ✗ RSS {url}: {ex}")
    return articles


def fetch_article(url: str):
    """(tekst artykułu do ~1800 znaków, og:image lub None)."""
    if not url or "news.google.com" in url:
        return "", None
    try:
        req = urllib.request.Request(url, headers=HEADERS)
        with urllib.request.urlopen(req, timeout=8) as r:
            raw = r.read(600_000).decode("utf-8", errors="ignore")
    except Exception:
        return "", None
    img = None
    for pat in (r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']',
                r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image["\']'):
        m = re.search(pat, raw, re.I)
        if m:
            u = html_lib.unescape(m.group(1).strip())
            img = "https:" + u if u.startswith("//") else u
            img = img if img.startswith("http") else None
            break
    paras = []
    for p in re.findall(r"<p[^>]*>(.*?)</p>", raw, re.S | re.I):
        t = re.sub(r"\s+", " ", html_lib.unescape(re.sub(r"<[^>]+>", " ", p))).strip()
        if len(t) >= 60:
            paras.append(t)
    return " ".join(paras)[:1800], img


def build_candidates(clustered: list) -> list:
    pool = interleave(clustered, MAX_PER_SOURCE, MAX_POOL)
    with ThreadPoolExecutor(max_workers=8) as ex:
        results = list(ex.map(lambda a: fetch_article(a["link"]), pool))
    for a, (text, og) in zip(pool, results):
        a["text"], a["og_image"] = text, og
        a["grounded"] = len(text) >= GROUNDED_MIN_CHARS
    grounded = [a for a in pool if a["grounded"]]
    ungrounded = [a for a in pool if not a["grounded"]][:MAX_UNGROUNDED_CAND]
    cands = (grounded + ungrounded)[:MAX_CANDIDATES]
    print(f"  kandydaci: {len(cands)} (z pełnym tekstem: {sum(c['grounded'] for c in cands)})")
    return cands


def pick_photo(photos: list, query: str, used: set, sensitive: bool, min_score: int):
    """Zdjęcie musi pasować do zapytania (opis alt); odrzuca obrazy sugerujące inne zdarzenie."""
    words = set(re.findall(r"[a-z]{4,}", query.lower())) - GENERIC_WORDS
    need = max(min_score, -(-len(words) // 2)) if min_score else 0
    best, best_score = None, -1
    for p in photos:
        src = p.get("src", {})
        u = src.get("large") or src.get("medium")
        alt = (p.get("alt") or "").lower()
        if not u or u in used or BAD_ALT_RE.search(alt) or (sensitive and PEOPLE_RE.search(alt)):
            continue
        score = sum(1 for w in words if w in alt)
        if score > best_score:
            best, best_score = (p, u), score
    return best if best and best_score >= need else None


def fetch_pexels(query: str, used: set, sensitive: bool, min_score: int):
    if not PEXELS_API_KEY:
        return None
    for attempt in range(3):
        try:
            url = f"https://api.pexels.com/v1/search?query={urllib.parse.quote(query)}&per_page=20&orientation=landscape"
            req = urllib.request.Request(url, headers={"Authorization": PEXELS_API_KEY,
                                                       "User-Agent": "SwiatWMinute-Bot/1.0"})
            with urllib.request.urlopen(req, timeout=8) as r:
                photos = json.loads(r.read().decode("utf-8")).get("photos", [])
            hit = pick_photo(photos, query, used, sensitive, min_score)
            if hit:
                used.add(hit[1])
                return {"url": hit[1], "credit": hit[0].get("photographer", ""), "credit_url": hit[0].get("url", "")}
            return None
        except Exception as ex:
            if attempt == 2:
                print(f"  Pexels '{query}': {ex}")
            time.sleep(1.5)
    return None


# ───────────────────────── GEMINI ─────────────────────────
def gen_json(client, prompt: str, temperature: float):
    resp = client.models.generate_content(
        model=GEMINI_MODEL, contents=prompt,
        config=types.GenerateContentConfig(response_mime_type="application/json", temperature=temperature))
    text = re.sub(r"^```(?:json)?|```$", "", (resp.text or "").strip()).strip()
    return json.loads(text)


PROMPT = """Jesteś ostrym, rzetelnym redaktorem serwisu „Świat w Minutę” (Instagram/Threads). Styl: dynamiczny, konkretny, z pazurem.
Ale wszystko, co piszesz, musi dać się obronić tekstem źródła.

FAKTY (ważniejsze niż styl):
1. Używaj WYŁĄCZNIE informacji z pól "title" i "text" danego artykułu. Nie dodawaj liczb, dat, cytatów, nazwisk, przyczyn,
   prognoz ani kontekstu spoza danych. Zastrzeżenia źródła ("prawdopodobnie", "wstępnie", "według") zachowaj we wszystkich polach.
2. Nie używaj nieokreślonych ilości ("kilkanaście", "liczne", "wiele", "setki"), jeśli źródło nie podaje takiego sformułowania.
3. Pozycje z "grounded": false mają tylko tytuł i krótki opis. Pisz je KRÓCEJ (threads_post łącznie 250-400 znaków), tylko
   z tego, co jest w tytule i opisie, bez dopełniania treści ogólnikami. Zastrzeżenie z nazwą źródła ("Fakt informuje:") daj RAZ,
   w hooku — nie powtarzaj "według doniesień" w każdym polu. Wybierz takich pozycji najwyżej 2.
4. Nie przypisuj nikomu intencji ani motywów, których nie podaje źródło.
5. Nie zakładaj pory dnia, miejsca ani sytuacji odbiorcy ("poranne", "stoisz w korku"). Pytanie ma wynikać wprost z faktu.

OSTRY STYL (w granicach faktów):
- "title": mocny czasownik lub konkretna liczba/fakt ze źródła, do 60 znaków, bez pytajników, bez przesady ponad treść.
- "comment": 1 zdanie (14-22 słów), CIĘTE, zbudowane na kontraście lub skali dwóch faktów/liczb ze źródła albo na
  nieoczywistym skutku. Wolno ironizować ze zjawisk, liczb i decyzji — nie z osób i grup ludzi.
  ZAKAZANE sformułowania: "pokazuje", "dowodzi", "ujawnia", "świadczy", "podkreśla", "dobitnie", "po raz kolejny",
  "kluczowy", "w sam punkt". Komentarz NIE może powtarzać summary innymi słowami.
  Zły: "To pokazuje, jak trudne jest życie w kryzysie."
  Dobry (fikcyjny wzór struktury): "Firma zapowiada 500 nowych miejsc pracy, ale w tym samym komunikacie zwalnia 700 osób."
- Zwracaj się do odbiorcy na „ty”. Zero formalnego „Państwa”. Naturalna polszczyzna, bez kalk z angielskiego.
- W threads_post nie powtarzaj komentarza słowo w słowo; zakończ pytaniem do odbiorców.

FORMAT:
- Każda pozycja = INNY temat. Nie wybieraj tematu dotyczącego tego samego wydarzenia co pozycje z archiwum, nawet jeśli
  źródło lub język są inne. Max 3 pozycje z jednego źródła, różnorodne kategorie.
- Wybierz do 14 tematów (mniej, jeśli brakuje dobrych, unikalnych — nie dobieraj na siłę).
- Kategoria: POLSKA, GOSPODARKA, BIZNES, GEOPOLITYKA, OBRONNOŚĆ (tylko wojsko/zbrojenia), TECHNOLOGIE, ŚWIAT (wypadki,
  katastrofy, zdrowie, wydarzenia ogólne).
- Emoji w tytule TYLKO z: 🚨 📉 📈 💥 🔥 ⚠️ ⚖️ 🏛️ 🛡️ 🪖 💰 🛢️ ⚡ 🤖 💻 🏥 🌍 🚀 🏗️ 📊 ⏰ 🏢 🌉 🏭 💵 🏦 🛒 🚗 ✈️ 🚢 🌾 ⚓ 🧬 🔋 📡 🗳️ 💼 🔒 ⛽
- Flagi tylko dla miejsca/tematu. Przy atakach, zamieszkach, konfliktach zbrojnych NIE dawaj flag stron konfliktu.

Zwróć TABLICĘ JSON obiektów:
- "id": liczba, id artykułu z danych (kopiuj dokładnie)
- "category", "title" (emoji + NAGŁÓWEK DUŻYMI LITERAMI), "hook" (1 zdanie), "summary" (2 zdania, same fakty), "comment"
- "threads_post": dwa posty rozdzielone linią ---ODPOWIEDŹ---
    Post 1 (320-380 znaków; dla "grounded": false krócej): NAGŁÓWEK Z EMOJI, linia-hook, 1-2 zdania sedna, na końcu:
      (Szczegóły i tło w odpowiedzi 👇🧵)
    Post 2 (380-450 znaków; dla "grounded": false krócej): kontekst i liczby ze źródła, pytanie do odbiorców kończące się 👇💬
    Linie oddzielaj podwójnym znakiem nowej linii.
- "question": pytanie do odbiorców na „ty”, zakończone 👇💬
- "image_query": 2-5 angielskich słów — konkretny, neutralny obiekt lub miejsce (bez nazwisk)
- "sensitive": true, jeśli temat dotyczy przemocy, wypadku, śmierci, przestępstwa lub zdrowia konkretnej osoby

Archiwum (te wydarzenia już były, nie powtarzaj ich):
__PREV__

Dane wejściowe:
__CANDIDATES__
"""

DEDUPE_PROMPT = """Poniżej NOWE pozycje i ARCHIWUM (to już opublikowano). Dla każdej nowej pozycji oceń, czy opisuje TO SAMO
WYDARZENIE (ten sam incydent, decyzję, raport, atak, sprawę) co którakolwiek pozycja z archiwum — niezależnie od źródła i języka.
Nowy, istotnie różny rozwój sprawy (nowe fakty, nowa decyzja) NIE jest powtórką.
Zwróć JSON: {"repeats": [id, id, ...]} — tylko id powtórek (pusta tablica, jeśli brak).

NOWE:
__NEW__

ARCHIWUM:
__OLD__
"""

REVIEW_PROMPT = """Jesteś redaktorem-weryfikatorem. Dla KAŻDEJ pozycji porównaj pola z "source_text" i "source_title".
1. Usuń lub zastąp ostrożniejszym sformułowaniem każde twierdzenie, liczbę, nazwisko, przyczynę lub prognozę, których NIE wspiera
   source_text. Zastrzeżenia źródła ("prawdopodobnie", "wstępnie", "według") muszą być zachowane we wszystkich polach,
   także w threads_post. Jeśli "grounded": false, trzymaj się wyłącznie tytułu i opisu.
2. Popraw błędy językowe: gramatykę, odmianę, ortografię, kalki z angielskiego.
3. Zachowaj ostry, dynamiczny styl, zwrot do odbiorcy na „ty” i strukturę threads_post (separator ---ODPOWIEDŹ---, podwójne
   nowe linie, emoji, długość ±15%). Nie łagodź stylu bez potrzeby.
4. Nie dodawaj nowych informacji.
Zwróć TABLICĘ JSON: dla każdej pozycji obiekt z polami id, title, hook, summary, comment, threads_post, question.

Pozycje:
__ITEMS__
"""


def validate_items(raw_items: list, candidates: list, known_links: set, known_titles: list) -> list:
    required = {"id", "category", "title", "hook", "summary", "comment", "threads_post", "question", "image_query"}
    valid, seen_titles, seen_ids, ungrounded_n = [], [], set(), 0
    rej = Counter()
    for it in raw_items:
        if not isinstance(it, dict) or not required.issubset(it.keys()):
            rej["brak pól"] += 1
            continue
        try:
            idx = int(it["id"])
            cand = candidates[idx]
        except Exception:
            rej["zły id"] += 1
            continue
        if idx in seen_ids or norm_link(cand["link"]) in known_links:
            rej["powtórka linku/id"] += 1
            continue
        category = normalize_category(it["category"])
        title = format_title(it["title"], category)
        summary, comment = str(it["summary"]).strip(), str(it["comment"]).strip()
        post = str(it["threads_post"]).strip()
        min_post = 400 if cand["grounded"] else 250
        if (len(title) < 10 or len(summary) < 25 or len(comment) < 10 or len(post) < min_post
                or "---ODPOWIEDŹ---" not in post):
            rej["za krótkie / zły format"] += 1
            continue
        if any(are_topics_duplicate(title, p, 0.35) for p in seen_titles + known_titles):
            rej["powtórka tematu"] += 1
            continue
        if not cand["grounded"]:
            if ungrounded_n >= MAX_UNGROUNDED_ITEMS:
                rej["limit pozycji bez tekstu"] += 1
                continue
            ungrounded_n += 1
        seen_ids.add(idx)
        seen_titles.append(title)
        valid.append({
            "id": short_id(cand["link"]), "category": category, "title": title,
            "hook": str(it["hook"]).strip(), "summary": summary, "comment": comment,
            "threads_post": post, "question": str(it["question"]).strip(),
            "image_query": str(it["image_query"]).strip() or "world news",
            "link": cand["link"], "source_name": cand["source_name"], "source_title": cand["title"],
            "grounded": cand["grounded"], "sensitive": bool(it.get("sensitive", False)),
            "_og": cand.get("og_image"),
            "_src": ((cand.get("text") or "") + " " + cand["snippet"])[:1800],
        })
    if rej:
        print(f"   odrzucone: {dict(rej)}")
    return valid


def review_items(client, items: list) -> list:
    """Drugi przebieg: usuwa twierdzenia bez pokrycia w źródle i poprawia język. Z zabezpieczeniami."""
    payload = [{"id": i["id"], "grounded": i["grounded"], "source_title": i["source_title"], "source_text": i["_src"],
                "title": i["title"], "hook": i["hook"], "summary": i["summary"], "comment": i["comment"],
                "threads_post": i["threads_post"], "question": i["question"]} for i in items]
    try:
        data = gen_json(client, REVIEW_PROMPT.replace("__ITEMS__", json.dumps(payload, ensure_ascii=False)), 0.1)
    except Exception as ex:
        print(f"  redakcja nie powiodła się (zostawiam wersję z 1. przebiegu): {ex}")
        return items
    fixed = {str(d.get("id")): d for d in data if isinstance(d, dict)} if isinstance(data, list) else {}
    changed = 0
    for it in items:
        d = fixed.get(it["id"])
        if not d:
            continue
        new = {k: str(d.get(k, "")).strip() for k in ("title", "hook", "summary", "comment", "threads_post", "question")}
        if (len(new["title"]) < 10 or len(new["summary"]) < 25 or len(new["comment"]) < 10
                or len(new["threads_post"]) < (400 if it["grounded"] else 250) or "---ODPOWIEDŹ---" not in new["threads_post"]):
            continue
        new["title"] = format_title(new["title"], it["category"])
        if any(new[k] != it[k] for k in new):
            changed += 1
        it.update(new)
    print(f"  redakcja: zmieniono {changed}/{len(items)} pozycji")
    return items


def drop_repeated_events(client, items: list, known_events: list) -> list:
    """Semantyczna kontrola: usuwa pozycje opisujące to samo wydarzenie co archiwum (inne źródło/język)."""
    if not items or not known_events:
        return items
    new = [{"id": i["id"], "title": i["title"], "summary": i["summary"][:200]} for i in items]
    prompt = (DEDUPE_PROMPT.replace("__NEW__", json.dumps(new, ensure_ascii=False))
                           .replace("__OLD__", json.dumps(known_events[:90], ensure_ascii=False)))
    try:
        data = gen_json(client, prompt, 0.0)
        ids = {str(x) for x in (data.get("repeats", []) if isinstance(data, dict) else [])}
    except Exception as ex:
        print(f"  kontrola powtórzeń nie powiodła się: {ex}")
        return items
    kept = [i for i in items if i["id"] not in ids]
    for i in items:
        if i["id"] in ids:
            print(f"  ↺ powtórka wydarzenia z archiwum → {i['title'][:55]}")
    return kept


def check_numbers(items: list) -> list:
    """Liczby w tekście muszą występować w źródle. Pozycje bez pełnego tekstu z obcymi liczbami odpadają."""
    out = []
    for it in items:
        blob = it["source_title"] + " " + it["_src"]
        mine = numbers_in(" ".join(it[k] for k in ("title", "hook", "summary", "comment", "threads_post", "question")))
        extra = sorted(mine - numbers_in(blob))
        if extra:
            print(f"  ⚠ liczby bez pokrycia w źródle {extra[:5]} → {it['title'][:50]}")
            if not it["grounded"]:
                continue
            it["needs_review"] = extra[:5]
        out.append(it)
    return out


def translate_titles(client, titles: list) -> list:
    if not titles:
        return []
    prompt = ("Przetłumacz na polski poniższe nagłówki prasowe. Zachowaj sens i nazwy własne, niczego nie dodawaj. "
              "Zwróć WYŁĄCZNIE tablicę JSON ze stringami, dokładnie tyle elementów co na wejściu, w tej samej kolejności.\n"
              + json.dumps(titles, ensure_ascii=False))
    try:
        data = gen_json(client, prompt, 0.1)
        if isinstance(data, list) and len(data) == len(titles):
            return [str(x).strip() or t for x, t in zip(data, titles)]
    except Exception as ex:
        print(f"  tłumaczenie nagłówków nie powiodło się: {ex}")
    return titles


# ───────────────────────── GŁÓWNY PRZEPŁYW ─────────────────────────
def main():
    if not GEMINI_API_KEY:
        sys.exit("Brak GEMINI_API_KEY")
    if not PEXELS_API_KEY:
        print("⚠ Brak PEXELS_API_KEY — zdjęcia będą zastępcze")

    now = datetime.now(PL_TZ)
    session = "poranne" if now.hour < 12 else "wieczorne"
    session_key = f"{now.strftime('%Y-%m-%d')}_{session}"

    print("1. RSS")
    raw = fetch_feeds()
    print(f"   razem {len(raw)} artykułów")
    if not raw:
        sys.exit("Brak artykułów z RSS — nie nadpisuję plików")

    archive = {}
    if os.path.exists("archive.json"):
        try:
            with open("archive.json", encoding="utf-8") as f:
                archive = json.load(f)
        except Exception:
            archive = {}

    # Wszystko, co już publikowaliśmy (w tym wydanie poranne przy wieczornym)
    known_links, known_titles, known_events = set(), [], []
    for n, sk in enumerate(sorted(archive.keys(), reverse=True)):
        sc = archive.get(sk)
        if not isinstance(sc, dict) or sk == session_key:
            continue
        for i in sc.get("items", []):
            if i.get("link"):
                known_links.add(norm_link(i["link"]))
            if n < DEDUPE_TITLE_SESSIONS:
                known_titles += [t for t in (i.get("title"), i.get("source_title")) if t]
                known_events.append(f"{i.get('title', '')} — {str(i.get('summary', ''))[:160]}")

    print("2. Deduplikacja (archiwum + wewnątrz feedu)")
    clustered, seen = [], set()
    for a in raw:
        k = norm_link(a["link"])
        if k in seen or k in known_links:
            continue
        if any(are_topics_duplicate(a["title"], p) for p in known_titles):
            continue
        if any(are_topics_duplicate(a["title"], c["title"]) for c in clustered):
            continue
        clustered.append(a)
        seen.add(k)
    print(f"   nowych, unikalnych tematów: {len(clustered)} (z {len(raw)})")
    if not clustered:
        sys.exit("Brak nowych tematów — nie nadpisuję plików")

    print("3. Kandydaci + pełny tekst")
    candidates = build_candidates(clustered)
    ai_input = [{"id": i, "title": c["title"], "source": c["source_name"], "grounded": c["grounded"],
                 "text": (c.get("text") or c["snippet"])[:1500]} for i, c in enumerate(candidates)]

    print("4. Gemini: wybór i pisanie")
    client = genai.Client(api_key=GEMINI_API_KEY)
    prompt = (PROMPT.replace("__PREV__", json.dumps(known_events[:40], ensure_ascii=False))
                    .replace("__CANDIDATES__", json.dumps(ai_input, ensure_ascii=False)))
    items = []
    for attempt in (1, 2):
        try:
            parsed = gen_json(client, prompt, 0.35)
            raw_items = parsed if isinstance(parsed, list) else parsed.get("items", [])
            got = validate_items(raw_items, candidates, known_links, known_titles)
            print(f"   próba {attempt}: {len(got)} poprawnych z {len(raw_items)}")
            if len(got) > len(items):
                items = got
            if len(items) >= MIN_ITEMS:
                break
        except Exception as ex:
            print(f"   próba {attempt}: błąd AI: {ex}")

    # Awaryjnie: pozycje oparte wyłącznie na streszczeniu z RSS (bez dopisywania treści)
    if len(items) < MIN_ITEMS:
        used = {i["link"] for i in items}
        titles = [i["title"] for i in items]
        for c in candidates:
            if len(items) >= MIN_ITEMS:
                break
            if c["link"] in used or len(c["snippet"]) < 25 or c["lang"] != "pl":
                continue
            cat = normalize_category(c["feed_category"])
            t = format_title("📰 " + c["title"][:60], cat)
            if any(are_topics_duplicate(t, p, 0.35) for p in titles + known_titles):
                continue
            items.append({"id": short_id(c["link"]), "category": cat, "title": t, "hook": "", "summary": c["snippet"],
                          "comment": "", "threads_post": "", "question": "", "image_query": GENERIC_QUERY.get(cat, "news"),
                          "link": c["link"], "source_name": c["source_name"], "source_title": c["title"],
                          "grounded": c["grounded"], "sensitive": False, "auto": True, "_og": c.get("og_image"), "_src": ""})
            used.add(c["link"])
            titles.append(t)
        print(f"   po uzupełnieniu awaryjnym: {len(items)}")

    if not items:
        sys.exit("AI nie zwróciło żadnych pozycji — nie nadpisuję istniejących plików")

    print("4b. Gemini: kontrola powtórzeń wydarzeń względem archiwum")
    items = drop_repeated_events(client, items, known_events)
    if not items:
        sys.exit("Wszystkie tematy już były — nie nadpisuję istniejących plików")

    print("5. Gemini: redakcja i weryfikacja względem źródeł")
    ai_items = [i for i in items if not i.get("auto")]
    review_items(client, ai_items)
    items = check_numbers(ai_items) + [i for i in items if i.get("auto")]
    if not items:
        sys.exit("Po weryfikacji nic nie zostało — nie nadpisuję istniejących plików")
    for cat, n in Counter(i["category"] for i in items).most_common():
        print(f"   {cat}: {n}")

    print("6. Zdjęcia (Pexels)")
    used_imgs = set()
    for it in items:
        sens = it.pop("sensitive", False)
        ph = fetch_pexels(it["image_query"], used_imgs, sens, 1)
        if not ph and not sens:  # tematy wrażliwe: lepiej bez zdjęcia niż z nietrafionym
            ph = fetch_pexels(GENERIC_QUERY.get(it["category"], "news"), used_imgs, sens, 0)
        it["image_url"] = ph["url"] if ph else ""
        it["image_illustrative"] = bool(ph)
        it["image_credit"] = ph["credit"] if ph else ""
        it["image_credit_url"] = ph["credit_url"] if ph else ""
        og = it.pop("_og", None)
        it["source_image_url"] = og if (USE_SOURCE_IMAGES and og) else it["image_url"]
        it["image"] = it["source_image_url"]
        it.pop("_src", None)

    print("7. Tłumaczenie nagłówków raw_feed")
    chosen = {norm_link(i["link"]) for i in items}
    raw_out = [dict(a) for a in clustered[:80] if norm_link(a["link"]) not in chosen]
    to_tr = [a for a in raw_out if a["lang"] == "en"]
    for a, t in zip(to_tr, translate_titles(client, [a["title"] for a in to_tr])):
        a["title_pl"] = t
    for a in raw_out:
        a.setdefault("title_pl", a["title"])
        a.pop("feed_category", None)

    print("8. Zapis")
    out = {"date": f"{now.day} {POLISH_MONTHS[now.month]} {now.year}", "time": now.strftime("%H:%M"),
           "timestamp": now.strftime("%Y-%m-%d_%H:%M"), "items": items}
    write_json("news.json", out)
    archive[session_key] = out
    for old in sorted(archive.keys())[:-ARCHIVE_MAX_SESSIONS]:
        del archive[old]
    write_json("archive.json", archive)
    write_json("raw_feed.json", {"date": out["date"], "time": out["time"], "timestamp": out["timestamp"],
                                 "count": len(raw_out), "items": raw_out})
    print(f"✓ Zapisano {len(items)} pozycji ({session}); bez pełnego tekstu: {sum(not i['grounded'] for i in items)}")


if __name__ == "__main__":
    main()
