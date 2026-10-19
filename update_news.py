#!/usr/bin/env python3
"""Świat w Minutę — generator newsów (Gemini + Pexels).

Prompt i styl wypowiedzi bez zmian. Dodane: źródła artykułów, podpisy zdjęć, więcej kanałów RSS,
wyrównanie liczby tematów z jednego źródła, pola potrzebne stronie i generatorowi karuzel.
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
from datetime import datetime, timedelta
from time import mktime
from urllib.parse import parse_qs, urlparse
from zoneinfo import ZoneInfo

import feedparser
from google import genai
from google.genai import types

pl_tz = ZoneInfo("Europe/Warsaw")

PEXELS_API_KEY = os.environ.get("PEXELS_API_KEY", "")          # BEZ wartości domyślnej — klucz tylko w sekretach
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-3.6-flash")
USE_SOURCE_IMAGES = os.environ.get("USE_SOURCE_IMAGES", "0") == "1"   # 0 = zdjęcia z Pexels, 1 = og:image artykułu

MAX_AGE_HOURS = 24
MIN_ITEMS = 12
MAX_PER_SOURCE = 3          # ile artykułów z jednego źródła trafia do AI (żeby Money/Bankier nie dominowały)
MAX_CANDIDATES = 40
SNIPPET_LEN = 500
ARCHIVE_MAX_SESSIONS = 60

# (url, język, domyślna kategoria, nazwa źródła)
FEEDS = [
    # --- POLSKA: wiadomości (Polsat News: adresy z oficjalnej strony; pozostałe sprawdź w logu) ---
    ("https://www.polsatnews.pl/rss/polska.xml", "pl", "POLSKA", "Polsat News"),
    ("https://www.polsatnews.pl/rss/swiat.xml", "pl", "GEOPOLITYKA", "Polsat News"),
    ("https://www.polsatnews.pl/rss/biznes.xml", "pl", "GOSPODARKA", "Polsat News"),
    ("https://www.polsatnews.pl/rss/technologie.xml", "pl", "TECHNOLOGIE", "Polsat News"),
    ("https://tvn24.pl/najnowsze.xml", "pl", "POLSKA", "TVN24"),
    ("https://tvn24.pl/biznes.xml", "pl", "GOSPODARKA", "TVN24"),
    ("https://fakty.interia.pl/feed", "pl", "POLSKA", "Interia"),
    ("https://biznes.interia.pl/feed", "pl", "GOSPODARKA", "Interia Biznes"),
    ("https://wiadomosci.onet.pl/.feed", "pl", "POLSKA", "Onet"),
    ("https://wiadomosci.wp.pl/rss.xml", "pl", "POLSKA", "WP Wiadomości"),
    ("https://wiadomosci.gazeta.pl/pub/rss/wiadomosci_kraj.htm", "pl", "POLSKA", "Gazeta.pl"),
    ("https://notesfrompoland.com/feed/", "en", "POLSKA", "Notes from Poland"),
    # --- POLSKA: gospodarka, biznes, przemysł, obronność ---
    ("https://www.money.pl/rss/", "pl", "GOSPODARKA", "Money.pl"),
    ("https://businessinsider.com.pl/.rss", "pl", "BIZNES", "Business Insider Polska"),
    ("https://www.bankier.pl/rss/wiadomosci.xml", "pl", "GOSPODARKA", "Bankier.pl"),
    ("https://www.wnp.pl/rss/artykuly.xml", "pl", "GOSPODARKA", "WNP.pl"),
    ("https://archiwum.rp.pl/rss/ekonomia", "pl", "GOSPODARKA", "Rzeczpospolita"),
    ("https://defence24.pl/rss", "pl", "OBRONNOŚĆ", "Defence24"),
    ("https://news.google.com/rss?hl=pl&gl=PL&ceid=PL:pl", "pl", "POLSKA", "Google News"),
    # --- ŚWIAT: rynki, finanse, surowce ---
    ("https://feeds.bloomberg.com/markets/news.rss", "en", "GOSPODARKA", "Bloomberg"),
    ("https://search.cnbc.com/rs/search/view.html?partnerId=2000&keywords=markets&sort=date", "en", "GOSPODARKA", "CNBC"),
    # --- GEOPOLITYKA I WYDARZENIA GLOBALNE ---
    ("https://feeds.bbci.co.uk/news/world/rss.xml", "en", "GEOPOLITYKA", "BBC News"),
    ("https://feeds.bbci.co.uk/news/world/us_and_canada/rss.xml", "en", "GEOPOLITYKA", "BBC News"),
    ("https://www.theguardian.com/world/rss", "en", "GEOPOLITYKA", "The Guardian"),
    ("https://www.aljazeera.com/xml/rss/all.xml", "en", "GEOPOLITYKA", "Al Jazeera"),
    ("https://rss.nytimes.com/services/xml/rss/nyt/World.xml", "en", "GEOPOLITYKA", "The New York Times"),
    ("https://rss.dw.com/rdf/rss-en-all", "en", "GEOPOLITYKA", "Deutsche Welle"),
    ("https://news.google.com/rss/search?q=world+news+geopolitics&hl=en-US&gl=US&ceid=US:en", "en", "GEOPOLITYKA", "Google News"),
    # --- TECHNOLOGIE / AI ---
    ("https://feeds.arstechnica.com/arstechnica/index", "en", "TECHNOLOGIE", "Ars Technica"),
    ("https://www.theverge.com/rss/index.xml", "en", "TECHNOLOGIE", "The Verge"),
]
# Usunięto: reutersagency.com/feed (feedy Reuters Agency nie działają od lat)

POLISH_MONTHS = {
    1: "stycznia", 2: "lutego", 3: "marca", 4: "kwietnia",
    5: "maja", 6: "czerwca", 7: "lipca", 8: "sierpnia",
    9: "września", 10: "października", 11: "listopada", 12: "grudnia"
}

STOP_WORDS = {
    "polsce", "polski", "polaków", "nowy", "nowa", "nowe", "roku", "swiat", "przez",
    "tylko", "rzad", "rząd", "beda", "będą", "moze", "może", "oraz", "jest", "jego",
    "bardzo", "nawet", "teraz", "after", "with", "from", "that", "this", "more"
}
HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"),
    "Accept": "text/html,application/xhtml+xml",
    "Accept-Language": "en-US,en;q=0.9,pl;q=0.8",
}
# zdjęcia sugerujące INNE wydarzenie (np. huragan przy zamieszkach) — nigdy nie wybierane
BAD_ALT_RE = re.compile(r"hurricane|tornado|flood|earthquake|tsunami|cemetery|grave|funeral|coffin|abandoned|ruins|corpse", re.I)
GENERIC_WORDS = {"view", "sign", "signs", "street", "night", "scene", "modern", "aerial", "system", "line",
                 "tracks", "landscape", "area", "concept", "background", "city"}


# ───────────────────────── NARZĘDZIA ─────────────────────────
def clean_link(url: str) -> str:
    if not url or url == "#":
        return "#"
    try:
        tracking_params = {
            "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
            "at_medium", "at_campaign", "fbclid", "gclid", "mc_cid", "mc_eid"
        }
        parsed = urlparse(url)
        if parsed.scheme not in ("http", "https"):
            return "#"
        if parsed.query:
            qs = parse_qs(parsed.query)
            clean_qs = {k: v[0] for k, v in qs.items() if k not in tracking_params}
            if clean_qs:
                return f"{parsed.scheme}://{parsed.netloc}{parsed.path}?{urllib.parse.urlencode(clean_qs)}"
            return f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
        return url
    except Exception:
        return url


def norm_link(url: str) -> str:
    """Klucz porównawczy linków (bez schematu, www, końcowego /, parametrów poza Google News)."""
    try:
        p = urlparse(str(url).strip().lower())
        host = p.netloc.removeprefix("www.")
        return f"{host}{p.path.rstrip('/')}" + (f"?{p.query}" if "news.google.com" in host and p.query else "")
    except Exception:
        return str(url)


def short_id(link: str) -> str:
    return hashlib.sha1(link.encode("utf-8")).hexdigest()[:10]


def is_recent(entry) -> bool:
    published = getattr(entry, "published_parsed", None) or getattr(entry, "updated_parsed", None)
    if not published:
        return True
    try:
        pub_dt = datetime.fromtimestamp(mktime(published), tz=pl_tz)
        return datetime.now(pl_tz) - pub_dt <= timedelta(hours=MAX_AGE_HOURS)
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
    if "GEOPOLITYK" in c or "ŚWIAT" in c:
        return "GEOPOLITYKA"
    if "BIZNES" in c or "SPÓŁK" in c or "FIRM" in c:
        return "BIZNES"
    return "GOSPODARKA"


def format_uppercase_title(title_str: str) -> str:
    s = re.sub(r"\s+\ufe0f", "\ufe0f", title_str.strip())      # naprawia „⚖ ” (spacja przed selektorem emoji)
    if not s:
        return ""
    match = re.match(r'^([\U00010000-\U0010ffff\u2600-\u27bf\ufe0f\s]+)(.*)$', s)
    if match:
        emoji_prefix = match.group(1).strip()
        rest = match.group(2).strip()
        return f"{emoji_prefix} {rest.upper()}".strip()
    return s.upper()


def extract_keywords(text: str) -> set:
    words = re.findall(r'[a-zA-ZąćęłńóśźżĄĆĘŁŃÓŚŹŻ]{4,}', text.lower())
    return {w for w in words if w not in STOP_WORDS}


def are_topics_duplicate(title1: str, title2: str, threshold: float = 0.40) -> bool:
    w1, w2 = extract_keywords(title1), extract_keywords(title2)
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


def gen_json(client, prompt: str, temperature: float, safety=None):
    cfg = dict(response_mime_type="application/json", temperature=temperature)
    if safety:
        cfg["safety_settings"] = safety
    resp = client.models.generate_content(model=GEMINI_MODEL, contents=prompt, config=types.GenerateContentConfig(**cfg))
    text = re.sub(r"^```(?:json)?|```$", "", (resp.text or "").strip()).strip()
    return json.loads(text)


# ───────────────────────── RSS ─────────────────────────
def load_feed(url: str):
    """Pobiera feed z przeglądarkowym User-Agent (domyślny UA feedparsera bywa blokowany)."""
    try:
        req = urllib.request.Request(url, headers={"User-Agent": HEADERS["User-Agent"],
                                                   "Accept": "application/rss+xml, application/xml, text/xml, */*"})
        with urllib.request.urlopen(req, timeout=15) as r:
            return feedparser.parse(r.read()), None
    except Exception as ex:
        return None, str(ex)[:70]


def fetch_feeds() -> list:
    articles = []
    for url, lang, cat, default_name in FEEDS:
        feed, err = load_feed(url)
        if feed is None:
            print(f"  ✗ RSS {default_name:<24} {err}  ({url[:60]})")
            continue
        n = 0
        for entry in feed.entries[:12]:
            if not is_recent(entry):
                continue
            title = getattr(entry, "title", "").strip()
            link = clean_link(getattr(entry, "link", "#"))
            if len(title) <= 15 or link == "#":
                continue
            src = default_name
            try:   # Google News podaje prawdziwego wydawcę w <source>
                src = (entry.get("source", {}) or {}).get("title") or default_name
            except Exception:
                pass
            if src and title.endswith(f" - {src}"):
                title = title[: -len(src) - 3].strip()
            summary = re.sub(r"<[^>]+>", "", getattr(entry, "summary", "")).strip()
            snippet = html_lib.unescape(re.sub(r"\s+", " ", summary))[:SNIPPET_LEN]
            articles.append({"title": title, "snippet": snippet, "link": link, "source_name": src,
                             "lang": lang, "feed_category": cat})
            n += 1
        print(f"  RSS {default_name:<24} {n:>2} art.")
        if n == 0:
            print(f"    ⚠ pusty feed: {url}")
    return articles


def interleave(items: list, per_source: int, limit: int) -> list:
    """Round-robin po źródłach: żadne źródło nie zdominuje listy kandydatów."""
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


# ───────────────────────── ZDJĘCIA ─────────────────────────
def pick_photo(photos: list, query: str, used: set):
    """Najpierw zdjęcie, którego opis (alt) pasuje do zapytania; zawsze pomija obrazy sugerujące inne zdarzenie."""
    words = set(re.findall(r"[a-z]{4,}", query.lower())) - GENERIC_WORDS
    best, best_score = None, -1
    for p in photos:
        src = p.get("src", {})
        u = src.get("large") or src.get("medium")
        alt = (p.get("alt") or "").lower()
        if not u or u in used or BAD_ALT_RE.search(alt):
            continue
        score = sum(1 for w in words if w in alt)
        if score > best_score:
            best, best_score = (p, u), score
    return best


def fetch_pexels(query: str, used: set, retries: int = 2):
    if not PEXELS_API_KEY:
        return None
    for attempt in range(retries + 1):
        try:
            url = f"https://api.pexels.com/v1/search?query={urllib.parse.quote(query)}&per_page=15&orientation=landscape"
            req = urllib.request.Request(url, headers={"Authorization": PEXELS_API_KEY, "User-Agent": "SwiatWMinute-Bot/1.0"})
            with urllib.request.urlopen(req, timeout=8) as resp:
                photos = json.loads(resp.read().decode("utf-8")).get("photos", [])
            hit = pick_photo(photos, query, used)
            if hit:
                p, u = hit
                used.add(u)
                src = p.get("src", {})
                return {"url": u, "portrait": src.get("portrait") or src.get("large2x") or u,
                        "credit": p.get("photographer", ""), "credit_url": p.get("url", "")}
            return None
        except Exception as ex:
            if attempt == retries:
                print(f"Błąd Pexels dla '{query}': {ex}")
            else:
                time.sleep(1.5)
    return None


def fetch_article_image(url: str):
    if not url or url == "#" or "news.google.com" in url:
        return None
    try:
        req = urllib.request.Request(url, headers=HEADERS)
        with urllib.request.urlopen(req, timeout=7) as resp:
            page = resp.read(800_000).decode("utf-8", errors="ignore")
        for pat in (r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']',
                    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image["\']',
                    r'<meta[^>]+name=["\']twitter:image["\'][^>]+content=["\']([^"\']+)["\']',
                    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+name=["\']twitter:image["\']'):
            m = re.search(pat, page, re.I)
            if m:
                img = html_lib.unescape(m.group(1).strip())
                if img.startswith("//"):
                    img = "https:" + img
                if img.startswith("http"):
                    return img
    except Exception as ex:
        print(f"  brak og:image ({url[:55]}…): {ex}")
    return None


# ───────────────────────── WALIDACJA I DOPASOWANIE ŹRÓDŁA ─────────────────────────
def validate_items(items: list) -> list:
    required = {"category", "title", "hook", "summary", "comment", "threads_post", "question", "image_query", "link"}
    valid, seen_titles, seen_links = [], [], set()
    for item in items:
        if not isinstance(item, dict) or not required.issubset(item.keys()):
            continue
        title = format_uppercase_title(str(item.get("title", "")))
        hook = str(item.get("hook", "")).strip()
        summary = str(item.get("summary", "")).strip()
        comment = str(item.get("comment", "")).strip()
        threads_post = str(item.get("threads_post", "")).strip()
        question = str(item.get("question", "")).strip()
        category = normalize_category(item.get("category", "GOSPODARKA"))
        image_query = str(item.get("image_query", "world news")).strip()
        link = clean_link(str(item.get("link", "#")))
        if len(title) < 10 or len(summary) < 25 or len(comment) < 10 or len(threads_post) < 420:
            continue
        if "---ODPOWIEDŹ---" not in threads_post:
            continue
        if link != "#" and link in seen_links:
            continue
        if any(are_topics_duplicate(title, prev, threshold=0.35) for prev in seen_titles):
            continue
        seen_titles.append(title)
        if link != "#":
            seen_links.add(link)
        valid.append({"category": category, "title": title, "hook": hook, "summary": summary, "comment": comment,
                      "threads_post": threads_post, "question": question, "image_query": image_query, "link": link})
    return valid


def resolve_sources(items: list, candidates: list) -> list:
    """Przypisuje każdej pozycji prawdziwy artykuł-źródło (link, nazwa). Pozycje bez źródła odpadają
    (model potrafi przepisać link z przykładu w prompcie)."""
    by_link = {norm_link(a["link"]): a for a in candidates}
    out, used = [], set()
    for it in items:
        a = by_link.get(norm_link(it["link"]))
        if not a:   # zapas: najlepsze dopasowanie po słowach kluczowych tytułu/streszczenia
            kw = extract_keywords(it["title"] + " " + it["summary"])
            best, best_n = None, 0
            for c in candidates:
                n = len(kw & extract_keywords(c["title"]))
                if n > best_n:
                    best, best_n = c, n
            a = best if best_n >= 2 else None
        if not a or a["link"] in used:
            print(f"  ✗ odrzucono (brak źródła w danych wejściowych): {it['title'][:55]}")
            continue
        used.add(a["link"])
        it["link"] = a["link"]
        it["source_name"] = a["source_name"]
        it["source_title"] = a["title"]
        it["lang"] = a["lang"]
        it["id"] = short_id(a["link"])
        out.append(it)
    return out


DEDUPE_PROMPT = """Poniżej NOWE pozycje i ARCHIWUM (to już opublikowano). Dla każdej nowej pozycji oceń, czy opisuje TO SAMO
WYDARZENIE (ten sam incydent, decyzję, raport, atak, sprawę) co którakolwiek pozycja z archiwum — niezależnie od źródła i języka.
Nowy, istotnie różny rozwój sprawy (nowe fakty, nowa decyzja) NIE jest powtórką.
Zwróć JSON: {"repeats": [id, id, ...]} — tylko id powtórek (pusta tablica, jeśli brak).

NOWE:
__NEW__

ARCHIWUM:
__OLD__
"""


def drop_repeated_events(client, items: list, known_events: list) -> list:
    if not items or not known_events:
        return items
    new = [{"id": i["id"], "title": i["title"], "summary": i["summary"][:200]} for i in items]
    prompt = DEDUPE_PROMPT.replace("__NEW__", json.dumps(new, ensure_ascii=False)).replace("__OLD__", json.dumps(known_events[:90], ensure_ascii=False))
    try:
        data = gen_json(client, prompt, 0.0)
        ids = {str(x) for x in (data.get("repeats", []) if isinstance(data, dict) else [])}
    except Exception as ex:
        print(f"  kontrola powtórzeń nie powiodła się: {ex}")
        return items
    for i in items:
        if i["id"] in ids:
            print(f"  ↺ powtórka wydarzenia z archiwum → {i['title'][:55]}")
    return [i for i in items if i["id"] not in ids]


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


# ───────────────────────── PROMPT (styl bez zmian) ─────────────────────────
def build_prompt(previous_titles: list, candidates: list) -> str:
    ai_input = [{"title": a["title"], "snippet": a["snippet"], "link": a["link"], "source": a["source_name"]} for a in candidates]
    return f"""Jesteś redaktorem naczelnym formatu informacyjno-analitycznego „Świat w Minucie” (Instagram/Threads). 
Twoje posty zdobywają wirale, ponieważ wybierasz RÓŻNORODNE, MOCNE I NAJCIEKAWSZE wydarzenia dnia.

KATEGORYCZNY ZAKAZ DUBLOWANIA TEMATÓW (1 TEMAT = DOKŁADNIE 1 WPIS):
- Każda wygenerowana wiadomość MUSI dotyczyć ZUPEŁNIE INNEJ sprawy, innej spółki, innego kraju lub problemu.
- Kategoryczny zakaz generowania dwóch wpisów o tej samej ustawie, tym samym polityku, tej samej spółce czy tym samym raporcie giełdowym!
- Jeśli w danych wejściowych jest kilka ciekawych tematów z Polski, technologii, surowców i obronności, MASZ WYBRAĆ PRZEKRÓJ NAJLEPSZYCH, a nie skupiać się na jednym wątku.

Zadanie: Z poniższych unikalnych artykułów wybierz DOKŁADNIE 14-15 NAJWAŻNIEJSZYCH I NAJBARDZIEJ WCIĄGAJĄCYCH tematów w formacie JSON.

ZASADA 1: NAGŁÓWEK ("title"):
[Trafna emotikona] [AGRESYWNY, MOCNY NAGŁÓWEK DUŻYMI LITERAMI DO 60 ZNAKÓW]

ZASADA 2: FORMAT THREADS ("threads_post") - DWA POSTY (650-800 ZNAKÓW):
CZĘŚĆ 1 (Post główny – 320-380 znaków):
[NAGŁÓWEK DUŻYMI LITERAMI Z EMOTIKONĄ]
[Krzykliwy podwójny hook z flagami i wykrzyknikiem]
[1-2 zdania uderzające w sedno problemu, zakończone:]
(Szczegóły i tło w odpowiedzi 👇🧵)

---ODPOWIEDŹ---

CZĘŚĆ 2 (Odpowiedź pod postem – 380-450 znaków):
[Konkretne liczby, kulisy i mechanizm, którego NIE MA na slajdzie graficznym]
[1 bezlitosne, cięte zdanie podsumowujące obłudę lub realne koszty]
[Konkretne pytanie prowokujące do dyskusji kończące się '👇💬']

ZASADA 3: CIĘTY KOMENTARZ NA SLAJD ("comment"):
- DOKŁADNIE 1 ZDANIE (14-22 słowa, KRÓTSZE NIŻ SUMMARY). Zero banałów.

ZASADA 4: POJEDYNCZE KATEGORIE:
Pole "category" to DOKŁADNIE JEDNO słowo:
- "POLSKA" (min. 4)
- "GOSPODARKA" (min. 4)
- "BIZNES" (2-3)
- "GEOPOLITYKA" (2)
- "OBRONNOŚĆ" (max 2)
- "TECHNOLOGIE" (max 1-2)

WZORCOWY OBIEKT:
{{
  "category": "GOSPODARKA",
  "title": "🚨 RZĄD PRZEPYCHA NOWY PODATEK: ZAPŁACĄ WSZYSCY KIEROWCY",
  "hook": "Nowa opłata paliwowa wchodzi tylnymi drzwiami bez konsultacji społecznych.",
  "summary": "Stawka wzrośnie o 14% od pierwszego dnia przyszłego miesiąca, co przełoży się na wzrost cen litra benzyny o 35 groszy. Ministerstwo tłumaczy decyzję koniecznością łatania dziury w Funduszu Drogowym.",
  "comment": "Rządzący znowu opowiadają bajki o ochronie portfeli, podczas gdy przy dystrybutorze ściągają z nas kolejny ukryty haracz.",
  "threads_post": "🚨 RZĄD PRZEPYCHA NOWY PODATEK: ZAPŁACĄ WSZYSCY KIEROWCY\\n\\nKolejny cichy haracz uderzy prosto w portfele milionów Polaków! ⛽🇵🇱\\n\\nBez zapowiedzi i bez debaty parlamentarnej rząd przeforsował korektę opłaty paliwowej. Od przyszłego miesiąca każda wizyta na stacji będzie zauważalnie droższa, a branża transportowa już liczy straty.\\n\\n(Szczegóły i tło w odpowiedzi 👇🧵)\\n\\n---ODPOWIEDŹ---\\n\\nNowe przepisy mają przynieść budżetowi ponad 4,2 miliarda złotych rocznie. Problem w tym, że wyższe koszty paliwa natychmiast przełożą się na ceny żywności i usług w sklepach.\\n\\nTo klasyczny mechanizm: politycy obiecują stabilizację, a dziury w finansach państwa łatają z pieniędzy kierowców. 📉⏳\\n\\nOdczujecie tę podwyżkę w codziennych wydatkach? 📊👇💬",
  "question": "Jak ta zmiana wpłynie bezpośrednio na Twój domowy budżet? 👇💬",
  "image_query": "gas station fuel price",
  "link": "https://example.com"
}}

Unikaj tematów z archiwum:
{json.dumps(previous_titles[:25], ensure_ascii=False)}

Dane wejściowe (wybierz z nich 14-15 najciekawszych, CAŁKOWICIE RÓŻNYCH tematów; pole "link" skopiuj dokładnie z wybranego artykułu):
{json.dumps(ai_input, ensure_ascii=False)}
"""


SAFETY = [
    types.SafetySetting(category=types.HarmCategory.HARM_CATEGORY_DANGEROUS_CONTENT, threshold=types.HarmBlockThreshold.BLOCK_NONE),
    types.SafetySetting(category=types.HarmCategory.HARM_CATEGORY_HARASSMENT, threshold=types.HarmBlockThreshold.BLOCK_NONE),
    types.SafetySetting(category=types.HarmCategory.HARM_CATEGORY_HATE_SPEECH, threshold=types.HarmBlockThreshold.BLOCK_NONE),
    types.SafetySetting(category=types.HarmCategory.HARM_CATEGORY_SEXUALLY_EXPLICIT, threshold=types.HarmBlockThreshold.BLOCK_NONE),
]


# ───────────────────────── GŁÓWNY PRZEPŁYW ─────────────────────────
def main():
    gemini_key = os.environ.get("GEMINI_API_KEY", "")
    if not gemini_key:
        sys.exit("Brak GEMINI_API_KEY")
    if not PEXELS_API_KEY:
        print("⚠ Brak PEXELS_API_KEY — pozycje będą bez zdjęć (strona pokaże kartę kategorii)")

    now_pl = datetime.now(pl_tz)
    session_name = "poranne" if now_pl.hour < 12 else "wieczorne"
    session_key = f"{now_pl.strftime('%Y-%m-%d')}_{session_name}"

    print("1. RSS")
    raw_articles = fetch_feeds()
    print(f"   razem {len(raw_articles)} surowych artykułów")
    if not raw_articles:
        sys.exit("Brak artykułów z RSS — nie nadpisuję plików")

    archive_data = {}
    if os.path.exists("archive.json"):
        try:
            with open("archive.json", encoding="utf-8") as f:
                archive_data = json.load(f)
        except Exception:
            archive_data = {}

    # Wszystko, co już publikowaliśmy (także wydanie poranne przy wieczornym), bez bieżącej sesji (nadpisywanej)
    known_links, previous_titles, known_events = set(), [], []
    for n, sk in enumerate(sorted(archive_data.keys(), reverse=True)):
        sc = archive_data.get(sk)
        if sk == session_key or not isinstance(sc, dict):
            continue
        for item in sc.get("items", []):
            if item.get("link"):
                known_links.add(norm_link(item["link"]))
            if n < 8:
                previous_titles += [t for t in (item.get("title"), item.get("source_title")) if t]
                known_events.append(f"{item.get('title', '')} — {str(item.get('summary', ''))[:160]}")

    print("2. Deduplikacja (archiwum + wewnątrz feedu)")
    clustered, seen = [], set()
    for art in raw_articles:
        k = norm_link(art["link"])
        if k in seen or k in known_links:
            continue
        if any(are_topics_duplicate(art["title"], prev, threshold=0.40) for prev in previous_titles):
            continue
        if any(are_topics_duplicate(art["title"], ex["title"], threshold=0.40) for ex in clustered):
            continue
        clustered.append(art)
        seen.add(k)
    print(f"   nowych, unikalnych tematów: {len(clustered)} (z {len(raw_articles)})")
    if not clustered:
        sys.exit("Brak nowych tematów — nie nadpisuję plików")

    candidates = interleave(clustered, MAX_PER_SOURCE, MAX_CANDIDATES)
    print(f"   kandydaci dla AI: {len(candidates)} z {len({c['source_name'] for c in candidates})} źródeł")

    print("3. Gemini")
    client = genai.Client(api_key=gemini_key)
    prompt = build_prompt(previous_titles, candidates)
    items = []
    for attempt in (1, 2):
        try:
            parsed = gen_json(client, prompt, 0.30, SAFETY)
            raw_items = parsed if isinstance(parsed, list) else parsed.get("items", [])
            got = resolve_sources(validate_items(raw_items), candidates)
            print(f"   próba {attempt}: {len(got)} poprawnych z {len(raw_items)}")
            if len(got) > len(items):
                items = got
            if len(items) >= MIN_ITEMS:
                break
        except Exception as e:
            print(f"   próba {attempt}: błąd AI: {e}")

    items = drop_repeated_events(client, items, known_events)

    # Awaryjnie: pozycje oparte wyłącznie na streszczeniu z RSS (bez dopisywania treści)
    if len(items) < MIN_ITEMS:
        existing = {i["link"] for i in items}
        titles = [i["title"] for i in items]
        for art in candidates:
            if len(items) >= MIN_ITEMS:
                break
            if art["link"] in existing or len(art["snippet"]) < 25 or art["lang"] != "pl":
                continue
            upper_t = format_uppercase_title(f"📰 {art['title'][:55]}")
            if any(are_topics_duplicate(upper_t, t, threshold=0.35) for t in titles + previous_titles):
                continue
            cat = normalize_category(art["feed_category"])
            items.append({"id": short_id(art["link"]), "category": cat, "title": upper_t, "hook": "", "summary": art["snippet"],
                          "comment": "", "threads_post": "", "question": "", "image_query": "news",
                          "link": art["link"], "source_name": art["source_name"], "source_title": art["title"],
                          "lang": art["lang"], "auto": True})
            existing.add(art["link"])
            titles.append(upper_t)
        print(f"   po uzupełnieniu awaryjnym: {len(items)}")

    if not items:
        sys.exit("AI nie zwróciło żadnych pozycji — nie nadpisuję istniejących plików")

    for cat, count in Counter(i["category"] for i in items).most_common():
        print(f"   {cat}: {count}")
    print("   źródła:", dict(Counter(i["source_name"] for i in items).most_common()))

    print("4. Zdjęcia: Pexels + źródła artykułów")
    used_imgs, source_ok = set(), 0
    for item in items:
        ph = fetch_pexels(item.get("image_query") or "business economy news", used_imgs)
        og = fetch_article_image(item["link"])
        item["source_image_url"] = og or ""
        if og:
            source_ok += 1
        if USE_SOURCE_IMAGES and og:
            item.update(image_url=og, image_portrait=og, image_credit="", image_credit_url="", image_illustrative=False, image_source="article")
        elif ph:
            item.update(image_url=ph["url"], image_portrait=ph["portrait"], image_credit=ph["credit"],
                        image_credit_url=ph["credit_url"], image_illustrative=True, image_source="pexels")
        else:
            item.update(image_url="", image_portrait="", image_credit="", image_credit_url="", image_illustrative=False, image_source="")
        item["image"] = item["image_url"]
    print(f"   og:image znaleziono: {source_ok}/{len(items)}; zdjęcia Pexels: {sum(i['image_source'] == 'pexels' for i in items)}")

    print("5. Zapis")
    date_pretty = f"{now_pl.day} {POLISH_MONTHS[now_pl.month]} {now_pl.year}"
    output_data = {"date": date_pretty, "time": now_pl.strftime("%H:%M"), "timestamp": now_pl.strftime("%Y-%m-%d_%H:%M"), "items": items}
    write_json("news.json", output_data)

    archive_data[session_key] = {**output_data, "items": [{k: v for k, v in i.items() if k not in ("threads_post", "question", "image_query")} for i in items]}
    for old in sorted(archive_data.keys())[:-ARCHIVE_MAX_SESSIONS]:
        del archive_data[old]
    write_json("archive.json", archive_data)

    chosen = {norm_link(i["link"]) for i in items}
    raw_out = [dict(a) for a in clustered[:80] if norm_link(a["link"]) not in chosen]
    to_tr = [a for a in raw_out if a["lang"] == "en"]
    for a, t in zip(to_tr, translate_titles(client, [a["title"] for a in to_tr])):
        a["title_pl"] = t
    for a in raw_out:
        a.setdefault("title_pl", a["title"])
        a.pop("feed_category", None)
    write_json("raw_feed.json", {"date": date_pretty, "time": output_data["time"], "timestamp": output_data["timestamp"],
                                 "count": len(raw_out), "items": raw_out})
    print(f"✓ Zapisano {len(items)} pozycji ({session_name}).")


if __name__ == "__main__":
    main()
