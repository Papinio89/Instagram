#!/usr/bin/env python3
"""Świat w Minutę — generator newsów (Gemini + Pexels).

Zapisuje: news.json, raw_feed.json, archive.json
Wymagane sekrety (zmienne środowiskowe): GEMINI_API_KEY, PEXELS_API_KEY
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
PEXELS_API_KEY = os.environ.get("PEXELS_API_KEY", "")  # BEZ wartości domyślnej!
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-3.6-flash")
# 0 = zdjęcia tylko z Pexels (bezpieczne licencyjnie); 1 = og:image z artykułów
USE_SOURCE_IMAGES = os.environ.get("USE_SOURCE_IMAGES", "0") == "1"

FALLBACK_IMG = "https://images.unsplash.com/photo-1451187580459-43490279c0fa?q=80&w=800&auto=format&fit=crop"
PL_TZ = ZoneInfo("Europe/Warsaw")
MAX_AGE_HOURS = 24
MIN_ITEMS = 10          # poniżej tego dobieramy uczciwe pozycje awaryjne
TARGET_ITEMS = 14
MAX_CANDIDATES = 35     # tyle artykułów trafia do AI
MAX_PER_SOURCE = 4      # limit z jednego źródła (żeby nie dominował Bankier)
ARCHIVE_MAX_SESSIONS = 60

# (url, język, domyślna kategoria, nazwa źródła)
FEEDS = [
    ("https://www.money.pl/rss/", "pl", "GOSPODARKA", "Money.pl"),
    ("https://businessinsider.com.pl/.rss", "pl", "BIZNES", "Business Insider Polska"),
    ("https://www.bankier.pl/rss/wiadomosci.xml", "pl", "GOSPODARKA", "Bankier.pl"),
    ("https://www.wnp.pl/rss/artykuly.xml", "pl", "GOSPODARKA", "WNP.pl"),
    ("https://archiwum.rp.pl/rss/ekonomia", "pl", "GOSPODARKA", "Rzeczpospolita"),
    ("https://news.google.com/rss?hl=pl&gl=PL&ceid=PL:pl", "pl", "POLSKA", "Google News"),
    ("https://feeds.bloomberg.com/markets/news.rss", "en", "GOSPODARKA", "Bloomberg"),
    ("https://search.cnbc.com/rs/search/view.html?partnerId=2000&keywords=markets&sort=date", "en", "GOSPODARKA", "CNBC"),
    ("https://feeds.bbci.co.uk/news/world/rss.xml", "en", "ŚWIAT", "BBC News"),
    ("https://news.google.com/rss/search?q=world+news+geopolitics&hl=en-US&gl=US&ceid=US:en", "en", "GEOPOLITYKA", "Google News"),
    ("https://defence24.pl/rss", "pl", "OBRONNOŚĆ", "Defence24"),
    ("https://feeds.bbci.co.uk/news/world/us_and_canada/rss.xml", "en", "ŚWIAT", "BBC News"),
]
# Usunięto: reutersagency.com/feed (feedy Reuters Agency nie działają od lat)

POLISH_MONTHS = {1: "stycznia", 2: "lutego", 3: "marca", 4: "kwietnia", 5: "maja", 6: "czerwca",
                 7: "lipca", 8: "sierpnia", 9: "września", 10: "października", 11: "listopada", 12: "grudnia"}
STOP_WORDS = {"polsce", "polski", "polaków", "nowy", "nowa", "nowe", "roku", "swiat", "przez", "tylko",
              "rzad", "rząd", "beda", "będą", "moze", "może", "oraz", "jest", "jego", "bardzo", "nawet",
              "teraz", "after", "with", "from", "that", "this", "more"}
CATEGORIES = ["POLSKA", "GOSPODARKA", "BIZNES", "GEOPOLITYKA", "OBRONNOŚĆ", "TECHNOLOGIE", "ŚWIAT"]
GENERIC_QUERY = {"POLSKA": "Poland city", "GOSPODARKA": "economy finance", "BIZNES": "business office",
                 "GEOPOLITYKA": "world map politics", "OBRONNOŚĆ": "military defense",
                 "TECHNOLOGIE": "technology", "ŚWIAT": "world news"}
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


def format_title(title: str) -> str:
    """Emoji na początku + reszta WIELKIMI LITERAMI. Naprawia 'ε ️' (spacja przed U+FE0F)."""
    s = re.sub(r"\s+\ufe0f", "\ufe0f", str(title or "").strip())
    s = re.sub(r"\s+", " ", s)
    if not s:
        return ""
    m = re.match(r"^([^\w]+)(.*)$", s)
    if m and m.group(2).strip():
        return f"{m.group(1).strip()} {m.group(2).strip().upper()}"
    return s.upper()


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


# ───────────────────────── POBIERANIE ─────────────────────────
def fetch_feeds() -> list:
    articles = []
    for url, lang, cat, default_name in FEEDS:
        try:
            feed = feedparser.parse(url)
            n = 0
            for e in feed.entries[:10]:
                if not is_recent(e):
                    continue
                title = getattr(e, "title", "").strip()
                link = clean_link(getattr(e, "link", "#"))
                if len(title) <= 15 or link == "#":
                    continue
                src = default_name
                try:  # Google News podaje prawdziwego wydawcę w <source>
                    src = (e.get("source", {}) or {}).get("title") or default_name
                except Exception:
                    pass
                if src and title.endswith(f" - {src}"):
                    title = title[: -len(src) - 3].strip()
                snippet = re.sub(r"<[^>]+>", "", getattr(e, "summary", "")).strip()
                snippet = html_lib.unescape(re.sub(r"\s+", " ", snippet))[:280]
                articles.append({"title": title, "snippet": snippet, "link": link,
                                 "source_name": src, "lang": lang, "feed_category": cat})
                n += 1
            print(f"  RSS {default_name:<24} {n:>2} art.  ({url[:50]})")
            if n == 0:
                print("    ⚠ pusty feed — sprawdź adres")
        except Exception as ex:
            print(f"  ✗ RSS {url}: {ex}")
    return articles


def fetch_article(url: str):
    """Zwraca (tekst artykułu do ~1800 znaków, og:image lub None)."""
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
            if not img.startswith("http"):
                img = None
            break
    paras = []
    for p in re.findall(r"<p[^>]*>(.*?)</p>", raw, re.S | re.I):
        t = html_lib.unescape(re.sub(r"<[^>]+>", " ", p))
        t = re.sub(r"\s+", " ", t).strip()
        if len(t) >= 60:
            paras.append(t)
    return " ".join(paras)[:1800], img


def build_candidates(clustered: list) -> list:
    by_src = defaultdict(list)
    for a in clustered:
        by_src[a["source_name"]].append(a)
    queues = [v[:MAX_PER_SOURCE] for v in by_src.values()]
    out = []
    while queues and len(out) < MAX_CANDIDATES:
        for q in queues:
            if q and len(out) < MAX_CANDIDATES:
                out.append(q.pop(0))
        queues = [q for q in queues if q]
    with ThreadPoolExecutor(max_workers=8) as ex:
        results = list(ex.map(lambda a: fetch_article(a["link"]), out))
    for a, (text, og) in zip(out, results):
        a["text"], a["og_image"] = text, og
    print(f"  pełny tekst pobrano dla {sum(1 for a in out if a['text'])}/{len(out)} artykułów")
    return out


def fetch_pexels(query: str, used: set):
    if not PEXELS_API_KEY:
        return None
    for attempt in range(3):
        try:
            url = f"https://api.pexels.com/v1/search?query={urllib.parse.quote(query)}&per_page=6&orientation=landscape"
            req = urllib.request.Request(url, headers={"Authorization": PEXELS_API_KEY,
                                                       "User-Agent": "SwiatWMinute-Bot/1.0"})
            with urllib.request.urlopen(req, timeout=8) as r:
                photos = json.loads(r.read().decode("utf-8")).get("photos", [])
            for p in photos:
                src = p.get("src", {})
                u = src.get("large") or src.get("medium")
                if u and u not in used:
                    used.add(u)
                    return {"url": u, "credit": p.get("photographer", ""), "credit_url": p.get("url", "")}
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
    text = (resp.text or "").strip()
    text = re.sub(r"^```(?:json)?|```$", "", text).strip()
    return json.loads(text)


PROMPT = """Jesteś redaktorem serwisu „Świat w Minutę” (Instagram/Threads). Piszesz zwięźle, dynamicznie i RZETELNIE.

ZASADY NADRZĘDNE (ważniejsze niż styl):
1. FAKTY WYŁĄCZNIE ZE ŹRÓDŁA. Używaj tylko informacji z pól "title" i "text" danego artykułu. NIE dodawaj liczb, dat, cytatów,
   nazwisk, przyczyn ani prognoz, których nie ma w danych. Gdy danych mało — napisz krócej, nie zgaduj.
2. Nagłówek musi zgadzać się z treścią źródła (zakaz przesady i clickbaitu niezgodnego z faktami).
3. Ton emocjonalny dopuszczalny, ale bez obelg, insynuacji i oskarżeń wobec osób, partii, narodów i grup.
   Nie przypisuj nikomu intencji ("kłamią", "okradają"). Komentarz ocenia skutki lub kontekst, nie wyśmiewa.
4. Poprawna, naturalna polszczyzna. Nie tłumacz słowo w słowo — sprawdź, czy tytuł ma sens.
5. Każda pozycja = INNY temat. Różnorodność kategorii i źródeł (max 3 pozycje z jednego źródła).
   Kategorię dobierz do treści: POLSKA, GOSPODARKA, BIZNES, GEOPOLITYKA, OBRONNOŚĆ (tylko wojsko/zbrojenia),
   TECHNOLOGIE, ŚWIAT (wypadki, katastrofy, wydarzenia ogólne). Nie wymuszaj proporcji.

Wybierz DOKŁADNIE 14 tematów z danych poniżej. Zwróć TABLICĘ JSON obiektów o polach:
- "id": liczba — id artykułu z danych wejściowych (kopiuj dokładnie)
- "category": jedno ze słów powyżej
- "title": emoji + NAGŁÓWEK DUŻYMI LITERAMI, do 60 znaków
- "hook": 1 zdanie zajawki
- "summary": 2 zdania, tylko fakty ze źródła
- "comment": DOKŁADNIE 1 zdanie (14-22 słów), krótsze niż summary, bez banałów i bez obelg
- "threads_post": dwa posty oddzielone linią ---ODPOWIEDŹ---
    Post 1 (320-380 znaków): NAGŁÓWEK Z EMOJI, linia z hookiem i flagami, 1-2 zdania sedna, na końcu: (Szczegóły i tło w odpowiedzi 👇🧵)
    Post 2 (380-450 znaków): kontekst ze źródła, 1 zdanie podsumowania, pytanie do dyskusji kończące się 👇💬
    Linie oddzielaj podwójnym znakiem nowej linii.
- "question": pytanie do odbiorców zakończone 👇💬
- "image_query": 2-5 angielskich słów do wyszukiwarki zdjęć stockowych (bez nazwisk osób)

Unikaj tematów z archiwum:
__PREV__

Dane wejściowe:
__CANDIDATES__
"""


def validate_items(raw_items: list, candidates: list) -> list:
    required = {"id", "category", "title", "hook", "summary", "comment", "threads_post", "question", "image_query"}
    valid, seen_titles, seen_ids = [], [], set()
    for it in raw_items:
        if not isinstance(it, dict) or not required.issubset(it.keys()):
            continue
        try:
            idx = int(it["id"])
            cand = candidates[idx]
        except Exception:
            continue
        if idx in seen_ids:
            continue
        title = format_title(it["title"])
        summary, comment = str(it["summary"]).strip(), str(it["comment"]).strip()
        post = str(it["threads_post"]).strip()
        if len(title) < 10 or len(summary) < 25 or len(comment) < 10 or len(post) < 400:
            continue
        if "---ODPOWIEDŹ---" not in post:
            continue
        if any(are_topics_duplicate(title, p, 0.35) for p in seen_titles):
            continue
        seen_ids.add(idx)
        seen_titles.append(title)
        valid.append({
            "id": short_id(cand["link"]),
            "category": normalize_category(it["category"]),
            "title": title,
            "hook": str(it["hook"]).strip(),
            "summary": summary,
            "comment": comment,
            "threads_post": post,
            "question": str(it["question"]).strip(),
            "image_query": str(it["image_query"]).strip() or "world news",
            "link": cand["link"],
            "source_name": cand["source_name"],
            "_og": cand.get("og_image"),
        })
    return valid


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
    day_key = now.strftime("%Y-%m-%d")
    session_key = f"{day_key}_{session}"

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

    prev_titles = []
    for sk in sorted(archive.keys(), reverse=True)[:8]:
        if session == "wieczorne" and sk == f"{day_key}_poranne":
            continue
        sc = archive.get(sk)
        if isinstance(sc, dict):
            prev_titles += [i.get("title", "") for i in sc.get("items", []) if i.get("title")]

    print("2. Deduplikacja")
    clustered, seen_links = [], set()
    for a in raw:
        if a["link"] in seen_links:
            continue
        if any(are_topics_duplicate(a["title"], p) for p in prev_titles):
            continue
        if any(are_topics_duplicate(a["title"], c["title"]) for c in clustered):
            continue
        clustered.append(a)
        seen_links.add(a["link"])
    if len(clustered) < TARGET_ITEMS:
        clustered = raw
    print(f"   unikalnych tematów: {len(clustered)}")

    print("3. Kandydaci + pełny tekst")
    candidates = build_candidates(clustered)
    ai_input = [{"id": i, "title": c["title"], "source": c["source_name"],
                 "text": (c.get("text") or c["snippet"])[:1500]} for i, c in enumerate(candidates)]

    print("4. Gemini")
    client = genai.Client(api_key=GEMINI_API_KEY)
    prompt = (PROMPT.replace("__PREV__", json.dumps(prev_titles[:25], ensure_ascii=False))
                    .replace("__CANDIDATES__", json.dumps(ai_input, ensure_ascii=False)))
    items = []
    for attempt in (1, 2):
        try:
            parsed = gen_json(client, prompt, 0.3)
            raw_items = parsed if isinstance(parsed, list) else parsed.get("items", [])
            got = validate_items(raw_items, candidates)
            print(f"   próba {attempt}: {len(got)} poprawnych z {len(raw_items)}")
            if len(got) > len(items):
                items = got
            if len(items) >= MIN_ITEMS:
                break
        except Exception as ex:
            print(f"   próba {attempt}: błąd AI: {ex}")

    # Awaryjnie: uczciwe pozycje z samego RSS (bez wymyślonej treści)
    if len(items) < MIN_ITEMS:
        used_links = {i["link"] for i in items}
        titles = [i["title"] for i in items]
        for c in candidates:
            if len(items) >= MIN_ITEMS:
                break
            if c["link"] in used_links or len(c["snippet"]) < 25 or c["lang"] != "pl":
                continue
            t = format_title("📰 " + c["title"][:60])
            if any(are_topics_duplicate(t, p, 0.35) for p in titles):
                continue
            items.append({"id": short_id(c["link"]), "category": normalize_category(c["feed_category"]),
                          "title": t, "hook": "", "summary": c["snippet"], "comment": "", "threads_post": "",
                          "question": "", "image_query": GENERIC_QUERY.get(c["feed_category"], "world news"),
                          "link": c["link"], "source_name": c["source_name"], "_og": c.get("og_image"),
                          "auto": True})
            used_links.add(c["link"])
            titles.append(t)
        print(f"   po uzupełnieniu awaryjnym: {len(items)}")

    if not items:
        sys.exit("AI nie zwróciło żadnych pozycji — nie nadpisuję istniejących plików")

    for cat, n in Counter(i["category"] for i in items).most_common():
        print(f"   {cat}: {n}")

    print("5. Zdjęcia (Pexels)")
    used_imgs = set()
    for it in items:
        ph = fetch_pexels(it["image_query"], used_imgs) or fetch_pexels(GENERIC_QUERY.get(it["category"], "news"), used_imgs)
        it["image_url"] = ph["url"] if ph else FALLBACK_IMG
        it["image_credit"] = ph["credit"] if ph else ""
        it["image_credit_url"] = ph["credit_url"] if ph else ""
        og = it.pop("_og", None)
        if USE_SOURCE_IMAGES and og:
            it["source_image_url"] = og
        else:
            it["source_image_url"] = it["image_url"]
        it["image"] = it["source_image_url"]

    print("6. Tłumaczenie nagłówków raw_feed")
    raw_out = [dict(a) for a in clustered[:80]]
    to_tr = [a for a in raw_out if a["lang"] == "en"]
    translated = translate_titles(client, [a["title"] for a in to_tr])
    for a, t in zip(to_tr, translated):
        a["title_pl"] = t
    for a in raw_out:
        a.setdefault("title_pl", a["title"])
        a.pop("feed_category", None)

    print("7. Zapis")
    out = {"date": f"{now.day} {POLISH_MONTHS[now.month]} {now.year}", "time": now.strftime("%H:%M"),
           "timestamp": now.strftime("%Y-%m-%d_%H:%M"), "items": items}
    write_json("news.json", out)
    archive[session_key] = out
    for old in sorted(archive.keys())[:-ARCHIVE_MAX_SESSIONS]:
        del archive[old]
    write_json("archive.json", archive)
    write_json("raw_feed.json", {"date": out["date"], "time": out["time"], "timestamp": out["timestamp"],
                                 "count": len(raw_out), "items": raw_out})
    print(f"✓ Zapisano {len(items)} pozycji ({session}).")


if __name__ == "__main__":
    main()
