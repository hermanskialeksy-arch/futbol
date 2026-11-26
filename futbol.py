#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FUTBOL ANALIZATOR – pomoc w analizie typów bukmacherskich (tylko biblioteka standardowa Pythona).

Źródła danych (wszystkie darmowe):
  * football-data.co.uk – historia 1. lig (wyniki, strzały, celne, rożne, faule, kartki) + kursy.
  * ESPN (publiczne API, bez klucza) – terminarz wszystkich lig i pucharów na kilka dni do przodu,
    wyniki i statystyki Ligi Mistrzów / Europy / Konferencji oraz kursy bukmacherskie.
  * API-Football (opcjonalnie, klucz w API_FOOTBALL_KEY) – kontuzje i braki kadrowe.
  * braki.json (opcjonalnie) – własne braki kadrowe wpisywane komendą `brak`.

Użycie:
  python futbol.py serve                   # pobierz dane, zbuduj raport i pokaż go w przeglądarce (telefon/Termux)
  python futbol.py serve --no-update       # j.w., ale bez pobierania danych (szybko)
  python futbol.py serve --share           # + adres dla osób w tej samej sieci Wi-Fi
  python futbol.py serve --tunnel          # + publiczny link (pkg install cloudflared)
  python futbol.py eksport                 # zapisz raport jako plik HTML i otwórz okno „Udostępnij”
  python futbol.py run --open              # pobierz + raport HTML (komputer)
  python futbol.py update | report         # tylko pobieranie / tylko raport
  python futbol.py backtest                # sprawdź historyczną skuteczność typów (zapisuje wynik)
  python futbol.py match Arsenal Chelsea   # analiza pary w konsoli
  python futbol.py brak dodaj Arsenal Saka atak     # ręczny brak kadrowy (atak/pomoc/obrona/bramkarz)
  python futbol.py brak lista | brak usun Arsenal [Saka]

UWAGA: model daje oszacowanie prawdopodobieństwa, nie pewność. Kursy zawierają marżę bukmachera,
a przewaga (edge) liczona z modelu bywa złudna. Graj odpowiedzialnie, tylko za środki, które możesz stracić.
"""
import argparse
import csv
import datetime as dt
import difflib
import glob
import html
import json
import math
import os
import re
import subprocess
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from collections import defaultdict

# --------------------------------------------------------------------------------------
# Konfiguracja
# --------------------------------------------------------------------------------------
HERE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(HERE, "dane")
REPORT_PATH = os.path.join(HERE, "raport.html")

# kod football-data: (nazwa ligi, kraj, identyfikator ESPN)
LEAGUES = {
    "E0": ("Premier League", "Anglia", "eng.1"),
    "SP1": ("La Liga", "Hiszpania", "esp.1"),
    "D1": ("Bundesliga", "Niemcy", "ger.1"),
    "I1": ("Serie A", "Włochy", "ita.1"),
    "F1": ("Ligue 1", "Francja", "fra.1"),
    "N1": ("Eredivisie", "Holandia", "ned.1"),
    "P1": ("Primeira Liga", "Portugalia", "por.1"),
    "B1": ("Jupiler Pro League", "Belgia", "bel.1"),
    "T1": ("Süper Lig", "Turcja", "tur.1"),
    "SC0": ("Scottish Premiership", "Szkocja", "sco.1"),
    "G1": ("Super League (Grecja)", "Grecja", "gre.1"),
}
EURO = {
    "uefa.champions": ("Liga Mistrzów", "Europa"),
    "uefa.europa": ("Liga Europy", "Europa"),
    "uefa.europa.conf": ("Liga Konferencji", "Europa"),
}
COMP_INFO = {v[0]: (v[1], v[2], "dom") for v in LEAGUES.values()}
COMP_INFO.update({v[0]: (v[1], k, "eu") for k, v in EURO.items()})
COMP_ORDER = ["Liga Mistrzów", "Liga Europy", "Liga Konferencji", "Premier League", "La Liga", "Bundesliga",
              "Serie A", "Ligue 1", "Eredivisie", "Primeira Liga", "Jupiler Pro League", "Süper Lig",
              "Scottish Premiership", "Super League (Grecja)"]

FD_STATS = {
    "goals": ("FTHG", "FTAG"), "shots": ("HS", "AS"), "sot": ("HST", "AST"),
    "corners": ("HC", "AC"), "fouls": ("HF", "AF"), "cards": ("HY", "AY"), "offsides": ("HO", "AO"),
}
NAMES = {"goals": "Gole", "shots": "Strzały", "sot": "Strzały celne", "corners": "Rożne",
         "fouls": "Faule", "cards": "Żółte kartki", "offsides": "Spalone"}
LINE_STEP = {"shots": 2.0, "fouls": 2.0, "sot": 1.0, "corners": 1.0, "cards": 1.0, "offsides": 1.0}
ESPN_STAT_KEYS = {"totalshots": "shots", "shots": "shots", "shotsontarget": "sot", "shotsongoal": "sot",
                  "woncorners": "corners", "cornerkicks": "corners", "corners": "corners",
                  "foulscommitted": "fouls", "fouls": "fouls", "yellowcards": "cards", "offsides": "offsides"}

HALF_LIFE_DAYS = 240   # po tylu dniach waga meczu spada o połowę
SHRINK_K = 5.0         # "wirtualne mecze" ściągające drużynę do średniej (lub priora)
VENUE_K = 6.0          # j.w. dla ocen osobno u siebie / na wyjeździe
PRIOR_STRENGTH = 0.5   # ile z siły drużyny w lidze krajowej przenosimy na puchary
MIN_MATCHES_LOW_CONF = 6
ESPN = "https://site.api.espn.com/apis/site/v2/sports/soccer"


def log(*a):
    print(*a, flush=True)


def num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def season_start_year(today=None):
    today = today or dt.date.today()
    return today.year if today.month >= 7 else today.year - 1


def season_code(y):
    return f"{y % 100:02d}{(y + 1) % 100:02d}"


def pdate(s):
    s = (s or "").strip()
    for f in ("%d/%m/%Y", "%d/%m/%y", "%Y-%m-%d"):
        try:
            return dt.datetime.strptime(s, f).date()
        except ValueError:
            pass
    return None


def last_sunday(y, m):
    d = dt.date(y, m, 31)
    while d.weekday() != 6:
        d -= dt.timedelta(days=1)
    return d


def utc_to_pl(utc):
    """UTC -> czas polski (CET/CEST wg reguł UE), bez zależności od zoneinfo."""
    y = utc.year
    s = dt.datetime.combine(last_sunday(y, 3), dt.time(1))
    e = dt.datetime.combine(last_sunday(y, 10), dt.time(1))
    return utc + dt.timedelta(hours=2 if s <= utc < e else 1)


def jload(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def jsave(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False)
    os.replace(tmp, path)


def P(name):
    return os.path.join(DATA_DIR, name)


# --------------------------------------------------------------------------------------
# Nazwy drużyn (różne źródła nazywają kluby inaczej)
# --------------------------------------------------------------------------------------
ALIASES = {
    "man city": "manchester city", "man united": "manchester united", "man utd": "manchester united",
    "spurs": "tottenham hotspur", "tottenham": "tottenham hotspur", "wolves": "wolverhampton wanderers",
    "newcastle": "newcastle united", "nott m forest": "nottingham forest", "nottm forest": "nottingham forest",
    "west ham": "west ham united", "brighton": "brighton and hove albion", "leeds": "leeds united",
    "leicester": "leicester city", "ipswich": "ipswich town", "norwich": "norwich city",
    "ath madrid": "atletico madrid", "atl madrid": "atletico madrid", "ath bilbao": "athletic club",
    "athletic bilbao": "athletic club", "sociedad": "real sociedad", "betis": "real betis",
    "vallecano": "rayo vallecano", "celta": "celta vigo", "espanol": "espanyol", "alaves": "deportivo alaves",
    "dortmund": "borussia dortmund", "m gladbach": "borussia monchengladbach", "mgladbach": "borussia monchengladbach",
    "monchengladbach": "borussia monchengladbach", "leverkusen": "bayer leverkusen", "bayern munich": "bayern munchen",
    "bayern": "bayern munchen", "ein frankfurt": "eintracht frankfurt", "frankfurt": "eintracht frankfurt",
    "leipzig": "rb leipzig", "fc koln": "koln", "cologne": "koln", "hoffenheim": "tsg hoffenheim",
    "mainz": "mainz 05", "stuttgart": "vfb stuttgart", "wolfsburg": "vfl wolfsburg", "freiburg": "sc freiburg",
    "bochum": "vfl bochum", "st pauli": "fc st pauli", "heidenheim": "fc heidenheim",
    "inter": "internazionale", "inter milan": "internazionale", "milan": "ac milan", "roma": "as roma",
    "verona": "hellas verona", "napoli": "napoli", "paris sg": "paris saint germain", "psg": "paris saint germain",
    "marseille": "olympique marseille", "lyon": "olympique lyonnais", "st etienne": "saint etienne",
    "sp lisbon": "sporting cp", "sporting": "sporting cp", "sporting lisbon": "sporting cp", "porto": "porto",
    "sp braga": "braga", "psv": "psv eindhoven", "ajax": "ajax", "feyenoord": "feyenoord", "az": "az alkmaar",
    "club brugge": "club brugge", "st gilloise": "union saint gilloise", "royale union sg": "union saint gilloise",
    "galatasaray": "galatasaray", "fenerbahce": "fenerbahce", "besiktas": "besiktas", "buyuksehyr": "basaksehir",
    "buyuksehir": "basaksehir", "istanbul basaksehir": "basaksehir", "celtic": "celtic", "rangers": "rangers",
    "olympiacos": "olympiakos", "olympiacos piraeus": "olympiakos", "aek athens": "aek athens",
    "paok": "paok", "panathinaikos": "panathinaikos", "bodo glimt": "bodo glimt", "slavia prague": "slavia praha",
    "sparta prague": "sparta praha", "red star belgrade": "crvena zvezda", "dinamo zagreb": "gnk dinamo zagreb",
    "young boys": "bsc young boys", "shakhtar donetsk": "shakhtar", "salzburg": "rb salzburg",
}
NOISE = {"fc", "cf", "afc", "sc", "fk", "sk", "if", "bk", "ssc", "us", "ud", "cd", "rc", "ac", "as", "ca", "de",
         "the", "club", "calcio", "1", "04", "1899", "1909", "1913"}


def norm_name(s):
    s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode().lower()
    s = s.replace("&", " and ").replace("'", " ").replace("-", " ").replace("/", " ")
    s = re.sub(r"[^a-z0-9 ]", " ", s)
    s = " ".join(s.split())
    return ALIASES.get(s, s)


def _tokens(n):
    return [t for t in n.split() if t not in NOISE]


def same_team(a, b):
    na, nb = norm_name(a), norm_name(b)
    if na == nb:
        return True
    ta, tb = set(_tokens(na)), set(_tokens(nb))
    if ta and tb and (ta <= tb or tb <= ta) and min(len(" ".join(ta)), len(" ".join(tb))) >= 5:
        return True
    return difflib.SequenceMatcher(None, na, nb).ratio() >= 0.86


class Canon:
    """Dopasowuje nazwę z innego źródła do listy znanych nazw drużyn."""

    def __init__(self, names):
        self.names = sorted(set(names))
        self.cache = {}
        self.by_norm = {norm_name(n): n for n in self.names}

    def resolve(self, name):
        if name in self.cache:
            return self.cache[name]
        res = None
        if name in self.names:
            res = name
        else:
            n = norm_name(name)
            res = self.by_norm.get(n)
            if res is None:
                best, br = None, 0.0
                for cand in self.names:
                    if same_team(name, cand):
                        r = difflib.SequenceMatcher(None, n, norm_name(cand)).ratio()
                        if r > br:
                            best, br = cand, r
                res = best
        self.cache[name] = res
        return res


# --------------------------------------------------------------------------------------
# Pobieranie danych
# --------------------------------------------------------------------------------------
def http_get(url, headers=None, timeout=40):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 futbol-analizator", **(headers or {})})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def http_json(url, headers=None, timeout=40, tries=2):
    last = None
    for _ in range(tries):
        try:
            return json.loads(http_get(url, headers, timeout))
        except urllib.error.HTTPError as e:
            if 400 <= e.code < 500:
                raise
            last = e
            time.sleep(0.6)
        except Exception as e:  # noqa
            last = e
            time.sleep(0.6)
    raise last


def load_config():
    cfg = jload(os.path.join(HERE, "config.json"), {})
    cfg["api_football_key"] = os.environ.get("API_FOOTBALL_KEY") or cfg.get("api_football_key")
    return cfg


def update_football_data(n_seasons):
    os.makedirs(DATA_DIR, exist_ok=True)
    y0 = season_start_year()
    ok = fail = 0
    for i in range(n_seasons):
        sc = season_code(y0 - i)
        for code in LEAGUES:
            url = f"https://www.football-data.co.uk/mmz4281/{sc}/{code}.csv"
            path = P(f"fd_{sc}_{code}.csv")
            if i > 0 and os.path.exists(path) and os.path.getsize(path) > 1000:
                continue
            try:
                data = http_get(url)
                if len(data) < 200:
                    raise ValueError("pusty plik")
                open(path, "wb").write(data)
                ok += 1
            except Exception as e:  # noqa
                fail += 1
                log(f"  ! {code} {sc}: {e}")
    try:
        open(P("fd_fixtures.csv"), "wb").write(http_get("https://www.football-data.co.uk/fixtures.csv"))
    except Exception as e:  # noqa
        log("  ! fixtures.csv:", e)
    log(f"football-data.co.uk: pobrano {ok} plików, błędów {fail}")


# ---- ESPN ----
def parse_scoreboard(js, comp, slug):
    out = []
    for ev in js.get("events", []) or []:
        try:
            c0 = ev["competitions"][0]
            teams = {c["homeAway"]: c for c in c0["competitors"]}
            h, a = teams["home"]["team"]["displayName"], teams["away"]["team"]["displayName"]
            loc = utc_to_pl(dt.datetime.strptime(ev["date"][:16], "%Y-%m-%dT%H:%M"))
            st = (ev.get("status") or {}).get("type") or {}
            rec = dict(id=str(ev["id"]), comp=comp, slug=slug, date=loc.date().isoformat(),
                       time=loc.strftime("%H:%M"), home=h, away=a, done=bool(st.get("completed")),
                       state=st.get("state"))
            if rec["done"]:
                rec["gh"] = int(float(teams["home"]["score"]))
                rec["ga"] = int(float(teams["away"]["score"]))
            out.append(rec)
        except (KeyError, ValueError, TypeError, IndexError):
            continue
    return out


def parse_summary_stats(js):
    """Statystyki meczu (po rozegraniu) z boxscore ESPN -> {stat: [gospodarze, goście]} lub {}."""
    st = {}
    for t in (js.get("boxscore") or {}).get("teams", []) or []:
        side = 0 if t.get("homeAway") == "home" else 1
        for s in t.get("statistics", []) or []:
            key = ESPN_STAT_KEYS.get(re.sub(r"[^a-z]", "", str(s.get("name", "")).lower()))
            if not key:
                continue
            v = num(s.get("value"))
            if v is None:
                v = num(str(s.get("displayValue", "")).replace("%", ""))
            if v is not None:
                st.setdefault(key, [None, None])[side] = v
    return {k: v for k, v in st.items() if v[0] is not None and v[1] is not None}


def to_dec(x):
    """Amerykańskie / ułamkowe / dziesiętne -> kurs dziesiętny."""
    if x is None or isinstance(x, bool):
        return None
    v = None
    if isinstance(x, (int, float)):
        v = float(x)
    else:
        s = str(x).strip().upper().replace(",", ".")
        if s in ("EVEN", "EV"):
            return 2.0
        if "/" in s:
            a, _, b = s.partition("/")
            fa, fb = num(a), num(b)
            return 1 + fa / fb if fa is not None and fb else None
        v = num(s.replace("+", ""))
    if v is None:
        return None
    if abs(v) >= 100:
        return 1 + v / 100 if v > 0 else 1 + 100 / abs(v)
    return v if v > 1.0 else None


def _find_ml(d, depth=0):
    if not isinstance(d, dict) or depth > 3:
        return None
    for k in ("moneyLine", "moneyline"):
        if k in d:
            v = d[k]
            if isinstance(v, dict):
                v = _find_ml(v, depth + 1) or v.get("odds") or v.get("value")
            return v
    for v in d.values():
        if isinstance(v, dict):
            r = _find_ml(v, depth + 1)
            if r is not None:
                return r
    return None


def parse_summary_odds(js):
    """Kursy 1X2 (i O/U 2.5 jeśli są) z `odds`/`pickcenter` ESPN. Ostrożnie: struktura bywa różna."""
    cands = []
    for key in ("odds", "pickcenter"):
        for o in js.get(key) or []:
            if not isinstance(o, dict):
                continue
            name = str((o.get("provider") or {}).get("name", "")).lower()
            h = to_dec(_find_ml(o.get("homeTeamOdds")))
            d = to_dec(_find_ml(o.get("drawOdds")))
            a = to_dec(_find_ml(o.get("awayTeamOdds")))
            ou = {}
            if num(o.get("overUnder")) == 2.5:
                ov, un = to_dec(o.get("overOdds")), to_dec(o.get("underOdds"))
                if ov and un:
                    ou = {"goals:total:over:2.5": ov, "goals:total:under:2.5": un}
            if h and d and a and 1.0 < 1 / h + 1 / d + 1 / a < 1.3:
                pri = 0 if "365" in name else 1 if "draftkings" in name else 2
                cands.append((pri, {"1x2:1": h, "1x2:X": d, "1x2:2": a, **ou}))
    cands.sort(key=lambda c: c[0])
    return cands[0][1] if cands else {}


def parse_summary_form(js, home, away):
    """Forma: ostatnie 5 meczów każdej drużyny z `lastFiveGames` (ESPN).
    Wpis: [wynik W/D/L, gospodarz, gość, gole gosp., gole gości, data, rozgrywki, czy_nasza_drużyna_gospodarzem]."""
    out = {"h": [], "a": []}
    blocks = [b for b in (js.get("lastFiveGames") or []) if isinstance(b, dict)]
    for i, b in enumerate(blocks[:2]):
        me = str((b.get("team") or {}).get("displayName", ""))
        side = "h" if me == home else "a" if me == away else ("h" if i == 0 else "a")
        evs = []
        for e in (b.get("events") or [])[:5]:
            if not isinstance(e, dict):
                continue
            opp = str((e.get("opponent") or {}).get("displayName", ""))
            is_home = str(e.get("atVs", "")).lower() != "@"
            hs, as_ = e.get("homeTeamScore"), e.get("awayTeamScore")
            if hs is None or as_ is None:
                m = re.match(r"\s*(\d+)\s*[-–:]\s*(\d+)", str(e.get("score", "")))
                hs, as_ = (m.group(1), m.group(2)) if m else ("", "")
            evs.append([str(e.get("gameResult", ""))[:1].upper(), me if is_home else opp, opp if is_home else me,
                        str(hs), str(as_), str(e.get("gameDate", ""))[:10],
                        str(e.get("leagueName") or e.get("leagueAbbreviation") or ""), is_home])
        out[side] = evs
    return out if (out["h"] or out["a"]) else {}


def espn_get(path, **params):
    time.sleep(0.12)
    url = f"{ESPN}/{path}" + ("?" + urllib.parse.urlencode(params) if params else "")
    return http_json(url)


def update_espn(days, budget):
    cache = jload(P("espn_cache.json"), {"events": {}, "fixtures": {}, "meta": {}})
    today = dt.date.today()
    calls = 0
    comps = [(slug, v[0]) for slug, v in EURO.items()] + [(v[2], v[0]) for v in LEAGUES.values()]
    from concurrent.futures import ThreadPoolExecutor

    def fetch_days(slug, days_list):
        def one(d):
            try:
                return d, espn_get(f"{slug}/scoreboard", dates=f"{d:%Y%m%d}"), None
            except Exception as e:  # noqa
                return d, None, e
        with ThreadPoolExecutor(max_workers=6) as ex:
            return list(ex.map(one, days_list))

    # 1) terminarz na najbliższe dni (wszystkie rozgrywki), zapytania dzień po dniu
    got, errs, first_err = 0, 0, None
    fx = {}
    day_list = [today + dt.timedelta(days=i) for i in range(days + 1)]
    for slug, comp in comps:
        for d, js, err in fetch_days(slug, day_list):
            if err:
                errs += 1
                first_err = first_err or f"{comp} {d}: {err}"
                continue
            for rec in parse_scoreboard(js, comp, slug):
                if rec["done"]:
                    continue
                old = cache["fixtures"].get(rec["id"], {})
                rec["odds"], rec["odds_ts"] = old.get("odds", {}), old.get("odds_ts", 0)
                fx[rec["id"]] = rec
                got += 1
    if got:
        cache["fixtures"] = fx
    log(f"ESPN: terminarz na {days} dni: {got} meczów" + (f" (błędy zapytań: {errs}, np. {first_err})" if errs else ""))
    # 2) historia pucharów europejskich (wyniki + statystyki) od początku sezonu
    start = dt.date(season_start_year(), 9, 1)
    for slug, (comp, _) in EURO.items():
        pending = []
        d = start
        while d <= today:
            if not cache["meta"].get(f"{slug}:{d:%Y%m%d}"):
                pending.append(d)
            d += dt.timedelta(days=1)
        for d, js, err in fetch_days(slug, pending):
            if err:
                continue
            for rec in parse_scoreboard(js, comp, slug):
                if rec["done"]:
                    old = cache["events"].get(rec["id"], {})
                    rec["stats"], rec["tries"] = old.get("stats"), old.get("tries", 0)
                    cache["events"][rec["id"]] = rec
            if d <= today - dt.timedelta(days=2):
                cache["meta"][f"{slug}:{d:%Y%m%d}"] = 1
    todo = [r for r in cache["events"].values() if r.get("stats") is None and r.get("tries", 0) < 2]
    todo.sort(key=lambda r: r["date"], reverse=True)
    got_st = 0
    for rec in todo:
        if calls >= budget:
            break
        calls += 1
        try:
            st = parse_summary_stats(espn_get(f"{rec['slug']}/summary", event=rec["id"]))
        except Exception as e:  # noqa
            log(f"  ! ESPN statystyki {rec['id']}: {e}")
            rec["tries"] = rec.get("tries", 0) + 1
            continue
        if st:
            rec["stats"] = st
            got_st += 1
        else:
            rec["stats"] = {}
            rec["tries"] = rec.get("tries", 0) + 1
    log(f"ESPN: mecze pucharowe w pamięci: {len(cache['events'])}, nowe statystyki: {got_st}, "
        f"do pobrania później: {max(len([r for r in todo if r.get('stats') is None]), 0)}")
    # 3) kursy do nadchodzących meczów
    now = time.time()
    got_odds = 0
    for rec in sorted(cache["fixtures"].values(), key=lambda r: (r["date"], r["time"])):
        if calls >= budget + 80:
            break
        if rec.get("odds") and rec.get("form_v") == 2 and now - rec.get("odds_ts", 0) < 6 * 3600:
            continue
        calls += 1
        try:
            sj = espn_get(f"{rec['slug']}/summary", event=rec["id"])
            odds = parse_summary_odds(sj)
            form = parse_summary_form(sj, rec["home"], rec["away"])
        except Exception:  # noqa
            continue
        if form:
            rec["form"], rec["form_v"] = form, 2
        rec["odds_ts"] = now
        if odds:
            rec["odds"] = odds
            got_odds += 1
    log(f"ESPN: kursy dla {got_odds} nadchodzących meczów")
    jsave(P("espn_cache.json"), cache)


# ---- API-Football (kontuzje) ----
class ApiFootball:
    base = "https://v3.football.api-sports.io"

    def __init__(self, key):
        self.key = key
        self.cache = jload(P("api_cache.json"), {})
        self.today = dt.datetime.utcnow().strftime("%Y-%m-%d")
        used = self.cache.get("used") or {}
        self.cache["used"] = {self.today: used.get(self.today, 0)}

    def save(self):
        jsave(P("api_cache.json"), self.cache)

    def left(self, budget):
        return max(0, min(budget, 97 - self.cache["used"][self.today]))

    def get(self, endpoint, **params):
        self.cache["used"][self.today] += 1
        url = f"{self.base}{endpoint}?{urllib.parse.urlencode(params)}"
        data = json.loads(http_get(url, headers={"x-apisports-key": self.key}))
        if data.get("errors"):
            raise RuntimeError(str(data["errors"]))
        return data.get("response", [])


ROLE_MAP = {"Goalkeeper": "bramkarz", "Defender": "obrona", "Midfielder": "pomoc", "Attacker": "atak"}
# wpływ jednego pewnego braku: (zmiana siły ataku własnej drużyny, zmiana siły ataku rywala)
ROLE_EFFECT = {"atak": (-0.045, 0.0), "pomoc": (-0.025, 0.010), "obrona": (0.0, 0.035),
               "bramkarz": (0.0, 0.060), "?": (-0.015, 0.012)}
KEY_MULT = 2.0   # wpis z "klucz": true (gwiazda / pewniak w składzie) liczy się podwójnie


def update_injuries(days, budget):
    key = load_config().get("api_football_key")
    if not key:
        log("Kontuzje: brak klucza API-Football – używam tylko własnych braków (komenda `brak`).")
        return
    api = ApiFootball(key)
    inj = api.cache.setdefault("injuries", {})
    pos = api.cache.setdefault("pos", {})
    squads = api.cache.setdefault("squads", {})
    now = time.time()
    left = api.left(budget)
    today = dt.date.today()
    n_new = 0
    for i in range(days + 1):
        if left <= 0:
            break
        k = (today + dt.timedelta(days=i)).isoformat()
        if inj.get(k) and now - inj[k]["ts"] < 12 * 3600:
            continue
        try:
            resp = api.get("/injuries", date=k)
            left -= 1
        except Exception as e:  # noqa
            log(f"  ! kontuzje {k}: {e}")
            break
        inj[k] = {"ts": now, "items": [
            {"team": r["team"]["name"], "tid": r["team"]["id"], "pid": r["player"]["id"],
             "name": r["player"]["name"], "type": r["player"].get("type"), "reason": r["player"].get("reason")}
            for r in resp if r.get("team") and r.get("player")]}
        n_new += len(inj[k]["items"])
    tids = {it["tid"] for v in inj.values() for it in v["items"] if str(it["pid"]) not in pos}
    for tid in sorted(tids):
        if left <= 0 or str(tid) in squads:
            continue
        try:
            resp = api.get("/players/squads", team=tid)
            left -= 1
        except Exception as e:  # noqa
            log(f"  ! skład {tid}: {e}")
            break
        squads[str(tid)] = now
        for team in resp:
            for p in team.get("players", []):
                pos[str(p["id"])] = p.get("position")
    api.save()
    log(f"API-Football: pobrano {n_new} wpisów o brakach; pozostały limit sesji: {left}")


def manual_absences():
    """Wpisy ręczne: braki.json w katalogu programu (wersjonowany w repozytorium) + dane/braki.json (komenda `brak`)."""
    out = {}
    for path in (os.path.join(HERE, "braki.json"), P("braki.json")):
        for k, lst in jload(path, {}).items():
            out.setdefault(k, []).extend(lst)
    return out


def absences_for(team, date_iso, api_cache, manual):
    out = []
    pos = api_cache.get("pos", {})
    for it in (api_cache.get("injuries", {}).get(date_iso) or {}).get("items", []):
        if same_team(it["team"], team):
            q = "question" in str(it.get("type", "")).lower()
            out.append(dict(n=it["name"], role=ROLE_MAP.get(pos.get(str(it["pid"])), "?"),
                            st="wątpliwy" if q else "nie zagra", reason=it.get("reason") or "", w=0.5 if q else 1.0, k=1.0))
    for k, lst in manual.items():
        if same_team(k, team):
            for e in lst:
                if e.get("do") and date_iso > e["do"]:
                    continue
                w = float(e.get("waga", 1.0))
                out.append(dict(n=e.get("gracz", "?"), role=e.get("rola", "?"),
                                st="nie zagra" if w >= 0.9 else "wątpliwy", reason=e.get("powod", ""), w=w,
                                k=KEY_MULT if e.get("klucz") else 1.0))
    return out


def absence_mult(lst):
    a = d = 0.0
    for e in lst:
        ea, ed = ROLE_EFFECT.get(e["role"], ROLE_EFFECT["?"])
        f = e["w"] * e.get("k", 1.0)
        a += ea * f
        d += ed * f
    return max(0.80, 1 + a), min(1.20, 1 + d)


def cmd_brak(args):
    data = manual_absences()
    act = args.akcja
    if act == "lista":
        if not data:
            log("Brak własnych wpisów.")
        for t, lst in data.items():
            for e in lst:
                log(f"{t}: {e.get('gracz')} ({e.get('rola')}, waga {e.get('waga', 1.0)})")
    elif act == "dodaj":
        if not (args.druzyna and args.gracz):
            log('Użycie: brak dodaj "Arsenal" "Saka" atak')
            return
        rola = (args.rola or "?").lower()
        if rola not in ("atak", "pomoc", "obrona", "bramkarz"):
            log("Rola musi być: atak, pomoc, obrona albo bramkarz")
            return
        data.setdefault(args.druzyna, []).append({"gracz": args.gracz, "rola": rola, "waga": args.waga})
        jsave(P("braki.json"), data)
        log(f"Dodano: {args.druzyna} – {args.gracz} ({rola}).")
    elif act == "usun":
        keys = [k for k in data if same_team(k, args.druzyna or "")]
        for k in keys:
            if args.gracz:
                data[k] = [e for e in data[k] if e.get("gracz", "").lower() != args.gracz.lower()]
                if not data[k]:
                    del data[k]
            else:
                del data[k]
        jsave(P("braki.json"), data)
        log("Usunięto.")


def update_all(n_seasons, days, espn_budget, inj_budget):
    log("== Aktualizacja danych ==")
    os.makedirs(DATA_DIR, exist_ok=True)
    update_football_data(n_seasons)
    try:
        update_espn(days, espn_budget)
    except Exception as e:  # noqa
        log("  ! ESPN:", e)
    try:
        update_injuries(days, inj_budget)
    except Exception as e:  # noqa
        log("  ! kontuzje:", e)


# --------------------------------------------------------------------------------------
# Wczytywanie danych
# --------------------------------------------------------------------------------------
def _first(row, names):
    for n in names:
        v = num(row.get(n))
        if v and v > 1:
            return v
    return None


def extract_odds(r):
    spec = {
        "1x2:1": ["AvgH", "B365H", "PSH", "MaxH"], "1x2:X": ["AvgD", "B365D", "PSD", "MaxD"],
        "1x2:2": ["AvgA", "B365A", "PSA", "MaxA"],
        "goals:total:over:2.5": ["Avg>2.5", "B365>2.5", "P>2.5", "Max>2.5"],
        "goals:total:under:2.5": ["Avg<2.5", "B365<2.5", "P<2.5", "Max<2.5"],
    }
    out = {}
    for k, names in spec.items():
        v = _first(r, names)
        if v:
            out[k] = v
    return out


def parse_fd(path, comp):
    out = []
    with open(path, newline="", encoding="utf-8-sig", errors="replace") as f:
        for r in csv.DictReader(f):
            d = pdate(r.get("Date"))
            if not d or not r.get("HomeTeam"):
                continue
            st = {}
            for k, (h, a) in FD_STATS.items():
                hv, av = num(r.get(h)), num(r.get(a))
                if hv is not None and av is not None:
                    st[k] = (hv, av)
            out.append(dict(comp=comp, date=d, home=r["HomeTeam"].strip(), away=r["AwayTeam"].strip(),
                            stats=st, odds=extract_odds(r), div=r.get("Div"), time=(r.get("Time") or "").strip()))
    return out


def load_domestic():
    played = defaultdict(list)
    for path in sorted(glob.glob(P("fd_*_*.csv"))):
        base = os.path.basename(path)[3:-4]
        if base == "fixtures":
            continue
        code = base.split("_", 1)[1]
        if code not in LEAGUES:
            continue
        for m in parse_fd(path, LEAGUES[code][0]):
            if "goals" in m["stats"]:
                played[m["comp"]].append(m)
    fix = []
    fp = P("fd_fixtures.csv")
    if os.path.exists(fp):
        for m in parse_fd(fp, ""):
            lg = LEAGUES.get(m.get("div"))
            if lg and "goals" not in m["stats"]:
                m["comp"] = lg[0]
                fix.append(m)
    return played, fix


def load_euro():
    cache = jload(P("espn_cache.json"), {"events": {}, "fixtures": {}})
    played = []
    for r in cache["events"].values():
        st = {"goals": (float(r["gh"]), float(r["ga"]))}
        for k, v in (r.get("stats") or {}).items():
            st[k] = (float(v[0]), float(v[1]))
        played.append(dict(comp=r["comp"], date=pdate(r["date"]), home=r["home"], away=r["away"], stats=st, odds={}))
    return played, list(cache["fixtures"].values())


# --------------------------------------------------------------------------------------
# Model
# --------------------------------------------------------------------------------------
def pmf(mu, alpha, n):
    """Rozkład Poissona (alpha~0) lub ujemny dwumianowy (wariancja = mu + alpha*mu^2)."""
    if mu <= 1e-9:
        return [1.0] + [0.0] * n
    out = []
    if alpha < 1e-4:
        for k in range(n + 1):
            out.append(math.exp(k * math.log(mu) - mu - math.lgamma(k + 1)))
    else:
        r = 1.0 / alpha
        p = r / (r + mu)
        for k in range(n + 1):
            out.append(math.exp(math.lgamma(k + r) - math.lgamma(r) - math.lgamma(k + 1)
                                + r * math.log(p) + k * math.log(1 - p)))
    s = sum(out)
    return [x / s for x in out]


def conv(a, b):
    out = [0.0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x < 1e-12:
            continue
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def over_prob(dist, line):
    return sum(dist[int(line) + 1:])


class StatModel:
    """Oceny siły ataku/obrony: ogólne oraz osobno u siebie i na wyjeździe (z ściąganiem do ocen ogólnych)."""

    def __init__(self, rows, ref, stat, prior=None):
        self.stat = stat
        self.prior = prior or {}
        wh = wa = sh = sa = 0.0
        ws = []
        for m in rows:
            w = 0.5 ** (max((ref - m["date"]).days, 0) / HALF_LIFE_DAYS)
            ws.append(w)
            x, y = m["stats"][stat]
            wh += w; sh += w * x; sa += w * y
        self.Lh, self.La = sh / wh, sa / wh
        self.L = L = (self.Lh + self.La) / 2
        prod, conc, wt = defaultdict(float), defaultdict(float), defaultdict(float)
        hp, hc, hw = defaultdict(float), defaultdict(float), defaultdict(float)
        ap, ac, aw = defaultdict(float), defaultdict(float), defaultdict(float)
        self.n = defaultdict(int)
        for m, w in zip(rows, ws):
            x, y = m["stats"][stat]
            h, a = m["home"], m["away"]
            for t, p, c in ((h, x, y), (a, y, x)):
                prod[t] += w * p; conc[t] += w * c; wt[t] += w; self.n[t] += 1
            hp[h] += w * x; hc[h] += w * y; hw[h] += w
            ap[a] += w * y; ac[a] += w * x; aw[a] += w
        self.att = {t: ((prod[t] + SHRINK_K * L * self.p_att(t)) / (wt[t] + SHRINK_K)) / L for t in wt}
        self.dfn = {t: ((conc[t] + SHRINK_K * L * self.p_dfn(t)) / (wt[t] + SHRINK_K)) / L for t in wt}
        K, Lh, La = VENUE_K, self.Lh, self.La
        self.att_h = {t: ((hp[t] + K * Lh * self.att[t]) / (hw[t] + K)) / Lh for t in hw}
        self.def_h = {t: ((hc[t] + K * La * self.dfn[t]) / (hw[t] + K)) / La for t in hw}
        self.att_a = {t: ((ap[t] + K * La * self.att[t]) / (aw[t] + K)) / La for t in aw}
        self.def_a = {t: ((ac[t] + K * Lh * self.dfn[t]) / (aw[t] + K)) / Lh for t in aw}
        num_, den = 0.0, 0.0
        for m in rows:
            lh, la = self.lam(m["home"], m["away"])
            x, y = m["stats"][stat]
            num_ += (x - lh) ** 2 - lh + (y - la) ** 2 - la
            den += lh * lh + la * la
        self.alpha = 0.0 if stat == "goals" else max(0.0, min(num_ / den if den else 0.0, 1.0))

    def p_att(self, t):
        pr = self.prior.get(t)
        return 1 + PRIOR_STRENGTH * (pr[0] - 1) if pr else 1.0

    def p_dfn(self, t):
        pr = self.prior.get(t)
        return 1 + PRIOR_STRENGTH * (pr[1] - 1) if pr else 1.0

    def r_att(self, t):
        return self.att.get(t, self.p_att(t))

    def r_dfn(self, t):
        return self.dfn.get(t, self.p_dfn(t))

    def lam(self, h, a):
        ah, da = self.att_h.get(h, self.r_att(h)), self.def_a.get(a, self.r_dfn(a))
        aa, dh = self.att_a.get(a, self.r_att(a)), self.def_h.get(h, self.r_dfn(h))
        return self.Lh * ah * da, self.La * aa * dh

    def count(self, t):
        return self.n.get(t, 0)


class Translated:
    """Opakowanie: model oparty na nazwach z innego źródła (np. krajowe -> puchary)."""

    def __init__(self, sm, canon):
        self.sm, self.canon = sm, canon
        self.alpha = sm.alpha

    def _t(self, n):
        return self.canon.resolve(n) or n

    def lam(self, h, a):
        return self.sm.lam(self._t(h), self._t(a))

    def count(self, t):
        return self.sm.count(self._t(t))


def mk(mid, family, label, p, odds):
    o = odds.get(mid)
    return dict(id=mid, family=family, label=label, p=p, fair=(1 / p if p > 0.001 else None),
                odds=o, ev=(p * o - 1 if o else None))


MARKET_W = 0.6   # ile z końcowej szansy pochodzi z rynku (kursy bez marży), gdy kursy są znane


def _pair_id(mid):
    """Id przeciwnego wyniku w tym samym rynku (do wyliczenia szansy z kursów bez marży)."""
    if mid.startswith("btts:"):
        return "btts:no" if mid.endswith("yes") else "btts:yes"
    p = mid.split(":")
    if len(p) == 4 and p[2] in ("over", "under"):
        p[2] = "under" if p[2] == "over" else "over"
        return ":".join(p)
    return None


def blend_with_market(ms, odds):
    """Model liczy z historii, a rynek zna skład i kontekst. Tam, gdzie mamy kursy po obu stronach rynku,
    szansę modelu uśredniamy z szansą wynikającą z kursów po usunięciu marży – to ucina przesadnie
    optymistyczne typy i fałszywe „value”."""
    if not odds:
        return ms
    tri = {k: odds.get(k) for k in ("1x2:1", "1x2:X", "1x2:2")}
    tri_ok = all(v and v > 1 for v in tri.values())
    inv = sum(1 / v for v in tri.values()) if tri_ok else 0
    for m in ms:
        mid, pm = m["id"], None
        if mid in tri and tri_ok and inv > 0:
            pm = (1 / tri[mid]) / inv
        else:
            q = _pair_id(mid)
            o1, o2 = odds.get(mid), odds.get(q) if q else None
            if o1 and o2 and o1 > 1 and o2 > 1:
                pm = (1 / o1) / (1 / o1 + 1 / o2)
        if pm is not None:
            m["p_model"] = m["p"]
            m["p"] = (1 - MARKET_W) * m["p"] + MARKET_W * pm
            m["fair"] = 1 / m["p"] if m["p"] > 0.001 else None
            m["ev"] = m["p"] * m["odds"] - 1 if m["odds"] else None
    return ms


def sb_lines(sb, stat, scope):
    """Linie Powyżej/Poniżej, które Superbet podał dla rynku (stat, total/home/away) – posortowane."""
    out = set()
    for k in (sb or {}):
        p = k.split(":")
        if len(p) == 4 and p[0] == stat and p[1] == scope and p[2] in ("over", "under"):
            try:
                out.add(float(p[3]))
            except ValueError:
                pass
    return sorted(out)


def auto_lines(mu, step, count):
    base = math.floor(mu) + 0.5
    idx = range(-(count // 2), count // 2 + 1)
    return [base + step * i for i in idx if base + step * i >= 0.5]


ADJ_EXP = {"goals": 1.0, "sot": 1.0, "shots": 0.6, "corners": 0.3}


class Model:
    def __init__(self, played, ref=None, priors=None, min_rows=20, fallback=None):
        self.ref = ref or dt.date.today()
        self.played = sorted([m for m in played if m["date"] <= self.ref], key=lambda m: m["date"])
        self.sm = {}
        for stat in FD_STATS:
            rows = [m for m in self.played if stat in m["stats"]]
            if len(rows) >= min_rows:
                self.sm[stat] = StatModel(rows, self.ref, stat, (priors or {}).get(stat))
        if fallback:  # brakujące statystyki (np. strzały w pucharach) bierzemy z modelu krajowego
            for stat, sm in fallback.items():
                self.sm.setdefault(stat, sm)
        self.teams = set()
        for m in self.played:
            self.teams.update((m["home"], m["away"]))

    def n_matches(self, team):
        sm = self.sm.get("goals")
        return sm.count(team) if sm else 0

    def predict(self, h, a, odds, adj=None, sb=None):
        if "goals" not in self.sm:
            return None
        exp, dist = {}, {}
        for stat, sm in self.sm.items():
            lh, la = sm.lam(h, a)
            e = ADJ_EXP.get(stat, 0.0)
            if adj and e:
                lh *= (adj["h"][0] * adj["a"][1]) ** e
                la *= (adj["a"][0] * adj["h"][1]) ** e
            exp[stat] = (lh, la)
            n = lambda mu: int(mu + 8 * math.sqrt(mu + sm.alpha * mu * mu)) + 12  # noqa
            dist[stat] = (pmf(lh, sm.alpha, n(lh)), pmf(la, sm.alpha, n(la)))
        ms = []
        ph, pa = dist["goals"]
        p1 = px = p2 = btts = 0.0
        for i, x in enumerate(ph):
            for j, y in enumerate(pa):
                pr = x * y
                if i > j: p1 += pr
                elif i == j: px += pr
                else: p2 += pr
                if i > 0 and j > 0: btts += pr
        ms += [mk("1x2:1", "1x2", f"Wygra {h}", p1, odds), mk("1x2:X", "1x2", "Remis", px, odds),
               mk("1x2:2", "1x2", f"Wygra {a}", p2, odds),
               mk("dc:1X", "dc", f"{h} lub remis (1X)", p1 + px, odds),
               mk("dc:X2", "dc", f"Remis lub {a} (X2)", px + p2, odds),
               mk("dc:12", "dc", "Bez remisu (12)", p1 + p2, odds),
               mk("btts:yes", "btts", "Obie strzelą – TAK", btts, odds),
               mk("btts:no", "btts", "Obie strzelą – NIE", 1 - btts, odds)]
        for stat, (dh, da) in dist.items():
            tot = conv(dh, da)
            step = LINE_STEP.get(stat, 1.0)
            lh, la = exp[stat]
            if stat == "goals":
                tl, hl, al = [0.5, 1.5, 2.5, 3.5, 4.5], [0.5, 1.5], [0.5, 1.5]
            else:
                tl, hl, al = auto_lines(lh + la, step, 5), auto_lines(lh, step, 3), auto_lines(la, step, 3)
            # Gdy Superbet podaje linie dla danego rynku, pokazujemy dokładnie te same linie co Superbet.
            tl, hl, al = (sb_lines(sb, stat, "total") or tl, sb_lines(sb, stat, "home") or hl,
                          sb_lines(sb, stat, "away") or al)
            for L in tl:
                po = over_prob(tot, L)
                ms.append(mk(f"{stat}:total:over:{L}", f"{stat}:total", "", po, odds))
                ms.append(mk(f"{stat}:total:under:{L}", f"{stat}:total", "", 1 - po, odds))
            for side, d, ls in (("home", dh, hl), ("away", da, al)):
                for L in ls:
                    po = over_prob(d, L)
                    ms.append(mk(f"{stat}:{side}:over:{L}", f"{stat}:{side}", "", po, odds))
                    ms.append(mk(f"{stat}:{side}:under:{L}", f"{stat}:{side}", "", 1 - po, odds))
        return dict(exp=exp, markets=blend_with_market(ms, odds))

    def profile(self, team, as_home):
        rows = [m for m in self.played if team in (m["home"], m["away"])]
        res = {}
        for stat in self.sm:
            vals, ven = [], []
            for m in rows:
                if stat not in m["stats"]:
                    continue
                home = m["home"] == team
                v = m["stats"][stat] if home else m["stats"][stat][::-1]
                vals.append(v)
                if home == as_home:
                    ven.append(v)
            if not vals:
                continue

            def avg(v, i):
                return sum(x[i] for x in v) / len(v) if v else None
            l6, l20, v6 = vals[-6:], vals[-20:], ven[-6:]
            res[stat] = dict(f6=avg(l6, 0), a6=avg(l6, 1), f20=avg(l20, 0), a20=avg(l20, 1),
                             fv=avg(v6, 0), av=avg(v6, 1), nv=len(v6), n=len(vals))
        return res

    def h2h(self, h, a, limit=6):
        rows = [m for m in self.played if {m["home"], m["away"]} == {h, a}]
        return rows[-limit:][::-1]


def outcome(mid, st):
    """Czy typ o danym id się sprawdził przy faktycznych statystykach meczu (None = brak danych)."""
    p = mid.split(":")
    g = st.get("goals")
    if not g:
        return None
    if p[0] == "1x2":
        return p[1] == ("1" if g[0] > g[1] else "X" if g[0] == g[1] else "2")
    if p[0] == "dc":
        return {"1X": g[0] >= g[1], "X2": g[1] >= g[0], "12": g[0] != g[1]}[p[1]]
    if p[0] == "btts":
        both = g[0] > 0 and g[1] > 0
        return both if p[1] == "yes" else not both
    if len(p) != 4 or p[0] not in st:
        return None
    h, a = st[p[0]]
    v = h + a if p[1] == "total" else h if p[1] == "home" else a
    over = v > float(p[3])
    return over if p[2] == "over" else not over


# --------------------------------------------------------------------------------------
# Backtest (skuteczność historyczna typów) – walk-forward: model widzi tylko mecze sprzed tygodnia testowego
# --------------------------------------------------------------------------------------
def bucket_of(p):
    return str(int(math.floor(p * 20)) * 5)


def run_backtest(dom_played, n_last=150):
    hist = defaultdict(lambda: defaultdict(lambda: [0, 0]))     # rodzina rynku -> przedział -> [ile, trafione]
    picks = defaultdict(lambda: [0, 0])                          # wybrane „najlepsze typy” (60-85%)
    groups = defaultdict(lambda: defaultdict(lambda: [0, 0]))   # grupa (gole, rożne...) -> przedział
    total = 0
    roi = defaultdict(lambda: [0, 0, 0.0])                      # nazwa strategii -> [zakładów, trafionych, zysk przy stawce 1]
    t0 = time.time()
    for comp, played in dom_played.items():
        ms = sorted(played, key=lambda m: m["date"])
        if len(ms) < n_last + 100:
            continue
        weeks = defaultdict(list)
        for m in ms[-n_last:]:
            weeks[m["date"] - dt.timedelta(days=m["date"].weekday())].append(m)
        for ws, lst in sorted(weeks.items()):
            ref = ws - dt.timedelta(days=1)
            model = Model([m for m in ms if m["date"] <= ref], ref)
            for m in lst:
                if model.n_matches(m["home"]) < 5 or model.n_matches(m["away"]) < 5:
                    continue
                pr = model.predict(m["home"], m["away"], m.get("odds") or {})
                if not pr:
                    continue
                total += 1
                best = {}
                fav = None
                for mkt in pr["markets"]:
                    o = mkt.get("odds")
                    if o and mkt["family"] in ("1x2", "goals:total"):
                        hit = outcome(mkt["id"], m["stats"])
                        if hit is not None:
                            gain = (o - 1) if hit else -1.0
                            kind = "1X2" if mkt["family"] == "1x2" else "Gole 2.5"
                            names = [(kind, "wszystkie zakłady po kolei")]
                            ev = mkt.get("ev")
                            if ev is not None and mkt["p"] >= 0.35:
                                for th in (0.03, 0.05, 0.10):
                                    if ev >= th:
                                        names.append((kind, f"przewaga ≥ {int(th * 100)}%"))
                            if mkt["family"] == "1x2" and (fav is None or mkt["p"] > fav[0]):
                                fav = (mkt["p"], gain, hit)
                            for nm in names:
                                r = roi[nm]
                                r[0] += 1
                                r[1] += int(hit)
                                r[2] += gain
                    if mkt["family"] == "dc" or not (0.5 <= mkt["p"] <= 0.95):
                        continue
                    hit = outcome(mkt["id"], m["stats"])
                    if hit is None:
                        continue
                    b = bucket_of(mkt["p"])
                    for tab in (hist[mkt["family"]], groups[mkt["family"].split(":")[0]]):
                        tab[b][0] += 1
                        tab[b][1] += int(hit)
                    if 0.6 <= mkt["p"] <= 0.85:
                        c = best.get(mkt["family"])
                        if c is None or mkt["p"] > c[0]:
                            best[mkt["family"]] = (mkt["p"], hit)
                for p, hit in best.values():
                    picks[bucket_of(p)][0] += 1
                    picks[bucket_of(p)][1] += int(hit)
                if fav:
                    r = roi[("1X2", "zawsze faworyt modelu")]
                    r[0] += 1
                    r[1] += int(fav[2])
                    r[2] += fav[1]
        log(f"  backtest {comp}: gotowe ({time.time() - t0:.0f}s)")
    res = {"generated": dt.date.today().isoformat(), "matches": total,
           "hist": {k: dict(v) for k, v in hist.items()}, "groups": {k: dict(v) for k, v in groups.items()},
           "picks": dict(picks),
           "roi": [[k[0], k[1], v[0], v[1], round(v[2], 2)] for k, v in sorted(roi.items())]}
    jsave(P("backtest.json"), res)
    return res


# --------------------------------------------------------------------------------------
# Składanie terminarza i analiz
# --------------------------------------------------------------------------------------
def fd_time_to_pl(t):
    try:
        h, m = t.split(":")
        return f"{(int(h) + 1) % 24:02d}:{m}"
    except ValueError:
        return ""


def superbet_odds(h, a):
    """Kursy z Superbet (kursy_superbet.json w repozytorium) – główne źródło, nadpisują inne."""
    for k, v in jload(os.path.join(HERE, "kursy_superbet.json"), {}).items():
        if k.startswith("_") or "|" not in k:
            continue
        kh, ka = k.split("|", 1)
        if same_team(kh, h) and same_team(ka, a):
            out = {}
            for i, o in v.items():
                if not isinstance(o, (int, float)) or o <= 1:
                    continue
                p = i.split(":")
                if len(p) == 4 and p[2] in ("over", "under"):
                    try:
                        p[3] = str(float(p[3]))  # "9.50" / "9.5" -> jeden zapis linii
                    except ValueError:
                        continue
                out[":".join(p)] = o
            return out
    return {}


def build_fixtures(days, dom_played, fd_fix, espn_fix):
    today = dt.date.today()
    end = today + dt.timedelta(days=days)
    canon = {c: Canon({t for m in p for t in (m["home"], m["away"])}) for c, p in dom_played.items()}
    fd_idx = {(f["comp"], f["home"], f["away"]): f for f in fd_fix}
    out = []
    espn_ok = [r for r in espn_fix if not r.get("done") and today <= pdate(r["date"]) <= end]
    if espn_ok:
        for r in espn_ok:
            comp, h, a = r["comp"], r["home"], r["away"]
            odds = dict(r.get("odds") or {})
            if comp in canon:
                h, a = canon[comp].resolve(h) or h, canon[comp].resolve(a) or a
                fo = fd_idx.get((comp, h, a))
                if fo and fo["odds"]:
                    odds = dict(fo["odds"])
            sb = superbet_odds(h, a)
            odds.update(sb)
            out.append(dict(comp=comp, date=pdate(r["date"]), time=r["time"], home=h, away=a, odds=odds, sb=sb,
                            form=r.get("form") if r.get("form_v") == 2 else None))
    else:
        for f in fd_fix:
            if today <= f["date"] <= end:
                sb = superbet_odds(f["home"], f["away"])
                out.append(dict(comp=f["comp"], date=f["date"], time=fd_time_to_pl(f["time"]), home=f["home"],
                                away=f["away"], odds={**f["odds"], **sb}, sb=sb))
    return out


def build_models(dom_played, euro_played, euro_teams):
    dom_models = {c: Model(p) for c, p in dom_played.items()}
    team_comp = {}
    for c, p in dom_played.items():
        for m in p:
            team_comp[m["home"]] = c
            team_comp[m["away"]] = c
    canon_all = Canon(team_comp.keys())
    priors = {s: {} for s in FD_STATS}
    for n in euro_teams:
        dn = canon_all.resolve(n)
        if not dn:
            continue
        for stat, sm in dom_models[team_comp[dn]].sm.items():
            if dn in sm.att:
                priors[stat][n] = (sm.att[dn], sm.dfn[dn])
    pool = Model([m for p in dom_played.values() for m in p])
    fallback = {s: Translated(sm, canon_all) for s, sm in pool.sm.items()}
    euro_model = Model(euro_played, priors=priors, min_rows=12, fallback=fallback)
    return dom_models, euro_model


def analyze_fixture(fx, model, api_cache, manual):
    h, a, di = fx["home"], fx["away"], fx["date"].isoformat()
    ab_h, ab_a = absences_for(h, di, api_cache, manual), absences_for(a, di, api_cache, manual)
    adj = {"h": absence_mult(ab_h), "a": absence_mult(ab_a)}
    pred = model.predict(h, a, fx["odds"], adj, fx.get("sb"))
    if not pred:
        return None
    return dict(comp=fx["comp"], date=fx["date"], time=fx.get("time", ""), home=h, away=a, odds=fx["odds"],
                form=fx.get("form") or {},
                exp=pred["exp"], markets=pred["markets"], prof_h=model.profile(h, True),
                prof_a=model.profile(a, False), h2h=model.h2h(h, a), n_h=model.n_matches(h),
                n_a=model.n_matches(a), abs={"h": ab_h, "a": ab_a}, adj=adj)


def build_analyses(days):
    dom_played, fd_fix = load_domestic()
    euro_played, espn_fix = load_euro()
    if not dom_played and not euro_played:
        return None
    fixtures = build_fixtures(days, dom_played, fd_fix, espn_fix)
    euro_teams = {t for m in euro_played for t in (m["home"], m["away"])}
    euro_teams |= {t for f in fixtures if COMP_INFO.get(f["comp"], ("", "", ""))[2] == "eu"
                   for t in (f["home"], f["away"])}
    dom_models, euro_model = build_models(dom_played, euro_played, euro_teams)
    api_cache, manual = jload(P("api_cache.json"), {}), manual_absences()
    out, skipped = [], defaultdict(int)
    for fx in sorted(fixtures, key=lambda f: (f["date"], f["time"], f["home"])):
        info = COMP_INFO.get(fx["comp"])
        if not info:
            continue
        model = euro_model if info[2] == "eu" else dom_models.get(fx["comp"])
        an = analyze_fixture(fx, model, api_cache, manual) if model else None
        if an:
            out.append(an)
        else:
            skipped[fx["comp"]] += 1
    if skipped:
        log("Pominięto (brak danych historycznych): " + ", ".join(f"{k} ×{v}" for k, v in skipped.items()))
    return out


def low_conf(an):
    return min(an["n_h"], an["n_a"]) < MIN_MATCHES_LOW_CONF


# --------------------------------------------------------------------------------------
# Raport HTML (aplikacja mobilna w stylu Flashscore / Superbet; dane osadzone jako JSON)
# --------------------------------------------------------------------------------------
def r2(x, n=2):
    return None if x is None else round(x, n)


def match_payload(i, an):
    country, _, kind = COMP_INFO[an["comp"]]
    ms = [[m["id"], m["family"], m["label"], round(m["p"], 4), m["odds"], r2(m["ev"], 3)] for m in an["markets"]]

    def prof(p):
        return {s: [r2(v["f6"]), r2(v["a6"]), r2(v["f20"]), r2(v["a20"]), r2(v["fv"]), r2(v["av"]), v["nv"]]
                for s, v in p.items()}

    def ab(lst):
        return [[e["n"], e["role"], e["st"], e["reason"]] for e in lst]
    h2h = [[m["date"].strftime("%d.%m.%y"), m["home"], m["away"], {k: [v[0], v[1]] for k, v in m["stats"].items()}]
           for m in an["h2h"]]
    return dict(i=i, comp=an["comp"], country=country, kind=kind, date=an["date"].isoformat(), time=an.get("time", ""),
                h=an["home"], a=an["away"], nh=an["n_h"], na=an["n_a"], low=low_conf(an), fm=an.get("form") or {},
                exp={s: [round(v[0], 2), round(v[1], 2)] for s, v in an["exp"].items()},
                ph=prof(an["prof_h"]), pa=prof(an["prof_a"]), h2h=h2h, m=ms,
                abs={"h": ab(an["abs"]["h"]), "a": ab(an["abs"]["a"])},
                adj={"h": [round((an["adj"]["h"][0] - 1) * 100, 1), round((an["adj"]["h"][1] - 1) * 100, 1)],
                     "a": [round((an["adj"]["a"][0] - 1) * 100, 1), round((an["adj"]["a"][1] - 1) * 100, 1)]})


APP_CSS = """
:root{--bg:#0d1117;--card:#161c25;--card2:#1e2632;--line:#262f3c;--tx:#e9eef5;--dim:#8a98aa;--acc:#2f8cff;
--g1:#1d5a39;--g2:#25804f;--val:#f5c542;--red:#c95757}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--tx);font:15px/1.35 system-ui,Segoe UI,Roboto,sans-serif}
button{font-family:inherit;color:inherit}
.top{position:sticky;top:0;z-index:5;background:var(--bg);border-bottom:1px solid var(--line)}
.hd{display:flex;justify-content:space-between;align-items:center;padding:6px 12px 0}
.hd b{font-size:17px}.hd span{font-size:11px;color:var(--dim)}
.tabs{display:flex;padding:2px 6px 0}
.tabs button{flex:1 1 auto;padding:8px 1px 7px;border:0;background:none;color:var(--dim);font-size:13.5px;font-weight:600;
border-bottom:3px solid transparent}
.tabs button.on{color:var(--tx);border-bottom-color:var(--acc)}
.strip{display:flex;gap:6px;overflow-x:auto;padding:6px 10px;scrollbar-width:none}
.strip::-webkit-scrollbar{display:none}
.dy{flex:none;min-width:54px;padding:4px 7px;border-radius:11px;border:1px solid var(--line);background:var(--card);
text-align:center;line-height:1.2}
.dy span{display:block;font-size:10.5px;color:var(--dim);text-transform:uppercase}.dy b{font-size:14px}
.dy small{display:none}
.dy.on{background:var(--acc);border-color:var(--acc)}.dy.on span,.dy.on small{color:#dcebff}
.chip{flex:none;padding:6px 12px;border-radius:17px;border:1px solid var(--line);background:var(--card);font-size:13.5px;
white-space:nowrap}
.chip.on{background:var(--tx);color:#0d1117;border-color:var(--tx);font-weight:700}
.chip small{opacity:.6;margin-left:4px}
main{padding:0 8px 90px}
.lgs{background:var(--card);border-radius:14px;margin:10px 0;overflow:hidden}
.lgh{display:flex;align-items:center;gap:8px;padding:10px 12px;background:var(--card2);cursor:pointer}
.lgh>div:first-child{flex:1;min-width:0}.lgh small{display:block;font-size:10.5px;letter-spacing:.06em;
text-transform:uppercase;color:var(--dim)}.lgh b{font-size:15px}
.lcols{display:flex;gap:5px}.lcols i{width:46px;text-align:center;font-style:normal;font-size:12px;color:var(--dim)}
.car{color:var(--dim);width:14px;text-align:right}
.mr{display:grid;grid-template-columns:42px 1fr auto;gap:6px 8px;align-items:center;padding:11px 12px 10px;
border-top:1px solid var(--line);cursor:pointer}
.mr:active{background:var(--card2)}
.tc{text-align:center;font-weight:700;font-size:14px;line-height:1.2}.tc small{display:block;font-weight:400;
color:var(--dim);font-size:10.5px}
.tn{min-width:0}.tn div{font-size:15px;line-height:1.28;padding:2px 0;overflow-wrap:anywhere}
.o3c{display:flex;gap:4px}
.oc{width:50px;padding:5px 0 4px;border-radius:9px;background:var(--card2);text-align:center;border:1.5px solid transparent;line-height:1.15}
.oc b{display:block;font-size:15px}.oc small{font-size:11px;color:var(--dim)}
.oc b.nb{font-size:13px;color:var(--dim);font-weight:500}
.oc.fv{background:var(--g1)}.oc.fv small{color:#cfe9d9}
.oc.val{border-color:var(--val)}
.tip{grid-column:2/-1;display:flex;justify-content:space-between;align-items:flex-start;gap:10px;font-size:13px;
color:var(--dim);border-top:1px dashed var(--line);padding-top:6px}.tip span{min-width:0}
.pill{flex:none;text-align:right;color:var(--tx);white-space:nowrap}
.pill b{display:inline-block;background:var(--g1);padding:1px 8px;border-radius:9px;font-size:13.5px}
.pill b.p2{background:var(--g2)}.pill b.p0{background:#5b4a1f}
.pill i{display:block;font-style:normal;font-size:11px;color:var(--dim);margin-top:1px}
.bds{grid-column:2/-1;margin-top:-2px}
.bd{display:inline-block;font-size:10.5px;font-weight:700;padding:1px 6px;border-radius:7px;margin-right:5px}
.bv{background:var(--val);color:#222}.bl{background:#5d2a2a;color:#fff}.bi{background:#3a3220;color:var(--val)}
.empty{color:var(--dim);text-align:center;padding:46px 10px}
.flt{display:flex;gap:6px;align-items:center;overflow-x:auto;padding:3px 2px 6px;scrollbar-width:none}.flt::-webkit-scrollbar{display:none}
.note{font-size:12px;color:var(--dim);padding:6px 6px}
.tp{display:flex;gap:10px;align-items:center;background:var(--card);border-radius:12px;padding:11px 12px;margin:7px 0;
border-left:4px solid #6b5a2a}
.tp.p1{border-left-color:var(--g1)}.tp.p2{border-left-color:#3fcf7f}
.ti{flex:1;min-width:0}.tt{font-weight:600;font-size:15px;line-height:1.3}.ts{font-size:12px;color:var(--dim);margin-top:3px}
.tk{flex:none;text-align:right;font-size:12px;color:var(--dim);line-height:1.35}.tk b{display:block;font-size:20px;color:var(--tx)}
.tk .kr{display:block;color:var(--tx);font-size:12.5px;font-weight:600}.tk em{font-style:normal;color:var(--val);font-weight:700}
.hs{color:#7fd49f}.hs.w{color:#e8b36a}
.det{position:fixed;inset:0;background:var(--bg);overflow-y:auto;z-index:10}
.dh{position:sticky;top:0;background:var(--bg);z-index:2;padding:8px 10px 0;border-bottom:1px solid var(--line)}
.back{border:0;background:var(--card);border-radius:10px;padding:8px 14px;font-size:14px}
.dt{padding:8px 4px 4px}.dt .mt{font-size:12.5px;color:var(--dim);display:flex;justify-content:space-between}
.dt .tm{font-size:20px;font-weight:700;margin-top:3px}
.sub{display:flex}.sub button{flex:1;padding:10px 2px;border:0;background:none;color:var(--dim);font-weight:600;
font-size:14px;border-bottom:3px solid transparent}.sub button.on{color:var(--tx);border-bottom-color:var(--acc)}
.dc{padding:8px 8px 90px}
.cell{background:var(--card2);border-radius:10px;padding:7px 4px;text-align:center;min-height:56px;display:flex;
flex-direction:column;justify-content:center;border:1.5px solid transparent;position:relative}
.cell .cl{font-size:11.5px;color:var(--dim)}.cell b{font-size:18px}.cell small{font-size:11.5px;color:var(--dim)}
.cell.g1{background:var(--g1)}.cell.g2{background:var(--g2)}
.cell.g1 small,.cell.g2 small,.cell.g1 .cl,.cell.g2 .cl{color:#cfe9d9}
.cell.val{border-color:var(--val)}.cell em{position:absolute;top:-8px;right:6px;background:var(--val);color:#222;
font-style:normal;font-size:10.5px;font-weight:700;padding:0 5px;border-radius:6px}
.o3{display:grid;grid-template-columns:repeat(3,1fr);gap:6px}.o2{display:grid;grid-template-columns:repeat(2,1fr);gap:6px}
details{background:var(--card);border-radius:14px;margin:8px 0;overflow:hidden}
summary{padding:13px 14px;font-weight:700;font-size:15px;cursor:pointer;list-style:none;display:flex;align-items:center}
summary::-webkit-details-marker{display:none}summary:after{content:'▾';color:var(--dim);margin-left:10px}
details[open] summary:after{content:'▴'}.in{padding:0 10px 10px}
.sh{font-size:12px;color:var(--dim);margin:10px 2px 6px;text-transform:uppercase;letter-spacing:.05em}
.row{display:grid;grid-template-columns:46px 1fr 1fr;gap:6px;margin:6px 0}
.row .ln{display:flex;align-items:center;justify-content:center;font-weight:700;color:var(--dim)}
.rl{font-size:12.5px;color:var(--dim);margin:0 2px 4px}
.cps{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;background:var(--card);border-radius:14px;padding:12px 8px;margin:8px 0;text-align:center}.cps small{display:block;color:var(--dim);font-size:11px}.cps b{font-size:17px}
.top3{background:var(--card);border-radius:14px;padding:6px 10px;margin:8px 0}
.top3 h4{margin:6px 2px;font-size:12.5px;color:var(--dim);text-transform:uppercase;letter-spacing:.05em;font-weight:600}
.top3 .tp,.sc .tp{background:var(--card2);margin:6px 0}
.sc{background:var(--card);border-radius:14px;padding:12px;margin:8px 0}.sc h4{margin:0 0 8px;font-size:15px}
.ex{display:grid;grid-template-columns:1fr auto auto auto 1fr;gap:8px;align-items:center;text-align:center}
.ex span{font-size:13px;color:var(--dim)}.ex b{font-size:21px}
.t2{width:100%;border-collapse:collapse;margin-top:8px;font-size:13px}
.t2 th{color:var(--dim);font-weight:500;text-align:right;padding:3px 4px}.t2 th:first-child{text-align:left}
.t2 td{padding:4px 4px;text-align:right;border-top:1px solid var(--line)}.t2 td:first-child{text-align:left;color:var(--dim)}
.t2 tr.vn td{color:var(--tx)}.t2 b{font-weight:700}
.hh{background:var(--card);border-radius:12px;padding:10px 12px;margin:8px 0}.hh .s{font-size:12.5px;color:var(--dim);margin-top:3px}
.ab{background:var(--card);border-radius:14px;padding:12px;margin:8px 0}.ab h4{margin:0 0 6px}
.ab li{margin:4px 0;font-size:14px}.ab small{color:var(--dim)}.ab ul{margin:0;padding-left:18px}
.bt{background:var(--card);border-radius:14px;padding:12px;margin:10px 0}.bt h3{margin:0 0 8px;font-size:15px}
.br{display:grid;grid-template-columns:70px 1fr 74px;gap:8px;align-items:center;margin:7px 0;font-size:13.5px}
.bar{height:10px;border-radius:5px;background:var(--card2);position:relative;overflow:hidden}
.bar i{position:absolute;left:0;top:0;bottom:0;background:var(--g2)}.bar u{position:absolute;top:-2px;bottom:-2px;width:2px;background:#fff}
.cph{display:flex;justify-content:space-between;gap:10px;padding:10px 6px 2px;font-weight:700;font-size:14.5px}
.cph span{flex:1}.cph span:last-child{text-align:right}
.d1,.d2{display:inline-block;width:10px;height:10px;border-radius:50%;margin:0 7px}.d1{background:var(--g2)}.d2{background:#3d7bd6}
.cs{font-size:12px;color:var(--dim);margin:-4px 0 6px}
.cp{display:grid;grid-template-columns:52px 1fr 52px;gap:8px;align-items:center;padding:7px 0;border-top:1px solid var(--line)}
.cv{font-size:17px;font-weight:600;color:var(--dim)}.cv.r{text-align:right}.cv.hi{color:var(--tx);font-weight:800}
.cl2{text-align:center;font-size:13px;color:var(--dim)}
.cb{height:6px;border-radius:3px;background:#3d7bd6;margin-top:5px;overflow:hidden}.cb i{display:block;height:100%;background:var(--g2)}
.fch{display:flex;gap:6px;margin:0 0 8px}
.fc{display:inline-flex;align-items:center;justify-content:center;width:24px;height:24px;border-radius:6px;font-size:12.5px;font-weight:800;color:#fff;flex:none}
.fw{background:#25804f}.fd{background:#8a7a2e}.fl{background:#b04848}
.fr{display:flex;align-items:center;gap:10px;padding:8px 0;border-top:1px solid var(--line)}
.fo{flex:1;min-width:0}.fo b{display:block;font-size:14px;font-weight:600}.fo small{color:var(--dim);font-size:11.5px}
.fs{font-weight:700;font-size:15px}
.fo{flex:1;min-width:0}.ft{display:flex;justify-content:space-between;gap:8px;font-size:14px;color:var(--dim);line-height:1.5}
.ft.me{color:var(--tx);font-weight:700}.ft b{font-weight:700;min-width:14px;text-align:right}
.fd2{flex:none;text-align:right;font-size:11px;color:var(--dim);line-height:1.35}
.ar{display:flex;align-items:center;gap:10px;padding:9px 0;border-top:1px solid var(--line)}
.ai{flex:none;width:26px;height:26px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:13px;font-weight:800;color:#fff}
.ao1{background:#b04848}.ao2{background:#8a7a2e}.ao3{background:#25804f}
.an{flex:1;min-width:0}.an b{display:block;font-size:14.5px}.an small{display:block;color:var(--dim);font-size:12px;margin-top:1px}
.tg{flex:none;font-size:11.5px;font-weight:700;padding:3px 9px;border-radius:9px}.tg1{background:#5d2a2a;color:#ffb4b4}.tg2{background:#3a3220;color:var(--val)}
.ef{margin-top:8px;padding-top:8px;border-top:1px dashed var(--line);font-size:12.5px;color:var(--dim)}
.hide{display:none}
.shr{border:1px solid var(--line);background:var(--card);border-radius:14px;padding:4px 11px;font-size:12.5px;margin-left:8px}
.toast{position:fixed;left:12px;right:12px;bottom:18px;background:#25804f;color:#fff;border-radius:12px;padding:12px 14px;
z-index:30;font-size:14px;text-align:center}
"""

APP_JS = r"""
const D=__DATA__;
const ST={goals:'Gole',shots:'Strzały',sot:'Strzały celne',corners:'Rożne',fouls:'Faule',cards:'Żółte kartki',offsides:'Spalone'};
const GRP={'1x2':'Wynik 1X2','btts':'Obie strzelą',...ST};
const CAT=[['all','Wszystko'],['1x2','1X2'],['goals','Gole'],['btts','Obie strzelą'],['corners','Rożne'],['shots','Strzały'],['sot','Celne'],['fouls','Faule'],['cards','Kartki'],['offsides','Spalone']];
const POL={over:'powyżej',under:'poniżej'};
const WD=['ndz','pon','wt','śr','czw','pt','sob'];
const DAYS=[...new Set(D.matches.map(x=>x.date))].sort();
const S={per:3,tab:'matches',day:DAYS.find(d=>d>=D.today)||DAYS[0]||'all',league:'all',minp:D.minp,cat:'all',coll:{},dtab:'bets',scroll:0,cn:4,cm:'safe',co:1.3,rm:'corners',rr:'all',ro:0,rn:4};
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const pc=p=>Math.round(p*100)+'%';
const fair=p=>p>0.001?(1/p).toFixed(2):'–';
const sgn=v=>(v>0?'+':'')+v;
function pid(id){const p=id.split(':');return p.length==4?{stat:p[0],scope:p[1],dir:p[2],line:parseFloat(p[3])}:null}
function lab(m,x){const q=pid(m[0]);if(!q)return m[2];const nm=ST[q.stat];
 if(q.scope==='total')return `${nm} łącznie – ${POL[q.dir]} ${q.line}`;
 return `${q.scope==='home'?x.h:x.a}: ${nm.toLowerCase()} ${POL[q.dir]} ${q.line}`}
const dayOf=d=>Math.round((new Date(d+'T00:00:00')-new Date(D.today+'T00:00:00'))/864e5);
function dname(d){const k=dayOf(d);return k===0?'Dziś':k===1?'Jutro':WD[new Date(d+'T00:00:00').getDay()]}
function dfull(d){return dname(d)+' '+d.slice(8)+'.'+d.slice(5,7)}
const byId=(x,id)=>x.m.find(m=>m[0]===id);
function hist(m){const b=String(Math.floor(m[3]*20)*5),t=D.bt;if(!t)return null;
 let h=t.hist[m[1]]&&t.hist[m[1]][b];if(!h||h[0]<25){const g=t.groups[m[1].split(':')[0]];h=g&&g[b]}
 return h&&h[0]>=25?{r:h[1]/h[0],n:h[0]}:null}
function histTxt(m){const h=hist(m);return h?`<span class="hs${h.r<m[3]-0.04?' w':''}">hist. ${Math.round(h.r*100)}%</span>`:''}
const pcls=p=>p>=0.75?'p2':p>=0.65?'p1':'p0';
function cell(top,m){const p=m[3],o=m[4],ev=m[5],val=ev!=null&&ev>=0.03,g=p>=0.7?' g2':p>=0.6?' g1':'';
 return `<div class="cell${g}${val?' val':''}"><span class="cl">${top}</span><b>${pc(p)}</b><small>${o?'kurs '+o.toFixed(2):'~'+fair(p)}</small>${val?`<em>EV ${sgn(Math.round(ev*100))}%</em>`:''}</div>`}
function picksFor(x,minp){const best={},value=[];
 for(const m of x.m){if(m[1]==='dc')continue;const p=m[3];
  if(p>=minp&&p<=D.maxp){const c=best[m[1]];if(!c||p>c[3])best[m[1]]=m}
  if(m[5]!=null&&m[5]>=0.03&&p>=0.35)value.push(m)}
 return{best:Object.values(best).sort((a,b)=>b[3]-a[3]),value}}
D.matches.forEach(x=>{x.nv=x.m.filter(m=>m[1]!=='dc'&&m[5]!=null&&m[5]>=0.03&&m[3]>=0.35).length;x.na_=(x.abs.h.length+x.abs.a.length)});
const vis=()=>D.matches.filter(x=>(S.day==='all'||x.date===S.day)&&(S.league==='all'||x.comp===S.league));
/* mecz już rozpoczęty (czas meczu jest w czasie polskim, jak na telefonie) – nie pokazujemy go w typach, value i kuponie */
function started(x){if(!x.time||!/^\d{1,2}:\d{2}$/.test(x.time))return x.date<D.today;const t=new Date(x.date+'T'+x.time.padStart(5,'0')+':00');return t<new Date()}
const visA=()=>vis().filter(x=>!started(x));
const badges=x=>(x.nv?`<span class="bd bv">VALUE ×${x.nv}</span>`:'')+(x.na_?`<span class="bd bi">braki ${x.na_}</span>`:'')+(x.low?`<span class="bd bl">mała próba</span>`:'');
/* ---------- nagłówek: dni i ligi ---------- */
function bar(){
 let t='';[['matches','Mecze'],['picks','Typy'],['mkt','Rynki'],['value','Value'],['cpn','Kupon'],['acc','Skuteczność']].forEach(([k,n])=>t+=`<button class="${S.tab===k?'on':''}" data-tab="${k}">${n}</button>`);
 $('tb').innerHTML=t;
 const showf=S.tab!=='acc';
 $('dy').classList.toggle('hide',!showf);$('lc').classList.toggle('hide',!showf);
 if(!showf)return;
 let d=`<button class="dy${S.day==='all'?' on':''}" data-day="all"><span>&nbsp;</span><b>Wszystkie</b><small>${D.matches.length}</small></button>`;
 for(const x of DAYS)d+=`<button class="dy${S.day===x?' on':''}" data-day="${x}"><span>${dname(x)}</span><b>${x.slice(8)}.${x.slice(5,7)}</b><small>${D.matches.filter(m=>m.date===x).length}</small></button>`;
 $('dy').innerHTML=d;
 const inDay=D.matches.filter(x=>S.day==='all'||x.date===S.day);
 const lg=[...new Set(inDay.map(x=>x.comp))].sort((a,b)=>D.ord[a]-D.ord[b]);
 if(S.league!=='all'&&!lg.includes(S.league))S.league='all';
 let h=`<button class="chip${S.league==='all'?' on':''}" data-lg="all">Wszystkie<small>${inDay.length}</small></button>`;
 for(const l of lg)h+=`<button class="chip${S.league===l?' on':''}" data-lg="${esc(l)}">${esc(l)}<small>${inDay.filter(x=>x.comp===l).length}</small></button>`;
 $('lc').innerHTML=h;
 const a=document.querySelector('#dy .on');if(a&&a.scrollIntoView)a.scrollIntoView({inline:'center',block:'nearest'})}
/* ---------- lista meczów ---------- */
function oc(x,id,fav){const m=byId(x,id);if(!m)return'<div class="oc"></div>';
 const p=m[3],v=m[5]!=null&&m[5]>=0.03;
 return `<div class="oc${id===fav?' fv':''}${v?' val':''}">${m[4]?`<b>${m[4].toFixed(2)}</b>`:`<b class="nb">~${fair(p)}</b>`}<small>${pc(p)}</small></div>`}
function row(x){
 const b=picksFor(x,S.minp).best[0];
 const three=['1x2:1','1x2:X','1x2:2'].map(id=>byId(x,id)),fav=three.filter(Boolean).sort((a,c)=>c[3]-a[3])[0];
 const hb=b&&hist(b);
 const tip=b?`<div class="tip"><span>★ ${esc(lab(b,x))}</span><div class="pill"><b class="${pcls(b[3])}">${pc(b[3])}</b>${hb?`<i>hist. ${Math.round(hb.r*100)}%</i>`:''}</div></div>`:'';
 return `<div class="mr" data-m="${x.i}"><div class="tc">${x.time||'–'}${S.day==='all'?`<small>${x.date.slice(8)}.${x.date.slice(5,7)}</small>`:''}</div>
 <div class="tn"><div>${esc(x.h)}</div><div>${esc(x.a)}</div></div>
 <div class="o3c">${['1x2:1','1x2:X','1x2:2'].map(id=>oc(x,id,fav&&fav[0])).join('')}</div>${tip}${badges(x)?`<div class="bds">${badges(x)}</div>`:''}</div>`}
function listMatches(){
 const ms=vis();if(!ms.length)return'<div class="empty">Brak meczów dla wybranych filtrów.</div>';
 const g={};ms.forEach(x=>(g[x.comp]=g[x.comp]||[]).push(x));
 let h='';
 for(const c of Object.keys(g).sort((a,b)=>D.ord[a]-D.ord[b])){
  const L=g[c].sort((a,b)=>(a.date+a.time).localeCompare(b.date+b.time)||a.h.localeCompare(b.h));
  h+=`<section class="lgs"><div class="lgh" data-coll="${esc(c)}"><div><small>${esc(L[0].country)}</small><b>${esc(c)}</b></div>
  <div class="lcols"><i>1</i><i>X</i><i>2</i></div><span class="car">${S.coll[c]?'▸':'▾'}</span></div>${S.coll[c]?'':L.map(row).join('')}</section>`}
 return h+'<div class="note">W polu: kurs bukmachera, pod nim szansa wg modelu (~ = brak kursu, pokazany kurs uczciwy). Zielone tło = faworyt modelu, żółta ramka = przewaga nad kursem. ★ = najpewniejszy typ modelu w meczu.</div>'}
/* ---------- typy ---------- */
function tipRow(x,m,showEv){const o=m[4];
 return `<div class="tp ${pcls(m[3])}" data-m="${x.i}"><div class="ti"><div class="tt">${esc(lab(m,x))}</div><div class="ts">${esc(x.h)} – ${esc(x.a)}<br>${dfull(x.date)} ${x.time} · ${esc(x.comp)}${x.low?' · mała próba':''}</div></div>
 <div class="tk"><b>${pc(m[3])}</b><span class="kr">${o?'kurs '+o.toFixed(2):'brak kursu'}</span>${showEv&&m[5]!=null?`<em>EV ${sgn(Math.round(m[5]*100))}%</em>`:histTxt(m)}</div></div>`}
function listPicks(){const hid=vis().length-visA().length;
 let all=[];for(const x of visA())for(const m of picksFor(x,S.minp).best)all.push([x,m]);
 if(S.cat!=='all')all=all.filter(([x,m])=>m[1].split(':')[0]===S.cat);
 all.sort((a,b)=>b[1][3]-a[1][3]);
 if(S.per>0){const cnt={};all=all.filter(([x,m])=>{cnt[x.i]=(cnt[x.i]||0)+1;return cnt[x.i]<=S.per})}
 let h='<div class="flt">'+CAT.map(([k,n])=>`<button class="chip${S.cat===k?' on':''}" data-cat="${k}">${n}</button>`).join('')+'</div>';
 h+='<div class="flt"><span class="note">Min.</span>'+[0.55,0.6,0.65,0.7,0.75].map(v=>`<button class="chip${S.minp===v?' on':''}" data-minp="${v}">${Math.round(v*100)}%</button>`).join('')+'<span class="note">Na mecz</span>'+[[1,'1'],[3,'3'],[0,'wsz.']].map(([v,n])=>`<button class="chip${S.per===v?' on':''}" data-per="${v}">${n}</button>`).join('')+'</div>';
 h+=`<div class="note">Najpewniejsze typy modelu, bez „oczywistych” powyżej ${Math.round(D.maxp*100)}%. hist. = jak często podobne typy trafiały w przeszłości.</div>`;
 return h+(hid?`<div class="note">Ukryto ${hid} mecz(e), które już się rozpoczęły.</div>`:'')+(all.length?all.slice(0,80).map(([x,m])=>tipRow(x,m,false)).join(''):'<div class="empty">Brak typów w tym przedziale.</div>')}
function listValue(){const hid=vis().length-visA().length;
 let all=[];for(const x of visA())for(const m of picksFor(x,0).value)all.push([x,m]);
 all.sort((a,b)=>b[1][5]-a[1][5]);
 return '<div class="note">Typy, w których model daje przewagę ≥3% nad kursem (kursy: 1X2 oraz Over/Under 2.5 gdy są dostępne). Szansa to średnia z modelu i z kursów bukmachera bez marży (tam, gdzie kursy są po obu stronach rynku), więc skrajne przewagi są ucięte. Backtest pokazuje, że sam model z kursami przynosił stratę – traktuj value jako podpowiedź, nie pewniak.</div>'+
  (hid?`<div class="note">Ukryto ${hid} mecz(e), które już się rozpoczęły.</div>`:'')+(all.length?all.slice(0,80).map(([x,m])=>tipRow(x,m,true)).join(''):'<div class="empty">Brak typów z przewagą.</div>')}
/* ---------- rynki: wybrany rodzaj zakładu, do 4 typów na mecz ---------- */
const MKT=[['goals','Gole'],['sot','Celne'],['shots','Strzały'],['corners','Rożne'],['cards','Kartki'],['fouls','Faule'],['offsides','Spalone'],['1x2','Wynik'],['btts','Obie strzelą']];
const RISK=[['all','Dowolne',0.3,0.93],['low','Niskie',0.7,0.93],['mid','Średnie',0.55,0.7],['high','Wysokie',0.35,0.55]];
const fam=m=>m[1].split(':')[0];
function mktPicks(x){const r=RISK.find(v=>v[0]===S.rr)||RISK[0],want=S.rm==='1x2'?['1x2','dc']:[S.rm];
 const c=x.m.filter(m=>{const p=m[3],o=m[4]||estOdds(p);return want.includes(fam(m))&&p>=r[2]&&p<=r[3]&&o>=S.ro});
 /* różnorodność: najpierw najlepszy typ z każdej grupy (łącznie/gospodarz/gość × powyżej/poniżej), potem reszta */
 const key=m=>{const q=pid(m[0]);return q?q.scope+q.dir:fam(m)+':'+m[0]};
 c.sort((a,b)=>b[3]-a[3]);const seen=new Set(),first=[],rest=[];
 for(const m of c){const k=key(m);(seen.has(k)?rest:first).push(m);seen.add(k)}
 return first.concat(rest).slice(0,S.rn).sort((a,b)=>b[3]-a[3])}
function listMkt(){const hid=vis().length-visA().length;
 let h='<div class="flt">'+MKT.map(([k,n])=>`<button class="chip${S.rm===k?' on':''}" data-rm="${k}">${n}</button>`).join('')+'</div>';
 h+='<div class="flt"><span class="note">Ryzyko</span>'+RISK.map(([k,n])=>`<button class="chip${S.rr===k?' on':''}" data-rr="${k}">${n}</button>`).join('')+'</div>';
 h+='<div class="flt"><span class="note">Kurs min.</span>'+[[0,'dowolny'],[1.3,'1.30'],[1.5,'1.50'],[1.8,'1.80'],[2.2,'2.20']].map(([v,n])=>`<button class="chip${S.ro===v?' on':''}" data-ro="${v}">${n}</button>`).join('')+'</div><div class="flt"><span class="note">Typów na mecz</span>'+[1,2,3,4].map(v=>`<button class="chip${S.rn===v?' on':''}" data-rn="${v}">${v}</button>`).join('')+'</div>';
 const nm=(MKT.find(v=>v[0]===S.rm)||['',''])[1],r=RISK.find(v=>v[0]===S.rr);
 h+=`<div class="note">Tylko typy z rynku „${esc(nm)}” – do ${S.rn} na mecz${S.rr!=='all'?`, ryzyko ${r[1].toLowerCase()} (szansa ${Math.round(r[2]*100)}–${Math.round(r[3]*100)}%)`:''}${S.ro?`, kurs min. ${S.ro.toFixed(2)}`:''}. „~” = brak kursu bukmachera, kurs szacowany z szansy modelu. Kliknij mecz, żeby zobaczyć szczegóły.</div>`;
 if(hid)h+=`<div class="note">Ukryto ${hid} mecz(e), które już się rozpoczęły.</div>`;
 const ms=visA().sort((a,b)=>(a.date+a.time).localeCompare(b.date+b.time)||a.h.localeCompare(b.h));let n=0;
 for(const x of ms){const L=mktPicks(x);if(!L.length)continue;n++;
  h+=`<section class="lgs"><div class="lgh" data-m="${x.i}"><div><small>${dfull(x.date)} ${x.time} · ${esc(x.comp)}</small><b>${esc(x.h)} – ${esc(x.a)}</b></div><span class="car">›</span></div>`+
  L.map(m=>{const o=m[4];return `<div class="tp ${pcls(m[3])}" data-m="${x.i}"><div class="ti"><div class="tt">${esc(lab(m,x))}</div></div><div class="tk"><b>${pc(m[3])}</b><span class="kr">${o?'kurs '+o.toFixed(2):'~'+estOdds(m[3]).toFixed(2)}</span>${histTxt(m)}</div></div>`}).join('')+'</section>'}
 return h+(n?'':'<div class="empty">Brak typów tego rynku dla wybranych filtrów.<br>Zmień ryzyko, kurs albo dzień.</div>')}
/* ---------- skuteczność (backtest) ---------- */
const ROIORD=['wszystkie zakłady po kolei','zawsze faworyt modelu','przewaga ≥ 3%','przewaga ≥ 5%','przewaga ≥ 10%'];
function listAcc(){
 const t=D.bt;
 if(!t)return'<div class="empty">Brak danych backtestu.<br>Uruchom w Termux:<br><b>python futbol.py backtest</b></div>';
 let h=`<div class="note">Test na ${t.matches} meczach ligowych z ostatnich miesięcy (model widział tylko mecze sprzed danego tygodnia). Dane z ${esc(t.generated)}. Biała kreska = średnia szansa przewidywana, zielony pasek = faktyczna trafność.</div>`;
 const rows=(obj,label)=>Object.keys(obj).map(Number).sort((a,b)=>a-b).filter(k=>obj[k][0]>=15).map(k=>{
  const [n,hit]=obj[k],r=hit/n,mid=(k+2.5)/100;
  return `<div class="br"><div>${k}–${k+5}%</div><div class="bar"><i style="width:${r*100}%"></i><u style="left:${mid*100}%"></u></div><div><b>${Math.round(r*100)}%</b> <span style="color:var(--dim)">n=${n}</span></div></div>`}).join('');
 if(t.roi&&t.roi.length){
  const byk={};t.roi.forEach(r=>(byk[r[0]]=byk[r[0]]||[]).push(r));
  h+='<div class="bt"><h3>Czy dałoby to zysk? (stawka 1 zł na typ)</h3><div class="note" style="padding:0 0 8px">Test na prawdziwych kursach z historii. Zysk = suma wygranych minus stawki, w % od obstawionych złotych. Minus oznacza, że typy z kursami bukmachera przynosiłyby stratę.</div>';
  for(const k of Object.keys(byk)){
   h+=`<div class="sh">${esc(k)}</div>`;
   byk[k].sort((a,b)=>ROIORD.indexOf(a[1])-ROIORD.indexOf(b[1])).forEach(([_,nm,n,hit,pr])=>{
    if(n<20)return;const roi=pr/n*100;
    h+=`<div class="br" style="grid-template-columns:1fr 70px 70px"><div>${esc(nm)}<br><span style="color:var(--dim);font-size:12px">${n} zakładów · trafione ${Math.round(hit/n*100)}%</span></div><div style="text-align:right;color:var(--dim);font-size:12px">${pr>=0?'+':''}${pr.toFixed(1)} zł</div><div style="text-align:right"><b style="color:${roi>=0?'#7fd49f':'#e07a7a'}">${roi>=0?'+':''}${roi.toFixed(1)}%</b></div></div>`})}
  h+='<div class="note" style="padding:6px 0 0">Kursy: średnia z kilku bukmacherów (football-data.co.uk) – tylko 1X2 i Over/Under 2.5, bo do reszty rynków nie ma historycznych kursów. Dla kartek, fauli, rożnych nie da się tego sprawdzić.</div></div>'}
 h+=`<div class="bt"><h3>Najlepsze typy modelu (60–85%)</h3>${rows(t.picks)||'brak'}</div>`;
 for(const g of Object.keys(t.groups).sort((a,b)=>(GRP[a]||a).localeCompare(GRP[b]||b))){
  const o={};for(const k in t.groups[g])if(+k>=60)o[k]=t.groups[g][k];const r=rows(o);
  if(r)h+=`<div class="bt"><h3>${esc(GRP[g]||g)} – typy ≥60%</h3>${r}</div>`}
 return h}
/* ---------- kupon: propozycja zakładu na wybrany dzień ---------- */
/* kurs szacowany (gdy brak kursu bukmachera): kurs uczciwy pomniejszony o typową marżę */
const estOdds=p=>0.93/p;
const PLUS=[1.4,2]; /* zakres kursów pojedynczego typu w stylu „Mocne+” */
/* szansa z samego kursu: bez marży, gdy znamy kursy wszystkich wyników rynku; inaczej kurs z typową marżą */
function marketP(x,m){const id=m[0],o=m[4],od=i=>{const k=byId(x,i);return k&&k[4]};
 if(id.startsWith('1x2:')){const t=['1x2:1','1x2:X','1x2:2'].map(od);if(t.every(v=>v))return (1/o)/t.reduce((a,v)=>a+1/v,0)}
 const q=id.endsWith(':yes')?id.slice(0,-3)+'no':id.endsWith(':no')?id.slice(0,-2)+'yes':id.includes(':over:')?id.replace(':over:',':under:'):id.includes(':under:')?id.replace(':under:',':over:'):null;
 const o2=q&&od(q);return o2?(1/o)/(1/o+1/o2):0.93/o}
/* ostrożna szansa do kuponu: model nie może przebić rynku o więcej niż CAP, a gdy jest ostrożniejszy – liczy się model */
const CAP=0.03;
const realP=(x,m)=>m[4]?Math.min(m[3],marketP(x,m)+CAP):m[3];
function couponLegs(n,mode){
 const L=[];
 /* „Mocne+” bierze wszystkie mecze wybranego dnia – bez filtra ligi */
 const pool=mode==='plus'?D.matches.filter(x=>(S.day==='all'||x.date===S.day)&&!started(x)):visA();
 for(const x of pool){let best=null,bs=-1;
  for(const m0 of x.m){
   /* w „Pewniakach” i „Mocne+” liczy się ostrożna szansa, w „Value” bez zmian */
   let m=m0;if(mode!=='value'&&m0[4]){const r=realP(x,m0);m=[m0[0],m0[1],m0[2],r,m0[4],r*m0[4]-1]}
   const p=m[3],o=m[4],ev=m[5];
   if(p>0.93)continue;
   let sc;
   if(mode==='safe'){if((o||estOdds(p))<S.co||(o&&ev!=null&&ev<-0.1))continue;sc=p}
   else if(mode==='plus'){if(!o||o<PLUS[0]||o>PLUS[1]||p<0.5||(ev!=null&&ev<-0.1))continue;sc=p}
   else{if(ev==null||ev<0.03||p<0.45)continue;sc=ev*Math.min(1,p/0.6)}
   if(mode==='value'&&x.low)sc*=0.8;
   /* w „Pewniakach” typ z prawdziwym kursem ma pierwszeństwo przed szacowanym */
   if(mode==='safe'&&o)sc+=1;
   if(sc>bs){bs=sc;best=m}}
  if(best)L.push([x,best,bs])}
 L.sort((a,b)=>b[2]-a[2]);return L.slice(0,n)}
function listCoupon(){
 let h='<div class="flt"><span class="note">Typów</span>'+[2,3,4,5].map(v=>`<button class="chip${S.cn===v?' on':''}" data-cn="${v}">${v}</button>`).join('')+
 '<span class="note">Styl</span>'+[['safe','Pewniaki'],['plus','Mocne+'],['value','Value']].map(([k,n])=>`<button class="chip${S.cm===k?' on':''}" data-cm="${k}">${n}</button>`).join('')+'</div>';
 if(S.cm==='safe')h+='<div class="flt"><span class="note">Min. kurs typu</span>'+[1.2,1.3,1.5].map(v=>`<button class="chip${S.co===v?' on':''}" data-co="${v}">${v.toFixed(2)}</button>`).join('')+'</div>';
 const L=couponLegs(S.cn,S.cm);
 if(!L.length)return h+'<div class="empty">Brak typów spełniających kryteria dla wybranego dnia i ligi.<br>Zmień dzień u góry albo styl kuponu.</div>';
 let P=1,O=1,est=false;
 const rows=L.map(([x,m],j)=>{const p=m[3],o=m[4]||estOdds(p);if(!m[4])est=true;P*=p;O*=o;const v=m[5]!=null&&m[5]>=0.03;
  return `<div class="tp ${pcls(p)}" data-m="${x.i}"><div class="ti"><div class="tt">${j+1}. ${esc(lab(m,x))}</div><div class="ts">${esc(x.h)} – ${esc(x.a)}<br>${dfull(x.date)} ${x.time} · ${esc(x.comp)}${x.low?' · mała próba':''}</div></div>
  <div class="tk"><b>${pc(p)}</b><span class="kr">${m[4]?'kurs '+m[4].toFixed(2):'~'+o.toFixed(2)+' (szac.)'}</span>${v?`<em>EV ${sgn(Math.round(m[5]*100))}%</em>`:histTxt(m)}</div></div>`}).join('');
 const ev=P*O-1;
 h+=`<div class="cps"><div><small>Kurs łączny</small><b>${est?'~':''}${O.toFixed(2)}</b></div><div><small>Szansa wejścia</small><b>${pc(P)}</b></div><div><small>EV kuponu</small><b style="color:${ev>=0?'#7fd49f':'#e07a7a'}">${est?'~':''}${sgn(Math.round(ev*100))}%</b></div><div><small>10 zł wygra</small><b>${est?'~':''}${(10*O).toFixed(0)} zł</b></div></div>`;
 h+=rows;
 if(L.length<S.cn)h+=`<div class="note">Znalazłem tylko ${L.length} typ(y) spełniające kryteria – nie dobijałem słabszymi.</div>`;
 h+=`<div class="note">Najlepszy typ z każdego meczu (jeden na mecz), ${S.cm==='safe'?`wybrane wg najwyższej ostrożnej szansy wśród typów z kursem min. ${S.co.toFixed(2)} (najpierw z prawdziwym kursem bukmachera)`:S.cm==='plus'?`najwyższe szanse ze wszystkich meczów dnia (filtr ligi pominięty), tylko prawdziwe kursy bukmachera ${PLUS[0].toFixed(2)}–${PLUS[1].toFixed(2)}, szansa ≥ 50%. Wyższy kurs = mniejsza pewność niż w „Pewniakach”`:'wybrane wg przewagi nad kursem (EV ≥ 3%, szansa ≥ 45%)'}. Szansa wejścia to iloczyn szans pojedynczych typów – im więcej typów, tym szybciej spada. ${est?'„~” = część typów nie ma kursu bukmachera, użyłem kursu szacowanego z szansy modelu (z odjętą marżą), więc wynik jest orientacyjny. ':''}${S.cm!=='value'?`Szansa w tym stylu jest ostrożna: model nie może przebić szansy z kursu bukmachera o więcej niż ${Math.round(CAP*100)} pkt proc., dlatego może być niższa niż w innych zakładkach. `:''}To propozycja z modelu, nie gwarancja – sprawdź składy tuż przed meczem i graj odpowiedzialnie. Kliknij typ, żeby zobaczyć mecz.</div>`;
 return h}
function toast(t){const e=document.createElement('div');e.className='toast';e.textContent=t;document.body.appendChild(e);setTimeout(()=>e.remove(),4500)}
async function shareReport(){
 const hst=location.hostname,hosted=location.protocol.startsWith('http')&&!/^(localhost|127\.|10\.|192\.168\.)/.test(hst);
 if(hosted){const u=location.href.split('#')[0];
  try{if(navigator.share){await navigator.share({title:'Typy piłkarskie',url:u});return}}catch(e){if(e&&e.name==='AbortError')return}
  try{await navigator.clipboard.writeText(u);toast('Skopiowano link – wklej go znajomym.');return}catch(e){}
  toast('Link do strony: '+u);return}
 let src;try{src=await (await fetch(location.href.split('#')[0],{cache:'no-store'})).text()}catch(e){src='<!doctype html>'+document.documentElement.outerHTML}
 const name='typy_'+D.today+'.html';
 try{const f=new File([src],name,{type:'text/html'});
  if(navigator.canShare&&navigator.canShare({files:[f]})){await navigator.share({files:[f],title:'Typy piłkarskie '+D.today});return}}
 catch(e){if(e&&e.name==='AbortError')return}
 const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([src],{type:'text/html'}));a.download=name;
 document.body.appendChild(a);a.click();a.remove();toast('Zapisano plik '+name+' w Pobranych – wyślij go znajomym (np. WhatsApp, Messenger, e-mail).')}
function render(){bar();
 $('main').innerHTML=S.tab==='matches'?listMatches():S.tab==='picks'?listPicks():S.tab==='value'?listValue():S.tab==='mkt'?listMkt():S.tab==='cpn'?listCoupon():listAcc()}
/* ---------- szczegóły meczu ---------- */
function groups(x){
 const tri=(ids,tops)=>ids.map((id,k)=>{const m=byId(x,id);return m?cell(tops[k],m):''}).join('');
 let out=`<details open><summary>Wynik meczu</summary><div class="in"><div class="rl">1X2</div><div class="o3">${tri(['1x2:1','1x2:X','1x2:2'],['1','X','2'])}</div>
 <div class="rl" style="margin-top:10px">Podwójna szansa</div><div class="o3">${tri(['dc:1X','dc:12','dc:X2'],['1X','12','X2'])}</div>
 <div class="rl" style="margin-top:10px">Obie drużyny strzelą</div><div class="o2">${tri(['btts:yes','btts:no'],['Tak','Nie'])}</div></div></details>`;
 for(const stat of Object.keys(x.exp)){
  let inner='';
  for(const sc of ['total','home','away']){
   const lines={};
   for(const m of x.m){const q=pid(m[0]);if(q&&q.stat===stat&&q.scope===sc)(lines[q.line]=lines[q.line]||{})[q.dir]=m}
   const ks=Object.keys(lines).map(Number).sort((a,b)=>a-b);if(!ks.length)continue;
   inner+=`<div class="sh">${sc==='total'?'Łącznie':esc(sc==='home'?x.h:x.a)}</div>`;
   for(const k of ks){const l=lines[k];
    inner+=`<div class="row"><div class="ln">${k}</div>${l.over?cell('Powyżej',l.over):'<div></div>'}${l.under?cell('Poniżej',l.under):'<div></div>'}</div>`}}
  const e=x.exp[stat];
  out+=`<details${stat==='goals'?' open':''}><summary>${ST[stat]}<span style="font-weight:400;color:var(--dim);font-size:13px;margin-left:auto">Σ ${(e[0]+e[1]).toFixed(1)}</span></summary><div class="in">${inner}</div></details>`}
 return out}
function cmpRow(l,a,b,d){
 const A=a==null?null:+a,B=b==null?null:+b,t=(A||0)+(B||0),pa=t>0?(A||0)/t*100:50;
 const f=v=>v==null?'–':(d===0?Math.round(v):v.toFixed(d));
 return `<div class="cp"><div class="cv${A!=null&&B!=null&&A>B?' hi':''}">${f(A)}</div><div class="cl2">${l}<div class="cb"><i style="width:${pa}%"></i></div></div><div class="cv r${A!=null&&B!=null&&B>A?' hi':''}">${f(B)}</div></div>`}
function cmpBlock(title,sub,rows){
 return `<div class="sc"><h4>${title}</h4>${sub?`<div class="cs">${sub}</div>`:''}${rows}</div>`}
function statsTab(x){
 const st=Object.keys(x.exp);
 const head=`<div class="cph"><span><i class="d1"></i>${esc(x.h)}</span><span>${esc(x.a)}<i class="d2"></i></span></div>`;
 const rows=fn=>st.map(k=>fn(k)).join('');
 const pv=(p,i)=>p&&p[i]!=null?p[i]:null;
 const nh=(x.ph.goals||[])[6],na=(x.pa.goals||[])[6];
 let h=head;
 h+=cmpBlock('Oczekiwane w meczu','Wynik modelu: ile każda drużyna ma średnio zdobyć w tym meczu.',
   rows(k=>cmpRow(ST[k],x.exp[k][0],x.exp[k][1],k==='goals'?2:1)));
 h+=cmpBlock('Forma: ostatnie 6 meczów','Średnio na mecz – zdobywa.',
   rows(k=>cmpRow(ST[k],pv(x.ph[k],0),pv(x.pa[k],0),1)));
 if(nh>0||na>0){
 h+=cmpBlock('Gospodarz u siebie vs gość na wyjeździe',`Średnia z meczów w tej roli (${esc(x.h)}: ${nh==null?'–':nh}, ${esc(x.a)}: ${na==null?'–':na}). Zdobywa:`,
   rows(k=>cmpRow(ST[k],pv(x.ph[k],4),pv(x.pa[k],4),1)));
 h+=cmpBlock('Tracone: u siebie vs na wyjeździe','Średnio na mecz – traci przeciwnikom (mniej = lepsza obrona).',
   rows(k=>cmpRow(ST[k],pv(x.ph[k],5),pv(x.pa[k],5),1)));
 }
 if((nh>0||na>0)&&((nh!=null&&nh<4)||(na!=null&&na<4)))h+='<div class="note">Uwaga: mało meczów w roli gospodarza/gościa – średnie są mało pewne.</div>';
 return h}
const RES={W:['W','fw'],D:['R','fd'],L:['P','fl']};
function formBlock(name,list){
 if(!list||!list.length)return`<div class="sc"><h4>${esc(name)}</h4><div class="cs">Brak danych o formie.</div></div>`;
 const chips=list.map(e=>{const r=RES[e[0]]||['?','fd'];return`<span class="fc ${r[1]}">${r[0]}</span>`}).join('');
 const rows=list.map(e=>{const r=RES[e[0]]||['?','fd'];if(e.length<8)return'';
  const d=e[5]?e[5].slice(8,10)+'.'+e[5].slice(5,7)+'.'+e[5].slice(2,4):'';
  return`<div class="fr"><span class="fc ${r[1]}">${r[0]}</span><div class="fo"><div class="ft${e[7]?' me':''}"><span>${esc(e[1])}</span><b>${esc(e[3])}</b></div><div class="ft${e[7]?'':' me'}"><span>${esc(e[2])}</span><b>${esc(e[4])}</b></div></div><div class="fd2">${esc(d)}<br>${esc(e[6])}</div></div>`}).join('');
 return`<div class="sc"><h4>${esc(name)}</h4><div class="fch">${chips}</div>${rows}</div>`}
function h2hTab(x){
 const f=x.fm||{};
 let out=`<div class="sh">Forma – ostatnie 5 meczów</div>`+formBlock(x.h,f.h)+formBlock(x.a,f.a)+`<div class="sh">Bezpośrednie spotkania (H2H)</div>`;
 if(!x.h2h.length)return out+'<div class="empty" style="padding:18px 10px">Brak bezpośrednich meczów w pobranych danych.</div>';
 return out+x.h2h.map(m=>{const s=m[3],p=k=>s[k]?`${s[k][0]}:${s[k][1]}`:'–';
  return `<div class="hh"><div class="s">${m[0]}</div><div><b>${esc(m[1])} ${p('goals')} ${esc(m[2])}</b></div>
  <div class="s">strzały ${p('shots')} · celne ${p('sot')} · rożne ${p('corners')} · faule ${p('fouls')} · kartki ${p('cards')}</div></div>`}).join('')}
const ROLEPL={bramkarz:'Bramkarz',obrona:'Obrońca',pomoc:'Pomocnik',atak:'Napastnik'};
function absTab(x){
 const blk=(name,list,adj)=>{
  const rows=list.map(e=>{const out=e[2].startsWith('nie zagra');
   const role=ROLEPL[e[1]]||'';
   return`<div class="ar"><span class="ai ${out?'ao1':'ao2'}">${out?'✕':'?'}</span><div class="an"><b>${esc(e[0])}</b><small>${[role,e[3]].filter(Boolean).map(esc).join(' · ')}</small></div><span class="tg ${out?'tg1':'tg2'}">${out?'Nie zagra':'Wątpliwy'}</span></div>`}).join('');
  const ef=[];if(Math.abs(adj[0])>=0.1)ef.push(`atak ${sgn(adj[0])}%`);if(adj[1]>=0.1)ef.push(`obrona: +${adj[1]}% traconych`);
  return`<div class="sc"><h4>${esc(name)}</h4>${rows||'<div class="ar ok"><span class="ai ao3">✓</span><div class="an"><b>Brak zgłoszonych braków</b></div></div>'}${ef.length?`<div class="ef">Wpływ na model: ${ef.join(' · ')}</div>`:''}</div>`};
 return blk(x.h,x.abs.h,x.adj.h)+blk(x.a,x.abs.a,x.adj.a)+
 '<div class="note">Źródło: zapowiedzi meczów (Flashscore), sprawdzane dwa razy dziennie. Brak wpisu nie oznacza, że wszyscy są zdrowi, a skład podany tuż przed meczem może wszystko zmienić.</div>'}
/* ---------- karta "Top typy": 2-3 najlepsze typy w każdej kategorii ---------- */
const TOPCAT=[['1x2','Wynik meczu',['1x2','dc']],['btts','Obie strzelą',['btts']],['goals','Gole',['goals']],['corners','Rożne',['corners']],['shots','Strzały',['shots']],['sot','Strzały celne',['sot']],['fouls','Faule',['fouls']],['cards','Kartki',['cards']],['offsides','Spalone',['offsides']]];
function topPicks(x,fams,n){const seen={},out=[];
 const c=x.m.filter(m=>fams.includes(m[1].split(':')[0])&&m[3]>=0.5&&m[3]<=0.93).sort((a,b)=>b[3]-a[3]);
 for(const m of c){const q=pid(m[0]),k=q?q.stat+q.scope+q.dir:m[0].split(':')[0]==='dc'?'dc':m[0];
  if(seen[k])continue;seen[k]=1;out.push(m);if(out.length>=n)break}
 return out}
function topTab(x){
 let h='<div class="note">Dla każdej kategorii: 2–3 najpewniejsze typy modelu (bez powtarzania tej samej linii i bez „oczywistych” powyżej 93%). EV = przewaga modelu nad kursem bukmachera.</div>';let any=false;
 for(const [k,name,fams] of TOPCAT){const L=topPicks(x,fams,3);if(!L.length)continue;any=true;
  h+=`<div class="sc"><h4>${name}</h4>`+L.map((m,j)=>{const o=m[4],v=m[5]!=null&&m[5]>=0.03;
   return `<div class="tp ${pcls(m[3])}"><div class="ti"><div class="tt">${j+1}. ${esc(lab(m,x))}</div></div><div class="tk"><b>${pc(m[3])}</b><span class="kr">${o?'kurs '+o.toFixed(2):'uczciwy ~'+fair(m[3])}</span>${v?`<em>EV ${sgn(Math.round(m[5]*100))}%</em>`:histTxt(m)}</div></div>`}).join('')+'</div>'}
 return any?h:h+'<div class="empty">Brak typów o szansie ≥50% w tym meczu.</div>'}
function detail(i){
 const x=D.matches[i];
 const body=S.dtab==='bets'?groups(x):S.dtab==='top'?topTab(x):S.dtab==='stats'?statsTab(x):S.dtab==='h2h'?h2hTab(x):absTab(x);
 const best=picksFor(x,S.minp).best.slice(0,4);
 const top=S.dtab==='bets'&&best.length?`<div class="top3"><h4>★ Najpewniejsze typy modelu</h4>${best.map(m=>`<div class="tp ${pcls(m[3])}"><div class="ti"><div class="tt">${esc(lab(m,x))}</div></div><div class="tk"><b>${pc(m[3])}</b><span class="kr">${m[4]?'kurs '+m[4].toFixed(2):'brak kursu'}</span>${histTxt(m)}</div></div>`).join('')}</div>`:'';
 const tabs=[['bets','Typy'],['top','Top typy'],['stats','Statystyki'],['h2h','Forma i H2H'],['abs','Kadra'+(x.na_?' ('+x.na_+')':'')]];
 $('det').innerHTML=`<div class="dh"><button class="back" data-back="1">← Wróć</button>
 <div class="dt"><div class="mt"><span>${esc(x.country)} · ${esc(x.comp)}</span><span>${dfull(x.date)} ${x.time}</span></div>
 <div class="tm">${esc(x.h)} – ${esc(x.a)}</div><div>${badges(x)}</div></div>
 <div class="sub">${tabs.map(([k,n])=>`<button class="${S.dtab===k?'on':''}" data-dtab="${k}">${n}</button>`).join('')}</div></div>
 <div class="dc">${top}${body}<div class="note">Mecze w modelu: ${esc(x.h)} ${x.nh}, ${esc(x.a)} ${x.na}. „~” / „fair” = uczciwy kurs (1/prawdopodobieństwo). Model uwzględnia osobno formę u siebie i na wyjeździe.</div></div>`;
 $('det').classList.remove('hide');document.body.style.overflow='hidden'}
function route(){
 const m=location.hash.match(/^#m(\d+)$/);
 if(m&&D.matches[+m[1]])detail(+m[1]);
 else{$('det').classList.add('hide');document.body.style.overflow='';render();window.scrollTo(0,S.scroll)}}
document.addEventListener('click',e=>{
 const t=e.target.closest('[data-share],[data-day],[data-lg],[data-tab],[data-minp],[data-per],[data-cat],[data-cn],[data-cm],[data-co],[data-rm],[data-rr],[data-ro],[data-rn],[data-coll],[data-m],[data-back],[data-dtab]');if(!t)return;
 const d=t.dataset;
 if(d.share!==undefined){shareReport()}
 else if(d.day!==undefined){S.day=d.day;render()}
 else if(d.lg!==undefined){S.league=d.lg;render()}
 else if(d.tab!==undefined){S.tab=d.tab;render();window.scrollTo(0,0)}
 else if(d.minp!==undefined){S.minp=parseFloat(d.minp);render()}
 else if(d.cat!==undefined){S.cat=d.cat;render()}
 else if(d.cn!==undefined){S.cn=parseInt(d.cn);render()}
 else if(d.cm!==undefined){S.cm=d.cm;render()}
 else if(d.co!==undefined){S.co=+d.co;render()}
 else if(d.rm!==undefined){S.rm=d.rm;render()}
 else if(d.rr!==undefined){S.rr=d.rr;render()}
 else if(d.ro!==undefined){S.ro=+d.ro;render()}
 else if(d.rn!==undefined){S.rn=parseInt(d.rn);render()}
 else if(d.per!==undefined){S.per=parseInt(d.per);render()}
 else if(d.coll!==undefined){S.coll[d.coll]=!S.coll[d.coll];render()}
 else if(d.dtab!==undefined){S.dtab=d.dtab;const m=location.hash.match(/^#m(\d+)$/);if(m){detail(+m[1]);$('det').scrollTop=0}}
 else if(d.back!==undefined){history.length>1?history.back():(location.hash='')}
 else if(d.m!==undefined){S.scroll=window.scrollY;S.dtab='bets';location.hash='#m'+d.m;$('det').scrollTop=0}
});
window.addEventListener('hashchange',route);
$('gen').textContent=D.generated;
route();
"""


def build_report(analyses, min_p, max_p, top=None):
    bt = jload(P("backtest.json"), None)
    ords = {c: i for i, c in enumerate(COMP_ORDER)}
    data = dict(generated=dt.datetime.now().strftime("%d.%m %H:%M"), today=dt.date.today().isoformat(),
                minp=min_p, maxp=max_p, ord=ords, bt=bt,
                matches=[match_payload(i, an) for i, an in enumerate(analyses)])
    js = APP_JS.replace("__DATA__", json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/"))
    return ("<!doctype html><html lang='pl'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width,initial-scale=1,viewport-fit=cover'>"
            "<meta name='color-scheme' content='dark'><title>Typy</title>"
            f"<style>{APP_CSS}</style></head><body>"
            "<div class='top'><div class='hd'><b>⚽ Typy</b><span>Aktualizacja: <span id='gen'></span><button class='shr' data-share='1'>↗ Udostępnij</button></span></div>"
            "<div class='tabs' id='tb'></div><div class='strip' id='dy'></div></div><div class='strip' id='lc'></div><main id='main'></main>"
            "<div class='note' style='padding:0 16px 30px'>Prawdopodobieństwa to wynik modelu statystycznego "
            "(Poisson / ujemny dwumianowy, z wagą świeżości meczów, osobno formą u siebie i na wyjeździe), "
            "nie gwarancja. EV = p × kurs − 1. Kursy bukmacherów pochodzą z zewnętrznych źródeł i mogą się różnić "
            "od Twojego bukmachera. Graj odpowiedzialnie.</div>"
            f"<div id='det' class='det hide'></div><script>{js}</script></body></html>")


# --------------------------------------------------------------------------------------
# Konsola / serwer / CLI
# --------------------------------------------------------------------------------------
def find_team(name, teams):
    n = name.lower()
    for t in teams:
        if t.lower() == n:
            return t
    c = sorted([t for t in teams if n in t.lower() or n in norm_name(t)], key=len)
    return c[0] if c else None


def label_py(m, h, a):
    if m["label"]:
        return m["label"]
    s, sc, d, line = m["id"].split(":")
    pol = "powyżej" if d == "over" else "poniżej"
    if sc == "total":
        return f"{NAMES[s]} łącznie – {pol} {line}"
    return f"{h if sc == 'home' else a}: {NAMES[s].lower()} {pol} {line}"


def cmd_match(hname, aname, manual_odds, show_all):
    dom_played, fd_fix = load_domestic()
    euro_played, espn_fix = load_euro()
    euro_teams = {t for m in euro_played for t in (m["home"], m["away"])}
    dom_models, euro_model = build_models(dom_played, euro_played, euro_teams)
    api_cache, manual = jload(P("api_cache.json"), {}), manual_absences()
    models = list(dom_models.items()) + [("Puchary europejskie", euro_model)]
    for comp, model in models:
        h, a = find_team(hname, model.teams), find_team(aname, model.teams)
        if not (h and a):
            continue
        odds = {}
        for fx in fd_fix:
            if fx["home"] == h and fx["away"] == a:
                odds = dict(fx["odds"])
        odds.update(manual_odds)
        fx = dict(comp=comp, date=dt.date.today(), time="", home=h, away=a, odds=odds)
        an = analyze_fixture(fx, model, api_cache, manual)
        if not an:
            continue
        print(f"\n=== {h} – {a}  ({comp}) ===  mecze w modelu: {an['n_h']}/{an['n_a']}"
              + ("  [MAŁA PRÓBA]" if low_conf(an) else ""))
        print(f"{'Statystyka':<15}{h[:14]:>15}{a[:14]:>15}{'Razem':>9}")
        for stat, (lh, la) in an["exp"].items():
            print(f"{NAMES[stat]:<15}{lh:>15.2f}{la:>15.2f}{lh + la:>9.2f}")
        for side, nm in (("h", h), ("a", a)):
            for e in an["abs"][side]:
                print(f"  brak: {nm} – {e['n']} ({e['role']}, {e['st']})")
        print("\nOstatnie H2H:")
        for m in an["h2h"]:
            g = m["stats"]["goals"]
            print(f"  {m['date']:%d.%m.%y} {m['home']} {g[0]:.0f}:{g[1]:.0f} {m['away']}")
        print(f"\n{'ID rynku':<30}{'Typ':<46}{'P':>5}{'Fair':>7}{'Kurs':>7}{'EV':>7}")
        for m in an["markets"]:
            if not show_all and (m["family"] == "dc" or not 0.30 <= m["p"] <= 0.90):
                continue
            ev = f"{m['ev'] * 100:+.0f}%" if m["ev"] is not None else ""
            print(f"{m['id']:<30}{label_py(m, h, a)[:45]:<46}{m['p'] * 100:>4.0f}%{m['fair']:>7.2f}"
                  f"{(f'{m['odds']:.2f}' if m['odds'] else ''):>7}{ev:>7}")
        return
    print("Nie znaleziono pary drużyn. Uruchom najpierw: python futbol.py update")


def maybe_backtest(args, force=False):
    bt = jload(P("backtest.json"), None)
    stale = (not bt) or "roi" not in bt or (dt.date.today() - dt.date.fromisoformat(bt["generated"])).days >= 7
    if force or (stale and not getattr(args, "no_backtest", False)):
        log("Liczę historyczną skuteczność typów (backtest) – jednorazowo, potem co tydzień...")
        dom_played, _ = load_domestic()
        res = run_backtest(dom_played, getattr(args, "bt_matches", 150))
        log(f"Backtest: {res['matches']} meczów.")


def make_report(args):
    analyses = build_analyses(args.days)
    if analyses is None:
        log("Brak danych. Uruchom: python futbol.py update")
        return False
    open(REPORT_PATH, "w", encoding="utf-8").write(build_report(analyses, args.min_prob, args.max_prob))
    by = defaultdict(int)
    for an in analyses:
        by[an["comp"]] += 1
    log(f"Raport zapisany: {REPORT_PATH} – {len(analyses)} meczów ("
        + ", ".join(f"{k}: {v}" for k, v in sorted(by.items(), key=lambda kv: COMP_ORDER.index(kv[0])
                                                    if kv[0] in COMP_ORDER else 99)) + ")")
    if not analyses:
        log("Uwaga: brak nadchodzących meczów w terminarzu (sprawdź połączenie lub zwiększ --days).")
    return True


def do_update(args):
    update_all(args.seasons, args.days, args.espn_budget, args.inj_budget)


def lan_ip():
    import socket
    sk = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        sk.connect(("10.255.255.255", 1))
        return sk.getsockname()[0]
    except OSError:
        return None
    finally:
        sk.close()


def start_tunnel(port):
    """Publiczny link przez cloudflared (opcjonalnie: pkg install cloudflared)."""
    import shutil
    import threading
    exe = shutil.which("cloudflared")
    if not exe:
        log("Brak programu cloudflared. Zainstaluj: pkg install cloudflared (i uruchom ponownie z --tunnel).")
        return None
    pr = subprocess.Popen([exe, "tunnel", "--url", f"http://127.0.0.1:{port}", "--no-autoupdate"],
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

    def reader():
        for line in pr.stdout:
            m = re.search(r"https://[a-z0-9-]+\.trycloudflare\.com", line)
            if m:
                log(f"\n🌍 PUBLICZNY LINK (działa dopóki program jest włączony): {m.group(0)}")
    threading.Thread(target=reader, daemon=True).start()
    return pr


def cmd_export(args):
    """Zapisuje raport jako jeden samodzielny plik HTML do wysłania znajomym."""
    import shutil
    if not make_report(args):
        return
    name = f"typy_{dt.datetime.now():%Y-%m-%d_%H%M}.html"
    dest_dir = os.path.expanduser("~/storage/downloads")
    if not os.path.isdir(dest_dir):
        dest_dir = HERE
    dest = os.path.join(dest_dir, name)
    try:
        shutil.copyfile(REPORT_PATH, dest)
        log(f"Zapisano: {dest}")
    except OSError as e:
        log(f"Nie udało się zapisać w {dest_dir}: {e}")
        dest = REPORT_PATH
    try:
        subprocess.Popen(["termux-open", "--send", dest], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        log("Otwieram okno udostępniania (wybierz WhatsApp, Messenger, e-mail itd.).")
    except OSError:
        log("Wyślij ten plik znajomym ręcznie – otworzą go w przeglądarce, nawet bez internetu.")


def cmd_serve(args):
    """Buduje raport i serwuje go lokalnie (działa m.in. w Termux na telefonie)."""
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

    if not args.no_update:
        do_update(args)
    maybe_backtest(args)
    if not make_report(args):
        return

    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def do_GET(self):
            if self.path.split("?")[0] in ("/", "/raport.html", "/index.html"):
                body = open(REPORT_PATH, "rb").read()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(body)
            else:
                self.send_error(404)

        def log_message(self, *a):
            pass

    class Server(ThreadingHTTPServer):
        allow_reuse_address = True

        def handle_error(self, request, client_address):
            pass

    port = args.port
    srv = None
    for p in range(port, port + 10):
        try:
            srv = Server(("0.0.0.0" if (args.share or args.tunnel) else "127.0.0.1", p), Handler)
            port = p
            break
        except OSError:
            continue
    if srv is None:
        log("Nie mogę uruchomić serwera (porty zajęte). Zamknij stare sesje Termux: pkill -f futbol.py")
        return
    url = f"http://127.0.0.1:{port}/"
    log(f"\nRaport działa pod adresem: {url}\nZatrzymanie: CTRL + C")
    if args.share:
        ip = lan_ip()
        if ip:
            log(f"📶 Dla osób w tej samej sieci Wi-Fi: http://{ip}:{port}/")
        else:
            log("Nie udało się ustalić adresu IP w sieci Wi-Fi.")
    tunnel = start_tunnel(port) if args.tunnel else None
    try:
        subprocess.Popen(["termux-open-url", url], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except OSError:
        pass
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        if tunnel:
            tunnel.terminate()


def main():
    global DATA_DIR, REPORT_PATH
    ap = argparse.ArgumentParser(description="Analizator typów piłkarskich")
    ap.add_argument("--data", help="katalog z danymi (domyślnie ./dane)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--days", type=int, default=7, help="ile dni do przodu (domyślnie 7)")
        p.add_argument("--min-prob", type=float, default=0.60)
        p.add_argument("--max-prob", type=float, default=0.85, help="odrzuć „oczywiste” typy powyżej tej szansy")
        p.add_argument("--seasons", type=int, default=3, help="ile sezonów historii (domyślnie 3)")
        p.add_argument("--espn-budget", type=int, default=250, help="limit zapytań ESPN o statystyki na sesję")
        p.add_argument("--inj-budget", type=int, default=60, help="limit zapytań API-Football na sesję")
        p.add_argument("--no-backtest", action="store_true")
        p.add_argument("--bt-matches", type=int, default=150)
        p.add_argument("--open", action="store_true", help="otwórz raport w przeglądarce")
    for name in ("update", "report", "run"):
        common(sub.add_parser(name))
    sv = sub.add_parser("serve"); common(sv)
    sv.add_argument("--port", type=int, default=8000)
    sv.add_argument("--no-update", action="store_true", help="pomiń pobieranie danych")
    sv.add_argument("--share", action="store_true", help="udostępnij w sieci Wi-Fi (inne urządzenia)")
    sv.add_argument("--tunnel", action="store_true", help="publiczny link (wymaga cloudflared)")
    common(sub.add_parser("eksport"))
    w = sub.add_parser("watch"); common(w)
    w.add_argument("--every", type=int, default=180, help="co ile minut odświeżać")
    bt = sub.add_parser("backtest")
    bt.add_argument("--bt-matches", type=int, default=150, help="ile ostatnich meczów na ligę")
    m = sub.add_parser("match")
    m.add_argument("home"); m.add_argument("away")
    m.add_argument("--odds", action="append", default=[], help='np. "corners:total:over:9.5=1.85"')
    m.add_argument("--all", action="store_true")
    b = sub.add_parser("brak", help="ręczne braki kadrowe")
    b.add_argument("akcja", choices=["dodaj", "lista", "usun"])
    b.add_argument("druzyna", nargs="?"); b.add_argument("gracz", nargs="?"); b.add_argument("rola", nargs="?")
    b.add_argument("--waga", type=float, default=1.0, help="1 = kluczowy zawodnik, 0.5 = rezerwowy")
    args = ap.parse_args()
    if args.data:
        DATA_DIR = os.path.abspath(args.data)
        REPORT_PATH = os.path.join(DATA_DIR, "raport.html")

    if args.cmd == "update":
        do_update(args)
    elif args.cmd == "report":
        if make_report(args) and args.open:
            webbrowser.open("file://" + REPORT_PATH)
    elif args.cmd == "run":
        do_update(args)
        maybe_backtest(args)
        if make_report(args) and args.open:
            webbrowser.open("file://" + REPORT_PATH)
    elif args.cmd == "serve":
        cmd_serve(args)
    elif args.cmd == "eksport":
        cmd_export(args)
    elif args.cmd == "watch":
        first = True
        while True:
            do_update(args)
            maybe_backtest(args)
            if make_report(args) and args.open and first:
                webbrowser.open("file://" + REPORT_PATH)
            first = False
            log(f"Następne odświeżenie za {args.every} min (Ctrl+C aby zakończyć)")
            time.sleep(args.every * 60)
    elif args.cmd == "backtest":
        maybe_backtest(args, force=True)
    elif args.cmd == "brak":
        cmd_brak(args)
    elif args.cmd == "match":
        odds = {}
        for o in args.odds:
            k, _, v = o.rpartition("=")
            if num(v):
                odds[k.strip()] = float(v)
        cmd_match(args.home, args.away, odds, args.all)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nPrzerwano.")
