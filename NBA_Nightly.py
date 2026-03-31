#!/usr/bin/env python3

import argparse
import hashlib
import http.cookiejar
import json
import os
import re
import time
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from typing import Dict, Iterable, List, Optional
from urllib.error import HTTPError, URLError
from zoneinfo import ZoneInfo


USER_AGENT = "Codex NBA Final Wikidata Updater/0.1"
TIMEZONE = "America/New_York"
SCHEDULE_URL = "https://cdn.nba.com/static/json/staticData/scheduleLeagueV2.json"
BOXSCORE_URL_TEMPLATE = "https://cdn.nba.com/static/json/liveData/boxscore/boxscore_{game_id}.json"
GAME_PAGE_NUMERIC_BOXSCORE_URL_TEMPLATE = "https://www.nba.com/game/{game_id}/box-score"
WIKIDATA_API_URL = "https://www.wikidata.org/w/api.php"
SPARQL_URL = "https://query.wikidata.org/sparql"

DEFAULT_GAME_ID_PREFIXES = "001,002,003,004,006"
SUPPORTED_GAME_ID_PREFIXES = ("001", "002", "003", "004", "006")
DEFAULT_START_HOUR = 11
DEFAULT_OVERNIGHT_END_HOUR = 5

STATE_DIR = os.path.join(".cache", "nba_final_wikidata")
LOOKUP_CACHE_DIR = os.path.join(STATE_DIR, "lookups")
SESSION_DIR = os.path.join(STATE_DIR, "session")
PLAYER_QID_CACHE_PATH = os.path.join(LOOKUP_CACHE_DIR, "player_qids.json")
BROADCASTER_QID_CACHE_PATH = os.path.join(LOOKUP_CACHE_DIR, "broadcaster_qids.json")
SESSION_COOKIE_PATH = os.path.join(SESSION_DIR, "wikidata_cookies.lwp")

NBA_LEAGUE_QID = "Q155223"
BASKETBALL_GAME_QID = "Q18431960"
HOME_TEAM_ROLE_QID = "Q24633211"
AWAY_TEAM_ROLE_QID = "Q24633216"
HTTPS_QID = "Q44484"
PRESEASON_QID = "Q2108803"
REGULAR_SEASON_QID = "Q10509145"
PLAYOFFS_QID = "Q868291"
NBA_CUP_QID = "Q120491297"
ALL_STAR_GAME_QID = "Q137341"
STARTING_LINEUP_QID = "Q203949"
MINUTE_UNIT_QID = "Q7727"
CALENDAR_MODEL_QID = "Q1985727"

WIKIDATA_TRANSIENT_API_CODES = {"maxlag", "ratelimited", "readonly"}
MAX_FETCH_ATTEMPTS = 4
SPARQL_MAX_ATTEMPTS = 5
WIKIDATA_POST_MAX_ATTEMPTS = 8
WIKIDATA_LOGIN_MAX_ATTEMPTS = 3
BROADCASTER_LOOKUP_MAX_ATTEMPTS = 1

TEAM_LABEL_ALIASES = {
    "LAC": "Los Angeles Clippers",
}
POSITION_QIDS = {
    "G": "Q2066131",
    "F": "Q3665646",
    "C": "Q193592",
    "G-F": "Q2066131",
    "F-G": "Q3665646",
    "F-C": "Q3665646",
    "C-F": "Q193592",
}
BROADCASTER_NAME_ALIASES = {
    "ESPNR": "ESPN Radio",
    "MSG": "MSG Network",
    "NBCSB": "NBC Sports Boston",
    "NBCSBA": "NBC Sports Bay Area",
    "NBCSCA": "NBC Sports California",
    "NBCSP": "NBC Sports Philadelphia",
    "SN": "Sportsnet",
    "SN1": "Sportsnet",
    "SNN": "Sportsnet",
    "SNN/SN1": "Sportsnet",
    "Sportsnet 590": "Sportsnet 590 The FAN",
    "TSN": "The Sports Network",
    "TSN1": "The Sports Network",
    "TSN1/3/4": "The Sports Network",
    "TSN1/4/5": "The Sports Network",
    "TSN1/4/5 (Raptors)": "The Sports Network",
    "TSN3": "The Sports Network",
    "TSN3/4": "The Sports Network",
    "TSN4/5": "The Sports Network",
    "YES": "YES Network",
}
BROADCASTER_DESCRIPTION_KEYWORDS = (
    "broadcast",
    "broadcasting",
    "channel",
    "network",
    "radio",
    "service",
    "sports",
    "station",
    "streaming",
    "television",
)

NBA_HTTP_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/123.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json,text/plain,*/*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://www.nba.com/",
    "Origin": "https://www.nba.com",
    "Connection": "keep-alive",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache",
}

WIKIDATA_TEAM_QUERY = """
SELECT ?team ?teamLabel WHERE {
  ?team wdt:P31 wd:Q13393265;
        wdt:P118 wd:Q155223.
  FILTER NOT EXISTS { ?team wdt:P576 ?ended }
  SERVICE wikibase:label { bd:serviceParam wikibase:language "en". }
}
ORDER BY ?teamLabel
""".strip()

VERBOSE = False


def log_progress(message: str) -> None:
    if not VERBOSE:
        return
    timestamp = datetime.now().strftime("%H:%M:%S")
    print(f"[{timestamp}] {message}", flush=True)


def log_event(message: str) -> None:
    print(message, flush=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Update Wikidata for completed NBA games only. Intended for hourly GitHub Actions runs."
    )
    parser.add_argument("--date", default="", help="Explicit local game date in YYYY-MM-DD.")
    parser.add_argument("--game-id", action="append", default=[], help="Specific NBA game ID(s) to restrict updates to.")
    parser.add_argument(
        "--game-id-prefixes",
        default=DEFAULT_GAME_ID_PREFIXES,
        help=f"Comma-separated game ID prefixes to consider. Defaults to {DEFAULT_GAME_ID_PREFIXES}.",
    )
    parser.add_argument("--start-hour", type=int, default=DEFAULT_START_HOUR)
    parser.add_argument("--overnight-end-hour", type=int, default=DEFAULT_OVERNIGHT_END_HOUR)
    parser.add_argument(
        "--ignore-window",
        action="store_true",
        help="Run even outside the normal nightly America/New_York update window.",
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    return parser.parse_args()


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def load_lookup_cache(path: str) -> Dict[str, str]:
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        return {}
    return {
        str(key): str(value)
        for key, value in payload.items()
        if str(key).strip()
    }


def save_lookup_cache(path: str, payload: Dict[str, str]) -> None:
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)


def validate_iso_date(value: str) -> None:
    datetime.strptime(value, "%Y-%m-%d")


def normalize_game_id_prefixes(values: Iterable[str]) -> List[str]:
    prefixes: List[str] = []
    for value in values:
        for token in str(value or "").split(","):
            prefix = token.strip()
            if not prefix:
                continue
            if prefix not in SUPPORTED_GAME_ID_PREFIXES:
                raise SystemExit(
                    f"Unsupported game ID prefix: {prefix}. Supported values are: {', '.join(SUPPORTED_GAME_ID_PREFIXES)}."
                )
            if prefix not in prefixes:
                prefixes.append(prefix)
    return prefixes or list(SUPPORTED_GAME_ID_PREFIXES)


def build_request_headers(url: str) -> Dict[str, str]:
    if "nba.com" in url:
        return dict(NBA_HTTP_HEADERS)
    return {"User-Agent": USER_AGENT}


def fetch_json(url: str, timeout: float = 20.0) -> dict:
    last_error: Optional[Exception] = None
    for attempt in range(1, MAX_FETCH_ATTEMPTS + 1):
        request = urllib.request.Request(url, headers=build_request_headers(url))
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return json.load(response)
        except (HTTPError, TimeoutError, URLError, OSError) as exc:
            last_error = exc
            if attempt == MAX_FETCH_ATTEMPTS:
                raise
            if VERBOSE:
                log_progress(
                    f"Retrying fetch after {type(exc).__name__} from {url} "
                    f"(attempt {attempt + 1}/{MAX_FETCH_ATTEMPTS})"
                )
            time.sleep(min(8.0, 1.5 * attempt))
    if last_error:
        raise last_error
    raise RuntimeError(f"Could not fetch JSON from {url}")


def run_sparql(query: str) -> dict:
    params = urllib.parse.urlencode({"format": "json", "query": query})
    url = f"{SPARQL_URL}?{params}"
    last_error: Optional[Exception] = None
    for attempt in range(1, SPARQL_MAX_ATTEMPTS + 1):
        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "application/sparql-results+json,application/json;q=0.9,*/*;q=0.8",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=30.0) as response:
                return json.load(response)
        except (HTTPError, TimeoutError, URLError, OSError) as exc:
            last_error = exc
            if attempt == SPARQL_MAX_ATTEMPTS:
                raise
            if VERBOSE:
                log_progress(
                    f"Retrying SPARQL query after {type(exc).__name__} "
                    f"(attempt {attempt + 1}/{SPARQL_MAX_ATTEMPTS})"
                )
            time.sleep(min(20.0, 2.0 * attempt))
    if last_error:
        raise last_error
    raise RuntimeError("Could not complete SPARQL query.")


def utc_timestamp() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def item_value(qid: str) -> dict:
    return {"entity-type": "item", "id": qid, "numeric-id": int(qid[1:])}


def quantity_value(amount: str, unit_qid: Optional[str] = None) -> dict:
    return {
        "amount": amount,
        "unit": "1" if not unit_qid else f"http://www.wikidata.org/entity/{unit_qid}",
    }


def time_value(date_string: str) -> dict:
    return {
        "time": f"+{date_string}T00:00:00Z",
        "timezone": 0,
        "before": 0,
        "after": 0,
        "precision": 11,
        "calendarmodel": f"http://www.wikidata.org/entity/{CALENDAR_MODEL_QID}",
    }


def make_snak(prop: str, datatype: str, value: object) -> dict:
    if datatype == "wikibase-item":
        datavalue = {"value": item_value(str(value)), "type": "wikibase-entityid"}
    elif datatype == "quantity":
        datavalue = {"value": value, "type": "quantity"}
    elif datatype == "time":
        datavalue = {"value": value, "type": "time"}
    else:
        datavalue = {"value": value, "type": "string"}
    return {
        "snaktype": "value",
        "property": prop,
        "datatype": datatype,
        "datavalue": datavalue,
    }


def append_claim(entity: dict, prop: str, claim: dict) -> None:
    entity.setdefault("claims", {}).setdefault(prop, []).append(claim)


def append_qualifier_to_claim(claim: dict, prop: str, snak: dict) -> None:
    claim.setdefault("qualifiers", {}).setdefault(prop, []).append(snak)
    qualifiers_order = claim.setdefault("qualifiers-order", [])
    if prop not in qualifiers_order:
        qualifiers_order.append(prop)


def append_reference_to_claim(claim: dict, reference: dict) -> None:
    claim.setdefault("references", []).append(reference)


def remove_qualifier_hashes_from_claim(claim: dict, prop: str, hashes: Iterable[str]) -> None:
    target_hashes = set(hashes)
    if not target_hashes:
        return
    filtered = [snak for snak in claim.get("qualifiers", {}).get(prop, []) if snak.get("hash") not in target_hashes]
    if filtered:
        claim.setdefault("qualifiers", {})[prop] = filtered
    elif prop in claim.get("qualifiers", {}):
        del claim["qualifiers"][prop]
    if prop not in claim.get("qualifiers", {}):
        claim["qualifiers-order"] = [pid for pid in claim.get("qualifiers-order", []) if pid != prop]


def build_entity_edit_data(entity: dict) -> dict:
    data: Dict[str, object] = {}
    if entity.get("descriptions"):
        data["descriptions"] = entity["descriptions"]
    claims: List[dict] = []
    for prop_claims in entity.get("claims", {}).values():
        claims.extend(prop_claims)
    if claims:
        data["claims"] = claims
    return data


def serialize_entity_edit_data(data: dict) -> str:
    return json.dumps(data, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def parse_amount_to_int(value: str) -> int:
    text = str(value or "").strip()
    if not text:
        return 0
    return int(float(text.lstrip("+")))


def fetch_entity(qid: str) -> dict:
    url = f"https://www.wikidata.org/wiki/Special:EntityData/{qid}.json"
    return fetch_json(url, timeout=20.0)["entities"][qid]


def fetch_entity_search(search: str, limit: int = 10) -> List[dict]:
    params = urllib.parse.urlencode(
        {
            "action": "wbsearchentities",
            "format": "json",
            "language": "en",
            "type": "item",
            "search": search,
            "limit": limit,
        }
    )
    url = f"{WIKIDATA_API_URL}?{params}"
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=20.0) as response:
        return json.load(response).get("search", [])


def find_matching_claim(entity: dict, prop: str, value: str) -> Optional[dict]:
    for claim in entity.get("claims", {}).get(prop, []):
        mainsnak = claim.get("mainsnak", {})
        datatype = mainsnak.get("datatype")
        datavalue = mainsnak.get("datavalue", {}).get("value")
        if datatype == "wikibase-item" and isinstance(datavalue, dict) and datavalue.get("id") == value:
            return claim
        if datatype == "time" and isinstance(datavalue, dict) and datavalue.get("time") == value:
            return claim
        if datatype == "quantity" and isinstance(datavalue, dict) and datavalue.get("amount") == value:
            return claim
        if datatype == "url" and datavalue == value:
            return claim
    return None


def find_team_claim(entity: dict, team_qid: str) -> Optional[dict]:
    return find_matching_claim(entity, "P1923", team_qid)


def extract_item_id_from_snak(snak: dict) -> str:
    return snak.get("datavalue", {}).get("value", {}).get("id", "")


def extract_quantity_amount_from_snak(snak: dict) -> str:
    return snak.get("datavalue", {}).get("value", {}).get("amount", "")


def string_qualifier_values(claim: dict, prop: str) -> List[str]:
    values: List[str] = []
    for snak in claim.get("qualifiers", {}).get(prop, []):
        datavalue = snak.get("datavalue", {}).get("value")
        if isinstance(datavalue, str):
            values.append(datavalue)
    return values


def qualifier_hashes(claim: dict, prop: str) -> List[str]:
    return [snak.get("hash", "") for snak in claim.get("qualifiers", {}).get(prop, []) if snak.get("hash")]


def find_reference_by_url(claim: dict, reference_url: str) -> Optional[dict]:
    for reference in claim.get("references", []):
        for snak in reference.get("snaks", {}).get("P854", []):
            if snak.get("datavalue", {}).get("value") == reference_url:
                return reference
    return None


class WikidataApiSession:
    def __init__(self, dry_run: bool):
        self.dry_run = dry_run
        ensure_dir(SESSION_DIR)
        self.cookie_jar = http.cookiejar.LWPCookieJar(SESSION_COOKIE_PATH)
        self.opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(self.cookie_jar))
        self.csrf_token = ""

    def _request(self, params: dict, post: bool) -> dict:
        encoded = urllib.parse.urlencode(params, doseq=True).encode("utf-8") if post else None
        url = WIKIDATA_API_URL if post else f"{WIKIDATA_API_URL}?{urllib.parse.urlencode(params, doseq=True)}"
        request = urllib.request.Request(url, data=encoded, headers={"User-Agent": USER_AGENT})
        with self.opener.open(request, timeout=30.0) as response:
            return json.load(response)

    def api_get(self, **params: object) -> dict:
        return self._request({"format": "json", "formatversion": "2", **params}, post=False)

    def api_post(self, max_attempts: int = WIKIDATA_POST_MAX_ATTEMPTS, **params: object) -> dict:
        payload = {"format": "json", "formatversion": "2", "maxlag": "5", **params}
        last_error: Optional[Exception] = None
        for attempt in range(1, max_attempts + 1):
            try:
                response = self._request(payload, post=True)
            except (HTTPError, TimeoutError, URLError, OSError) as exc:
                last_error = exc
                if attempt == max_attempts:
                    raise
                time.sleep(min(30.0, attempt * 3.0))
                continue
            error = response.get("error")
            if not error:
                return response
            code = error.get("code", "")
            if code not in WIKIDATA_TRANSIENT_API_CODES or attempt == max_attempts:
                raise RuntimeError(
                    f"Wikidata API error {code}: {error.get('info', '')} :: {json.dumps(error, sort_keys=True)}"
                )
            wait_seconds = min(60.0, attempt * 5.0)
            if code == "maxlag":
                try:
                    wait_seconds = max(wait_seconds, float(error.get("lag", 0.0)) * 2.0)
                except (TypeError, ValueError):
                    pass
            if VERBOSE:
                log_progress(
                    f"Wikidata API {code}; retrying in {wait_seconds:.0f}s "
                    f"(attempt {attempt}/{max_attempts})."
                )
            time.sleep(wait_seconds)
        if last_error:
            raise last_error
        raise RuntimeError("Unexpected empty MediaWiki API response")

    def login_from_env(self) -> None:
        if self.dry_run:
            return
        username = (
            os.environ.get("WIKIDATA_USERNAME")
            or os.environ.get("WIKIDATA_USER")
            or ""
        ).strip()
        password = (
            os.environ.get("WIKIDATA_PASSWORD")
            or os.environ.get("WIKIDATA_BOT_PASSWORD")
            or ""
        ).strip()
        if not username or not password:
            raise SystemExit(
                "Set WIKIDATA_USERNAME and WIKIDATA_PASSWORD (or WIKIDATA_BOT_PASSWORD) in the environment."
            )
        login_token = self.api_get(action="query", meta="tokens", type="login")["query"]["tokens"]["logintoken"]
        response = self.api_post(
            action="login",
            lgname=username,
            lgpassword=password,
            lgtoken=login_token,
            max_attempts=WIKIDATA_LOGIN_MAX_ATTEMPTS,
        )
        if response.get("login", {}).get("result") != "Success":
            raise SystemExit(f"Wikidata login failed: {response}")
        self.csrf_token = self.api_get(action="query", meta="tokens", type="csrf")["query"]["tokens"]["csrftoken"]

    def write(self, action: str, summary: str, **params: object) -> dict:
        if self.dry_run:
            if VERBOSE:
                log_progress(f"DRY RUN {action}: {summary}")
            return {}
        if not self.csrf_token:
            raise RuntimeError("Cannot write to Wikidata before login")
        return self.api_post(action=action, token=self.csrf_token, bot="1", summary=summary, **params)

    def edit_entity(self, qid: str, data: dict, summary: str, baserevid: Optional[int] = None) -> dict:
        params: Dict[str, object] = {"id": qid, "data": serialize_entity_edit_data(data)}
        if baserevid is not None:
            params["baserevid"] = str(baserevid)
        return self.write("wbeditentity", summary, **params)


def canonicalize_broadcaster_name(value: str) -> str:
    broadcaster_name = str(value or "").strip()
    if not broadcaster_name:
        return ""
    if broadcaster_name in BROADCASTER_NAME_ALIASES:
        return BROADCASTER_NAME_ALIASES[broadcaster_name]
    normalized_name = normalize_lookup_key(broadcaster_name)
    for alias_name, canonical_name in BROADCASTER_NAME_ALIASES.items():
        if normalize_lookup_key(alias_name) == normalized_name:
            return canonical_name
    return broadcaster_name


def normalize_lookup_key(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", str(value or "").lower())


def normalize_broadcaster_scope(value: str) -> str:
    scope = str(value or "").strip().lower()
    if scope in {"home", "away", "natl", "can"}:
        return scope
    if scope == "national":
        return "natl"
    return scope


def normalize_broadcaster_medium(value: str) -> str:
    medium = str(value or "").strip().lower()
    if medium in {"tv", "radio"}:
        return medium
    if medium in {"ott", "stream", "streaming", "nss"}:
        return "stream"
    return medium


def extract_game_page_broadcasters(page_broadcasters: dict) -> List[dict]:
    broadcasters: List[dict] = []
    if not isinstance(page_broadcasters, dict):
        return broadcasters
    for bucket_name, bucket_entries in page_broadcasters.items():
        if not isinstance(bucket_entries, list):
            continue
        bucket_name_lower = bucket_name.lower()
        scope = ""
        if bucket_name_lower.startswith("home"):
            scope = "home"
        elif bucket_name_lower.startswith("away"):
            scope = "away"
        elif bucket_name_lower.startswith("national"):
            scope = "natl"
        if "radio" in bucket_name_lower:
            medium = "radio"
        elif "ott" in bucket_name_lower:
            medium = "stream"
        else:
            medium = "tv"
        for broadcaster in bucket_entries:
            label = str(
                broadcaster.get("broadcasterDisplay")
                or broadcaster.get("broadcastDisplay")
                or broadcaster.get("display")
                or ""
            ).strip()
            if not label:
                continue
            broadcasters.append(
                {
                    "label": label,
                    "canonicalLabel": canonicalize_broadcaster_name(label),
                    "entityExternalId": str(broadcaster.get("broadcasterId", "")).strip(),
                    "scope": scope,
                    "medium": medium,
                    "language": str(broadcaster.get("language", "") or broadcaster.get("languageName", "")).strip(),
                }
            )
    return broadcasters


def dedupe_broadcasters(broadcasters: Iterable[dict]) -> List[dict]:
    deduped: List[dict] = []
    seen = set()
    for broadcaster in broadcasters:
        key = (
            broadcaster.get("canonicalLabel", ""),
            broadcaster.get("scope", ""),
            broadcaster.get("medium", ""),
            broadcaster.get("entityExternalId", ""),
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append(dict(broadcaster))
    return deduped


def extract_schedule_broadcasters(game: dict) -> List[dict]:
    if isinstance(game.get("broadcasters"), dict):
        return extract_game_page_broadcasters(game.get("broadcasters", {}))
    broadcasters: List[dict] = []
    for broadcaster in game.get("bd", {}).get("b", []):
        label = str(broadcaster.get("disp", "")).strip()
        if not label:
            continue
        broadcasters.append(
            {
                "label": label,
                "canonicalLabel": canonicalize_broadcaster_name(label),
                "entityExternalId": str(broadcaster.get("broadcasterId", "")).strip(),
                "scope": normalize_broadcaster_scope(broadcaster.get("scope", "")),
                "medium": normalize_broadcaster_medium(broadcaster.get("type", "")),
                "language": str(broadcaster.get("lan", "")).strip(),
            }
        )
    return broadcasters


def is_broadcaster_search_result(result: dict) -> bool:
    description = str(result.get("description", "") or "").lower()
    if any(keyword in description for keyword in BROADCASTER_DESCRIPTION_KEYWORDS):
        return True
    label = str(result.get("label", "") or "").lower()
    return any(keyword in label for keyword in ("radio", "sports", "television", "network", "channel", "station"))


def resolve_broadcaster_qid(broadcaster_name: str, cache: Dict[str, str]) -> str:
    canonical_name = canonicalize_broadcaster_name(broadcaster_name)
    raw_name = str(broadcaster_name or "").strip()
    if not canonical_name:
        return ""
    if canonical_name in cache:
        return cache[canonical_name]
    if raw_name in cache:
        return cache[raw_name]
    candidate_names = [canonical_name]
    if raw_name and raw_name != canonical_name:
        candidate_names.append(raw_name)
    for candidate_name in candidate_names:
        normalized_candidate = normalize_lookup_key(candidate_name)
        for attempt in range(1, BROADCASTER_LOOKUP_MAX_ATTEMPTS + 1):
            try:
                results = fetch_entity_search(candidate_name)
                break
            except (HTTPError, URLError, OSError):
                if attempt == BROADCASTER_LOOKUP_MAX_ATTEMPTS:
                    results = []
                    break
                time.sleep(float(attempt))
        for result in results:
            result_label = str(result.get("label", "") or "")
            result_match = str(result.get("match", {}).get("text", "") or "")
            if (
                normalize_lookup_key(result_label) != normalized_candidate
                and normalize_lookup_key(result_match) != normalized_candidate
            ):
                continue
            if not is_broadcaster_search_result(result):
                continue
            cache[canonical_name] = result["id"]
            if raw_name:
                cache[raw_name] = result["id"]
            return result["id"]
    cache[canonical_name] = ""
    if raw_name:
        cache[raw_name] = ""
    return ""


def build_today_wikidata_query(target_date: str) -> str:
    date_value = f'"{target_date}T00:00:00Z"^^xsd:dateTime'
    return f"""
    SELECT ?item ?itemLabel ?entityUrl WHERE {{
      ?item wdt:P31 wd:{BASKETBALL_GAME_QID};
            wdt:P118 wd:{NBA_LEAGUE_QID};
            wdt:P585 {date_value}.
      OPTIONAL {{ ?item wdt:P856 ?entityUrl. }}
      SERVICE wikibase:label {{ bd:serviceParam wikibase:language "en". }}
    }}
    ORDER BY ?itemLabel
    """.strip()


def load_wikidata_games_for_date(target_date: str) -> Dict[str, dict]:
    results = run_sparql(build_today_wikidata_query(target_date))
    rows: Dict[str, dict] = {}
    for binding in results.get("results", {}).get("bindings", []):
        qid = binding["item"]["value"].rsplit("/", 1)[-1]
        rows[qid] = {
            "qid": qid,
            "label": binding["itemLabel"]["value"],
            "entity_url": binding.get("entityUrl", {}).get("value", ""),
        }
    return rows


def game_id_prefix(game_id: str) -> str:
    game_id_text = str(game_id or "").strip()
    return game_id_text[:3] if len(game_id_text) >= 3 else ""


def normalize_current_schedule_game(game: dict, target_date: str) -> dict:
    normalized = dict(game)
    normalized["gameId"] = str(game.get("gameId", ""))
    normalized["gameDateLocal"] = target_date
    normalized["scheduleSourceUrl"] = SCHEDULE_URL
    return normalized


def load_current_season_games_for_date(
    target_date: str,
    requested_game_ids: Iterable[str],
    game_id_prefixes: Iterable[str],
) -> List[dict]:
    requested_ids = {str(game_id) for game_id in requested_game_ids if game_id}
    allowed_prefixes = set(game_id_prefixes)
    raw_schedule = fetch_json(SCHEDULE_URL)
    filtered: List[dict] = []
    for game_date in raw_schedule.get("leagueSchedule", {}).get("gameDates", []):
        for raw_game in game_date.get("games", []):
            game_id = str(raw_game.get("gameId", ""))
            if game_id_prefix(game_id) not in allowed_prefixes:
                continue
            if requested_ids and game_id not in requested_ids:
                continue
            if str(raw_game.get("gameDateEst", ""))[:10] != target_date:
                continue
            filtered.append(normalize_current_schedule_game(raw_game, target_date))
    return filtered


def format_label_date(iso_date: str) -> str:
    parsed = datetime.strptime(iso_date, "%Y-%m-%d").date()
    return f"{parsed.day} {parsed.strftime('%B %Y')}"


def format_description_date(iso_date: str) -> str:
    parsed = datetime.strptime(iso_date, "%Y-%m-%d").date()
    return parsed.strftime("%B %d, %Y").replace(" 0", " ")


def build_game_entity_url(game: dict) -> str:
    away_team_slug = str(game.get("awayTeam", {}).get("teamTricode", "")).strip().lower()
    home_team_slug = str(game.get("homeTeam", {}).get("teamTricode", "")).strip().lower()
    return f"https://www.nba.com/game/{away_team_slug}-vs-{home_team_slug}-{game.get('gameId', '')}"


def build_game_page_url(game: dict) -> str:
    return f"{build_game_entity_url(game)}/box-score"


def build_numeric_game_page_url(game_id: str) -> str:
    return GAME_PAGE_NUMERIC_BOXSCORE_URL_TEMPLATE.format(game_id=game_id)


def normalize_team_label(team_data: dict) -> str:
    team_tricode = team_data.get("teamTricode", "")
    if team_tricode in TEAM_LABEL_ALIASES:
        return TEAM_LABEL_ALIASES[team_tricode]
    return f"{str(team_data.get('teamCity', '')).strip()} {str(team_data.get('teamName', '')).strip()}".strip()


def build_wikidata_label(away_team_label: str, home_team_label: str, game_date_local: str, is_neutral: bool) -> str:
    connector = "vs" if is_neutral else "at"
    return f"{away_team_label} {connector} {home_team_label}, {format_label_date(game_date_local)}"


def load_current_team_qids() -> Dict[str, str]:
    results = run_sparql(WIKIDATA_TEAM_QUERY)
    mapping = {}
    for binding in results["results"]["bindings"]:
        label = binding["teamLabel"]["value"]
        qid = binding["team"]["value"].rsplit("/", 1)[-1]
        mapping[label] = qid
    return mapping


def match_tracked_games(wikidata_games_by_qid: Dict[str, dict], schedule_games: Iterable[dict], target_date: str) -> List[dict]:
    by_entity_url = {
        row["entity_url"]: row
        for row in wikidata_games_by_qid.values()
        if row.get("entity_url")
    }
    by_label = {row["label"]: row for row in wikidata_games_by_qid.values()}
    tracked_games: List[dict] = []
    for schedule_game in schedule_games:
        entity_url = build_game_entity_url(schedule_game)
        home_label = normalize_team_label(schedule_game["homeTeam"])
        away_label = normalize_team_label(schedule_game["awayTeam"])
        label = build_wikidata_label(
            away_label,
            home_label,
            target_date,
            is_neutral=bool(schedule_game.get("isNeutral")),
        )
        wikidata_row = by_entity_url.get(entity_url) or by_label.get(label)
        if wikidata_row is None:
            if VERBOSE:
                log_progress(f"Skipping game with no Wikidata item match: {label}")
            continue
        tracked_games.append(
            {
                "qid": wikidata_row["qid"],
                "label": wikidata_row["label"],
                "entity_url": entity_url,
                "schedule_game": schedule_game,
            }
        )
    return tracked_games


def fetch_boxscore_game_uncached(game: dict) -> Optional[dict]:
    game_id = str(game.get("gameId", ""))
    boxscore_url = BOXSCORE_URL_TEMPLATE.format(game_id=game_id)
    canonical_boxscore_url = build_game_page_url(game)
    try:
        request_url = f"{boxscore_url}?_={int(time.time() * 1000)}"
        request = urllib.request.Request(request_url, headers=build_request_headers(boxscore_url))
        with urllib.request.urlopen(request, timeout=15.0) as response:
            payload = json.load(response).get("game", {})
        if payload:
            payload["sourceProvider"] = "liveData"
            payload["apiEndpointUrl"] = boxscore_url
            payload["referenceUrl"] = canonical_boxscore_url
            payload["entityUrl"] = build_game_entity_url(game)
            return payload
    except HTTPError as exc:
        if exc.code != 403:
            raise
    except (TimeoutError, URLError, OSError):
        pass

    payload = fetch_game_page_boxscore_game(game)
    if not payload:
        return None
    return payload


def fetch_boxscores_for_tracked_games(tracked_games: Iterable[dict]) -> Dict[str, Optional[dict]]:
    import concurrent.futures

    results: Dict[str, Optional[dict]] = {}
    tracked_games = list(tracked_games)
    if not tracked_games:
        return results
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        future_map = {
            executor.submit(fetch_boxscore_game_uncached, tracked_game["schedule_game"]): tracked_game
            for tracked_game in tracked_games
        }
        for future in concurrent.futures.as_completed(future_map):
            tracked_game = future_map[future]
            try:
                results[tracked_game["qid"]] = future.result()
            except Exception as exc:
                if VERBOSE:
                    log_progress(f"Boxscore fetch failed for {tracked_game['label']}: {exc}")
                results[tracked_game["qid"]] = None
    return results


def fetch_game_page_props(url: str, timeout: float = 20.0) -> dict:
    headers = dict(NBA_HTTP_HEADERS)
    headers["Accept"] = "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
    last_error: Optional[Exception] = None
    for attempt in range(1, MAX_FETCH_ATTEMPTS + 1):
        request = urllib.request.Request(url, headers=headers)
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                html = response.read().decode("utf-8", "replace")
            break
        except (HTTPError, TimeoutError, URLError, OSError) as exc:
            last_error = exc
            if attempt == MAX_FETCH_ATTEMPTS:
                raise
            if VERBOSE:
                log_progress(
                    f"Retrying game page fetch after {type(exc).__name__} from {url} "
                    f"(attempt {attempt + 1}/{MAX_FETCH_ATTEMPTS})"
                )
            time.sleep(min(8.0, 1.5 * attempt))
    else:
        if last_error:
            raise last_error
        raise RuntimeError(f"Could not fetch NBA game page props from {url}")

    match = re.search(
        r'<script id="__NEXT_DATA__" type="application/json">(.*?)</script>',
        html,
        re.DOTALL,
    )
    if not match:
        raise ValueError(f"Could not find __NEXT_DATA__ on NBA game page {url}")
    return json.loads(match.group(1)).get("props", {}).get("pageProps", {})


def coerce_integer_string(value: object) -> str:
    text = str(value or "").strip()
    if not text:
        return ""
    normalized = text.replace(",", "")
    try:
        return str(int(float(normalized)))
    except ValueError:
        return ""


def coerce_duration_minutes(value: object) -> str:
    text = str(value or "").strip()
    if not text:
        return ""
    if ":" in text:
        try:
            hours_text, minutes_text = text.split(":", 1)
            return str((int(hours_text) * 60) + int(minutes_text))
        except ValueError:
            return ""
    return coerce_integer_string(text)


def fetch_game_page_boxscore_game(game: dict) -> Optional[dict]:
    game_id = str(game.get("gameId", ""))
    page_props = None
    for game_page_url in [build_game_page_url(game), build_numeric_game_page_url(game_id)]:
        try:
            page_props = fetch_game_page_props(game_page_url)
            break
        except (HTTPError, TimeoutError, URLError, OSError, ValueError):
            continue
    if page_props is None:
        return None

    page_game = page_props.get("game")
    if not isinstance(page_game, dict):
        return None

    normalized = dict(page_game)
    normalized["attendance"] = coerce_integer_string(normalized.get("attendance", ""))
    normalized["duration"] = coerce_duration_minutes(normalized.get("duration", ""))
    normalized["broadcasters"] = extract_game_page_broadcasters(page_game.get("broadcasters", {}))
    canonical_entity_url = build_game_entity_url(
        {
            "gameId": page_game.get("gameId", game_id),
            "awayTeam": page_game.get("awayTeam", {}),
            "homeTeam": page_game.get("homeTeam", {}),
        }
    )
    canonical_boxscore_url = f"{canonical_entity_url}/box-score"
    normalized["sourceProvider"] = "gamePage"
    normalized["apiEndpointUrl"] = canonical_boxscore_url
    normalized["entityUrl"] = canonical_entity_url
    normalized["referenceUrl"] = canonical_boxscore_url
    return normalized


def load_player_qids(player_ids: Iterable[str], cache: Dict[str, str]) -> Dict[str, str]:
    player_ids = sorted({str(player_id) for player_id in player_ids if player_id})
    if not player_ids:
        return {}
    missing_ids = [player_id for player_id in player_ids if player_id not in cache]
    if missing_ids:
        total_batches = (len(missing_ids) + 199) // 200
        if VERBOSE:
            log_progress(f"Resolving {len(missing_ids)} unique player IDs across {total_batches} Wikidata batches...")
        for batch_index in range(0, len(missing_ids), 200):
            chunk = missing_ids[batch_index:batch_index + 200]
            values = " ".join(f'"{player_id}"' for player_id in chunk)
            query = f"""
            SELECT ?item ?nbaId WHERE {{
              VALUES ?nbaId {{ {values} }}
              ?item wdt:P3647 ?nbaId .
            }}
            """.strip()
            results = run_sparql(query)
            resolved = {}
            for binding in results["results"]["bindings"]:
                resolved[binding["nbaId"]["value"]] = binding["item"]["value"].rsplit("/", 1)[-1]
            for player_id in chunk:
                cache[player_id] = resolved.get(player_id, "")
            if VERBOSE and (batch_index + 200 >= len(missing_ids) or ((batch_index // 200) + 1) % 10 == 0):
                log_progress(f"Resolved player ID batches: {(batch_index // 200) + 1}/{total_batches}")
        save_lookup_cache(PLAYER_QID_CACHE_PATH, cache)
    return {player_id: cache.get(player_id, "") for player_id in player_ids if cache.get(player_id, "")}


def parse_minutes_to_decimal(raw_value: str) -> str:
    raw_text = str(raw_value).strip()
    if not raw_text:
        return ""
    if not raw_text.startswith("PT"):
        clock_match = re.match(r"^(?P<minutes>\d+):(?P<seconds>\d{1,2})(?:\.\d+)?$", raw_text)
        if clock_match:
            minutes = int(clock_match.group("minutes"))
            seconds = int(clock_match.group("seconds"))
            return f"{minutes + (seconds / 60.0):.3f}"
        decimal_match = re.match(r"^\d+(?:\.\d+)?$", raw_text)
        if decimal_match:
            return f"{float(raw_text):.3f}"
        return ""
    body = raw_text[2:]
    minutes = 0
    seconds = 0.0
    if "M" in body:
        minutes_part, body = body.split("M", 1)
        if minutes_part:
            minutes = int(minutes_part)
    if body.endswith("S"):
        seconds_part = body[:-1]
        if seconds_part:
            seconds = float(seconds_part)
    return f"{minutes + (seconds / 60.0):.3f}"


def build_player_display_name(player: dict) -> str:
    direct_name = str(player.get("name", "")).strip()
    if direct_name:
        return direct_name
    first_name = str(player.get("firstName", "")).strip()
    family_name = str(player.get("familyName", "")).strip()
    return f"{first_name} {family_name}".strip()


def build_game_context_role_qids(game: dict) -> List[str]:
    role_qids: List[str] = []
    prefix = game_id_prefix(game.get("gameId", ""))
    if prefix == "001":
        role_qids.append(PRESEASON_QID)
    elif prefix == "002":
        role_qids.append(REGULAR_SEASON_QID)
    elif prefix == "004":
        role_qids.append(PLAYOFFS_QID)
    elif prefix == "006":
        role_qids.append(NBA_CUP_QID)
    context_text = " ".join(
        [
            str(game.get("gameLabel", "")),
            str(game.get("gameSubLabel", "")),
            str(game.get("seriesText", "")),
            str(game.get("gameSubtype", "")),
            str(game.get("gameStatusText", "")),
        ]
    ).lower()
    if "nba cup" in context_text or "emirates nba cup" in context_text:
        role_qids.append(NBA_CUP_QID)
    if "all-star" in context_text and ALL_STAR_GAME_QID not in role_qids:
        role_qids.append(ALL_STAR_GAME_QID)
    if "playoff" in context_text and PLAYOFFS_QID not in role_qids:
        role_qids.append(PLAYOFFS_QID)
    deduped: List[str] = []
    for qid in role_qids:
        if qid not in deduped:
            deduped.append(qid)
    return deduped


def build_game_context_description_fragment(role_qids: Iterable[str]) -> str:
    role_qid_set = set(role_qids)
    if ALL_STAR_GAME_QID in role_qid_set:
        return "All-Star Game"
    if NBA_CUP_QID in role_qid_set and REGULAR_SEASON_QID in role_qid_set:
        return "regular-season NBA Cup game"
    if NBA_CUP_QID in role_qid_set:
        return "NBA Cup game"
    if PLAYOFFS_QID in role_qid_set:
        return "playoff game"
    if PRESEASON_QID in role_qid_set:
        return "preseason game"
    if REGULAR_SEASON_QID in role_qid_set:
        return "regular-season game"
    return "game"


def build_final_description(game_date_local: str, role_qids: Iterable[str]) -> str:
    game_phrase = build_game_context_description_fragment(role_qids)
    return f"National Basketball Association {game_phrase} played on {format_description_date(game_date_local)}"


def build_player_snapshot(player: dict, player_qid: str, team_qid: str, team_label: str) -> Optional[dict]:
    stats = player.get("statistics", {})
    minutes_decimal = parse_minutes_to_decimal(stats.get("minutes", ""))
    if not minutes_decimal:
        return None
    try:
        if float(minutes_decimal) <= 0.0:
            return None
    except ValueError:
        return None
    return {
        "player_qid": player_qid,
        "player_name": build_player_display_name(player),
        "team_qid": team_qid,
        "team_label": team_label,
        "jersey_number": str(player.get("jerseyNum", "")).strip(),
        "position_qid": POSITION_QIDS.get(str(player.get("position", "")).strip(), ""),
        "minutes_amount": f"+{minutes_decimal}",
        "points_amount": f"+{int(stats.get('points', 0) or 0)}",
        "starter": str(player.get("starter", "")).strip() in {"1", "true", "True"},
    }


def build_final_snapshot(
    tracked_game: dict,
    boxscore_game: dict,
    player_qids: Dict[str, str],
    broadcaster_qid_cache: Dict[str, str],
    team_qids_by_label: Dict[str, str],
    target_date: str,
) -> dict:
    schedule_game = tracked_game["schedule_game"]
    home_team_data = boxscore_game["homeTeam"]
    away_team_data = boxscore_game["awayTeam"]
    home_label = normalize_team_label(home_team_data)
    away_label = normalize_team_label(away_team_data)
    home_qid = team_qids_by_label.get(home_label, "")
    away_qid = team_qids_by_label.get(away_label, "")
    if not home_qid or not away_qid:
        raise SystemExit(f"Could not resolve team QIDs for {tracked_game['label']}")

    home_score = int(home_team_data.get("score", 0) or 0)
    away_score = int(away_team_data.get("score", 0) or 0)
    winner_team_qid = ""
    if home_score != away_score:
        winner_team_qid = home_qid if home_score > away_score else away_qid

    players: List[dict] = []
    for team_data, team_qid, team_label in [
        (home_team_data, home_qid, home_label),
        (away_team_data, away_qid, away_label),
    ]:
        for player in team_data.get("players", []):
            player_qid = player_qids.get(str(player.get("personId", "")), "")
            if not player_qid:
                continue
            player_snapshot = build_player_snapshot(player, player_qid, team_qid, team_label)
            if player_snapshot:
                players.append(player_snapshot)

    broadcasters: List[dict] = []
    for broadcaster in dedupe_broadcasters(extract_schedule_broadcasters(schedule_game)):
        broadcaster_qid = resolve_broadcaster_qid(
            broadcaster.get("canonicalLabel", "") or broadcaster.get("label", ""),
            broadcaster_qid_cache,
        )
        if not broadcaster_qid:
            continue
        broadcasters.append({"qid": broadcaster_qid, "scope": broadcaster.get("scope", "")})

    role_qids = build_game_context_role_qids(schedule_game)
    return {
        "qid": tracked_game["qid"],
        "label": tracked_game["label"],
        "description": build_final_description(target_date, role_qids),
        "entity_url": tracked_game["entity_url"],
        "api_endpoint_url": boxscore_game.get("apiEndpointUrl", BOXSCORE_URL_TEMPLATE.format(game_id=str(schedule_game.get("gameId", "")))),
        "reference_url": boxscore_game.get("referenceUrl", build_game_page_url(schedule_game)),
        "retrieved_date": target_date,
        "game_status": 3,
        "home_team_label": home_label,
        "home_team_qid": home_qid,
        "away_team_label": away_label,
        "away_team_qid": away_qid,
        "home_score_amount": f"+{home_score}",
        "away_score_amount": f"+{away_score}",
        "winner_team_qid": winner_team_qid,
        "attendance_amount": f"+{boxscore_game.get('attendance', '')}" if str(boxscore_game.get("attendance", "")).strip() else "",
        "duration_amount": f"+{boxscore_game.get('duration', '')}" if str(boxscore_game.get("duration", "")).strip() else "",
        "players": sorted(players, key=lambda row: (row["team_qid"], row["player_qid"])),
        "broadcasters": sorted(broadcasters, key=lambda row: (row["scope"], row["qid"])),
    }


def create_claim(entity_qid: str, prop: str, datatype: str, value: object) -> dict:
    return {
        "mainsnak": make_snak(prop, datatype, value),
        "type": "statement",
        "rank": "normal",
        "qualifiers": {},
        "qualifiers-order": [],
        "references": [],
    }


def set_claim_value(claim: dict, datatype: str, value: object) -> None:
    claim["mainsnak"] = make_snak(claim["mainsnak"]["property"], datatype, value)


def add_qualifier(claim: dict, prop: str, datatype: str, value: object) -> None:
    append_qualifier_to_claim(claim, prop, make_snak(prop, datatype, value))


def remove_qualifiers(claim: dict, prop: str, hashes: Iterable[str]) -> None:
    remove_qualifier_hashes_from_claim(claim, prop, hashes)


def set_description(entity: dict, description: str) -> None:
    entity.setdefault("descriptions", {})["en"] = {"language": "en", "value": description}


def set_reference(claim: dict, reference_url: str, retrieved_date: str) -> None:
    if not reference_url or find_reference_by_url(claim, reference_url) is not None:
        return
    snaks = {
        "P854": [make_snak("P854", "url", reference_url)],
        "P813": [make_snak("P813", "time", time_value(retrieved_date))],
    }
    append_reference_to_claim(claim, {"snaks": snaks, "snaks-order": ["P854", "P813"]})


def ensure_reference(claim: dict, reference_url: str, retrieved_date: str) -> None:
    if reference_url:
        set_reference(claim, reference_url, retrieved_date)


def ensure_url_claim(entity: dict, qid: str, prop: str, url_value: str, reference_url: str, retrieved_date: str) -> dict:
    claim = find_matching_claim(entity, prop, url_value)
    if claim is None:
        claim = create_claim(qid, prop, "url", url_value)
        append_claim(entity, prop, claim)
    ensure_reference(claim, reference_url, retrieved_date)
    return claim


def ensure_item_claim(entity: dict, qid: str, prop: str, value_qid: str, reference_url: str, retrieved_date: str) -> dict:
    claim = find_matching_claim(entity, prop, value_qid)
    if claim is None:
        claim = create_claim(qid, prop, "wikibase-item", value_qid)
        append_claim(entity, prop, claim)
    ensure_reference(claim, reference_url, retrieved_date)
    return claim


def ensure_quantity_claim(
    entity: dict,
    qid: str,
    prop: str,
    amount: str,
    unit_qid: Optional[str],
    reference_url: str,
    retrieved_date: str,
) -> dict:
    target_value = quantity_value(amount, unit_qid)
    matching_claim = None
    for claim in entity.get("claims", {}).get(prop, []):
        datavalue = claim.get("mainsnak", {}).get("datavalue", {}).get("value", {})
        if datavalue.get("amount") != amount:
            continue
        if unit_qid and not datavalue.get("unit", "").endswith(f"/{unit_qid}"):
            continue
        if not unit_qid and datavalue.get("unit") != "1":
            continue
        matching_claim = claim
        break
    if matching_claim is None and entity.get("claims", {}).get(prop):
        matching_claim = entity["claims"][prop][0]
        set_claim_value(matching_claim, "quantity", target_value)
    elif matching_claim is None:
        matching_claim = create_claim(qid, prop, "quantity", target_value)
        append_claim(entity, prop, matching_claim)
    ensure_reference(matching_claim, reference_url, retrieved_date)
    return matching_claim


def ensure_single_item_qualifier(claim: dict, prop: str, value_qid: str) -> None:
    existing_values = {extract_item_id_from_snak(snak) for snak in claim.get("qualifiers", {}).get(prop, [])}
    if existing_values == {value_qid}:
        return
    existing_hashes = qualifier_hashes(claim, prop)
    if existing_hashes:
        remove_qualifiers(claim, prop, existing_hashes)
    add_qualifier(claim, prop, "wikibase-item", value_qid)


def ensure_optional_item_qualifier(claim: dict, prop: str, value_qid: str) -> None:
    if not value_qid:
        return
    existing_values = {extract_item_id_from_snak(snak) for snak in claim.get("qualifiers", {}).get(prop, [])}
    if value_qid in existing_values:
        return
    add_qualifier(claim, prop, "wikibase-item", value_qid)


def ensure_single_string_qualifier(claim: dict, prop: str, value_text: str) -> None:
    if not value_text:
        return
    existing_values = set(string_qualifier_values(claim, prop))
    if existing_values == {value_text}:
        return
    existing_hashes = qualifier_hashes(claim, prop)
    if existing_hashes:
        remove_qualifiers(claim, prop, existing_hashes)
    add_qualifier(claim, prop, "string", value_text)


def ensure_single_quantity_qualifier(claim: dict, prop: str, amount: str, unit_qid: Optional[str] = None) -> None:
    existing_amounts = {extract_quantity_amount_from_snak(snak) for snak in claim.get("qualifiers", {}).get(prop, [])}
    if existing_amounts == {amount}:
        return
    existing_hashes = qualifier_hashes(claim, prop)
    if existing_hashes:
        remove_qualifiers(claim, prop, existing_hashes)
    add_qualifier(claim, prop, "quantity", quantity_value(amount, unit_qid))


def claim_matches_broadcaster_scope(claim: dict, role_qid: str) -> bool:
    qualifier_roles = {extract_item_id_from_snak(snak) for snak in claim.get("qualifiers", {}).get("P3831", [])}
    if role_qid:
        return role_qid in qualifier_roles
    return HOME_TEAM_ROLE_QID not in qualifier_roles and AWAY_TEAM_ROLE_QID not in qualifier_roles


def ensure_description_matches(entity: dict, snapshot: dict) -> None:
    if entity.get("descriptions", {}).get("en", {}).get("value", "") != snapshot["description"]:
        set_description(entity, snapshot["description"])


def ensure_game_entity_url(entity: dict, snapshot: dict) -> None:
    ensure_url_claim(
        entity,
        snapshot["qid"],
        "P856",
        snapshot["entity_url"],
        snapshot["reference_url"],
        snapshot["retrieved_date"],
    )


def ensure_https_api_claim(entity: dict, snapshot: dict) -> None:
    api_claim = find_matching_claim(entity, "P6269", snapshot["api_endpoint_url"])
    if api_claim is None:
        api_claim = create_claim(snapshot["qid"], "P6269", "url", snapshot["api_endpoint_url"])
        append_claim(entity, "P6269", api_claim)
    ensure_single_item_qualifier(api_claim, "P2700", HTTPS_QID)
    ensure_reference(api_claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_team_score_claims(entity: dict, snapshot: dict) -> None:
    for team_qid, role_qid, score_amount in [
        (snapshot["home_team_qid"], HOME_TEAM_ROLE_QID, snapshot["home_score_amount"]),
        (snapshot["away_team_qid"], AWAY_TEAM_ROLE_QID, snapshot["away_score_amount"]),
    ]:
        claim = find_team_claim(entity, team_qid)
        if claim is None:
            claim = create_claim(snapshot["qid"], "P1923", "wikibase-item", team_qid)
            append_claim(entity, "P1923", claim)
        ensure_optional_item_qualifier(claim, "P3831", role_qid)
        ensure_single_quantity_qualifier(claim, "P1351", score_amount)
        ensure_reference(claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_broadcasters(entity: dict, snapshot: dict) -> None:
    for broadcaster in snapshot["broadcasters"]:
        desired_role_qid = ""
        if broadcaster["scope"] == "home":
            desired_role_qid = HOME_TEAM_ROLE_QID
        elif broadcaster["scope"] == "away":
            desired_role_qid = AWAY_TEAM_ROLE_QID
        matching_claim = None
        for claim in entity.get("claims", {}).get("P3301", []):
            datavalue = claim.get("mainsnak", {}).get("datavalue", {}).get("value", {})
            if datavalue.get("id") != broadcaster["qid"]:
                continue
            if claim_matches_broadcaster_scope(claim, desired_role_qid):
                matching_claim = claim
                break
        if matching_claim is None:
            matching_claim = create_claim(snapshot["qid"], "P3301", "wikibase-item", broadcaster["qid"])
            append_claim(entity, "P3301", matching_claim)
        if desired_role_qid:
            ensure_optional_item_qualifier(matching_claim, "P3831", desired_role_qid)
        ensure_reference(matching_claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_player_claims(entity: dict, snapshot: dict) -> None:
    for player_snapshot in snapshot["players"]:
        claim = find_matching_claim(entity, "P710", player_snapshot["player_qid"])
        if claim is None:
            claim = create_claim(snapshot["qid"], "P710", "wikibase-item", player_snapshot["player_qid"])
            append_claim(entity, "P710", claim)
        ensure_single_item_qualifier(claim, "P54", player_snapshot["team_qid"])
        if player_snapshot["jersey_number"]:
            ensure_single_string_qualifier(claim, "P1618", player_snapshot["jersey_number"])
        if player_snapshot["position_qid"]:
            ensure_single_item_qualifier(claim, "P413", player_snapshot["position_qid"])
        ensure_single_quantity_qualifier(claim, "P9140", player_snapshot["minutes_amount"], MINUTE_UNIT_QID)
        ensure_single_quantity_qualifier(claim, "P1351", player_snapshot["points_amount"])
        if player_snapshot["starter"]:
            ensure_optional_item_qualifier(claim, "P3831", STARTING_LINEUP_QID)
        ensure_reference(claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_winner_claim(entity: dict, snapshot: dict) -> None:
    if snapshot["winner_team_qid"]:
        ensure_item_claim(
            entity,
            snapshot["qid"],
            "P1346",
            snapshot["winner_team_qid"],
            snapshot["reference_url"],
            snapshot["retrieved_date"],
        )


def ensure_attendance_and_duration(entity: dict, snapshot: dict) -> None:
    if snapshot["attendance_amount"]:
        ensure_quantity_claim(
            entity,
            snapshot["qid"],
            "P1110",
            snapshot["attendance_amount"],
            None,
            snapshot["reference_url"],
            snapshot["retrieved_date"],
        )
    if snapshot["duration_amount"]:
        ensure_quantity_claim(
            entity,
            snapshot["qid"],
            "P2047",
            snapshot["duration_amount"],
            MINUTE_UNIT_QID,
            snapshot["reference_url"],
            snapshot["retrieved_date"],
        )


def update_wikidata_game(session: WikidataApiSession, game_qid: str, snapshot: dict) -> bool:
    entity = fetch_entity(game_qid)
    original_payload = serialize_entity_edit_data(build_entity_edit_data(entity))
    ensure_description_matches(entity, snapshot)
    ensure_game_entity_url(entity, snapshot)
    ensure_https_api_claim(entity, snapshot)
    ensure_team_score_claims(entity, snapshot)
    ensure_broadcasters(entity, snapshot)
    ensure_player_claims(entity, snapshot)
    ensure_winner_claim(entity, snapshot)
    ensure_attendance_and_duration(entity, snapshot)
    updated_data = build_entity_edit_data(entity)
    updated_payload = serialize_entity_edit_data(updated_data)
    if updated_payload == original_payload:
        return False
    session.edit_entity(game_qid, updated_data, "Update NBA game data", baserevid=entity.get("lastrevid"))
    return True


def determine_target_dates(explicit_date: str, now_local: datetime, start_hour: int, overnight_end_hour: int) -> List[str]:
    if explicit_date:
        return [explicit_date]
    hour = now_local.hour
    if hour >= start_hour:
        return [now_local.date().isoformat()]
    if hour <= overnight_end_hour:
        return [(now_local.date() - timedelta(days=1)).isoformat()]
    return []


def process_date(
    target_date: str,
    requested_game_ids: List[str],
    game_id_prefixes: List[str],
    session: WikidataApiSession,
    player_qid_cache: Dict[str, str],
    broadcaster_qid_cache: Dict[str, str],
) -> Dict[str, int]:
    schedule_games = load_current_season_games_for_date(target_date, requested_game_ids, game_id_prefixes)
    if not schedule_games:
        if VERBOSE:
            log_progress(f"{target_date}: no schedule games found.")
        return {"tracked": 0, "final_seen": 0, "updated": 0, "unchanged": 0, "unfinished": 0, "errors": 0}
    wikidata_games_by_qid = load_wikidata_games_for_date(target_date)
    if not wikidata_games_by_qid:
        if VERBOSE:
            log_progress(f"{target_date}: no Wikidata game items found.")
        return {"tracked": 0, "final_seen": 0, "updated": 0, "unchanged": 0, "unfinished": len(schedule_games), "errors": 0}
    team_qids_by_label = load_current_team_qids()
    tracked_games = match_tracked_games(wikidata_games_by_qid, schedule_games, target_date)
    boxscores_by_qid = fetch_boxscores_for_tracked_games(tracked_games)

    player_ids = []
    for boxscore_game in boxscores_by_qid.values():
        if not boxscore_game:
            continue
        for team_key in ["homeTeam", "awayTeam"]:
            for player in boxscore_game.get(team_key, {}).get("players", []):
                player_id = str(player.get("personId", "")).strip()
                if player_id:
                    player_ids.append(player_id)
    player_qids = load_player_qids(player_ids, player_qid_cache)

    updated = 0
    unchanged = 0
    unfinished = 0
    final_seen = 0
    errors = 0
    broadcaster_cache_before = dict(broadcaster_qid_cache)
    for tracked_game in tracked_games:
        boxscore_game = boxscores_by_qid.get(tracked_game["qid"])
        if not boxscore_game:
            unfinished += 1
            continue
        if int(boxscore_game.get("gameStatus", 0) or 0) != 3:
            unfinished += 1
            continue
        final_seen += 1
        try:
            snapshot = build_final_snapshot(
                tracked_game,
                boxscore_game,
                player_qids,
                broadcaster_qid_cache,
                team_qids_by_label,
                target_date,
            )
        except Exception as exc:
            errors += 1
            if VERBOSE:
                log_progress(f"{target_date}: skipping {tracked_game['label']} after snapshot error: {exc}")
            continue
        try:
            wrote_changes = update_wikidata_game(session, tracked_game["qid"], snapshot)
        except RuntimeError as exc:
            errors += 1
            if VERBOSE:
                log_progress(f"{target_date}: failed updating {tracked_game['label']}: {exc}")
            continue
        if wrote_changes:
            updated += 1
            log_event(f"Final data synced for {tracked_game['label']}.")
        else:
            unchanged += 1
            if VERBOSE:
                log_progress(f"{target_date}: final data already up to date for {tracked_game['label']}.")
    if broadcaster_qid_cache != broadcaster_cache_before:
        save_lookup_cache(BROADCASTER_QID_CACHE_PATH, broadcaster_qid_cache)
    return {
        "tracked": len(tracked_games),
        "final_seen": final_seen,
        "updated": updated,
        "unchanged": unchanged,
        "unfinished": unfinished,
        "errors": errors,
    }


def main() -> int:
    global VERBOSE
    args = parse_args()
    VERBOSE = args.verbose
    ensure_dir(LOOKUP_CACHE_DIR)
    if args.date:
        validate_iso_date(args.date)
    game_id_prefixes = normalize_game_id_prefixes([args.game_id_prefixes])
    requested_game_ids = list(dict.fromkeys(args.game_id))
    now_local = datetime.now(ZoneInfo(TIMEZONE))
    if args.ignore_window and not args.date:
        target_dates = [now_local.date().isoformat()]
    else:
        target_dates = determine_target_dates(args.date, now_local, args.start_hour, args.overnight_end_hour)
    if not target_dates:
        if VERBOSE:
            log_progress("Outside the nightly final-update window in America/New_York; exiting without work.")
        return 0

    session = WikidataApiSession(dry_run=args.dry_run)
    session.login_from_env()

    player_qid_cache = load_lookup_cache(PLAYER_QID_CACHE_PATH)
    broadcaster_qid_cache = load_lookup_cache(BROADCASTER_QID_CACHE_PATH)

    overall = {"tracked": 0, "final_seen": 0, "updated": 0, "unchanged": 0, "unfinished": 0, "errors": 0}
    for target_date in target_dates:
        counts = process_date(
            target_date,
            requested_game_ids,
            game_id_prefixes,
            session,
            player_qid_cache,
            broadcaster_qid_cache,
        )
        for key, value in counts.items():
            overall[key] += value
        if VERBOSE:
            log_progress(
                f"{target_date}: tracked={counts['tracked']}, final_seen={counts['final_seen']}, "
                f"updated={counts['updated']}, unchanged={counts['unchanged']}, "
                f"unfinished={counts['unfinished']}, errors={counts['errors']}"
            )
    if VERBOSE:
        log_progress(
            f"Overall: tracked={overall['tracked']}, final_seen={overall['final_seen']}, "
            f"updated={overall['updated']}, unchanged={overall['unchanged']}, "
            f"unfinished={overall['unfinished']}, errors={overall['errors']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
