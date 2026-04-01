#!/usr/bin/env python3

import argparse
import http.cookiejar
import json
import os
import re
import time
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from typing import Dict, Iterable, List, Optional, Set, Tuple
from urllib.error import HTTPError, URLError
from zoneinfo import ZoneInfo


def env_float(name: str, default: float) -> float:
    raw_value = str(os.environ.get(name, "")).strip()
    if not raw_value:
        return default
    try:
        return float(raw_value)
    except ValueError:
        return default


USER_AGENT = "Codex MLB Final Wikidata Updater/0.1"
TIMEZONE = "America/New_York"
SCHEDULE_URL_TEMPLATE = "https://statsapi.mlb.com/api/v1/schedule?sportId=1&date={target_date}"
BOXSCORE_URL_TEMPLATE = "https://statsapi.mlb.com/api/v1/game/{game_pk}/boxscore"
LIVE_FEED_URL_TEMPLATE = "https://statsapi.mlb.com/api/v1.1/game/{game_pk}/feed/live"
GAME_PAGE_URL_TEMPLATE = "https://www.mlb.com/gameday/{game_pk}"
GAME_PAGE_BOX_URL_TEMPLATE = "https://www.mlb.com/gameday/{game_pk}/final/box"
WIKIDATA_API_URL = "https://www.wikidata.org/w/api.php"
SPARQL_URL = "https://query.wikidata.org/sparql"

DEFAULT_GAME_TYPE_CODES = "A,D,F,L,R,S,W"
SUPPORTED_GAME_TYPE_CODES = ("A", "D", "E", "F", "L", "R", "S", "W")
DEFAULT_OVERNIGHT_END_HOUR = 4

STATE_DIR = os.path.join(".cache", "mlb_final_wikidata")
LOOKUP_CACHE_DIR = os.path.join(STATE_DIR, "lookups")
SESSION_DIR = os.path.join(STATE_DIR, "session")
PLAYER_QID_CACHE_PATH = os.path.join(LOOKUP_CACHE_DIR, "player_qids.json")
OFFICIAL_QID_CACHE_PATH = os.path.join(LOOKUP_CACHE_DIR, "official_qids.json")
SESSION_COOKIE_PATH = os.path.join(SESSION_DIR, "wikidata_cookies.lwp")

MLB_LEAGUE_QID = "Q1163715"
BASEBALL_GAME_QID = "Q27927857"
BASEBALL_TEAM_QID = "Q13027888"
HOME_TEAM_ROLE_QID = "Q24633211"
AWAY_TEAM_ROLE_QID = "Q24633216"
HTTPS_QID = "Q44484"
ENGLISH_QID = "Q1860"
MINUTE_UNIT_QID = "Q7727"
CALENDAR_MODEL_QID = "Q1985727"

WIKIDATA_TRANSIENT_API_CODES = {"maxlag", "ratelimited", "readonly"}
MAX_FETCH_ATTEMPTS = 4
SPARQL_MAX_ATTEMPTS = 5
WIKIDATA_POST_MAX_ATTEMPTS = 8
WIKIDATA_LOGIN_MAX_ATTEMPTS = 8
WIKIDATA_WRITE_MAX_ATTEMPTS = 2
WIKIDATA_WRITE_MAXLAG_SECONDS = env_float("WIKIDATA_WRITE_MAXLAG_SECONDS", 30.0)
WIKIDATA_WRITE_MAXLAG_WAIT_CAP_SECONDS = 15.0
WIKIDATA_WRITE_SPACING_SECONDS = 5.0
WIKIDATA_MAXLAG_COOLDOWN_SECONDS = 20.0
WIKIDATA_WRITE_MAXLAG_BREAKER_THRESHOLD = 1
OFFICIAL_LOOKUP_MAX_ATTEMPTS = 1

TEAM_LABEL_ALIASES = {
    "D-backs": "Arizona Diamondbacks",
}
OFFICIAL_DESCRIPTION_KEYWORDS = (
    "umpire",
    "referee",
    "baseball umpire",
)
TEAM_STAT_FIELDS = (
    ("P1351", "runs"),
    ("P9180", "atBats"),
    ("P9184", "hits"),
    ("P9188", "baseOnBalls"),
    ("P9190", "rbi"),
    ("P9217", "stolenBases"),
    ("P9220", "doubles"),
    ("P9225", "triples"),
)
PLAYER_STAT_FIELDS = TEAM_STAT_FIELDS

WIKIDATA_TEAM_QUERY = """
SELECT ?team ?teamLabel WHERE {
  ?team wdt:P31 wd:Q13027888;
        wdt:P118 wd:Q1163715.
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


def is_wikidata_maxlag_error(exc: BaseException) -> bool:
    return "Wikidata API error maxlag" in str(exc)


def is_wikidata_badtoken_error(exc: BaseException) -> bool:
    return "Wikidata API error badtoken" in str(exc)


def is_no_automatic_entity_id_error(exc: BaseException) -> bool:
    return "no-automatic-entity-id" in str(exc)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Update Wikidata for completed MLB games only. Intended for hourly GitHub Actions runs."
    )
    parser.add_argument("--date", default="", help="Explicit local official date in YYYY-MM-DD.")
    parser.add_argument("--game-pk", action="append", default=[], help="Specific MLB gamePk value(s) to restrict updates to.")
    parser.add_argument(
        "--game-type-codes",
        default=DEFAULT_GAME_TYPE_CODES,
        help=f"Comma-separated MLB gameType codes to consider. Defaults to {DEFAULT_GAME_TYPE_CODES}.",
    )
    parser.add_argument(
        "--overnight-end-hour",
        type=int,
        default=DEFAULT_OVERNIGHT_END_HOUR,
        help=(
            "When no explicit date is supplied, treat runs at or before this America/New_York hour "
            "as targeting the previous local official date."
        ),
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


def normalize_game_type_codes(values: Iterable[str]) -> List[str]:
    codes: List[str] = []
    for value in values:
        for token in str(value or "").split(","):
            code = token.strip().upper()
            if not code:
                continue
            if code not in SUPPORTED_GAME_TYPE_CODES:
                raise SystemExit(
                    f"Unsupported game type code: {code}. Supported values are: {', '.join(SUPPORTED_GAME_TYPE_CODES)}."
                )
            if code not in codes:
                codes.append(code)
    return codes or list(SUPPORTED_GAME_TYPE_CODES)


def build_request_headers() -> Dict[str, str]:
    return {"User-Agent": USER_AGENT}


def fetch_json(url: str, timeout: float = 20.0) -> dict:
    last_error: Optional[Exception] = None
    for attempt in range(1, MAX_FETCH_ATTEMPTS + 1):
        request = urllib.request.Request(url, headers=build_request_headers())
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
    if entity.get("labels"):
        data["labels"] = entity["labels"]
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


def fetch_entity(qid: str) -> dict:
    url = f"https://www.wikidata.org/wiki/Special:EntityData/{qid}.json"
    return fetch_json(url, timeout=20.0)["entities"][qid]


def fetch_entities(qids: Iterable[str]) -> Dict[str, dict]:
    ordered_qids = [str(qid).strip() for qid in qids if str(qid).strip()]
    if not ordered_qids:
        return {}
    params = urllib.parse.urlencode(
        {
            "action": "wbgetentities",
            "format": "json",
            "ids": "|".join(ordered_qids),
            "props": "labels|descriptions|claims|info",
        }
    )
    url = f"{WIKIDATA_API_URL}?{params}"
    return fetch_json(url, timeout=30.0).get("entities", {})


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
        self.load_cookies()
        self.opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(self.cookie_jar))
        self.csrf_token = ""
        self.next_write_not_before_monotonic = 0.0

    def load_cookies(self) -> None:
        if not os.path.exists(SESSION_COOKIE_PATH):
            return
        try:
            self.cookie_jar.load(ignore_discard=True, ignore_expires=True)
        except (FileNotFoundError, OSError, http.cookiejar.LoadError):
            return

    def save_cookies(self) -> None:
        try:
            self.cookie_jar.save(ignore_discard=True, ignore_expires=True)
        except OSError:
            return

    def _request(self, params: dict, post: bool) -> dict:
        encoded = urllib.parse.urlencode(params, doseq=True).encode("utf-8") if post else None
        url = WIKIDATA_API_URL if post else f"{WIKIDATA_API_URL}?{urllib.parse.urlencode(params, doseq=True)}"
        request = urllib.request.Request(url, data=encoded, headers={"User-Agent": USER_AGENT})
        with self.opener.open(request, timeout=30.0) as response:
            return json.load(response)

    def api_get(self, **params: object) -> dict:
        return self._request({"format": "json", "formatversion": "2", **params}, post=False)

    def is_logged_in(self, expected_username: str = "") -> bool:
        try:
            response = self.api_get(action="query", meta="userinfo")
        except (HTTPError, TimeoutError, URLError, OSError):
            return False
        userinfo = response.get("query", {}).get("userinfo", {})
        current_username = str(userinfo.get("name", "")).strip()
        if not current_username or userinfo.get("anon"):
            return False
        if expected_username and current_username != expected_username:
            return False
        return True

    def refresh_csrf_token(self) -> None:
        self.csrf_token = self.api_get(action="query", meta="tokens", type="csrf")["query"]["tokens"]["csrftoken"]

    def wait_for_write_slot(self) -> None:
        if self.dry_run:
            return
        now = time.monotonic()
        if now < self.next_write_not_before_monotonic:
            wait_seconds = self.next_write_not_before_monotonic - now
            if VERBOSE:
                log_progress(f"Pacing Wikidata write; sleeping {wait_seconds:.1f}s before next edit.")
            time.sleep(wait_seconds)
            now = time.monotonic()
        self.next_write_not_before_monotonic = now + WIKIDATA_WRITE_SPACING_SECONDS

    def api_post(
        self,
        max_attempts: int = WIKIDATA_POST_MAX_ATTEMPTS,
        include_maxlag: bool = False,
        **params: object,
    ) -> dict:
        payload = {"format": "json", "formatversion": "2", **params}
        if include_maxlag:
            payload["maxlag"] = str(max(1, int(round(WIKIDATA_WRITE_MAXLAG_SECONDS))))
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
                if include_maxlag:
                    wait_seconds = min(wait_seconds, WIKIDATA_WRITE_MAXLAG_WAIT_CAP_SECONDS)
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
        expected_username = username.split("@", 1)[0]
        if self.is_logged_in(expected_username):
            self.refresh_csrf_token()
            return
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
        self.save_cookies()
        self.refresh_csrf_token()

    def write(self, action: str, summary: str, **params: object) -> dict:
        if self.dry_run:
            if VERBOSE:
                log_progress(f"DRY RUN {action}: {summary}")
            return {}
        for attempt in range(1, 3):
            if not self.csrf_token:
                self.login_from_env()
            self.wait_for_write_slot()
            try:
                return self.api_post(
                    action=action,
                    token=self.csrf_token,
                    bot="1",
                    summary=summary,
                    max_attempts=WIKIDATA_WRITE_MAX_ATTEMPTS,
                    include_maxlag=True,
                    **params,
                )
            except RuntimeError as exc:
                if not is_wikidata_badtoken_error(exc) or attempt >= 2:
                    raise
                if VERBOSE:
                    log_progress("Wikidata API badtoken; refreshing login session and retrying write.")
                self.csrf_token = ""
                self.login_from_env()
        raise RuntimeError("Cannot write to Wikidata before login")

    def edit_entity(self, qid: str, data: dict, summary: str, baserevid: Optional[int] = None) -> dict:
        params: Dict[str, object] = {"id": qid, "data": serialize_entity_edit_data(data)}
        if baserevid is not None:
            params["baserevid"] = str(baserevid)
        return self.write("wbeditentity", summary, **params)

    def remove_claims(self, claim_ids: Iterable[str], summary: str) -> dict:
        filtered_ids = [str(claim_id).strip() for claim_id in claim_ids if str(claim_id).strip()]
        if not filtered_ids:
            return {}
        return self.write("wbremoveclaims", summary, claim="|".join(filtered_ids))


def normalize_lookup_key(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", str(value or "").lower())


def is_official_search_result(result: dict) -> bool:
    description = str(result.get("description", "") or "").lower()
    label = str(result.get("label", "") or "").lower()
    return any(keyword in description for keyword in OFFICIAL_DESCRIPTION_KEYWORDS) or "umpire" in label


def resolve_official_qid(official_name: str, cache: Dict[str, str]) -> str:
    normalized_name = str(official_name or "").strip()
    if not normalized_name:
        return ""
    if normalized_name in cache:
        return cache[normalized_name]
    for attempt in range(1, OFFICIAL_LOOKUP_MAX_ATTEMPTS + 1):
        try:
            results = fetch_entity_search(normalized_name)
            break
        except (HTTPError, URLError, OSError):
            if attempt == OFFICIAL_LOOKUP_MAX_ATTEMPTS:
                results = []
                break
            time.sleep(float(attempt))
    normalized_key = normalize_lookup_key(normalized_name)
    for result in results:
        result_label = str(result.get("label", "") or "")
        result_match = str(result.get("match", {}).get("text", "") or "")
        if normalize_lookup_key(result_label) != normalized_key and normalize_lookup_key(result_match) != normalized_key:
            continue
        if not is_official_search_result(result):
            continue
        cache[normalized_name] = result["id"]
        return result["id"]
    cache[normalized_name] = ""
    return ""


def schedule_url_for_date(target_date: str) -> str:
    return SCHEDULE_URL_TEMPLATE.format(target_date=target_date)


def build_today_wikidata_query(target_date: str) -> str:
    date_value = f'"{target_date}T00:00:00Z"^^xsd:dateTime'
    return f"""
    SELECT ?item ?itemLabel ?entityUrl ?team WHERE {{
      ?item wdt:P31 wd:{BASEBALL_GAME_QID};
            wdt:P118 wd:{MLB_LEAGUE_QID};
            wdt:P585 {date_value}.
      OPTIONAL {{ ?item wdt:P856 ?entityUrl. }}
      OPTIONAL {{ ?item wdt:P1923 ?team. }}
      SERVICE wikibase:label {{ bd:serviceParam wikibase:language "en". }}
    }}
    ORDER BY ?itemLabel
    """.strip()


def extract_mlb_game_pk_from_url(url: str) -> str:
    url_text = str(url or "").strip()
    if not url_text:
        return ""
    match = re.search(r"/gameday/(?:[^/]+/\d{4}/\d{2}/\d{2}/)?(\d+)(?:/|$)", url_text)
    if match:
        return match.group(1)
    return ""


def load_wikidata_games_for_date(target_date: str) -> Dict[str, dict]:
    results = run_sparql(build_today_wikidata_query(target_date))
    rows: Dict[str, dict] = {}
    for binding in results.get("results", {}).get("bindings", []):
        qid = binding["item"]["value"].rsplit("/", 1)[-1]
        row = rows.setdefault(
            qid,
            {
                "qid": qid,
                "label": binding["itemLabel"]["value"],
                "entity_url": "",
                "entity_game_pk": "",
                "team_qids": set(),
            },
        )
        entity_url = binding.get("entityUrl", {}).get("value", "")
        if entity_url and not row["entity_url"]:
            row["entity_url"] = entity_url
            row["entity_game_pk"] = extract_mlb_game_pk_from_url(entity_url)
        team_url = binding.get("team", {}).get("value", "")
        if team_url:
            row["team_qids"].add(team_url.rsplit("/", 1)[-1])
    for row in rows.values():
        row["team_qids"] = sorted(row["team_qids"])
        row["team_key"] = tuple(sorted(row["team_qids"]))
    return rows


def normalize_current_schedule_game(game: dict, target_date: str) -> dict:
    normalized = dict(game)
    normalized["gamePk"] = str(game.get("gamePk", ""))
    normalized["gameDateLocal"] = target_date
    normalized["scheduleSourceUrl"] = schedule_url_for_date(target_date)
    return normalized


def load_current_season_games_for_date(
    target_date: str,
    requested_game_pks: Iterable[str],
    game_type_codes: Iterable[str],
) -> List[dict]:
    requested_pks = {str(game_pk) for game_pk in requested_game_pks if game_pk}
    allowed_game_types = set(game_type_codes)
    raw_schedule = fetch_json(schedule_url_for_date(target_date))
    filtered: List[dict] = []
    for game_date in raw_schedule.get("dates", []):
        for raw_game in game_date.get("games", []):
            game_pk = str(raw_game.get("gamePk", ""))
            if requested_pks and game_pk not in requested_pks:
                continue
            if str(raw_game.get("officialDate", ""))[:10] != target_date:
                continue
            if str(raw_game.get("gameType", "")).upper() not in allowed_game_types:
                continue
            filtered.append(normalize_current_schedule_game(raw_game, target_date))
    return filtered


def format_item_label_date(iso_date: str) -> str:
    parsed = datetime.strptime(iso_date, "%Y-%m-%d").date()
    return parsed.strftime("%B %d, %Y").replace(" 0", " ")


def format_description_date(iso_date: str) -> str:
    parsed = datetime.strptime(iso_date, "%Y-%m-%d").date()
    return parsed.strftime("%B %d, %Y").replace(" 0", " ")


def build_game_entity_url(game: dict) -> str:
    return GAME_PAGE_URL_TEMPLATE.format(game_pk=str(game.get("gamePk", "")).strip())


def build_game_page_url(game: dict) -> str:
    return GAME_PAGE_BOX_URL_TEMPLATE.format(game_pk=str(game.get("gamePk", "")).strip())


def normalize_team_label(team_data: dict) -> str:
    label = str(team_data.get("name", "") or team_data.get("teamName", "")).strip()
    return TEAM_LABEL_ALIASES.get(label, label)


def build_wikidata_label_variants(away_team_label: str, home_team_label: str, game_date_local: str) -> Set[str]:
    date_label = format_item_label_date(game_date_local)
    return {
        f"{away_team_label} at {home_team_label} ({date_label})",
        f"{away_team_label} vs {home_team_label} ({date_label})",
    }


def load_current_team_qids() -> Dict[str, str]:
    results = run_sparql(WIKIDATA_TEAM_QUERY)
    mapping: Dict[str, str] = {}
    for binding in results.get("results", {}).get("bindings", []):
        label = binding["teamLabel"]["value"]
        qid = binding["team"]["value"].rsplit("/", 1)[-1]
        mapping[label] = qid
    return mapping


def match_tracked_games(
    wikidata_games_by_qid: Dict[str, dict],
    schedule_games: Iterable[dict],
    target_date: str,
    team_qids_by_label: Dict[str, str],
) -> List[dict]:
    by_game_pk = {
        row["entity_game_pk"]: row
        for row in wikidata_games_by_qid.values()
        if row.get("entity_game_pk")
    }
    by_team_key: Dict[Tuple[str, ...], List[dict]] = {}
    for row in wikidata_games_by_qid.values():
        team_key = tuple(row.get("team_key", ()))
        if not team_key:
            continue
        by_team_key.setdefault(team_key, []).append(row)

    tracked_games: List[dict] = []
    for schedule_game in schedule_games:
        game_pk = str(schedule_game.get("gamePk", ""))
        home_label = normalize_team_label(schedule_game.get("teams", {}).get("home", {}).get("team", {}))
        away_label = normalize_team_label(schedule_game.get("teams", {}).get("away", {}).get("team", {}))
        home_qid = team_qids_by_label.get(home_label, "")
        away_qid = team_qids_by_label.get(away_label, "")
        if not home_qid or not away_qid:
            if VERBOSE:
                log_progress(f"Skipping MLB game with unresolved team QIDs: {away_label} at {home_label} ({target_date})")
            continue

        entity_url = build_game_entity_url(schedule_game)
        wikidata_row = by_game_pk.get(game_pk)
        if wikidata_row is None:
            team_key = tuple(sorted((away_qid, home_qid)))
            candidates = by_team_key.get(team_key, [])
            if len(candidates) == 1:
                wikidata_row = candidates[0]
            elif len(candidates) > 1:
                label_variants = build_wikidata_label_variants(away_label, home_label, target_date)
                matching_candidates = [row for row in candidates if row.get("label", "") in label_variants]
                if len(matching_candidates) == 1:
                    wikidata_row = matching_candidates[0]
                elif VERBOSE:
                    log_progress(
                        f"Skipping ambiguous MLB game match for {away_label} at {home_label} ({target_date}); "
                        f"{len(candidates)} candidate Wikidata items share the same teams/date."
                    )
                    continue
        if wikidata_row is None:
            if VERBOSE:
                log_progress(f"Skipping MLB game with no Wikidata item match: {away_label} at {home_label} ({target_date})")
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
    game_pk = str(game.get("gamePk", ""))
    boxscore_url = BOXSCORE_URL_TEMPLATE.format(game_pk=game_pk)
    payload = fetch_json(boxscore_url, timeout=20.0)
    if not payload:
        return None
    payload["sourceProvider"] = "boxscore"
    payload["apiEndpointUrl"] = LIVE_FEED_URL_TEMPLATE.format(game_pk=game_pk)
    payload["referenceUrl"] = build_game_page_url(game)
    payload["entityUrl"] = build_game_entity_url(game)
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


def coerce_integer_string(value: object) -> str:
    if value is None:
        return ""
    text = str(value).strip().rstrip(".")
    if not text:
        return ""
    normalized = text.replace(",", "")
    try:
        return str(int(float(normalized)))
    except ValueError:
        return ""


def coerce_stat_amount(value: object) -> str:
    normalized = coerce_integer_string(value)
    if normalized == "":
        return ""
    return f"+{normalized}"


def coerce_duration_minutes(value: object) -> str:
    text = str(value or "").strip().rstrip(".")
    if not text:
        return ""
    if ":" in text:
        try:
            hours_text, minutes_text = text.split(":", 1)
            return str((int(hours_text) * 60) + int(minutes_text))
        except ValueError:
            return ""
    return coerce_integer_string(text)


def extract_boxscore_info_value(boxscore_game: dict, label: str) -> str:
    for row in boxscore_game.get("info", []):
        if str(row.get("label", "")).strip() == label:
            return str(row.get("value", "")).strip()
    return ""


def parse_attendance_amount(boxscore_game: dict) -> str:
    return coerce_stat_amount(extract_boxscore_info_value(boxscore_game, "Att"))


def parse_duration_amount(boxscore_game: dict) -> str:
    minutes = coerce_duration_minutes(extract_boxscore_info_value(boxscore_game, "T"))
    if not minutes:
        return ""
    return f"+{minutes}"


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
            SELECT ?item ?mlbId WHERE {{
              VALUES ?mlbId {{ {values} }}
              ?item wdt:P3541 ?mlbId .
            }}
            """.strip()
            results = run_sparql(query)
            resolved: Dict[str, str] = {}
            for binding in results.get("results", {}).get("bindings", []):
                resolved[binding["mlbId"]["value"]] = binding["item"]["value"].rsplit("/", 1)[-1]
            for player_id in chunk:
                cache[player_id] = resolved.get(player_id, "")
            if VERBOSE and (batch_index + 200 >= len(missing_ids) or ((batch_index // 200) + 1) % 10 == 0):
                log_progress(f"Resolved player ID batches: {(batch_index // 200) + 1}/{total_batches}")
        save_lookup_cache(PLAYER_QID_CACHE_PATH, cache)
    return {player_id: cache.get(player_id, "") for player_id in player_ids if cache.get(player_id, "")}


def build_game_context_description_fragment(game: dict) -> str:
    game_type = str(game.get("gameType", "")).upper()
    if game_type == "A":
        return "All-Star Game"
    if game_type == "D":
        return "Division Series game"
    if game_type == "E":
        return "exhibition game"
    if game_type == "F":
        return "Wild Card Series game"
    if game_type == "L":
        return "League Championship Series game"
    if game_type == "R":
        return "regular-season game"
    if game_type == "S":
        return "spring training game"
    if game_type == "W":
        return "World Series game"
    return "game"


def build_final_description(game_date_local: str, game: dict) -> str:
    game_phrase = build_game_context_description_fragment(game)
    if game_phrase == "All-Star Game":
        return f"Major League Baseball All-Star Game played on {format_description_date(game_date_local)}"
    return f"Major League Baseball {game_phrase} played on {format_description_date(game_date_local)}"


def extract_team_stat_amounts(team_data: dict) -> Dict[str, str]:
    batting_stats = team_data.get("teamStats", {}).get("batting", {})
    stat_amounts: Dict[str, str] = {}
    for prop, field in TEAM_STAT_FIELDS:
        if field not in batting_stats:
            continue
        amount = coerce_stat_amount(batting_stats.get(field))
        if amount:
            stat_amounts[prop] = amount
    return stat_amounts


def extract_player_stat_amounts(player: dict) -> Dict[str, str]:
    batting_stats = player.get("stats", {}).get("batting", {})
    if not isinstance(batting_stats, dict):
        return {}
    stat_amounts: Dict[str, str] = {}
    for prop, field in PLAYER_STAT_FIELDS:
        if field not in batting_stats:
            continue
        amount = coerce_stat_amount(batting_stats.get(field))
        if amount and amount != "+0":
            stat_amounts[prop] = amount
    return stat_amounts


def build_player_snapshot(
    player: dict,
    player_qid: str,
    team_qid: str,
    team_label: str,
    appeared_in_game: bool,
) -> Optional[dict]:
    if not player_qid or not appeared_in_game:
        return None
    return {
        "player_qid": player_qid,
        "player_name": str(player.get("person", {}).get("fullName", "")).strip(),
        "team_qid": team_qid,
        "team_label": team_label,
        "jersey_number": str(player.get("jerseyNumber", "")).strip(),
        "stat_amounts": extract_player_stat_amounts(player),
    }


def extract_officials_snapshot(boxscore_game: dict, official_qid_cache: Dict[str, str]) -> List[dict]:
    officials: List[dict] = []
    seen: Set[str] = set()
    for official in boxscore_game.get("officials", []):
        name = str(official.get("official", {}).get("fullName", "")).strip()
        if not name:
            continue
        official_qid = resolve_official_qid(name, official_qid_cache)
        if not official_qid or official_qid in seen:
            continue
        seen.add(official_qid)
        officials.append(
            {
                "qid": official_qid,
                "role": str(official.get("officialType", "")).strip(),
            }
        )
    return officials


def build_final_snapshot(
    tracked_game: dict,
    boxscore_game: dict,
    player_qids: Dict[str, str],
    official_qid_cache: Dict[str, str],
    team_qids_by_label: Dict[str, str],
    target_date: str,
) -> dict:
    schedule_game = tracked_game["schedule_game"]
    home_team_data = boxscore_game["teams"]["home"]
    away_team_data = boxscore_game["teams"]["away"]
    home_label = normalize_team_label(home_team_data.get("team", {}))
    away_label = normalize_team_label(away_team_data.get("team", {}))
    home_qid = team_qids_by_label.get(home_label, "")
    away_qid = team_qids_by_label.get(away_label, "")
    if not home_qid or not away_qid:
        raise SystemExit(f"Could not resolve team QIDs for {tracked_game['label']}")

    home_stat_amounts = extract_team_stat_amounts(home_team_data)
    away_stat_amounts = extract_team_stat_amounts(away_team_data)
    home_runs = int(home_stat_amounts.get("P1351", "+0").lstrip("+"))
    away_runs = int(away_stat_amounts.get("P1351", "+0").lstrip("+"))
    winner_team_qid = ""
    if home_runs != away_runs:
        winner_team_qid = home_qid if home_runs > away_runs else away_qid

    players: List[dict] = []
    for team_data, team_qid, team_label in [
        (home_team_data, home_qid, home_label),
        (away_team_data, away_qid, away_label),
    ]:
        used_player_ids = {str(player_id) for player_id in team_data.get("batters", []) + team_data.get("pitchers", [])}
        for player_id in sorted(used_player_ids, key=lambda value: int(value)):
            player = team_data.get("players", {}).get(f"ID{player_id}")
            if not player:
                continue
            player_qid = player_qids.get(player_id, "")
            player_snapshot = build_player_snapshot(
                player,
                player_qid,
                team_qid,
                team_label,
                appeared_in_game=True,
            )
            if player_snapshot:
                players.append(player_snapshot)

    officials = extract_officials_snapshot(boxscore_game, official_qid_cache)
    return {
        "qid": tracked_game["qid"],
        "label": tracked_game["label"],
        "description": build_final_description(target_date, schedule_game),
        "game_pk": str(schedule_game.get("gamePk", "")).strip(),
        "entity_url": tracked_game["entity_url"],
        "api_endpoint_url": boxscore_game.get("apiEndpointUrl", LIVE_FEED_URL_TEMPLATE.format(game_pk=str(schedule_game.get("gamePk", "")))),
        "reference_url": boxscore_game.get("referenceUrl", build_game_page_url(schedule_game)),
        "retrieved_date": target_date,
        "home_team_label": home_label,
        "home_team_qid": home_qid,
        "away_team_label": away_label,
        "away_team_qid": away_qid,
        "home_stat_amounts": home_stat_amounts,
        "away_stat_amounts": away_stat_amounts,
        "winner_team_qid": winner_team_qid,
        "attendance_amount": parse_attendance_amount(boxscore_game),
        "duration_amount": parse_duration_amount(boxscore_game),
        "players": sorted(players, key=lambda row: (row["team_qid"], row["player_qid"])),
        "officials": sorted(officials, key=lambda row: row["qid"]),
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
    if prop == "P856":
        ensure_single_item_qualifier(claim, "P407", ENGLISH_QID)
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


def ensure_description_matches(entity: dict, snapshot: dict) -> None:
    if not entity.get("descriptions", {}).get("en", {}).get("value", "").strip():
        set_description(entity, snapshot["description"])


def find_matching_mlb_game_url_claim(entity: dict, prop: str, game_pk: str) -> Optional[dict]:
    for claim in entity.get("claims", {}).get(prop, []):
        url_value = claim.get("mainsnak", {}).get("datavalue", {}).get("value", "")
        if extract_mlb_game_pk_from_url(url_value) == game_pk:
            return claim
    return None


def ensure_game_entity_url(entity: dict, snapshot: dict) -> None:
    claim = find_matching_mlb_game_url_claim(entity, "P856", snapshot["game_pk"])
    if claim is None:
        claim = ensure_url_claim(
            entity,
            snapshot["qid"],
            "P856",
            snapshot["entity_url"],
            snapshot["reference_url"],
            snapshot["retrieved_date"],
        )
    else:
        ensure_single_item_qualifier(claim, "P407", ENGLISH_QID)
        ensure_reference(claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_https_api_claim(entity: dict, snapshot: dict) -> None:
    api_claim = find_matching_claim(entity, "P6269", snapshot["api_endpoint_url"])
    if api_claim is None:
        api_claim = create_claim(snapshot["qid"], "P6269", "url", snapshot["api_endpoint_url"])
        append_claim(entity, "P6269", api_claim)
    ensure_single_item_qualifier(api_claim, "P2700", HTTPS_QID)
    ensure_reference(api_claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_team_stat_claims(entity: dict, snapshot: dict) -> None:
    for team_qid, role_qid, stat_amounts in [
        (snapshot["home_team_qid"], HOME_TEAM_ROLE_QID, snapshot["home_stat_amounts"]),
        (snapshot["away_team_qid"], AWAY_TEAM_ROLE_QID, snapshot["away_stat_amounts"]),
    ]:
        claim = find_team_claim(entity, team_qid)
        if claim is None:
            claim = create_claim(snapshot["qid"], "P1923", "wikibase-item", team_qid)
            append_claim(entity, "P1923", claim)
        ensure_optional_item_qualifier(claim, "P3831", role_qid)
        for prop, amount in stat_amounts.items():
            ensure_single_quantity_qualifier(claim, prop, amount)
        ensure_reference(claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_officials(entity: dict, snapshot: dict) -> None:
    for official in snapshot["officials"]:
        ensure_item_claim(
            entity,
            snapshot["qid"],
            "P1652",
            official["qid"],
            snapshot["reference_url"],
            snapshot["retrieved_date"],
        )


def ensure_player_claims(entity: dict, snapshot: dict) -> None:
    for player_snapshot in snapshot["players"]:
        claim = find_matching_claim(entity, "P710", player_snapshot["player_qid"])
        if claim is None:
            claim = create_claim(snapshot["qid"], "P710", "wikibase-item", player_snapshot["player_qid"])
            append_claim(entity, "P710", claim)
        ensure_single_item_qualifier(claim, "P54", player_snapshot["team_qid"])
        if player_snapshot["jersey_number"]:
            ensure_single_string_qualifier(claim, "P1618", player_snapshot["jersey_number"])
        for prop, amount in player_snapshot["stat_amounts"].items():
            ensure_single_quantity_qualifier(claim, prop, amount)
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
    ensure_team_stat_claims(entity, snapshot)
    ensure_officials(entity, snapshot)
    ensure_player_claims(entity, snapshot)
    ensure_winner_claim(entity, snapshot)
    ensure_attendance_and_duration(entity, snapshot)
    updated_data = build_entity_edit_data(entity)
    updated_payload = serialize_entity_edit_data(updated_data)
    if updated_payload == original_payload:
        return False
    session.edit_entity(game_qid, updated_data, "Update MLB game data", baserevid=entity.get("lastrevid"))
    return True


def determine_target_dates(explicit_date: str, now_local: datetime, overnight_end_hour: int) -> List[str]:
    if explicit_date:
        return [explicit_date]
    if now_local.hour <= overnight_end_hour:
        return [(now_local.date() - timedelta(days=1)).isoformat()]
    return [now_local.date().isoformat()]


def process_date(
    target_date: str,
    requested_game_pks: List[str],
    game_type_codes: List[str],
    session: WikidataApiSession,
    player_qid_cache: Dict[str, str],
    official_qid_cache: Dict[str, str],
) -> Dict[str, int]:
    schedule_games = load_current_season_games_for_date(target_date, requested_game_pks, game_type_codes)
    if not schedule_games:
        if VERBOSE:
            log_progress(f"{target_date}: no MLB schedule games found.")
        return {"tracked": 0, "final_seen": 0, "updated": 0, "unchanged": 0, "unfinished": 0, "deferred": 0, "errors": 0}

    team_qids_by_label = load_current_team_qids()
    wikidata_games_by_qid = load_wikidata_games_for_date(target_date)
    if not wikidata_games_by_qid:
        if VERBOSE:
            log_progress(f"{target_date}: no Wikidata MLB game items found.")
        return {
            "tracked": 0,
            "final_seen": 0,
            "updated": 0,
            "unchanged": 0,
            "unfinished": len(schedule_games),
            "deferred": 0,
            "errors": 0,
        }

    tracked_games = match_tracked_games(wikidata_games_by_qid, schedule_games, target_date, team_qids_by_label)
    boxscores_by_qid = fetch_boxscores_for_tracked_games(tracked_games)

    player_ids: List[str] = []
    for boxscore_game in boxscores_by_qid.values():
        if not boxscore_game:
            continue
        for side in ("away", "home"):
            team_data = boxscore_game.get("teams", {}).get(side, {})
            player_ids.extend(str(player_id) for player_id in team_data.get("batters", []))
            player_ids.extend(str(player_id) for player_id in team_data.get("pitchers", []))
    player_qids = load_player_qids(player_ids, player_qid_cache)

    updated = 0
    unchanged = 0
    unfinished = 0
    deferred = 0
    final_seen = 0
    errors = 0
    maxlag_failures = 0
    official_cache_before = dict(official_qid_cache)

    for tracked_game_index, tracked_game in enumerate(tracked_games):
        schedule_game = tracked_game["schedule_game"]
        if str(schedule_game.get("status", {}).get("abstractGameState", "")) != "Final":
            unfinished += 1
            continue
        boxscore_game = boxscores_by_qid.get(tracked_game["qid"])
        if not boxscore_game:
            unfinished += 1
            continue
        final_seen += 1
        try:
            snapshot = build_final_snapshot(
                tracked_game,
                boxscore_game,
                player_qids,
                official_qid_cache,
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
            if is_wikidata_maxlag_error(exc):
                maxlag_failures += 1
                if VERBOSE:
                    log_progress(
                        f"{target_date}: cooling down {WIKIDATA_MAXLAG_COOLDOWN_SECONDS:.0f}s "
                        f"after maxlag before the next game update."
                    )
                time.sleep(WIKIDATA_MAXLAG_COOLDOWN_SECONDS)
                if maxlag_failures >= WIKIDATA_WRITE_MAXLAG_BREAKER_THRESHOLD:
                    for remaining_tracked_game in tracked_games[tracked_game_index + 1:]:
                        remaining_schedule_game = remaining_tracked_game["schedule_game"]
                        if str(remaining_schedule_game.get("status", {}).get("abstractGameState", "")) != "Final":
                            unfinished += 1
                            continue
                        deferred += 1
                    if VERBOSE:
                        log_progress(
                            f"{target_date}: stopping additional writes after {maxlag_failures} maxlag hit(s); "
                            f"deferring {deferred} remaining final game update(s) to a later run."
                        )
                    break
            continue
        if wrote_changes:
            updated += 1
            log_event(f"Final data synced for {tracked_game['label']}.")
        else:
            unchanged += 1
            if VERBOSE:
                log_progress(f"{target_date}: final data already up to date for {tracked_game['label']}.")

    if official_qid_cache != official_cache_before:
        save_lookup_cache(OFFICIAL_QID_CACHE_PATH, official_qid_cache)
    return {
        "tracked": len(tracked_games),
        "final_seen": final_seen,
        "updated": updated,
        "unchanged": unchanged,
        "unfinished": unfinished,
        "deferred": deferred,
        "errors": errors,
    }


def main() -> int:
    global VERBOSE
    args = parse_args()
    VERBOSE = args.verbose
    ensure_dir(LOOKUP_CACHE_DIR)
    if args.date:
        validate_iso_date(args.date)

    game_type_codes = normalize_game_type_codes([args.game_type_codes])
    requested_game_pks = list(dict.fromkeys(str(game_pk).strip() for game_pk in args.game_pk if str(game_pk).strip()))
    now_local = datetime.now(ZoneInfo(TIMEZONE))
    target_dates = determine_target_dates(args.date, now_local, args.overnight_end_hour)

    session = WikidataApiSession(dry_run=args.dry_run)
    session.login_from_env()

    player_qid_cache = load_lookup_cache(PLAYER_QID_CACHE_PATH)
    official_qid_cache = load_lookup_cache(OFFICIAL_QID_CACHE_PATH)

    overall = {"tracked": 0, "final_seen": 0, "updated": 0, "unchanged": 0, "unfinished": 0, "deferred": 0, "errors": 0}
    for target_date in target_dates:
        counts = process_date(
            target_date,
            requested_game_pks,
            game_type_codes,
            session,
            player_qid_cache,
            official_qid_cache,
        )
        for key, value in counts.items():
            overall[key] += value
        if VERBOSE:
            log_progress(
                f"{target_date}: tracked={counts['tracked']}, final_seen={counts['final_seen']}, "
                f"updated={counts['updated']}, unchanged={counts['unchanged']}, "
                f"unfinished={counts['unfinished']}, deferred={counts['deferred']}, errors={counts['errors']}"
            )

    if VERBOSE:
        log_progress(
            f"Overall: tracked={overall['tracked']}, final_seen={overall['final_seen']}, "
            f"updated={overall['updated']}, unchanged={overall['unchanged']}, "
            f"unfinished={overall['unfinished']}, deferred={overall['deferred']}, errors={overall['errors']}"
        )
    return 0 if overall["errors"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
