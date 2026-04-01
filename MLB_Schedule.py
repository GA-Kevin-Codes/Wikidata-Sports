#!/usr/bin/env python3

import argparse
import json
import os
import time
import urllib.parse
import urllib.request
from datetime import datetime
from typing import Dict, Iterable, List, Optional, Set, Tuple
from urllib.error import HTTPError, URLError
from zoneinfo import ZoneInfo

import MLB_Nightly as mlb


TIMEZONE = mlb.TIMEZONE
USER_AGENT = "Codex MLB Schedule Wikidata Seeder/0.1"
SCHEDULE_RANGE_URL_TEMPLATE = "https://statsapi.mlb.com/api/v1/schedule?sportId=1&startDate={start_date}&endDate={end_date}"

STATE_DIR = os.path.join(".cache", "mlb_schedule_wikidata")
LOOKUP_CACHE_DIR = os.path.join(STATE_DIR, "lookups")
TEAM_QID_CACHE_PATH = os.path.join(LOOKUP_CACHE_DIR, "team_qids.json")
VENUE_QID_CACHE_PATH = os.path.join(LOOKUP_CACHE_DIR, "venue_qids.json")

DEFAULT_GAME_TYPE_CODES = "A,D,F,L,R,S,W"
SUPPORTED_GAME_TYPE_CODES = mlb.SUPPORTED_GAME_TYPE_CODES
DEFAULT_MAX_CREATE = 300
TEAM_DESCRIPTION_KEYWORDS = (
    "baseball team",
    "all-star team",
    "sports team",
)
VENUE_DESCRIPTION_KEYWORDS = (
    "baseball stadium",
    "stadium",
    "ballpark",
    "park",
    "sports venue",
)

VERBOSE = False


def set_verbose(value: bool) -> None:
    global VERBOSE
    VERBOSE = value
    mlb.VERBOSE = value


def log_progress(message: str) -> None:
    if VERBOSE:
        mlb.log_progress(message)


def log_event(message: str) -> None:
    mlb.log_event(message)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Create or enrich Wikidata items for scheduled MLB games."
    )
    parser.add_argument("--season", type=int, default=0, help="Season year to seed. Defaults to next local year.")
    parser.add_argument("--start-date", default="", help="Explicit start date in YYYY-MM-DD.")
    parser.add_argument("--end-date", default="", help="Explicit end date in YYYY-MM-DD.")
    parser.add_argument(
        "--game-type-codes",
        default=DEFAULT_GAME_TYPE_CODES,
        help=f"Comma-separated MLB gameType codes to consider. Defaults to {DEFAULT_GAME_TYPE_CODES}.",
    )
    parser.add_argument("--game-pk", action="append", default=[], help="Specific MLB gamePk value(s) to restrict work to.")
    parser.add_argument("--max-create", type=int, default=DEFAULT_MAX_CREATE, help="Maximum number of new items to create in one run.")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    return parser.parse_args()


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


def determine_date_range(args: argparse.Namespace, now_local: datetime) -> Tuple[str, str]:
    if bool(args.start_date) != bool(args.end_date):
        raise SystemExit("Provide both --start-date and --end-date together.")
    if args.start_date and args.end_date:
        validate_iso_date(args.start_date)
        validate_iso_date(args.end_date)
        if args.start_date > args.end_date:
            raise SystemExit("--start-date must be on or before --end-date.")
        return args.start_date, args.end_date
    season = args.season or (now_local.year + 1)
    return f"{season}-03-01", f"{season}-11-30"


def load_lookup_cache(path: str) -> Dict[str, str]:
    return mlb.load_lookup_cache(path)


def save_lookup_cache(path: str, payload: Dict[str, str]) -> None:
    return mlb.save_lookup_cache(path, payload)


def schedule_range_url(start_date: str, end_date: str) -> str:
    return SCHEDULE_RANGE_URL_TEMPLATE.format(start_date=start_date, end_date=end_date)


def fetch_schedule_games(
    start_date: str,
    end_date: str,
    requested_game_pks: Iterable[str],
    game_type_codes: Iterable[str],
) -> List[dict]:
    requested_pks = {str(game_pk) for game_pk in requested_game_pks if game_pk}
    allowed_game_types = set(game_type_codes)
    raw_schedule = mlb.fetch_json(schedule_range_url(start_date, end_date))
    schedule_games: List[dict] = []
    for game_date in raw_schedule.get("dates", []):
        official_date = str(game_date.get("date", "")).strip()
        for raw_game in game_date.get("games", []):
            game_pk = str(raw_game.get("gamePk", "")).strip()
            if requested_pks and game_pk not in requested_pks:
                continue
            if str(raw_game.get("officialDate", "")).strip() != official_date:
                continue
            if str(raw_game.get("gameType", "")).upper() not in allowed_game_types:
                continue
            normalized = dict(raw_game)
            normalized["gamePk"] = game_pk
            normalized["gameDateLocal"] = official_date
            normalized["scheduleSourceUrl"] = schedule_range_url(start_date, end_date)
            schedule_games.append(normalized)
    schedule_games.sort(key=lambda game: (game["gameDateLocal"], int(game["gamePk"])))
    return schedule_games


def build_existing_games_query(start_date: str, end_date: str) -> str:
    start_value = f'"{start_date}T00:00:00Z"^^xsd:dateTime'
    end_value = f'"{end_date}T00:00:00Z"^^xsd:dateTime'
    return f"""
    SELECT ?item ?itemLabel ?entityUrl ?team WHERE {{
      ?item wdt:P31 wd:{mlb.BASEBALL_GAME_QID};
            wdt:P118 wd:{mlb.MLB_LEAGUE_QID};
            wdt:P585 ?date.
      FILTER(?date >= {start_value} && ?date <= {end_value})
      OPTIONAL {{ ?item wdt:P856 ?entityUrl. }}
      OPTIONAL {{ ?item wdt:P1923 ?team. }}
      SERVICE wikibase:label {{ bd:serviceParam wikibase:language "en". }}
    }}
    ORDER BY ?itemLabel
    """.strip()


def load_existing_games(start_date: str, end_date: str) -> Dict[str, dict]:
    results = mlb.run_sparql(build_existing_games_query(start_date, end_date))
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
            row["entity_game_pk"] = mlb.extract_mlb_game_pk_from_url(entity_url)
        team_url = binding.get("team", {}).get("value", "")
        if team_url:
            row["team_qids"].add(team_url.rsplit("/", 1)[-1])
    for row in rows.values():
        row["team_qids"] = sorted(row["team_qids"])
        row["team_key"] = tuple(sorted(row["team_qids"]))
    return rows


def is_search_result_with_keywords(result: dict, keywords: Iterable[str]) -> bool:
    description = str(result.get("description", "") or "").lower()
    label = str(result.get("label", "") or "").lower()
    return any(keyword in description for keyword in keywords) or any(keyword in label for keyword in keywords)


def resolve_entity_qid(name: str, cache: Dict[str, str], description_keywords: Iterable[str]) -> str:
    normalized_name = str(name or "").strip()
    if not normalized_name:
        return ""
    if normalized_name in cache:
        return cache[normalized_name]
    normalized_key = mlb.normalize_lookup_key(normalized_name)
    results: List[dict] = []
    for attempt in range(1, 2):
        try:
            results = mlb.fetch_entity_search(normalized_name)
            break
        except (HTTPError, URLError, OSError):
            if attempt == 1:
                results = []
            else:
                time.sleep(float(attempt))
    for result in results:
        result_label = str(result.get("label", "") or "")
        result_match = str(result.get("match", {}).get("text", "") or "")
        if mlb.normalize_lookup_key(result_label) != normalized_key and mlb.normalize_lookup_key(result_match) != normalized_key:
            continue
        if not is_search_result_with_keywords(result, description_keywords):
            continue
        cache[normalized_name] = result["id"]
        return result["id"]
    cache[normalized_name] = ""
    return ""


def resolve_team_qid(team_name: str, current_team_qids: Dict[str, str], cache: Dict[str, str]) -> str:
    if team_name in current_team_qids:
        return current_team_qids[team_name]
    return resolve_entity_qid(team_name, cache, TEAM_DESCRIPTION_KEYWORDS)


def resolve_venue_qid(venue_name: str, cache: Dict[str, str]) -> str:
    return resolve_entity_qid(venue_name, cache, VENUE_DESCRIPTION_KEYWORDS)


def uses_vs_connector(game: dict) -> bool:
    return str(game.get("gameType", "")).upper() == "A"


def is_doubleheader_game(game: dict) -> bool:
    return str(game.get("doubleHeader", "N")).upper() != "N" or int(game.get("gameNumber", 1) or 1) > 1


def build_item_label(game: dict, away_label: str, home_label: str) -> str:
    connector = "vs" if uses_vs_connector(game) else "at"
    date_label = mlb.format_item_label_date(game["gameDateLocal"])
    if is_doubleheader_game(game):
        return f"{away_label} {connector} {home_label} (Game {int(game.get('gameNumber', 1) or 1)}, {date_label})"
    return f"{away_label} {connector} {home_label} ({date_label})"


def build_item_description(game: dict, venue_label: str) -> str:
    base_phrase = mlb.build_game_context_description_fragment(game)
    date_text = mlb.format_description_date(game["gameDateLocal"])
    prefix = "Major League Baseball"
    if base_phrase == "All-Star Game":
        prefix = "Major League Baseball All-Star Game"
        phrase = ""
    else:
        phrase = f" {base_phrase}"
    doubleheader_phrase = ""
    if is_doubleheader_game(game):
        doubleheader_phrase = f" doubleheader game {int(game.get('gameNumber', 1) or 1)}"
    venue_phrase = f" at {venue_label}" if venue_label else ""
    return f"{prefix}{phrase}{doubleheader_phrase}{venue_phrase} on {date_text}."


def build_schedule_snapshot(
    schedule_game: dict,
    current_team_qids: Dict[str, str],
    team_cache: Dict[str, str],
    venue_cache: Dict[str, str],
    retrieved_date: str,
) -> Optional[dict]:
    home_team_data = schedule_game.get("teams", {}).get("home", {}).get("team", {})
    away_team_data = schedule_game.get("teams", {}).get("away", {}).get("team", {})
    home_label = mlb.normalize_team_label(home_team_data)
    away_label = mlb.normalize_team_label(away_team_data)
    home_qid = resolve_team_qid(home_label, current_team_qids, team_cache)
    away_qid = resolve_team_qid(away_label, current_team_qids, team_cache)
    if not home_qid or not away_qid:
        return None
    venue_label = str(schedule_game.get("venue", {}).get("name", "")).strip()
    venue_qid = resolve_venue_qid(venue_label, venue_cache) if venue_label else ""
    game_pk = str(schedule_game.get("gamePk", "")).strip()
    return {
        "game_pk": game_pk,
        "label": build_item_label(schedule_game, away_label, home_label),
        "description": build_item_description(schedule_game, venue_label),
        "entity_url": mlb.build_game_entity_url(schedule_game),
        "api_endpoint_url": mlb.LIVE_FEED_URL_TEMPLATE.format(game_pk=game_pk),
        "reference_url": schedule_game["scheduleSourceUrl"],
        "retrieved_date": retrieved_date,
        "official_date": schedule_game["gameDateLocal"],
        "home_team_qid": home_qid,
        "away_team_qid": away_qid,
        "home_team_label": home_label,
        "away_team_label": away_label,
        "venue_qid": venue_qid,
    }


def find_matching_time_claim(entity: dict, date_string: str) -> Optional[dict]:
    target_time = f"+{date_string}T00:00:00Z"
    return mlb.find_matching_claim(entity, "P585", target_time)


def ensure_time_claim(entity: dict, qid: str, date_string: str, reference_url: str, retrieved_date: str) -> dict:
    claim = find_matching_time_claim(entity, date_string)
    if claim is None:
        claim = mlb.create_claim(qid, "P585", "time", mlb.time_value(date_string))
        mlb.append_claim(entity, "P585", claim)
    mlb.ensure_reference(claim, reference_url, retrieved_date)
    return claim


def ensure_game_entity_url(entity: dict, qid: str, snapshot: dict) -> None:
    claim = None
    for existing_claim in entity.get("claims", {}).get("P856", []):
        url_value = existing_claim.get("mainsnak", {}).get("datavalue", {}).get("value", "")
        if mlb.extract_mlb_game_pk_from_url(url_value) == snapshot["game_pk"]:
            claim = existing_claim
            break
    if claim is None:
        claim = mlb.ensure_url_claim(entity, qid, "P856", snapshot["entity_url"], snapshot["reference_url"], snapshot["retrieved_date"])
    else:
        mlb.ensure_reference(claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_https_api_claim(entity: dict, qid: str, snapshot: dict) -> None:
    api_claim = mlb.find_matching_claim(entity, "P6269", snapshot["api_endpoint_url"])
    if api_claim is None:
        api_claim = mlb.create_claim(qid, "P6269", "url", snapshot["api_endpoint_url"])
        mlb.append_claim(entity, "P6269", api_claim)
    mlb.ensure_single_item_qualifier(api_claim, "P2700", mlb.HTTPS_QID)
    mlb.ensure_reference(api_claim, snapshot["reference_url"], snapshot["retrieved_date"])


def ensure_team_claims(entity: dict, qid: str, snapshot: dict) -> None:
    for team_qid, role_qid in [
        (snapshot["home_team_qid"], mlb.HOME_TEAM_ROLE_QID),
        (snapshot["away_team_qid"], mlb.AWAY_TEAM_ROLE_QID),
    ]:
        claim = mlb.find_team_claim(entity, team_qid)
        if claim is None:
            claim = mlb.create_claim(qid, "P1923", "wikibase-item", team_qid)
            mlb.append_claim(entity, "P1923", claim)
        mlb.ensure_optional_item_qualifier(claim, "P3831", role_qid)
        mlb.ensure_reference(claim, snapshot["reference_url"], snapshot["retrieved_date"])


def build_item_data(snapshot: dict) -> dict:
    qid = "Q0"
    entity = {
        "labels": {"en": {"language": "en", "value": snapshot["label"]}},
        "descriptions": {"en": {"language": "en", "value": snapshot["description"]}},
        "claims": {},
    }
    mlb.ensure_item_claim(entity, qid, "P31", mlb.BASEBALL_GAME_QID, snapshot["reference_url"], snapshot["retrieved_date"])
    mlb.ensure_item_claim(entity, qid, "P118", mlb.MLB_LEAGUE_QID, snapshot["reference_url"], snapshot["retrieved_date"])
    mlb.ensure_item_claim(entity, qid, "P641", "Q5369", snapshot["reference_url"], snapshot["retrieved_date"])
    ensure_time_claim(entity, qid, snapshot["official_date"], snapshot["reference_url"], snapshot["retrieved_date"])
    if snapshot["venue_qid"]:
        mlb.ensure_item_claim(entity, qid, "P276", snapshot["venue_qid"], snapshot["reference_url"], snapshot["retrieved_date"])
    ensure_game_entity_url(entity, qid, snapshot)
    ensure_https_api_claim(entity, qid, snapshot)
    ensure_team_claims(entity, qid, snapshot)
    return mlb.build_entity_edit_data(entity)


def ensure_existing_item(entity: dict, snapshot: dict) -> bool:
    original_payload = mlb.serialize_entity_edit_data(mlb.build_entity_edit_data(entity))
    qid = entity["id"]
    if not entity.get("descriptions", {}).get("en", {}).get("value", "").strip():
        entity.setdefault("descriptions", {})["en"] = {"language": "en", "value": snapshot["description"]}
    mlb.ensure_item_claim(entity, qid, "P31", mlb.BASEBALL_GAME_QID, snapshot["reference_url"], snapshot["retrieved_date"])
    mlb.ensure_item_claim(entity, qid, "P118", mlb.MLB_LEAGUE_QID, snapshot["reference_url"], snapshot["retrieved_date"])
    mlb.ensure_item_claim(entity, qid, "P641", "Q5369", snapshot["reference_url"], snapshot["retrieved_date"])
    ensure_time_claim(entity, qid, snapshot["official_date"], snapshot["reference_url"], snapshot["retrieved_date"])
    if snapshot["venue_qid"]:
        mlb.ensure_item_claim(entity, qid, "P276", snapshot["venue_qid"], snapshot["reference_url"], snapshot["retrieved_date"])
    ensure_game_entity_url(entity, qid, snapshot)
    ensure_https_api_claim(entity, qid, snapshot)
    ensure_team_claims(entity, qid, snapshot)
    updated_payload = mlb.serialize_entity_edit_data(mlb.build_entity_edit_data(entity))
    return updated_payload != original_payload


def create_item(session: mlb.WikidataApiSession, snapshot: dict) -> str:
    data = build_item_data(snapshot)
    if session.dry_run:
        log_progress(f"DRY RUN create item: {snapshot['label']}")
        return "Q0"
    response = session.write("wbeditentity", "Create MLB game item", new="item", data=mlb.serialize_entity_edit_data(data))
    return str(response.get("entity", {}).get("id", "")).strip()


def find_matching_existing_row(
    existing_rows_by_qid: Dict[str, dict],
    schedule_game: dict,
    snapshot: dict,
) -> Tuple[Optional[dict], bool]:
    by_game_pk = {
        row["entity_game_pk"]: row
        for row in existing_rows_by_qid.values()
        if row.get("entity_game_pk")
    }
    by_team_key: Dict[Tuple[str, ...], List[dict]] = {}
    for row in existing_rows_by_qid.values():
        team_key = tuple(row.get("team_key", ()))
        if not team_key:
            continue
        by_team_key.setdefault(team_key, []).append(row)

    direct = by_game_pk.get(snapshot["game_pk"])
    if direct is not None:
        return direct, False

    team_key = tuple(sorted((snapshot["away_team_qid"], snapshot["home_team_qid"])))
    candidates = by_team_key.get(team_key, [])
    if not candidates:
        return None, False
    if len(candidates) == 1 and not is_doubleheader_game(schedule_game):
        return candidates[0], False
    matching_labels = {snapshot["label"]}
    for row in candidates:
        if row.get("label", "") in matching_labels:
            return row, False
    return None, len(candidates) > 1


def process_schedule(
    session: mlb.WikidataApiSession,
    schedule_games: List[dict],
    existing_rows_by_qid: Dict[str, dict],
    current_team_qids: Dict[str, str],
    team_cache: Dict[str, str],
    venue_cache: Dict[str, str],
    max_create: int,
) -> Dict[str, int]:
    counts = {"scheduled": len(schedule_games), "created": 0, "updated": 0, "unchanged": 0, "skipped": 0, "errors": 0, "remaining": 0}
    retrieved_date = datetime.now(ZoneInfo(TIMEZONE)).date().isoformat()
    for index, game in enumerate(schedule_games):
        snapshot = build_schedule_snapshot(game, current_team_qids, team_cache, venue_cache, retrieved_date)
        if snapshot is None:
            counts["skipped"] += 1
            if VERBOSE:
                away_label = mlb.normalize_team_label(game.get("teams", {}).get("away", {}).get("team", {}))
                home_label = mlb.normalize_team_label(game.get("teams", {}).get("home", {}).get("team", {}))
                log_progress(f"Skipping MLB game with unresolved team QIDs: {away_label} at {home_label} ({game['gameDateLocal']})")
            continue

        existing_row, ambiguous_match = find_matching_existing_row(existing_rows_by_qid, game, snapshot)
        if ambiguous_match:
            counts["skipped"] += 1
            if VERBOSE:
                log_progress(
                    f"Skipping ambiguous MLB schedule match for {snapshot['label']}: "
                    "multiple same-date Wikidata items exist and no gamePk URL match was available."
                )
            continue
        if existing_row is None:
            if counts["created"] >= max(0, max_create):
                counts["remaining"] += 1
                continue
            try:
                new_qid = create_item(session, snapshot)
            except RuntimeError as exc:
                counts["errors"] += 1
                if VERBOSE:
                    log_progress(f"Failed creating {snapshot['label']}: {exc}")
                if mlb.is_wikidata_maxlag_error(exc):
                    break
                continue
            counts["created"] += 1
            if not session.dry_run and new_qid:
                existing_rows_by_qid[new_qid] = {
                    "qid": new_qid,
                    "label": snapshot["label"],
                    "entity_url": snapshot["entity_url"],
                    "entity_game_pk": snapshot["game_pk"],
                    "team_qids": sorted([snapshot["away_team_qid"], snapshot["home_team_qid"]]),
                    "team_key": tuple(sorted([snapshot["away_team_qid"], snapshot["home_team_qid"]])),
                }
                log_event(f"Created MLB game item {new_qid} for {snapshot['label']}.")
            elif session.dry_run:
                log_event(f"Would create MLB game item for {snapshot['label']}.")
            continue

        try:
            entity = mlb.fetch_entity(existing_row["qid"])
            changed = ensure_existing_item(entity, snapshot)
        except Exception as exc:
            counts["errors"] += 1
            if VERBOSE:
                log_progress(f"Failed preparing update for {snapshot['label']}: {exc}")
            continue
        if not changed:
            counts["unchanged"] += 1
            continue
        try:
            if session.dry_run:
                log_progress(f"DRY RUN update item: {snapshot['label']}")
            else:
                session.edit_entity(existing_row["qid"], mlb.build_entity_edit_data(entity), "Seed MLB game schedule item", baserevid=entity.get("lastrevid"))
            counts["updated"] += 1
            log_event(f"Seeded MLB schedule data for {snapshot['label']}.")
        except RuntimeError as exc:
            counts["errors"] += 1
            if VERBOSE:
                log_progress(f"Failed updating {snapshot['label']}: {exc}")
            if mlb.is_wikidata_maxlag_error(exc):
                break
    return counts


if __name__ == "__main__":
    args = parse_args()
    set_verbose(args.verbose)
    mlb.ensure_dir(LOOKUP_CACHE_DIR)

    now_local = datetime.now(ZoneInfo(TIMEZONE))
    start_date, end_date = determine_date_range(args, now_local)
    requested_game_pks = list(dict.fromkeys(str(game_pk).strip() for game_pk in args.game_pk if str(game_pk).strip()))
    game_type_codes = normalize_game_type_codes([args.game_type_codes])

    schedule_games = fetch_schedule_games(start_date, end_date, requested_game_pks, game_type_codes)
    if not schedule_games:
        if VERBOSE:
            log_progress(f"No MLB schedule games found between {start_date} and {end_date}.")
        raise SystemExit(0)

    current_team_qids = mlb.load_current_team_qids()
    team_cache = load_lookup_cache(TEAM_QID_CACHE_PATH)
    venue_cache = load_lookup_cache(VENUE_QID_CACHE_PATH)
    existing_rows_by_qid = load_existing_games(start_date, end_date)

    session = mlb.WikidataApiSession(dry_run=args.dry_run)
    if not args.dry_run:
        session.login_from_env()

    counts = process_schedule(
        session,
        schedule_games,
        existing_rows_by_qid,
        current_team_qids,
        team_cache,
        venue_cache,
        args.max_create,
    )
    save_lookup_cache(TEAM_QID_CACHE_PATH, team_cache)
    save_lookup_cache(VENUE_QID_CACHE_PATH, venue_cache)

    if VERBOSE:
        log_progress(
            f"Range {start_date}..{end_date}: scheduled={counts['scheduled']}, created={counts['created']}, "
            f"updated={counts['updated']}, unchanged={counts['unchanged']}, skipped={counts['skipped']}, "
            f"remaining={counts['remaining']}, errors={counts['errors']}"
        )
    raise SystemExit(0 if counts["errors"] == 0 else 1)
