import os
import json
import html
import math
import re
import difflib
import heapq
import time
import hashlib
import threading
import subprocess
from queue import Queue, Empty
from datetime import datetime
from collections import defaultdict, Counter

import pandas as pd
import folium
from folium import plugins

# ---------------------------
# Optional web server (for live updates)
# ---------------------------
try:
    from flask import Flask, Response, send_from_directory, render_template_string, request
except ImportError as e:
    raise SystemExit(
        "\nFlask is required for live hosting.\n"
        "Install it with:\n"
        "  pip install flask\n"
    ) from e

# =========================================================
# 0. SETTINGS
# =========================================================

BASE_DIR = os.path.abspath(os.path.dirname(__file__))

MASTER_TRACKER_PATH = os.path.join(BASE_DIR, "MASTER TRACKER(RAW DATA).csv")
CENTRELINE_PATH = os.path.join(BASE_DIR, "Centreline - Version 2 - 4326.csv")

OUTPUT_DIR = os.path.join(BASE_DIR, "outputs_work_orders")
os.makedirs(OUTPUT_DIR, exist_ok=True)

OUTPUT_HTML = os.path.join(OUTPUT_DIR, "work_orders_map.html")
OUTPUT_GEOJSON = os.path.join(OUTPUT_DIR, "work_orders.geojson")
OUTPUT_MAPPED_CSV = os.path.join(OUTPUT_DIR, "master_tracker_mapped.csv")
OUTPUT_SKIPPED_CSV = os.path.join(OUTPUT_DIR, "master_tracker_skipped.csv")
OUTPUT_INTAKE_DEBUG_CSV = os.path.join(OUTPUT_DIR, "intake_submissions_debug.csv")

POLL_INTERVAL_SECONDS = 30
MIN_SIM_LOCATION = 0.80
MIN_SIM_CROSS = 0.78

HOST = "127.0.0.1"
PORT = 8008

DRAW_INTERSECTION_POINTS = True
INTERSECTION_POINT_RADIUS = 4
INTERSECTION_POINT_OPACITY = 0.95
INTERSECTION_POINT_FILL_OPACITY = 0.85
INTERSECTION_POINTS_SHOW_BY_DEFAULT = True

DRAW_WO_SEGMENTS = True
SEGMENT_OPACITY = 0.01
SEGMENT_WEIGHT = 12

# =========================================================
# 0B. DATA-ENTRY (INTAKE) SETTINGS
# =========================================================

INTAKE_PATH = os.path.join(BASE_DIR, "intake_submissions.csv")
INTAKE_POLL_SECONDS = 10

UI_USER = os.environ.get("WO_UI_USER", "").strip()
UI_PASS = os.environ.get("WO_UI_PASS", "").strip()

STRICT_DISTRICTS = []
STRICT_WARDS = []
STRICT_SUPERVISORS = []
STRICT_SHIFTS = []
STRICT_TYPES = []

FILE_LOCK = threading.RLock()
BUILD_LOCK = threading.Lock()

LAST_MASTER_WRITE_BY_INTAKE_AT = 0.0
LAST_MASTER_WRITE_LOCK = threading.Lock()

# Last applied intake batch (for UI announcements)
LAST_INTAKE_APPLIED_LOCK = threading.Lock()
LAST_INTAKE_APPLIED = []          # list[dict]
LAST_INTAKE_APPLIED_AT = 0.0      # float epoch seconds


# =========================================================
# 1. LOGGING + NOTIFICATIONS
# =========================================================

def log(msg: str):
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{stamp}] {msg}", flush=True)


def notify_user(title: str, message: str):
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print("\n" + "!" * 70)
    print(f"[{stamp}] {title}")
    print(message)
    print("!" * 70 + "\n")

    try:
        if os.uname().sysname.lower() == "darwin":
            script = f'display notification "{message}" with title "{title}"'
            subprocess.run(["osascript", "-e", script], check=False)
    except Exception:
        pass


# =========================================================
# 2. FILE FINGERPRINTING
# =========================================================

def sha256_of_file(path: str, chunk_size: int = 1024 * 1024) -> str:
    if not os.path.exists(path):
        return ""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(chunk_size)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def file_fingerprint(path: str):
    if not os.path.exists(path):
        return ("MISSING", 0, "")
    st = os.stat(path)
    mtime = int(st.st_mtime)
    size = int(st.st_size)
    sha = sha256_of_file(path)
    return (mtime, size, sha)


# =========================================================
# 3. INTAKE SYSTEM
# =========================================================

MASTER_COLUMNS = [
    "WO",
    "District\n",
    "Ward\n",
    "Date\n",
    "Shift\n",
    "Supervisor\n",
    "Location",
    "From ",
    "To",
    "Type (Road Class/ School, Bridge)\n",
]

FORM_TO_MASTER = {
    "WO": "WO",
    "District__NL": "District\n",
    "Ward__NL": "Ward\n",
    "Date__NL": "Date\n",
    "Shift__NL": "Shift\n",
    "Supervisor__NL": "Supervisor\n",
    "Location": "Location",
    "From": "From ",
    "To": "To",
    "Type__NL": "Type (Road Class/ School, Bridge)\n",
}
MASTER_TO_FORM = {v: k for k, v in FORM_TO_MASTER.items()}


def ensure_intake_file():
    if not os.path.exists(INTAKE_PATH):
        log(f"INTAKE: creating new intake file at {INTAKE_PATH}")
        df = pd.DataFrame(columns=MASTER_COLUMNS + ["__submitted_at", "__submission_id"])
        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")


def compute_submission_id(row_dict: dict) -> str:
    base = {k: str(row_dict.get(k, "")).strip() for k in MASTER_COLUMNS}
    raw = json.dumps(base, sort_keys=True, ensure_ascii=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]


def basic_auth_required() -> bool:
    return bool(UI_USER and UI_PASS)


def check_basic_auth(req) -> bool:
    auth = req.authorization
    if not auth:
        return False
    return auth.username == UI_USER and auth.password == UI_PASS


def require_auth_or_401():
    if not basic_auth_required():
        return None
    if check_basic_auth(request):
        return None
    return Response(
        "Authentication required", 401,
        {"WWW-Authenticate": 'Basic realm="WorkOrders"'}
    )


def normalize_blank(s):
    if s is None:
        return ""
    return str(s).strip()


def validate_submission(values: dict, allowed_sets: dict, streets_set: set):
    errors = []

    required = [
        "WO", "District\n", "Ward\n", "Date\n", "Shift\n", "Supervisor\n",
        "Location", "Type (Road Class/ School, Bridge)\n"
    ]
    for k in required:
        if not normalize_blank(values.get(k)):
            errors.append(f"Missing required field: {k}")

    fromv = normalize_blank(values.get("From "))
    tov = normalize_blank(values.get("To"))
    loc = normalize_blank(values.get("Location"))

    if "ENTIRE STREET" not in loc.upper():
        if (not fromv) and (not tov):
            errors.append("Provide at least one of From or To (unless Location contains 'ENTIRE STREET').")

    def check_allowed(field, label):
        val = normalize_blank(values.get(field))
        if not val:
            return
        allowed = allowed_sets.get(field) or set()
        if allowed and val not in allowed:
            errors.append(f"{label} not allowed: '{val}'")

    check_allowed("District\n", "District")
    check_allowed("Ward\n", "Ward")
    check_allowed("Supervisor\n", "Supervisor")
    check_allowed("Shift\n", "Shift")
    check_allowed("Type (Road Class/ School, Bridge)\n", "Type")

    def norm_street_for_check(s: str) -> str:
        return re.sub(r"\s+", " ", str(s).upper().strip())

    def is_special_street(s: str) -> bool:
        u = norm_street_for_check(s)
        if not u or u in ("-", ""):
            return True
        if "ENTIRE STREET" in u:
            return True
        if "DEAD END" in u or "DEAD-END" in u or "DEADEND" in u:
            return True
        return False

    def fuzzy_in_set(val: str, sset: set, min_ratio=0.86):
        if val in sset:
            return True
        if len(val) < 3:
            return False
        prefix = val[0]
        cands = [x for x in sset if x and x[0] == prefix]
        cands = cands[:5000]
        best = 0.0
        for c in cands:
            sc = difflib.SequenceMatcher(None, val, c).ratio()
            if sc > best:
                best = sc
                if best >= min_ratio:
                    return True
        return False

    for field in ["Location", "From ", "To"]:
        raw = normalize_blank(values.get(field))
        if not raw or is_special_street(raw):
            continue
        u = norm_street_for_check(raw)
        if not fuzzy_in_set(u, streets_set):
            errors.append(f"{field} does not look like a valid street in centreline: '{raw}'")

    return errors


def append_to_intake(values: dict):
    ensure_intake_file()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    row = {k: normalize_blank(values.get(k, "")) for k in MASTER_COLUMNS}
    submission_id = compute_submission_id(row)

    row["__submitted_at"] = now
    row["__submission_id"] = submission_id

    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        if "__submission_id" in df.columns and submission_id in set(df["__submission_id"].astype(str)):
            log(f"INTAKE: duplicate submission ignored (id={submission_id})")
            return submission_id, False

        df = pd.concat([df, pd.DataFrame([row])], ignore_index=True)
        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")

    log(f"INTAKE: accepted submission id={submission_id} WO={row.get('WO')}")
    return submission_id, True


def get_intake_submission_details(submission_id: str) -> dict:
    """
    Returns a clean dict of the intake row, if found. Otherwise {}.
    """
    sid = (submission_id or "").strip()
    if not sid or not os.path.exists(INTAKE_PATH):
        return {}
    try:
        df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
    except Exception:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")
        except Exception:
            return {}

    if "__submission_id" not in df.columns:
        return {}
    hit = df[df["__submission_id"].astype(str) == sid]
    if hit.empty:
        return {}
    r = hit.iloc[-1].to_dict()
    out = {}
    for k in MASTER_COLUMNS + ["__submitted_at", "__submission_id"]:
        out[k] = str(r.get(k, "")).strip()
    return out


def apply_intake_to_master():
    """
    Applies any new intake submissions to MASTER_TRACKER_PATH.

    Returns:
        (applied_count: int, applied_items: list[dict])
    """
    global LAST_MASTER_WRITE_BY_INTAKE_AT

    ensure_intake_file()
    if not os.path.exists(MASTER_TRACKER_PATH):
        log("INTAKE APPLY: master tracker missing; cannot apply.")
        return 0, []

    with FILE_LOCK:
        log("INTAKE APPLY: loading intake + master...")
        try:
            intake = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            intake = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        master = pd.read_csv(MASTER_TRACKER_PATH, encoding="latin-1")

        if "__submission_id" not in master.columns:
            master["__submission_id"] = ""

        intake_ids = set(intake.get("__submission_id", pd.Series([], dtype=str)).astype(str))
        master_ids = set(master.get("__submission_id", pd.Series([], dtype=str)).astype(str))

        new_ids = [sid for sid in intake_ids if sid and sid not in master_ids]
        if not new_ids:
            log("INTAKE APPLY: no new submissions to apply.")
            return 0, []

        new_rows = intake[intake["__submission_id"].astype(str).isin(set(new_ids))].copy()

        to_append = []
        master_cols = list(master.columns)
        applied_items = []

        for _, r in new_rows.iterrows():
            row = {c: "" for c in master_cols}
            for col in MASTER_COLUMNS:
                if col in row:
                    row[col] = r.get(col, "")
            row["__submission_id"] = r.get("__submission_id", "")
            to_append.append(row)

            applied_items.append({
                "__submission_id": str(r.get("__submission_id", "")).strip(),
                "__submitted_at": str(r.get("__submitted_at", "")).strip(),
                "WO": str(r.get("WO", "")).strip(),
                "District": str(r.get("District\n", "")).strip(),
                "Ward": str(r.get("Ward\n", "")).strip(),
                "Date": str(r.get("Date\n", "")).strip(),
                "Shift": str(r.get("Shift\n", "")).strip(),
                "Supervisor": str(r.get("Supervisor\n", "")).strip(),
                "Type": str(r.get("Type (Road Class/ School, Bridge)\n", "")).strip(),
                "Location": str(r.get("Location", "")).strip(),
                "From": str(r.get("From ", "")).strip(),
                "To": str(r.get("To", "")).strip(),
            })

        before = len(master)
        master = pd.concat([master, pd.DataFrame(to_append)], ignore_index=True)
        master.to_csv(MASTER_TRACKER_PATH, index=False, encoding="latin-1")

        with LAST_MASTER_WRITE_LOCK:
            LAST_MASTER_WRITE_BY_INTAKE_AT = time.time()

        after = len(master)
        applied = after - before
        log(f"INTAKE APPLY: applied {applied} new row(s) into MASTER_TRACKER.")
        return applied, applied_items


# =========================================================
# 4. BUILD EVERYTHING (MAP BUILD)
# =========================================================

def build_everything():
    with BUILD_LOCK:
        log("==================================================")
        log(f"BUILD START: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        log("==================================================")

        intake_ids_set = set()
        try:
            if os.path.exists(INTAKE_PATH):
                _intake = pd.read_csv(INTAKE_PATH, encoding="utf-8")
                if "__submission_id" in _intake.columns:
                    intake_ids_set = set(_intake["__submission_id"].fillna("").astype(str).tolist())
        except Exception:
            try:
                _intake = pd.read_csv(INTAKE_PATH, encoding="latin-1")
                if "__submission_id" in _intake.columns:
                    intake_ids_set = set(_intake["__submission_id"].fillna("").astype(str).tolist())
            except Exception:
                intake_ids_set = set()

        intake_debug_rows = []

        def normalize_street_name(name: str) -> str:
            if not isinstance(name, str):
                return ""
            n = name.upper().strip()

            n = re.sub(r"^(EB|WB|NB|SB)\s*[/\-]?\s+", "", n)
            n = re.sub(r"\s*-\s*(SB|NB|EB|WB)\s*$", "", n)
            n = re.sub(r"\s+(SB|NB|EB|WB)\s*$", "", n)

            n = n.replace("-", " ")
            n = re.sub(r"\s+", " ", n)
            n = re.sub(r"\bDVP\b", "DON VALLEY PARKWAY", n)

            replacements = {
                " RD": " ROAD",
                " ST": " STREET",
                " AVE": " AVENUE",
                " BLVD": " BOULEVARD",
                " HWY": " HIGHWAY",
                " PKWY": " PARKWAY",
                " DR": " DRIVE",
                " CRES": " CRESCENT",
                " CR": " CRESCENT",
                " LN": " LANE",
                " SQ": " SQUARE",
                " CIR": " CIRCLE",
                " PL": " PLACE",
            }
            for short, full in replacements.items():
                n = re.sub(rf"{short}($|\s)", f"{full} ", n)

            n = re.sub(r"\s+", " ", n).strip()

            dir_map = {"N": "NORTH", "S": "SOUTH", "E": "EAST", "W": "WEST"}
            parts = n.split()
            if parts and parts[-1] in dir_map:
                parts[-1] = dir_map[parts[-1]]
                n = " ".join(parts)

            return n.strip()

        # --- Direction-aware matching helpers ---
        def dir_tag(s: str) -> str:
            """
            Returns 'EAST','WEST','NORTH','SOUTH' if present as a standalone token.
            Otherwise ''.
            """
            if not s:
                return ""
            toks = set(re.split(r"\s+", s.upper().strip()))
            for d in ("EAST", "WEST", "NORTH", "SOUTH"):
                if d in toks:
                    return d
            return ""

        OPP = {"EAST": "WEST", "WEST": "EAST", "NORTH": "SOUTH", "SOUTH": "NORTH"}

        STREET_TYPE_PATTERN = (
            r"(ST|STREET|AVE|AVENUE|RD|ROAD|BLVD|BOULEVARD|DR|DRIVE|CRES|CRESCENT|"
            r"LN|LANE|TR|TRAIL|PKWY|PARKWAY|SQ|SQUARE|CIR|CIRCLE|PL|PLACE|HWY|HIGHWAY)"
        )

        CORE_STREET_REGEX = re.compile(
            rf"([A-Z0-9'. ]+\s{STREET_TYPE_PATTERN}(?:\s+[NESW])?)\b"
        )

        def extract_street_token(raw: str) -> str:
            if not isinstance(raw, str):
                return ""
            t = raw.upper().strip()

            if t in ("-", ""):
                return ""

            special_codes = {
                "LSBW": "LAKE SHORE BOULEVARD WEST",
                "LSBE": "LAKE SHORE BOULEVARD EAST",
            }
            if t in special_codes:
                return special_codes[t]

            if "ENTIRE STREET" in t:
                return ""

            t = re.sub(r"^\(IN PROGRESS\)\s*", "", t)
            t = re.sub(r"^\(CONTINUATION\)\s*", "", t)
            t = re.sub(r"^POLLING SITES?:\s*\d*\s*", "", t)
            t = re.sub(r"^POLLING SITES?:\s*", "", t)

            t = re.sub(r"\s+BRIDGE OVER.*$", "", t)
            t = re.sub(r"\s+BRIDGE\b.*$", "", t)
            t = re.sub(r"\s+OVER CN RAILS.*$", "", t)
            t = re.sub(r"\s+OVER RAIL.*$", "", t)
            t = re.sub(r"\s+OVER HWY.*$", "", t)
            t = re.sub(r"\s+OVER 401.*$", "", t)

            if re.search(r"\bDVP\b", t):
                return "DVP"
            if re.search(r"\b401\b", t):
                return "HWY 401"
            if re.search(r"\b2A\b", t):
                return "HWY 2A"

            matches = list(CORE_STREET_REGEX.finditer(t))
            if matches:
                return matches[-1].group(1).strip()

            return t

        def compute_multiline_length(multiline):
            total = 0.0
            for line in multiline:
                for (lon1, lat1), (lon2, lat2) in zip(line, line[1:]):
                    dx = lon2 - lon1
                    dy = lat2 - lon1  # intentionally kept as your code; length used only for weights
                    total += math.hypot(dx, dy)
            return total

        def first_point_of_multiline(coords):
            if not coords:
                return None
            for line in coords:
                if line:
                    return line[0]
            return None

        def last_point_of_multiline(coords):
            if not coords:
                return None
            for line in reversed(coords):
                if line:
                    return line[-1]
            return None

        def haversine_m(lat1, lon1, lat2, lon2):
            R = 6371000.0
            phi1 = math.radians(lat1)
            phi2 = math.radians(lat2)
            dphi = math.radians(lat2 - lat1)
            dl = math.radians(lon2 - lon1)
            a = math.sin(dphi / 2.0) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dl / 2.0) ** 2
            c = 2.0 * math.atan2(math.sqrt(a), math.sqrt(1.0 - a))
            return R * c

        def multiline_distance_m(coords_multiline):
            if not coords_multiline:
                return 0.0
            total = 0.0
            for line in coords_multiline:
                if not line or len(line) < 2:
                    continue
                for (lon1, lat1), (lon2, lat2) in zip(line, line[1:]):
                    total += haversine_m(lat1, lon1, lat2, lon2)
            return total

        def fmt_sigfig(x, sig=2):
            try:
                x = float(x)
            except Exception:
                return ""
            if not math.isfinite(x):
                return ""
            if x == 0:
                return "0"
            ax = abs(x)
            p = math.floor(math.log10(ax))
            decimals = max(0, sig - 1 - p)
            val = round(x, decimals)
            return f"{val:,.{decimals}f}"

        intersection_accum = {}

        def add_intersection_coord(intersection_id: int, lon: float, lat: float):
            if intersection_id is None:
                return
            if not (isinstance(lon, (int, float)) and isinstance(lat, (int, float))):
                return
            if intersection_id not in intersection_accum:
                intersection_accum[intersection_id] = [0.0, 0.0, 0]
            intersection_accum[intersection_id][0] += float(lon)
            intersection_accum[intersection_id][1] += float(lat)
            intersection_accum[intersection_id][2] += 1

        def get_intersection_latlng(intersection_id: int):
            v = intersection_accum.get(intersection_id)
            if not v or v[2] <= 0:
                return None
            lon = v[0] / v[2]
            lat = v[1] / v[2]
            return [lat, lon]

        log("Loading input files...")
        if not os.path.exists(MASTER_TRACKER_PATH):
            raise FileNotFoundError(f"MASTER_TRACKER_PATH not found: {MASTER_TRACKER_PATH}")
        if not os.path.exists(CENTRELINE_PATH):
            raise FileNotFoundError(f"CENTRELINE_PATH not found: {CENTRELINE_PATH}")

        master = pd.read_csv(MASTER_TRACKER_PATH, encoding="latin-1")
        centre = pd.read_csv(CENTRELINE_PATH, encoding="latin-1")

        log(f"Centreline rows: {len(centre)}")
        log(f"Master tracker rows: {len(master)}")

        street_edges = defaultdict(list)
        street_nodes = defaultdict(set)
        intersection_to_streets = defaultdict(set)
        bad_geom = 0

        # GLOBAL graph (fallback routing)
        global_edges = []
        global_adj = defaultdict(list)

        for _, row in centre.iterrows():
            name_raw = (
                row.get("LINEAR_NAME_FULL_LEGAL")
                or row.get("LINEAR_NAME_FULL")
                or row.get("LINEAR_NAME")
            )
            norm_name = normalize_street_name(str(name_raw))
            if not norm_name:
                continue

            from_id = row.get("FROM_INTERSECTION_ID")
            to_id = row.get("TO_INTERSECTION_ID")

            if pd.isna(from_id) or pd.isna(to_id):
                continue

            try:
                from_id = int(from_id)
                to_id = int(to_id)
            except (ValueError, TypeError):
                continue

            intersection_to_streets[from_id].add(norm_name)
            intersection_to_streets[to_id].add(norm_name)

            geom_str = row.get("geometry")
            if not isinstance(geom_str, str):
                bad_geom += 1
                continue

            try:
                geom = json.loads(geom_str)
                if geom.get("type") != "MultiLineString":
                    bad_geom += 1
                    continue
                coords = geom.get("coordinates", [])
                if not coords:
                    bad_geom += 1
                    continue
            except Exception:
                bad_geom += 1
                continue

            p_start = first_point_of_multiline(coords)
            p_end = last_point_of_multiline(coords)
            if p_start and len(p_start) >= 2:
                add_intersection_coord(from_id, p_start[0], p_start[1])
            if p_end and len(p_end) >= 2:
                add_intersection_coord(to_id, p_end[0], p_end[1])

            length = compute_multiline_length(coords)

            edge = {"from": from_id, "to": to_id, "coords": coords, "length": length, "street": norm_name}
            street_edges[norm_name].append(edge)
            street_nodes[norm_name].update([from_id, to_id])

            # global graph edge
            ge_idx = len(global_edges)
            global_edges.append(edge)
            global_adj[from_id].append((to_id, ge_idx, length))
            global_adj[to_id].append((from_id, ge_idx, length))

        log(f"Unique streets in centreline (normalized): {len(street_edges)}")
        log(f"Rows with unusable geometry: {bad_geom}")
        log(f"Intersection coords collected: {len(intersection_accum)}")

        street_graphs = {}
        for name, edges in street_edges.items():
            adj = defaultdict(list)
            for i, e in enumerate(edges):
                u = e["from"]
                v = e["to"]
                w = e["length"]
                adj[u].append((v, i, w))
                adj[v].append((u, i, w))
            street_graphs[name] = {"edges": edges, "adj": adj}

        # ✅ FULL + ALPHA ORDERED list of centreline streets for the form (and matching)
        ALL_CENTRE_STREETS = sorted(
            [s for s in street_nodes.keys() if isinstance(s, str) and s.strip()],
            key=lambda x: x.casefold()
        )

        TYPE_TOKENS = {
            " STREET", " AVENUE", " ROAD", " BOULEVARD",
            " DRIVE", " LANE", " CRESCENT", " TRAIL",
            " PARKWAY", " HIGHWAY", " COURT", " PLACE",
            " SQUARE", " CIRCLE"
        }

        DEAD_END_TOKENS = {"DEAD END", "DEAD-END", "DEADEND"}

        def pick_cross_street(intersection_id: int, location_street_key: str) -> str:
            try:
                streets = intersection_to_streets.get(int(intersection_id), set())
            except Exception:
                streets = set()
            cands = [s for s in streets if s and s != location_street_key]
            if not cands:
                return ""
            cands.sort(key=lambda s: (len(s), s))
            return cands[0]

        def style_for_feature(feat):
            props = feat["properties"]
            color = props.get("stroke_color", "red")
            work_type = props.get("Type", "").upper()

            weight = 4
            dash_array = "0"

            if "ARTERIAL" in work_type:
                weight = 6
            elif "COLLECTOR" in work_type:
                weight = 5
            elif "LOCAL" in work_type:
                weight = 3

            if "BRIDGE" in work_type:
                dash_array = "5,5"

            return {"color": color, "weight": weight, "opacity": 0.9, "dashArray": dash_array}

        def style_for_segment(feat):
            props = feat["properties"]
            color = props.get("stroke_color", "red")
            return {"color": color, "weight": SEGMENT_WEIGHT, "opacity": SEGMENT_OPACITY, "dashArray": "0"}

        def similarity(a: str, b: str) -> float:
            return difflib.SequenceMatcher(None, a, b).ratio()

        def has_type_suffix(norm_name: str) -> bool:
            for tok in TYPE_TOKENS:
                if norm_name.endswith(tok):
                    return True
            return False

        def resolve_street_name(norm_name: str, min_ratio: float):
            if not norm_name:
                return None, 0.0

            if norm_name in street_nodes:
                return norm_name, 1.0

            if not has_type_suffix(norm_name):
                candidates = [
                    norm_name + " AVENUE",
                    norm_name + " STREET",
                    norm_name + " ROAD",
                    norm_name + " BOULEVARD",
                    norm_name + " DRIVE",
                    norm_name + " LANE",
                ]
                for cand in candidates:
                    if cand in street_nodes:
                        return cand, 1.0

            in_dir = dir_tag(norm_name)

            best_key = None
            best_score = 0.0

            for cand in ALL_CENTRE_STREETS:
                if not cand:
                    continue
                if len(norm_name) > 3 and len(cand) > 3 and cand[0] != norm_name[0]:
                    continue

                # Direction-aware rejection: EAST should not match WEST etc.
                if in_dir:
                    cand_dir = dir_tag(cand)
                    if cand_dir and cand_dir == OPP.get(in_dir):
                        continue

                score = similarity(norm_name, cand)
                if cand.startswith(norm_name) or norm_name.startswith(cand):
                    score = max(score, 0.9)

                if score > best_score:
                    best_score = score
                    best_key = cand

            if best_key is not None and best_score >= min_ratio:
                return best_key, best_score
            return None, best_score

        def find_intersection_node(street1_key, street2_key):
            nodes1 = street_nodes.get(street1_key)
            nodes2 = street_nodes.get(street2_key)
            if not nodes1 or not nodes2:
                return None
            inter = nodes1 & nodes2
            if not inter:
                return None
            return min(inter)

        def shortest_path_for_street(street_key, start_node, end_node, max_hops=5000):
            g = street_graphs.get(street_key)
            if not g:
                return None
            adj = g["adj"]
            if start_node not in adj or end_node not in adj:
                return None

            heap = [(0.0, start_node, None, None)]
            visited = {}
            hops = 0

            while heap and hops < max_hops:
                dist, node, prev_node, prev_edge = heapq.heappop(heap)
                if node in visited:
                    continue
                visited[node] = (dist, prev_node, prev_edge)
                if node == end_node:
                    break

                for neigh, edge_idx, w in adj[node]:
                    if neigh in visited:
                        continue
                    heapq.heappush(heap, (dist + w, neigh, node, edge_idx))
                hops += 1

            if end_node not in visited:
                return None

            node_path = []
            edge_indices = []
            cur = end_node
            while True:
                node_path.append(cur)
                _, prev_node, prev_edge = visited[cur]
                if prev_node is None:
                    break
                edge_indices.append(prev_edge)
                cur = prev_node

            node_path.reverse()
            edge_indices.reverse()
            return node_path, edge_indices

        def shortest_path_global(start_node, end_node, max_hops=250000):
            if start_node not in global_adj or end_node not in global_adj:
                return None

            heap = [(0.0, start_node, None, None)]
            visited = {}
            hops = 0

            while heap and hops < max_hops:
                dist, node, prev_node, prev_edge = heapq.heappop(heap)
                if node in visited:
                    continue
                visited[node] = (dist, prev_node, prev_edge)
                if node == end_node:
                    break

                for neigh, edge_idx, w in global_adj[node]:
                    if neigh in visited:
                        continue
                    heapq.heappush(heap, (dist + w, neigh, node, edge_idx))
                hops += 1

            if end_node not in visited:
                return None

            node_path = []
            edge_indices = []
            cur = end_node
            while True:
                node_path.append(cur)
                _, prev_node, prev_edge = visited[cur]
                if prev_node is None:
                    break
                edge_indices.append(prev_edge)
                cur = prev_node

            node_path.reverse()
            edge_indices.reverse()
            return node_path, edge_indices

        def build_path_multiline(street_key, node_path, edge_indices):
            g = street_graphs[street_key]
            edges = g["edges"]
            final = []
            for i, edge_idx in enumerate(edge_indices):
                u = node_path[i]
                v = node_path[i + 1]
                e = edges[edge_idx]
                coords = e["coords"]

                if e["from"] == u and e["to"] == v:
                    oriented = coords
                elif e["from"] == v and e["to"] == u:
                    oriented = [list(reversed(line)) for line in coords]
                else:
                    oriented = coords

                final.extend(oriented)
            return final

        def build_path_multiline_global(node_path, edge_indices):
            final = []
            for i, edge_idx in enumerate(edge_indices):
                u = node_path[i]
                v = node_path[i + 1]
                e = global_edges[edge_idx]
                coords = e["coords"]

                if e["from"] == u and e["to"] == v:
                    oriented = coords
                elif e["from"] == v and e["to"] == u:
                    oriented = [list(reversed(line)) for line in coords]
                else:
                    oriented = coords

                final.extend(oriented)
            return final

        def build_edge_segments(street_key, node_path, edge_indices):
            g = street_graphs[street_key]
            edges = g["edges"]
            segments = []
            for i, edge_idx in enumerate(edge_indices):
                u = node_path[i]
                v = node_path[i + 1]
                e = edges[edge_idx]
                coords = e["coords"]

                if e["from"] == u and e["to"] == v:
                    oriented = coords
                elif e["from"] == v and e["to"] == u:
                    oriented = [list(reversed(line)) for line in coords]
                else:
                    oriented = coords

                segments.append({"u": int(u), "v": int(v), "coords": oriented})
            return segments

        def full_street_multiline(street_key):
            edges = street_edges.get(street_key, [])
            all_coords = []
            for e in edges:
                all_coords.extend(e["coords"])
            return all_coords

        def make_supervisor_key(name: str) -> str:
            s = str(name).upper().strip()
            if not s:
                return ""
            key = re.sub(r"[^A-Z0-9]+", "_", s)
            return key.strip("_")

        def make_supervisor_link(name: str, key: str) -> str:
            label = html.escape(str(name))
            if not key:
                return label
            filename = f"supervisor_{key}.html"
            return f"<a href='{filename}' target='_blank' rel='noopener noreferrer'>{label}</a>"

        def format_shift_with_icons(shift_raw) -> str:
            return html.escape(str(shift_raw))

        def build_popup_html(row, popup_columns, popup_labels,
                             supervisor_cell_html, shift_cell_html) -> str:
            rows = []
            for col in popup_columns:
                label = popup_labels.get(col, col)
                if col == "Supervisor\n":
                    cell_html = supervisor_cell_html
                elif col == "Shift\n":
                    cell_html = shift_cell_html
                else:
                    val = row.get(col, "")
                    cell_html = html.escape(str(val))

                rows.append(
                    "<tr><th style='text-align:left;padding-right:6px;'>{}</th><td>{}</td></tr>".format(
                        html.escape(str(label)), cell_html
                    )
                )
            return "<table>" + "".join(rows) + "</table>"

        def build_intersection_popup(wo_id, loc_raw, from_raw, to_raw, intersection_id):
            return f"""
            <div style="font-family:Arial;font-size:13px;">
              <b>Intersection Point</b><br>
              <b>WO:</b> {html.escape(str(wo_id))}<br>
              <b>Location:</b> {html.escape(str(loc_raw))}<br>
              <b>From:</b> {html.escape(str(from_raw))}<br>
              <b>To:</b> {html.escape(str(to_raw))}<br>
              <b>Intersection ID:</b> {html.escape(str(intersection_id))}<br>
            </div>
            """

        def build_segment_popup(props: dict) -> str:
            wo_m_str = props.get("WO_m_display", "")
            wo_km_str = props.get("WO_km_display", "")
            sup_html = props.get("Supervisor_link_html", html.escape(str(props.get("Supervisor", ""))))
            shift_html = props.get("Shift_html", html.escape(str(props.get("Shift", ""))))

            extra = ""
            if props.get("route_mode"):
                extra = (
                    "<div style='margin-top:6px;padding:6px;border-radius:6px;background:#fff3cd;border:1px solid #ffeeba;'>"
                    f"<b>Routing:</b> {html.escape(str(props.get('route_mode')))}"
                    "</div>"
                )

            return f"""
            <div style="font-family:Arial;font-size:13px;line-height:1.25;">
              <b>WO:</b> {html.escape(str(props.get("WO_ID","")))}<br>
              <b>Total Segments:</b> {html.escape(str(props.get("Segment_count","")))}<br>
              <b>Location:</b> {html.escape(str(props.get("Location","")))}<br>
              <b>To:</b> {html.escape(str(props.get("To","")))}<br>
              <b>From:</b> {html.escape(str(props.get("From","")))}<br>
              <b>Distance (m):</b> {html.escape(str(wo_m_str))}<br>
              <b>Distance (km):</b> {html.escape(str(wo_km_str))}<br>
              {extra}
              <hr style="margin:6px 0;">
              <b>Supervisor:</b> {sup_html}<br>
              <b>District:</b> {html.escape(str(props.get("District","")))}<br>
              <b>Ward:</b> {html.escape(str(props.get("Ward","")))}<br>
              <b>Date:</b> {html.escape(str(props.get("Date","")))}<br>
              <b>Shift:</b> {shift_html}<br>
              <b>Type:</b> {html.escape(str(props.get("Type","")))}<br>
            </div>
            """

        m = folium.Map(location=[43.7, -79.4], zoom_start=11, tiles=None)
        folium.TileLayer("OpenStreetMap", name="OpenStreetMap", control=True).add_to(m)
        folium.TileLayer("CartoDB positron", name="Light (CartoDB)", control=True).add_to(m)
        folium.TileLayer("CartoDB dark_matter", name="Dark (CartoDB)", control=True).add_to(m)
        folium.TileLayer(
            tiles="https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}",
            attr="Esri World Imagery",
            name="Satellite (Esri)",
            control=True,
        ).add_to(m)

        plugins.Fullscreen(position="topright", title="Fullscreen", title_cancel="Exit fullscreen").add_to(m)
        plugins.MiniMap(tile_layer="OpenStreetMap", position="bottomright", zoom_level_offset=-4, toggle_display=True).add_to(m)
        plugins.MeasureControl(
            position="topleft",
            primary_length_unit="meters",
            secondary_length_unit="kilometers",
            primary_area_unit="sqmeters",
            secondary_area_unit="hectares",
        ).add_to(m)

        title_html = """
        <div style="
            position: fixed;
            top: 10px; left: 50%;
            transform: translateX(-50%);
            z-index: 9999;
            background-color: rgba(255, 255, 255, 0.9);
            padding: 6px 12px;
            border-radius: 4px;
            font-size: 16px;
            font-weight: bold;
            box-shadow: 0 0 4px rgba(0,0,0,0.3);
        ">
            Winter Operations – Work Orders Map (Live)
        </div>
        """
        m.get_root().html.add_child(folium.Element(title_html))

        footer_html = f"""
        <div style="
            position: fixed;
            bottom: 0; right: 0;
            z-index: 9999;
            background-color: rgba(255, 255, 255, 0.8);
            padding: 4px 8px;
            font-size: 10px;
            border-top-left-radius: 4px;
        ">
            Generated {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}<br>
            Source: MASTER TRACKER(RAW DATA).csv
        </div>
        """
        m.get_root().html.add_child(folium.Element(footer_html))

        # =========================================================
        # Live-update UX: show a clean toast for intake updates, then reload
        # =========================================================
        live_ui_css = """
        <style>
          #woLiveToast {
            position: fixed;
            top: 64px;
            left: 10px;
            z-index: 10000;
            width: 420px;
            max-width: calc(100vw - 20px);
            background: rgba(255, 255, 255, 0.98);
            border: 1px solid rgba(0,0,0,0.12);
            box-shadow: 0 8px 22px rgba(0,0,0,0.18);
            border-radius: 12px;
            padding: 12px 12px;
            display: none;
            font-family: Arial, sans-serif;
          }
          #woLiveToast .hdr {
            display:flex; align-items:center; justify-content:space-between;
            gap: 10px;
          }
          #woLiveToast .title {
            font-size: 14px;
            font-weight: 800;
            color: #111;
          }
          #woLiveToast .meta {
            margin-top: 6px;
            font-size: 12px;
            color: #333;
            line-height: 1.25;
          }
          #woLiveToast .list {
            margin-top: 10px;
            max-height: 220px;
            overflow-y: auto;
            border-top: 1px solid rgba(0,0,0,0.06);
            padding-top: 8px;
          }
          #woLiveToast .item {
            padding: 8px 8px;
            border-radius: 10px;
            background: rgba(0, 128, 0, 0.06);
            border: 1px solid rgba(0, 128, 0, 0.12);
            margin-bottom: 8px;
          }
          #woLiveToast .item b {
            color: #0a3;
          }
          #woLiveToast .btns {
            margin-top: 10px;
            display:flex;
            gap: 8px;
          }
          #woLiveToast button {
            border: none;
            border-radius: 10px;
            padding: 9px 10px;
            font-weight: 800;
            cursor: pointer;
            font-size: 13px;
          }
          #woLiveToast .primary { background: #111; color: #fff; }
          #woLiveToast .ghost { background: #f2f2f2; color: #111; }
        </style>
        <div id="woLiveToast" role="status" aria-live="polite">
          <div class="hdr">
            <div class="title" id="woLiveToastTitle">Update detected</div>
            <div style="font-size:12px;color:#666;" id="woLiveToastWhen"></div>
          </div>
          <div class="meta" id="woLiveToastMeta"></div>
          <div class="list" id="woLiveToastList"></div>
          <div class="btns">
            <button class="primary" id="woLiveToastReload">Reload map now</button>
            <button class="ghost" id="woLiveToastDismiss">Dismiss</button>
          </div>
        </div>
        """
        m.get_root().html.add_child(folium.Element(live_ui_css))

        live_js = """
        <script>
          (function() {
            var toast = null, tTitle=null, tWhen=null, tMeta=null, tList=null, btnReload=null, btnDismiss=null;
            var reloadTimer = null;

            function el(id){ return document.getElementById(id); }

            function showToast(payload){
              toast = toast || el('woLiveToast');
              tTitle = tTitle || el('woLiveToastTitle');
              tWhen  = tWhen  || el('woLiveToastWhen');
              tMeta  = tMeta  || el('woLiveToastMeta');
              tList  = tList  || el('woLiveToastList');
              btnReload = btnReload || el('woLiveToastReload');
              btnDismiss= btnDismiss|| el('woLiveToastDismiss');

              if (!toast) return;

              var now = new Date();
              tWhen.textContent = now.toLocaleTimeString();

              var kind = payload && payload.kind ? payload.kind : 'update';
              var items = (payload && payload.items && Array.isArray(payload.items)) ? payload.items : [];
              var count = (payload && typeof payload.count === 'number') ? payload.count : items.length;

              if (kind === 'intake') {
                tTitle.textContent = (count === 1) ? 'New Work Order added ✅' : ('New Work Orders added ✅ (' + count + ')');
                tMeta.innerHTML = 'New intake submissions were applied and the map is about to refresh.';
              } else if (kind === 'master') {
                tTitle.textContent = 'Master tracker changed ✅';
                tMeta.innerHTML = 'Input data changed and the map is about to refresh.';
              } else {
                tTitle.textContent = 'Map update detected ✅';
                tMeta.innerHTML = 'The map is about to refresh.';
              }

              // list details (only for intake)
              tList.innerHTML = '';
              if (items.length) {
                items.forEach(function(it){
                  var wo = (it.WO || '').toString();
                  var loc = (it.Location || '').toString();
                  var fr  = (it.From || '').toString();
                  var to  = (it.To || '').toString();
                  var dist= (it.District || '').toString();
                  var ward= (it.Ward || '').toString();
                  var sup = (it.Supervisor || '').toString();
                  var dt  = (it.Date || '').toString();
                  var sh  = (it.Shift || '').toString();
                  var sid = (it.__submission_id || '').toString();

                  var div = document.createElement('div');
                  div.className = 'item';
                  div.innerHTML =
                    '<div><b>WO:</b> ' + escapeHtml(wo) + (sid ? (' &nbsp; <span style="color:#666;">(' + escapeHtml(sid) + ')</span>') : '') + '</div>' +
                    '<div style="margin-top:4px;"><b>Location:</b> ' + escapeHtml(loc) + '</div>' +
                    '<div><b>From:</b> ' + escapeHtml(fr) + '</div>' +
                    '<div><b>To:</b> ' + escapeHtml(to) + '</div>' +
                    '<div style="margin-top:4px;color:#333;"><b>District:</b> ' + escapeHtml(dist) +
                    ' &nbsp; <b>Ward:</b> ' + escapeHtml(ward) + '</div>' +
                    '<div style="color:#333;"><b>Supervisor:</b> ' + escapeHtml(sup) + '</div>' +
                    '<div style="color:#333;"><b>Date:</b> ' + escapeHtml(dt) + ' &nbsp; <b>Shift:</b> ' + escapeHtml(sh) + '</div>';
                  tList.appendChild(div);
                });
              } else {
                // keep list collapsed if none
                if (kind === 'intake') {
                  tList.innerHTML = '<div style="color:#666;font-size:12px;">Details not available.</div>';
                }
              }

              // show
              toast.style.display = 'block';

              // buttons
              btnReload.onclick = function(){
                safeReload();
              };
              btnDismiss.onclick = function(){
                toast.style.display = 'none';
                if (reloadTimer) { clearTimeout(reloadTimer); reloadTimer = null; }
              };

              // auto reload after short delay (still allows reading)
              if (reloadTimer) clearTimeout(reloadTimer);
              reloadTimer = setTimeout(function(){ safeReload(); }, 2200);
            }

            function safeReload(){
              try { window.location.reload(true); } catch(e) { window.location.reload(); }
            }

            function escapeHtml(s){
              return (s || '').toString()
                .replaceAll('&','&amp;')
                .replaceAll('<','&lt;')
                .replaceAll('>','&gt;')
                .replaceAll('"','&quot;')
                .replaceAll("'","&#39;");
            }

            try {
              var es = new EventSource('/events');
              es.onmessage = function(ev) {
                if (!ev || !ev.data) return;
                if (ev.data === 'ping') return;

                // Back-compat: if server sends "updated"
                if (ev.data === 'updated') {
                  showToast({ kind: 'update', count: 0, items: [] });
                  return;
                }

                // New: JSON payload
                var payload = null;
                try { payload = JSON.parse(ev.data); } catch(e) {}
                if (payload && payload.event === 'updated') {
                  showToast(payload);
                  return;
                }

                // Unknown payload: just reload quietly
                safeReload();
              };
            } catch (e) {
              console.log('Live updates not available:', e);
            }
          })();
        </script>
        """
        m.get_root().html.add_child(folium.Element(live_js))

        # =========================================================
        # FORCE ALL LINKS ON THE MAP PAGE TO OPEN IN A NEW TAB
        # =========================================================
        force_new_tab_js = """
        <script>
          (function() {
            function forceLinksToBlank(root) {
              try {
                var links = (root || document).querySelectorAll("a[href]");
                links.forEach(function(a) {
                  var href = (a.getAttribute("href") || "").trim();
                  if (!href || href.startsWith("#") || href.toLowerCase().startsWith("javascript:")) return;
                  a.setAttribute("target", "_blank");
                  a.setAttribute("rel", "noopener noreferrer");
                });
              } catch (e) {}
            }

            // initial pass
            forceLinksToBlank(document);

            // enforce for dynamically-created content (Leaflet popups/tooltips etc.)
            var obs = new MutationObserver(function(muts) {
              muts.forEach(function(m) {
                if (m.addedNodes && m.addedNodes.length) {
                  m.addedNodes.forEach(function(n) {
                    if (n && n.querySelectorAll) forceLinksToBlank(n);
                  });
                }
              });
            });
            obs.observe(document.documentElement, { childList: true, subtree: true });

            // last-resort: ensure clicked links are blank
            document.addEventListener("click", function(ev) {
              var a = ev.target && ev.target.closest ? ev.target.closest("a[href]") : null;
              if (!a) return;
              var href = (a.getAttribute("href") || "").trim();
              if (!href || href.startsWith("#") || href.toLowerCase().startsWith("javascript:")) return;
              a.setAttribute("target", "_blank");
              a.setAttribute("rel", "noopener noreferrer");
            }, true);
          })();
        </script>
        """
        m.get_root().html.add_child(folium.Element(force_new_tab_js))

        geocoder_css = "<link rel='stylesheet' href='https://cdn.jsdelivr.net/npm/leaflet-control-geocoder/dist/Control.Geocoder.css' />"
        m.get_root().header.add_child(folium.Element(geocoder_css))

        geocoder_js = "<script defer src='https://cdn.jsdelivr.net/npm/leaflet-control-geocoder/dist/Control.Geocoder.js'></script>"
        m.get_root().html.add_child(folium.Element(geocoder_js))

        geocoder_style = """
        <style>
          .leaflet-control-geocoder {
            border-radius: 10px !important;
            box-shadow: 0 2px 10px rgba(0,0,0,0.25) !important;
            border: 1px solid rgba(0,0,0,0.15) !important;
            overflow: hidden !important;
            background: rgba(255,255,255,0.98) !important;
          }
          .leaflet-control-geocoder-form input {
            width: 320px !important;
            padding: 10px 12px !important;
            font-size: 14px !important;
            border: none !important;
            outline: none !important;
          }
          .leaflet-control-geocoder-icon { display: none !important; }
          .leaflet-control-geocoder-alternatives {
            border-top: 1px solid rgba(0,0,0,0.08) !important;
            max-height: 260px !important;
            overflow-y: auto !important;
          }
          .leaflet-control-geocoder-alternatives a {
            padding: 8px 10px !important;
            font-size: 13px !important;
          }
        </style>
        """
        m.get_root().html.add_child(folium.Element(geocoder_style))

        map_var = m.get_name()
        toronto_viewbox = "-79.65,43.55,-79.10,43.86"

        add_geocoder_control = f"""
        <script>
          (function() {{
            function pick(obj, keys) {{
              for (var i = 0; i < keys.length; i++) {{
                var k = keys[i];
                if (obj && obj[k]) return obj[k];
              }}
              return '';
            }}

            function buildNiceLabel(geocode, fallbackName) {{
              var props = geocode && geocode.properties ? geocode.properties : {{}};
              var addr = props.address ? props.address : {{}};
              var named = props.namedetails ? props.namedetails : {{}};

              var placeName =
                pick(named, ['name', 'brand']) ||
                pick(addr, ['amenity', 'shop', 'tourism', 'leisure', 'building', 'office']) ||
                '';

              var house = pick(addr, ['house_number']) || '';
              var road  = pick(addr, ['road', 'pedestrian', 'footway', 'street']) || '';
              var unit  = pick(addr, ['unit', 'flat', 'suite', 'floor']) || '';

              var city =
                pick(addr, ['city', 'town', 'village']) ||
                pick(addr, ['borough', 'suburb', 'neighbourhood']) ||
                'Toronto';

              var province = pick(addr, ['state', 'province']) || 'Ontario';
              var country = pick(addr, ['country']) || 'Canada';

              var line1Parts = [];
              if (placeName) line1Parts.push(placeName);

              var streetParts = [];
              if (unit) streetParts.push(unit);
              if (house) streetParts.push(house);
              if (road) streetParts.push(road);

              var streetLine = streetParts.join(' ');
              if (!placeName && !streetLine && fallbackName) streetLine = fallbackName;

              if (streetLine) line1Parts.push(streetLine);

              var line2Parts = [];
              if (city) line2Parts.push(city);
              if (province) line2Parts.push(province);
              if (country) line2Parts.push(country);

              var label = line1Parts.join(' — ');
              if (line2Parts.length) label += "<br>" + line2Parts.join(", ");

              if (!label || label === "<br>") {{
                label = fallbackName || 'Result';
              }}
              return label;
            }}

            function tryInit() {{
              try {{
                if (typeof L === 'undefined') return false;
                var map = {map_var};
                if (!map) return false;
                if (!L.Control || !L.Control.Geocoder) return false;

                if (window.__wo_geocoder_added) return true;

                var searchMarker = null;

                var geocoder = L.Control.Geocoder.nominatim({{
                  geocodingQueryParams: {{
                    countrycodes: 'ca',
                    viewbox: '{toronto_viewbox}',
                    bounded: 0,
                    addressdetails: 1,
                    namedetails: 1,
                    extratags: 1,
                    'accept-language': 'en'
                  }}
                }});

                var control = L.Control.geocoder({{
                  position: 'topleft',
                  collapsed: false,
                  defaultMarkGeocode: false,
                  placeholder: 'Search an address...',
                  errorMessage: 'No address found.',
                  suggestMinLength: 3,
                  geocoder: geocoder
                }}).addTo(map);

                control.on('markgeocode', function(e) {{
                  try {{
                    var bbox = e.geocode.bbox;
                    var center = e.geocode.center;
                    var providerName = e.geocode.name || 'Result';

                    if (bbox) {{
                      map.fitBounds(bbox, {{ padding: [30, 30] }});
                    }} else {{
                      map.setView(center, Math.max(map.getZoom(), 16));
                    }}

                    if (searchMarker) {{
                      searchMarker.setLatLng(center);
                    }} else {{
                      searchMarker = L.marker(center, {{ draggable: false }});
                      searchMarker.addTo(map);
                    }}

                    var nice = buildNiceLabel(e.geocode, providerName);
                    searchMarker.bindPopup('<div style="font-size:13px;line-height:1.25;">' + nice + '</div>').openPopup();
                  }} catch (err) {{
                    console.log('markgeocode handler error:', err);
                  }}
                }});

                window.__wo_geocoder_added = true;
                return true;
              }} catch (e) {{
                console.log('Geocoder init failed:', e);
                return false;
              }}
            }}

            var tries = 0;
            var maxTries = 80;
            var t = setInterval(function() {{
              tries += 1;
              if (tryInit() || tries >= maxTries) {{
                clearInterval(t);
              }}
            }}, 250);
          }})();
        </script>
        """
        m.get_root().html.add_child(folium.Element(add_geocoder_control))

        district_colors = {}
        color_cycle = [
            "red", "blue", "green", "orange", "purple",
            "darkred", "lightred", "beige", "darkblue",
            "darkgreen", "cadetblue", "darkpurple",
            "white", "pink", "lightblue", "lightgreen",
            "gray", "black", "lightgray",
        ]
        color_idx = 0

        def get_color_for_district(district: str) -> str:
            nonlocal color_idx
            if district not in district_colors:
                district_colors[district] = color_cycle[color_idx % len(color_cycle)]
                color_idx += 1
            return district_colors[district]

        work_orders_group = folium.FeatureGroup(name="Work Orders", show=True)
        work_orders_group.add_to(m)

        intersections_group = None
        if DRAW_INTERSECTION_POINTS:
            intersections_group = folium.FeatureGroup(
                name="Intersections",
                show=bool(INTERSECTION_POINTS_SHOW_BY_DEFAULT),
            )
            intersections_group.add_to(m)

        popup_columns = [
            "WO",
            "District\n",
            "Ward\n",
            "Date\n",
            "Shift\n",
            "Supervisor\n",
            "Location",
            "From ",
            "To",
            "Type (Road Class/ School, Bridge)\n",
        ]
        popup_labels = {col: col.replace("\n", " ").strip() for col in popup_columns}

        subsegment_count = 0
        skipped_count = 0
        mapped_records = []
        skipped_records = []
        geojson_features = []
        supervisor_rows = defaultdict(list)

        def is_dead_end(raw_val, norm_val):
            s = str(raw_val).upper()
            if any(tok in s for tok in DEAD_END_TOKENS):
                return True
            if norm_val in DEAD_END_TOKENS:
                return True
            return False

        def add_intersection_points_for_path(group_for_points, district_color, wo_id, loc_raw, from_raw, to_raw, node_path):
            if not DRAW_INTERSECTION_POINTS:
                return
            if group_for_points is None:
                return
            if not node_path or len(node_path) < 2:
                return

            for intersection_id in node_path:
                latlng = get_intersection_latlng(intersection_id)
                if not latlng:
                    continue

                popup_html = build_intersection_popup(wo_id, loc_raw, from_raw, to_raw, intersection_id)

                folium.CircleMarker(
                    location=latlng,
                    radius=INTERSECTION_POINT_RADIUS,
                    color=district_color,
                    weight=2,
                    opacity=INTERSECTION_POINT_OPACITY,
                    fill=True,
                    fill_opacity=INTERSECTION_POINT_FILL_OPACITY,
                    popup=folium.Popup(popup_html, max_width=320),
                    tooltip=f"WO {wo_id} | Intersection {intersection_id}",
                ).add_to(group_for_points)

                geojson_features.append({
                    "type": "Feature",
                    "geometry": {"type": "Point", "coordinates": [latlng[1], latlng[0]]},
                    "properties": {
                        "feature_kind": "intersection_node",
                        "WO_ID": str(wo_id),
                        "Intersection_ID": int(intersection_id),
                        "Location": str(loc_raw),
                        "From": str(from_raw),
                        "To": str(to_raw),
                        "stroke_color": str(district_color),
                    }
                })

        def add_wo_segments(
            street_key, node_path, edge_indices, district_color,
            wo_id, loc_raw, from_raw, to_raw, district_val, ward, date_str, shift_str,
            supervisor_raw, sup_key, work_type, supervisor_link_html, shift_display_html, wo_total_m,
            route_mode=""
        ):
            if not DRAW_WO_SEGMENTS:
                return
            if not node_path or len(node_path) < 2 or not edge_indices:
                return

            segments = build_edge_segments(street_key, node_path, edge_indices)
            seg_count = len(segments)

            wo_total_km = wo_total_m / 1000.0

            for idx, seg in enumerate(segments, start=1):
                seg_coords = seg["coords"]
                seg_m = multiline_distance_m(seg_coords)
                seg_km = seg_m / 1000.0

                seg_geometry = {"type": "MultiLineString", "coordinates": seg_coords}

                seg_from_label = pick_cross_street(seg["u"], street_key)
                seg_to_label = pick_cross_street(seg["v"], street_key)

                props = {
                    "feature_kind": "workorder_segment",
                    "WO_ID": str(wo_id),
                    "Location": str(loc_raw),
                    "From": str(from_raw),
                    "To": str(to_raw),
                    "Location_resolved": str(street_key),
                    "District": str(district_val),
                    "Ward": str(ward),
                    "Date": str(date_str),
                    "Shift": str(shift_str),
                    "Supervisor": str(supervisor_raw),
                    "SupervisorKey": str(sup_key),
                    "Type": str(work_type),

                    "From_Intersection_ID": int(seg["u"]),
                    "To_Intersection_ID": int(seg["v"]),
                    "Segment_idx": int(idx),
                    "Segment_count": int(seg_count),
                    "Segment_m": float(seg_m),
                    "Segment_km": float(seg_km),

                    "Segment_m_display": fmt_sigfig(seg_m, 2),
                    "Segment_km_display": fmt_sigfig(seg_km, 2),

                    "Seg_From": str(seg_from_label),
                    "Seg_To": str(seg_to_label),

                    "WO_m": float(wo_total_m),
                    "WO_km": float(wo_total_km),
                    "WO_m_display": fmt_sigfig(wo_total_m, 2),
                    "WO_km_display": fmt_sigfig(wo_total_km, 2),

                    "Supervisor_link_html": supervisor_link_html,
                    "Shift_html": shift_display_html,
                    "route_mode": route_mode,

                    "stroke_color": str(district_color),
                }

                seg_feature = {"type": "Feature", "geometry": seg_geometry, "properties": props}
                geojson_features.append(seg_feature)

                seg_popup = build_segment_popup(props)

                seg_gj = folium.GeoJson(
                    data=seg_feature,
                    style_function=style_for_segment,
                    highlight_function=lambda feat: {
                        "color": feat["properties"].get("stroke_color", "red"),
                        "weight": 8,
                        "opacity": 0.9,
                    },
                    name=f"WO {wo_id} segment",
                )

                seg_tooltip = folium.GeoJsonTooltip(
                    fields=[
                        "WO_ID",
                        "Segment_idx",
                        "Segment_count",
                        "Location",
                        "Seg_To",
                        "Seg_From",
                        "Segment_m_display",
                        "Segment_km_display",
                    ],
                    aliases=[
                        "WO",
                        "Segment",
                        "Total Segments",
                        "Location",
                        "To",
                        "From",
                        "Distance (m)",
                        "Distance (km)",
                    ],
                    sticky=False,
                )
                seg_tooltip.add_to(seg_gj)

                folium.Popup(seg_popup, max_width=420).add_to(seg_gj)
                seg_gj.add_to(work_orders_group)

        log("Adding work orders to map...")

        skip_reason_counter = Counter()
        intake_skipped_counter = 0
        intake_mapped_counter = 0

        def record_intake_debug(status, submission_id, wo_id, reason, loc_raw, from_raw, to_raw,
                                loc_key="", from_key="", to_key=""):
            intake_debug_rows.append({
                "__submission_id": submission_id,
                "WO": wo_id,
                "Status": status,
                "skip_reason": reason,
                "Location": loc_raw,
                "From": from_raw,
                "To": to_raw,
                "Location_resolved": loc_key,
                "From_resolved": from_key,
                "To_resolved": to_key,
            })

        def add_line_feature(row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                             supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                             loc_key=None, from_key=None, to_key=None, route_mode=""):
            popup_html = build_popup_html(
                row, popup_columns, popup_labels,
                make_supervisor_link(supervisor_raw, sup_key),
                format_shift_with_icons(row.get("Shift\n", ""))
            )

            props = {
                "feature_kind": "workorder_line",
                "WO_ID": wo_id,
                "Location": str(loc_raw),
                "From": str(from_raw),
                "To": str(to_raw),
                "Location_resolved": loc_key,
                "From_resolved": from_key,
                "To_resolved": to_key,
                "District": district_val,
                "Ward": ward_val,
                "Date": date_val,
                "Shift": shift_val,
                "Supervisor": str(supervisor_raw).strip(),
                "SupervisorKey": sup_key,
                "Type": type_val,
                "stroke_color": color,
                "route_mode": route_mode,
            }

            feature = {"type": "Feature", "geometry": geometry, "properties": props}
            geojson_features.append(feature)

            gj = folium.GeoJson(
                data=feature,
                style_function=style_for_feature,
                highlight_function=lambda feat: {
                    "color": feat["properties"].get("stroke_color", "red"),
                    "weight": 7,
                    "opacity": 1.0,
                },
                name=f"WO {wo_id}",
            )

            tooltip = folium.GeoJsonTooltip(
                fields=["WO_ID", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
                aliases=["WO", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
                sticky=False,
            )
            tooltip.add_to(gj)

            # Add route mode note into popup visually
            if route_mode:
                popup_html = popup_html.replace(
                    "</table>",
                    f"</table><div style='margin-top:8px;padding:6px;border-radius:6px;background:#fff3cd;border:1px solid #ffeeba;'>"
                    f"<b>Routing:</b> {html.escape(route_mode)}</div>"
                )

            folium.Popup(popup_html, max_width=420).add_to(gj)
            gj.add_to(work_orders_group)

        for _, row in master.iterrows():
            row_dict = row.to_dict()

            submission_id = str(row.get("__submission_id", "")).strip()
            is_intake_row = bool(submission_id) and (submission_id in intake_ids_set)

            loc_raw = row.get("Location", "")
            from_raw = row.get("From ", "")
            to_raw = row.get("To", "")

            loc_core = extract_street_token(loc_raw)
            from_core = extract_street_token(from_raw)
            to_core = extract_street_token(to_raw)

            loc_norm = normalize_street_name(loc_core)
            from_norm = normalize_street_name(from_core)
            to_norm = normalize_street_name(to_core)

            loc_key, loc_score = resolve_street_name(loc_norm, MIN_SIM_LOCATION)
            if not loc_key:
                reason = f"Location not matched to centreline (core='{loc_core}', norm='{loc_norm}', best_score={loc_score:.2f})"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={row.get('WO','')} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, row.get("WO", ""), reason, loc_raw, from_raw, to_raw)
                continue

            wo_id = str(row.get("WO", ""))
            district_val = str(row.get("District\n", "Unknown")).strip() or "Unknown"
            color = get_color_for_district(district_val)
            ward_val = str(row.get("Ward\n", "")).strip()
            date_val = str(row.get("Date\n", "")).strip()
            shift_val = str(row.get("Shift\n", "")).strip()
            type_val = str(row.get("Type (Road Class/ School, Bridge)\n", "")).strip()

            supervisor_raw = row.get("Supervisor\n", "")
            sup_key = make_supervisor_key(supervisor_raw)

            from_is_str = isinstance(from_raw, str)
            to_is_str = isinstance(to_raw, str)
            entire_flag = (
                (from_is_str and "ENTIRE STREET" in from_raw.upper())
                or (to_is_str and "ENTIRE STREET" in to_raw.upper())
            )

            # ENTIRE STREET
            if entire_flag:
                coords_to_use = full_street_multiline(loc_key)
                if not coords_to_use:
                    reason = "Entire Street requested but no geometry found for Location"
                    row_dict["skip_reason"] = reason
                    skipped_records.append(row_dict)
                    skipped_count += 1
                    skip_reason_counter[reason] += 1
                    if is_intake_row:
                        intake_skipped_counter += 1
                        log(f"INTAKE SKIP: WO={wo_id} id={submission_id} -> {reason}")
                        record_intake_debug("SKIPPED", submission_id, wo_id, reason, loc_raw, from_raw, to_raw, loc_key)
                    continue

                geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
                add_line_feature(row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                                 supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                                 loc_key=loc_key, route_mode="ENTIRE STREET")
                subsegment_count += 1

                if is_intake_row:
                    intake_mapped_counter += 1
                    record_intake_debug("MAPPED", submission_id, wo_id, "", loc_raw, from_raw, to_raw, loc_key, "", "")
                continue

            # NORMAL FROM/TO
            if not from_norm or not to_norm:
                reason = f"Missing usable From/To after extraction (From_raw='{from_raw}', To_raw='{to_raw}')"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={wo_id} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, wo_id, reason, loc_raw, from_raw, to_raw, loc_key)
                continue

            from_key, from_score = resolve_street_name(from_norm, MIN_SIM_CROSS)
            to_key, to_score = resolve_street_name(to_norm, MIN_SIM_CROSS)

            if not from_key or not to_key:
                reason = f"From/To not matched (From='{from_norm}', score={from_score:.2f}; To='{to_norm}', score={to_score:.2f})"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={wo_id} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, wo_id, reason, loc_raw, from_raw, to_raw, loc_key, from_key or "", to_key or "")
                continue

            start_node = find_intersection_node(loc_key, from_key)
            end_node = find_intersection_node(loc_key, to_key)

            # ---------- FIX B1: If endpoints can't be found, draw FULL STREET (best effort) ----------
            if start_node is None or end_node is None or start_node == end_node:
                coords_to_use = full_street_multiline(loc_key)
                if coords_to_use:
                    geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
                    add_line_feature(
                        row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                        supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                        loc_key=loc_key, from_key=from_key, to_key=to_key,
                        route_mode="FALLBACK: FULL STREET (endpoints not found on centreline)"
                    )
                    subsegment_count += 1
                    if is_intake_row:
                        intake_mapped_counter += 1
                        record_intake_debug(
                            "MAPPED", submission_id, wo_id,
                            "Fallback used: full street because endpoints not found",
                            loc_raw, from_raw, to_raw, loc_key, from_key, to_key
                        )
                    continue

                reason = f"Could not find both intersection nodes (Location='{loc_key}', From='{from_key}', To='{to_key}')"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={wo_id} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, wo_id, reason, loc_raw, from_raw, to_raw, loc_key, from_key, to_key)
                continue

            # Try strict path along Location
            path = shortest_path_for_street(loc_key, start_node, end_node)

            # ---------- FIX B2: If no path on Location, use GLOBAL shortest path ----------
            if path is None:
                gpath = shortest_path_global(start_node, end_node)
                if gpath is not None:
                    node_path_g, edge_idx_g = gpath
                    coords_to_use = build_path_multiline_global(node_path_g, edge_idx_g)
                    if coords_to_use:
                        geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
                        add_line_feature(
                            row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                            supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                            loc_key=loc_key, from_key=from_key, to_key=to_key,
                            route_mode="FALLBACK: GLOBAL ROUTE (Location street disconnected)"
                        )
                        subsegment_count += 1
                        if is_intake_row:
                            intake_mapped_counter += 1
                            record_intake_debug(
                                "MAPPED", submission_id, wo_id,
                                "Fallback used: global route because location street had no path",
                                loc_raw, from_raw, to_raw, loc_key, from_key, to_key
                            )
                        continue

                reason = f"No path along Location between nodes (Location='{loc_key}', From='{from_key}', To='{to_key}')"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={wo_id} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, wo_id, reason, loc_raw, from_raw, to_raw, loc_key, from_key, to_key)
                continue

            node_path, edge_indices = path
            coords_to_use = build_path_multiline(loc_key, node_path, edge_indices)
            if not coords_to_use:
                reason = "Empty geometry after path building"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={wo_id} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, wo_id, reason, loc_raw, from_raw, to_raw, loc_key, from_key, to_key)
                continue

            geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
            add_line_feature(
                row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                loc_key=loc_key, from_key=from_key, to_key=to_key,
                route_mode="STRICT: LOCATION STREET"
            )
            subsegment_count += 1

            wo_total_m = multiline_distance_m(coords_to_use)
            add_wo_segments(
                street_key=loc_key,
                node_path=node_path,
                edge_indices=edge_indices,
                district_color=color,
                wo_id=wo_id,
                loc_raw=loc_raw,
                from_raw=from_raw,
                to_raw=to_raw,
                district_val=district_val,
                ward=ward_val,
                date_str=date_val,
                shift_str=shift_val,
                supervisor_raw=supervisor_raw,
                sup_key=sup_key,
                work_type=type_val,
                supervisor_link_html=make_supervisor_link(supervisor_raw, sup_key),
                shift_display_html=format_shift_with_icons(row.get("Shift\n", "")),
                wo_total_m=wo_total_m,
                route_mode="STRICT: LOCATION STREET"
            )

            if DRAW_INTERSECTION_POINTS:
                add_intersection_points_for_path(intersections_group, color, wo_id, loc_raw, from_raw, to_raw, node_path)

            if is_intake_row:
                intake_mapped_counter += 1
                record_intake_debug("MAPPED", submission_id, wo_id, "", loc_raw, from_raw, to_raw, loc_key, from_key, to_key)

        log(f"Work orders drawn: {subsegment_count}")
        log(f"Work orders skipped: {skipped_count}")
        if skipped_count:
            top = skip_reason_counter.most_common(8)
            log("Top skip reasons (sample):")
            for reason, cnt in top:
                log(f"  - {cnt}x: {reason[:160]}")

        log(f"INTAKE SUMMARY: mapped={intake_mapped_counter} skipped={intake_skipped_counter}")
        if intake_debug_rows:
            try:
                pd.DataFrame(intake_debug_rows).to_csv(OUTPUT_INTAKE_DEBUG_CSV, index=False, encoding="utf-8")
                log(f"INTAKE DEBUG CSV saved: {OUTPUT_INTAKE_DEBUG_CSV}")
            except Exception as e:
                log(f"INTAKE DEBUG CSV write failed: {e}")

        COLOR_NAME_TO_HEX = {
            "darkred": "#8B0000",
            "lightred": "#FF7F7F",
            "darkblue": "#00008B",
            "lightblue": "#ADD8E6",
            "darkgreen": "#006400",
            "lightgreen": "#90EE90",
            "darkpurple": "#4B0082",
            "cadetblue": "#5F9EA0",
            "beige": "#F5F5DC",
            "lightgray": "#D3D3D3",
        }

        def css_color(c: str) -> str:
            c = (c or "").strip().lower()
            return COLOR_NAME_TO_HEX.get(c, c or "#000000")

        district_rows_html = []
        for d in sorted(district_colors.keys(), key=lambda x: (x or "").lower()):
            c = district_colors.get(d, "red")
            swatch = css_color(c)
            district_rows_html.append(
                f"""
                <div style="display:flex;align-items:center;margin:3px 0;">
                  <span style="width:14px;height:14px;display:inline-block;border:1px solid #444;
                               background:{swatch};margin-right:8px;border-radius:2px;"></span>
                  <span>{html.escape(str(d))}</span>
                </div>
                """
            )

        legend_html = f"""
        <div style="
            position: fixed;
            bottom: 20px; left: 10px;
            z-index: 9999;
            background-color: rgba(255, 255, 255, 0.92);
            padding: 10px 12px;
            border-radius: 6px;
            font-size: 12px;
            box-shadow: 0 0 6px rgba(0,0,0,0.28);
            max-height: 240px;
            overflow-y: auto;
            min-width: 210px;
        ">
            {''.join(district_rows_html) if district_rows_html else ''}
        </div>
        """
        m.get_root().html.add_child(folium.Element(legend_html))

        folium.LayerControl(collapsed=False).add_to(m)

        m.save(OUTPUT_HTML)
        log(f"Map saved: {OUTPUT_HTML}")

        if geojson_features:
            feature_collection = {"type": "FeatureCollection", "features": geojson_features}
            with open(OUTPUT_GEOJSON, "w", encoding="utf-8") as f:
                json.dump(feature_collection, f)
            log(f"GeoJSON saved: {OUTPUT_GEOJSON}")

        if mapped_records:
            pd.DataFrame(mapped_records).to_csv(OUTPUT_MAPPED_CSV, index=False)
            log(f"Mapped CSV saved: {OUTPUT_MAPPED_CSV}")

        if skipped_records:
            pd.DataFrame(skipped_records).to_csv(OUTPUT_SKIPPED_CSV, index=False)
            log(f"Skipped CSV saved: {OUTPUT_SKIPPED_CSV}")

        log(f"BUILD DONE: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        return {
            "master_rows": int(len(master)),
            "drawn": int(subsegment_count),
            "skipped": int(skipped_count),
            "centre_streets_count": int(len(ALL_CENTRE_STREETS)),
            "centre_streets": ALL_CENTRE_STREETS,
        }


# =========================================================
# 5. LIVE SERVER + SSE EVENTS + DATA ENTRY UI
# =========================================================

app = Flask(__name__)
events = Queue()
latest_build_stats = {"status": "not built yet"}
latest_centre_streets = []
latest_allowed_sets = {}

# =========================================================
# UI: Cleaner “submitted” experience
# - After POST success -> redirect to /new?sid=<submission_id>
# - /new shows a top green banner with details
# =========================================================

INDEX_HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Live Work Orders Map</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 16px; }
    .card { border: 1px solid #ddd; border-radius: 12px; padding: 14px; margin-bottom: 12px; }
    code { background: #f6f6f6; padding: 2px 5px; border-radius: 4px; }
    a.btn {
      display:inline-block; padding:10px 12px; border-radius:10px;
      background:#111; color:#fff; text-decoration:none; font-weight:800;
    }
    .muted { color:#666; font-size: 12px; }
  </style>
</head>
<body>
  <div class="card">
    <h2 style="margin:0 0 6px 0;">Live Work Orders Map</h2>
    <p><b>Status:</b> {{ status }}</p>
    <p><b>Last build:</b> {{ last_build }}</p>
    <p><b>Master rows:</b> {{ master_rows }} | <b>Drawn:</b> {{ drawn }} | <b>Skipped:</b> {{ skipped }}</p>
    <p>
      Open map:
      <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">work_orders_map.html</a>
    </p>
    <p>
      <a class="btn" href="/new">+ Add a New Work Order (Form)</a>
    </p>
    <p class="muted">
      Debug:
      <a href="/outputs/intake_submissions_debug.csv" target="_blank" rel="noopener noreferrer">intake_submissions_debug.csv</a>
    </p>
  </div>
</body>
</html>
"""

NEW_FORM_HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Add Work Order</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 16px; max-width: 900px; }
    .card { border: 1px solid #ddd; border-radius: 12px; padding: 14px; margin-bottom: 12px; }
    label { display:block; margin-top: 10px; font-weight: 800; }
    input, select {
      width: 100%; padding: 10px 10px; border-radius: 10px;
      border: 1px solid #ccc; font-size: 14px;
    }
    .row { display:flex; gap: 12px; }
    .col { flex: 1; }
    .help { color:#555; font-size: 13px; margin-top: 6px; }
    .err { background:#ffecec; border:1px solid #ffb2b2; padding:10px; border-radius:10px; }
    .ok  { background:#eaffea; border:1px solid #a6e6a6; padding:12px; border-radius:12px; }
    button {
      margin-top: 14px; padding: 12px 14px; border-radius: 12px;
      border: none; background: #111; color: #fff; font-size: 15px; font-weight: 900;
      cursor: pointer;
    }
    a { color:#111; }
    code { background:#f6f6f6; padding: 2px 6px; border-radius: 6px; }
    .pill {
      display:inline-block;
      padding: 3px 8px;
      border-radius: 999px;
      background:#111;
      color:#fff;
      font-size: 12px;
      font-weight: 900;
    }
    .kv { display:grid; grid-template-columns: 140px 1fr; gap: 6px 10px; margin-top: 8px; }
    .kv div { padding: 2px 0; }
    .kv .k { color:#444; font-weight: 800; }
  </style>
</head>
<body>
  <div class="card">
    <h2 style="margin:0 0 6px 0;">Add a Work Order</h2>
    <p class="help" style="margin:0;">
      <a href="/">← Back</a> |
      <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">Open Map</a>
    </p>
  </div>

  {% if notice and notice.get('__submission_id') %}
  <div class="card ok" id="submittedBanner">
    <div style="display:flex;align-items:center;justify-content:space-between;gap:10px;">
      <div>
        <span class="pill">Submitted ✅</span>
        <div style="margin-top:6px;font-weight:900;font-size:14px;">
          New work order was added to intake.
        </div>
        <div style="margin-top:6px;color:#333;font-size:13px;">
          Submission ID: <code>{{ notice.get('__submission_id') }}</code>
          &nbsp; • &nbsp;
          Submitted at: <code>{{ notice.get('__submitted_at','') }}</code>
        </div>
      </div>
      <div>
        <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer"
           style="display:inline-block;padding:10px 12px;border-radius:10px;background:#111;color:#fff;text-decoration:none;font-weight:900;">
          Open Map
        </a>
      </div>
    </div>

    <div class="kv">
      <div class="k">WO</div><div>{{ notice.get('WO','') }}</div>
      <div class="k">Location</div><div>{{ notice.get('Location','') }}</div>
      <div class="k">From</div><div>{{ notice.get('From ','') }}</div>
      <div class="k">To</div><div>{{ notice.get('To','') }}</div>
      <div class="k">District</div><div>{{ notice.get('District\\n','') }}</div>
      <div class="k">Ward</div><div>{{ notice.get('Ward\\n','') }}</div>
      <div class="k">Supervisor</div><div>{{ notice.get('Supervisor\\n','') }}</div>
      <div class="k">Shift</div><div>{{ notice.get('Shift\\n','') }}</div>
      <div class="k">Date</div><div>{{ notice.get('Date\\n','') }}</div>
      <div class="k">Type</div><div>{{ notice.get('Type (Road Class/ School, Bridge)\\n','') }}</div>
    </div>

    <div style="margin-top:10px;color:#555;font-size:12px;">
      The server applies intake to the master automatically (polls every {{ intake_poll_seconds }}s). The map page will pop a “New Work Order added” toast and refresh itself when it rebuilds.
    </div>
  </div>

  <script>
    // Make it "unambiguous + clean": after showing confirmation, reset URL so refresh doesn't re-show forever.
    (function(){
      try {
        var url = new URL(window.location.href);
        if (url.searchParams.get('sid')) {
          setTimeout(function(){
            url.searchParams.delete('sid');
            window.history.replaceState({}, document.title, url.toString());
          }, 1200);
        }
      } catch(e) {}
    })();
  </script>
  {% endif %}

  {% if errors and errors|length %}
  <div class="card err">
    <b>Fix these:</b>
    <ul>
      {% for e in errors %}
      <li>{{ e }}</li>
      {% endfor %}
    </ul>
  </div>
  {% endif %}

  <div class="card">
    <form method="post" action="/new" autocomplete="off">
      <div class="row">
        <div class="col">
          <label>WO</label>
          <input name="WO" required placeholder="e.g., 12345" value="{{ form.get('WO','') }}" />
        </div>
        <div class="col">
          <label>Date</label>
          <input name="Date__NL" required placeholder="e.g., 3-Mar-25" value="{{ form.get('Date__NL','') }}" />
        </div>
      </div>

      <div class="row">
        <div class="col">
          <label>District</label>
          <select name="District__NL" required>
            <option value="">-- choose --</option>
            {% for d in districts %}
            <option value="{{ d }}" {% if form.get('District__NL','') == d %}selected{% endif %}>{{ d }}</option>
            {% endfor %}
          </select>
        </div>
        <div class="col">
          <label>Ward</label>
          <select name="Ward__NL" required>
            <option value="">-- choose --</option>
            {% for w in wards %}
            <option value="{{ w }}" {% if form.get('Ward__NL','') == w %}selected{% endif %}>{{ w }}</option>
            {% endfor %}
          </select>
        </div>
      </div>

      <div class="row">
        <div class="col">
          <label>Supervisor</label>
          <select name="Supervisor__NL" required>
            <option value="">-- choose --</option>
            {% for s in supervisors %}
            <option value="{{ s }}" {% if form.get('Supervisor__NL','') == s %}selected{% endif %}>{{ s }}</option>
            {% endfor %}
          </select>
        </div>
        <div class="col">
          <label>Shift</label>
          <select name="Shift__NL" required>
            <option value="">-- choose --</option>
            {% for sh in shifts %}
            <option value="{{ sh }}" {% if form.get('Shift__NL','') == sh %}selected{% endif %}>{{ sh }}</option>
            {% endfor %}
          </select>
        </div>
      </div>

      <label>Type (Road Class/ School, Bridge)</label>
      <select name="Type__NL" required>
        <option value="">-- choose --</option>
        {% for t in types %}
        <option value="{{ t }}" {% if form.get('Type__NL','') == t %}selected{% endif %}>{{ t }}</option>
        {% endfor %}
      </select>

      <label>Location (street)</label>
      <input name="Location" list="streets" required placeholder="Start typing..." value="{{ form.get('Location','') }}" />

      <div class="row">
        <div class="col">
          <label>From</label>
          <input name="From" list="streets" placeholder="Start typing..." value="{{ form.get('From','') }}" />
          <div class="help">Leave blank only if Location includes <b>ENTIRE STREET</b>.</div>
        </div>
        <div class="col">
          <label>To</label>
          <input name="To" list="streets" placeholder="Start typing..." value="{{ form.get('To','') }}" />
          <div class="help">Leave blank only if Location includes <b>ENTIRE STREET</b>.</div>
        </div>
      </div>

      <datalist id="streets">
        {% for st in streets %}
        <option value="{{ st }}"></option>
        {% endfor %}
      </datalist>

      <button type="submit">Submit Work Order</button>

      <div class="help" style="margin-top:10px;">
        Tip: After submit, you’ll be redirected back here with a green confirmation banner (no ambiguity), and the map page will announce + auto-refresh when the intake gets applied.
      </div>
    </form>
  </div>
</body>
</html>
"""


@app.get("/")
def home():
    return render_template_string(
        INDEX_HTML,
        status=latest_build_stats.get("status", ""),
        last_build=latest_build_stats.get("last_build", ""),
        master_rows=latest_build_stats.get("master_rows", ""),
        drawn=latest_build_stats.get("drawn", ""),
        skipped=latest_build_stats.get("skipped", ""),
    )


@app.get("/new")
def new_form():
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    sid = (request.args.get("sid") or "").strip()
    notice = get_intake_submission_details(sid) if sid else {}

    return render_template_string(
        NEW_FORM_HTML,
        errors=[],
        form={},
        notice=notice,
        intake_poll_seconds=INTAKE_POLL_SECONDS,
        districts=sorted(list(latest_allowed_sets.get("District\n", set()))),
        wards=sorted(list(latest_allowed_sets.get("Ward\n", set()))),
        supervisors=sorted(list(latest_allowed_sets.get("Supervisor\n", set()))),
        shifts=sorted(list(latest_allowed_sets.get("Shift\n", set()))),
        types=sorted(list(latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", set()))),
        # ✅ DO NOT TRUNCATE: show ALL streets, already sorted in build_everything()
        streets=latest_centre_streets,
    )


@app.post("/new")
def new_submit():
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    form = request.form.to_dict()

    values = {master_key: "" for master_key in MASTER_COLUMNS}
    for form_key, master_key in FORM_TO_MASTER.items():
        values[master_key] = form.get(form_key, "")

    streets_set = set(
        s.upper().strip()
        for s in latest_centre_streets
        if isinstance(s, str) and s.strip()
    )

    errors = validate_submission(values, latest_allowed_sets, streets_set)
    if errors:
        log(f"INTAKE: submission rejected with {len(errors)} error(s)")
        return render_template_string(
            NEW_FORM_HTML,
            errors=errors,
            form=form,
            notice={},
            intake_poll_seconds=INTAKE_POLL_SECONDS,
            districts=sorted(list(latest_allowed_sets.get("District\n", set()))),
            wards=sorted(list(latest_allowed_sets.get("Ward\n", set()))),
            supervisors=sorted(list(latest_allowed_sets.get("Supervisor\n", set()))),
            shifts=sorted(list(latest_allowed_sets.get("Shift\n", set()))),
            types=sorted(list(latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", set()))),
            # ✅ DO NOT TRUNCATE: show ALL streets, already sorted
            streets=latest_centre_streets,
        )

    submission_id, inserted = append_to_intake(values)

    # UI-friendly: redirect back to GET /new with sid, so the page "refreshes" cleanly and shows a banner.
    return Response(
        "", 303,
        {"Location": f"/new?sid={submission_id}"}
    )


@app.get("/outputs/<path:filename>")
def outputs(filename):
    return send_from_directory(OUTPUT_DIR, filename)


@app.get("/events")
def sse_events():
    def stream():
        while True:
            try:
                msg = events.get(timeout=25)
                yield f"data: {msg}\n\n"
            except Empty:
                yield "data: ping\n\n"
    return Response(stream(), mimetype="text/event-stream")


# =========================================================
# 6. WATCHER THREADS
# =========================================================

def recompute_allowed_sets_from_master():
    allowed = {}

    def set_or_empty(lst):
        return set([str(x).strip() for x in lst if str(x).strip()])

    allowed["District\n"] = set_or_empty(STRICT_DISTRICTS)
    allowed["Ward\n"] = set_or_empty(STRICT_WARDS)
    allowed["Supervisor\n"] = set_or_empty(STRICT_SUPERVISORS)
    allowed["Shift\n"] = set_or_empty(STRICT_SHIFTS)
    allowed["Type (Road Class/ School, Bridge)\n"] = set_or_empty(STRICT_TYPES)

    try:
        df = pd.read_csv(MASTER_TRACKER_PATH, encoding="latin-1")
    except Exception:
        return allowed

    def learn(col):
        if allowed.get(col):
            return
        if col not in df.columns:
            allowed[col] = set()
            return
        vals = []
        for v in df[col].fillna("").astype(str).tolist():
            v = v.strip()
            if v:
                vals.append(v)
        allowed[col] = set(sorted(set(vals)))

    learn("District\n")
    learn("Ward\n")
    learn("Supervisor\n")
    learn("Shift\n")
    learn("Type (Road Class/ School, Bridge)\n")

    for k in list(allowed.keys()):
        if len(allowed[k]) > 4000:
            allowed[k] = set(list(sorted(allowed[k]))[:4000])

    return allowed


def _emit_updated_event(kind: str, items=None):
    """
    Sends a JSON payload into SSE so the map can show a clean toast + details.
    """
    payload = {
        "event": "updated",
        "kind": kind,
        "count": int(len(items) if items else 0),
        "items": items or [],
        "ts": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    }
    try:
        events.put(json.dumps(payload, ensure_ascii=False))
    except Exception:
        # last resort compatibility
        events.put("updated")


def watcher_loop():
    global latest_build_stats, latest_centre_streets, latest_allowed_sets

    last_fp = file_fingerprint(MASTER_TRACKER_PATH)

    try:
        with FILE_LOCK:
            stats = build_everything()
        latest_allowed_sets = recompute_allowed_sets_from_master()
        latest_centre_streets = stats.get("centre_streets", [])
        latest_build_stats = {
            "status": "ready",
            "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            **{k: v for k, v in stats.items() if k != "centre_streets"},
        }
        _emit_updated_event("master", items=[])
    except Exception as e:
        latest_build_stats = {
            "status": f"build error: {e}",
            "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        notify_user("Build failed", str(e))

    while True:
        time.sleep(POLL_INTERVAL_SECONDS)

        cur_fp = file_fingerprint(MASTER_TRACKER_PATH)
        if cur_fp != last_fp:
            with LAST_MASTER_WRITE_LOCK:
                recent_intake_write = (time.time() - LAST_MASTER_WRITE_BY_INTAKE_AT) < 4.0

            if recent_intake_write:
                log("Watcher: master changed but was just written by intake. Skipping watcher rebuild.")
                last_fp = cur_fp
                continue

            notify_user(
                "Detected change in input data",
                f"Master tracker updated. Rebuilding map...\n{MASTER_TRACKER_PATH}"
            )
            try:
                with FILE_LOCK:
                    stats = build_everything()
                latest_allowed_sets = recompute_allowed_sets_from_master()
                latest_centre_streets = stats.get("centre_streets", [])
                latest_build_stats = {
                    "status": "ready",
                    "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    **{k: v for k, v in stats.items() if k != "centre_streets"},
                }
                _emit_updated_event("master", items=[])
                notify_user(
                    "Map updated ✅",
                    f"New master tracker detected and map rebuilt.\nDrawn: {stats.get('drawn')} | Skipped: {stats.get('skipped')}",
                )
            except Exception as e:
                latest_build_stats = {
                    "status": f"build error: {e}",
                    "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                }
                notify_user("Build failed", str(e))

            last_fp = cur_fp
        else:
            log(f"No master change. Watching... ({MASTER_TRACKER_PATH})")


def intake_poll_loop():
    global latest_build_stats, latest_centre_streets, latest_allowed_sets
    global LAST_INTAKE_APPLIED, LAST_INTAKE_APPLIED_AT

    ensure_intake_file()

    while True:
        time.sleep(INTAKE_POLL_SECONDS)
        try:
            applied, applied_items = apply_intake_to_master()
            if applied > 0:
                with LAST_INTAKE_APPLIED_LOCK:
                    LAST_INTAKE_APPLIED = applied_items[:]
                    LAST_INTAKE_APPLIED_AT = time.time()

                log(f"INTAKE POLL: applied {applied} new row(s). Rebuilding map...")
                with FILE_LOCK:
                    stats = build_everything()
                latest_allowed_sets = recompute_allowed_sets_from_master()
                latest_centre_streets = stats.get("centre_streets", [])
                latest_build_stats = {
                    "status": "ready",
                    "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    **{k: v for k, v in stats.items() if k != "centre_streets"},
                }

                # This is the key: map page will show toast + the new WO details, then reload
                _emit_updated_event("intake", items=applied_items)

                notify_user("Map updated ✅", f"Applied {applied} intake row(s) and rebuilt map.")
        except Exception as e:
            log(f"INTAKE POLL: error: {e}")


# =========================================================
# 7. RUN
# =========================================================

def main():
    log("Starting threads...")

    t1 = threading.Thread(target=watcher_loop, daemon=True)
    t1.start()

    t2 = threading.Thread(target=intake_poll_loop, daemon=True)
    t2.start()

    log(f"Local server running at: http://{HOST}:{PORT}/")
    log(f"Map URL: http://{HOST}:{PORT}/outputs/work_orders_map.html")
    log(f"New WO form: http://{HOST}:{PORT}/new")
    log(f"(Serving folder: {OUTPUT_DIR})")

    if basic_auth_required():
        log("UI AUTH: Basic Auth is ENABLED for /new (WO_UI_USER / WO_UI_PASS).")
    else:
        log("UI AUTH: Basic Auth is DISABLED. (Set WO_UI_USER and WO_UI_PASS to enable.)")

    app.run(host=HOST, port=PORT, debug=False, use_reloader=False)


if __name__ == "__main__":
    main()
