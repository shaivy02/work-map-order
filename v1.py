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
# District → Ward dependency (UI + validation)
# =========================================================
DISTRICT_TO_WARDS = {
    "EY":  ["1", "2", "3", "5", "7"],
    "NY":  ["6", "8", "15", "16", "17", "18"],
    "TEY": ["4", "9", "10", "11", "12", "13", "14", "19"],
    "SC":  ["20", "21", "22", "23", "24", "25"],
}

DUMP_TRUCK_PROVIDERS = [
    "Contractor: DVP-FGGE",
    "Contractor: TOA 1-1",
    "Contractor: TOA 1-2",
    "Contractor: TOA 1-3",
    "Contractor: TOA 1-4",
    "Contractor: TOA 1-5",
    "Contractor: TOA 2-1",
    "Contractor: TOA 2-2",
    "Contractor: TOA 2-3",
    "Contractor: TOA 2-4",
    "Contractor: TOA 2-5",
    "In-House: Bayview",
    "In-House: Bering",
    "In-House: Bermondsey",
    "In-House: Boncer",
    "In-House: Castlefield",
    "In-House: Disco",
    "In-House: Eastern",
    "In-House: Ellesmere/Midland",
    "In-House: Ingram",
    "In-House: King",
    "In-House: Leslie",
    "In-House: Morningside",
    "In-House: Murray",
    "In-House: Nantucket",
    "In-House: New Toronto",
    "In-House: Sheppard",
    "In-House: Toryork",
    "In-House: Transit Road",
    "In-House: Wellington",
    "N/A",
]

TOA_AREAS = [
    "TOA 1-1", "TOA 1-2", "TOA 1-3", "TOA 1-4", "TOA 1-5",
    "TOA 2-1", "TOA 2-2", "TOA 2-3", "TOA 2-4", "TOA 2-5",
    "DVP-FGGE",
]

SIDE_OPTIONS = ["Both Sides", "One Side"]

ROAD_SIDE_OPTIONS = ["North", "South", "East", "West", "East/West", "North/South"]

SNOW_DUMP_SITES = [
    "Bering Yard",
    "Eastern Yard",
    "Keelesdale Yard",
    "King Yard",
    "Morningside Yard",
    "New Toronto Yard",
    "Unwin Yard",
    "N/A - Relocation of snow",
    "Other",
]


def wards_for_district(district_val: str):
    d = str(district_val or "").strip().upper()
    return DISTRICT_TO_WARDS.get(d, [])

# =========================================================
# 0B. DATA-ENTRY (INTAKE) SETTINGS
# =========================================================

INTAKE_PATH = os.path.join(BASE_DIR, "intake_submissions.csv")
INTAKE_POLL_SECONDS = 10
INTAKE_EXTRA_COLS = ["__submitted_at", "__edited_at", "__submission_id", "__batch_id", "__status"]
PENDING_GRACE_SECONDS = 60  # keep rows editable for 60s before they can be applied


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
    # === EXISTING (DO NOT MOVE) ===
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

    # === NEW — ADMIN / OPS FIELDS ===
    "Shift Start Date and Time",
    "Shift End Date and Time",
    "Hours Worked",

    "Supervisor 1",
    "Supervisor 2",
    "Supervisor 3",

    "Equipment Method",
    "Contracted Crew?",
    "Contractor: # of Crews",
    "Contractor: Crew TOA Area",
    "Contractor: Crew Number",

    "In-House: Staff Responsibility",
    "In-House: # of Staff",

    "# of Equipment (Dump Trucks)",
    "Dump Truck Provider Contractor",

    "RequestID",

    "# of Loads",
    "Tonnes",

    "One Side/ Both Sides",
    "Side of Road Cleared",

    "Snow Dumped Site",

    # === NEW — COMMENTS ===
    "Comments",
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

DISPLAY_FIELDS_FORM = [
    "WO",
    "District__NL",
    "Ward__NL",
    "Date__NL",
    "Shift__NL",
    "Supervisor__NL",
    "Location",
    "From",
    "To",
    "Type__NL",

    "# of Equipment (Dump Trucks)",
    "Dump Truck Provider Contractor",
    "# of Loads",
    "Tonnes",
    "One Side/ Both Sides",
    "Side of Road Cleared",
    "Snow Dumped Site",
    "Comments",

    "__submission_id",
]

def master_col_for_form_field(form_key: str) -> str:
    # FORM_TO_MASTER covers the “__NL” ones + From/To/Type etc.
    # Any fields not listed there are assumed to match master column names exactly.
    return FORM_TO_MASTER.get(form_key, form_key)

def value_for_form_field(row: dict, form_key: str):
    mcol = master_col_for_form_field(form_key)
    return row.get(mcol, "")

def ensure_intake_file():
    if not os.path.exists(INTAKE_PATH):
        log(f"INTAKE: creating new intake file at {INTAKE_PATH}")
        df = pd.DataFrame(columns=MASTER_COLUMNS + INTAKE_EXTRA_COLS)
        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")
        return

    # If file exists but missing new columns, patch it safely
    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        changed = False
        for c in INTAKE_EXTRA_COLS:
            if c not in df.columns:
                df[c] = ""
                changed = True

        for c in MASTER_COLUMNS:
            if c not in df.columns:
                df[c] = ""
                changed = True

        if changed:
            df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")
            log("INTAKE: patched intake file to include required columns.")

def ensure_master_has_columns():
    """
    Make sure MASTER_TRACKER_PATH contains all MASTER_COLUMNS (safe patch).
    Without this, intake fields that don't exist in the master CSV get dropped.
    """
    if not os.path.exists(MASTER_TRACKER_PATH):
        return

    with FILE_LOCK:
        try:
            df = pd.read_csv(MASTER_TRACKER_PATH, encoding="latin-1")
        except Exception:
            # fallback
            df = pd.read_csv(MASTER_TRACKER_PATH, encoding="utf-8")

        changed = False
        for c in MASTER_COLUMNS:
            if c not in df.columns:
                df[c] = ""
                changed = True

        # Keep __submission_id if present; if missing, create it
        if "__submission_id" not in df.columns:
            df["__submission_id"] = ""
            changed = True

        if changed:
            df.to_csv(MASTER_TRACKER_PATH, index=False, encoding="latin-1")
            log("MASTER: patched master tracker to include required columns.")




def compute_submission_id(row_dict: dict) -> str:
    """
    Compute a stable submission ID that ignores cosmetic differences
    (case, spacing, formatting) so logical duplicates are caught.
    """
    base = {}

    for k in MASTER_COLUMNS:
        v = str(row_dict.get(k, "")).strip().upper()

        # collapse whitespace
        v = re.sub(r"\s+", " ", v)

        # normalize common street abbreviations
        v = re.sub(r"\bST\b", "STREET", v)
        v = re.sub(r"\bAVE\b", "AVENUE", v)
        v = re.sub(r"\bRD\b", "ROAD", v)
        v = re.sub(r"\bBLVD\b", "BOULEVARD", v)
        v = re.sub(r"\bDR\b", "DRIVE", v)

        base[k] = v

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

    def check_allowed(field, label, allow_custom=False):
        val = normalize_blank(values.get(field))
        if not val:
            return

        # If allow_custom, do NOT restrict to allowed values
        if allow_custom:
            return

        allowed = allowed_sets.get(field) or []
        allowed_set = set(str(x).strip() for x in allowed if str(x).strip())
        if allowed_set and val not in allowed_set:
            errors.append(f"{label} not allowed: '{val}'")

    check_allowed("District\n", "District")
    check_allowed("Ward\n", "Ward")
    check_allowed("Supervisor\n", "Supervisor", allow_custom=True)
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


def compute_batch_id(rows: list) -> str:
    """
    Batch id is stable-ish for the whole submission (order-sensitive).
    """
    payload = json.dumps(rows, sort_keys=True, ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def append_batch_to_intake(list_of_values: list):
    """
    list_of_values: list[dict] where each dict has MASTER_COLUMNS keys.
    Writes multiple rows to intake with:
      - __batch_id shared
      - __submission_id per row
      - __status = PENDING
    Returns: (batch_id, inserted_count, per_row_results)
    """
    ensure_intake_file()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    clean_rows = []
    for values in list_of_values:
        row = {k: normalize_blank(values.get(k, "")) for k in MASTER_COLUMNS}
        clean_rows.append(row)

    batch_id = compute_batch_id(clean_rows)

    per_row_results = []
    inserted_count = 0

    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        if "__submission_id" not in df.columns:
            df["__submission_id"] = ""
        if "__batch_id" not in df.columns:
            df["__batch_id"] = ""
        if "__status" not in df.columns:
            df["__status"] = ""
        if "__submitted_at" not in df.columns:
            df["__submitted_at"] = ""

        existing_ids = set(df["__submission_id"].fillna("").astype(str).tolist())

        for row in clean_rows:
            submission_id = compute_submission_id(row)

            if submission_id in existing_ids:
                per_row_results.append({"__submission_id": submission_id, "inserted": False, "reason": "duplicate"})
                continue

            out = dict(row)
            out["__submitted_at"] = now
            out["__edited_at"] = ""
            out["__submission_id"] = submission_id
            out["__batch_id"] = batch_id
            out["__status"] = "PENDING"

            df = pd.concat([df, pd.DataFrame([out])], ignore_index=True)
            existing_ids.add(submission_id)
            inserted_count += 1
            per_row_results.append({"__submission_id": submission_id, "inserted": True, "reason": ""})

        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")

    log(f"INTAKE: accepted batch id={batch_id} inserted={inserted_count}/{len(clean_rows)}")
    return batch_id, inserted_count, per_row_results


def get_intake_row_by_submission_id(submission_id: str) -> dict:
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
    for k in MASTER_COLUMNS + INTAKE_EXTRA_COLS:
        out[k] = str(r.get(k, "")).strip()
    return out


def get_intake_batch_details(batch_id: str) -> list:
    bid = (batch_id or "").strip()
    if not bid or not os.path.exists(INTAKE_PATH):
        return []
    try:
        df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
    except Exception:
        df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

    if "__batch_id" not in df.columns:
        return []
    sub = df[df["__batch_id"].astype(str) == bid].copy()
    if sub.empty:
        return []

    rows = []
    for _, r in sub.iterrows():
        d = {}
        for k in MASTER_COLUMNS + INTAKE_EXTRA_COLS:
            d[k] = str(r.get(k, "")).strip()
        rows.append(d)
    return rows


def update_intake_row(submission_id: str, new_values: dict) -> bool:
    """
    Edit a single intake row (only if status is PENDING).
    IMPORTANT: Editing should NOT reset __submitted_at, otherwise it delays apply.
    Returns True if updated.
    """
    ensure_intake_file()
    sid = (submission_id or "").strip()
    if not sid:
        return False

    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        if "__submission_id" not in df.columns:
            return False
        if "__status" not in df.columns:
            df["__status"] = ""
        if "__edited_at" not in df.columns:
            df["__edited_at"] = ""

        idxs = df.index[df["__submission_id"].astype(str) == sid].tolist()
        if not idxs:
            return False

        i = idxs[-1]
        status = str(df.at[i, "__status"] or "").strip().upper()
        if status and status != "PENDING":
            # Don’t allow editing once applied (keeps master clean)
            return False

        # update master columns only
        for k in MASTER_COLUMNS:
            if k in new_values:
                df.at[i, k] = normalize_blank(new_values.get(k, ""))

        # record edit time (audit only) — DOES NOT affect apply eligibility
        df.at[i, "__edited_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")
        return True


def delete_intake_row(submission_id: str) -> bool:
    """
    Soft-delete a row by setting __status = DELETED (only if PENDING).
    """
    ensure_intake_file()
    sid = (submission_id or "").strip()
    if not sid:
        return False

    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        if "__submission_id" not in df.columns:
            return False
        if "__status" not in df.columns:
            df["__status"] = ""

        idxs = df.index[df["__submission_id"].astype(str) == sid].tolist()
        if not idxs:
            return False

        i = idxs[-1]
        status = str(df.at[i, "__status"] or "").strip().upper()
        if status and status != "PENDING":
            return False

        df.at[i, "__status"] = "DELETED"
        df.at[i, "__submitted_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")
        return True


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
    ensure_master_has_columns()
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

        # Ensure intake status columns exist
        if "__status" not in intake.columns:
            intake["__status"] = "PENDING"
        if "__batch_id" not in intake.columns:
            intake["__batch_id"] = ""

        intake["__status"] = intake["__status"].fillna("").astype(str)

        intake_ids = set(intake.get("__submission_id", pd.Series([], dtype=str)).astype(str))
        master_ids = set(master.get("__submission_id", pd.Series([], dtype=str)).astype(str))

        # Only apply rows that are:
        # - status == PENDING
        # - not already in master
        # - AND have been pending for at least PENDING_GRACE_SECONDS

        pending = intake[intake["__status"].astype(str).str.upper().eq("PENDING")].copy()

        # Parse __submitted_at safely
        ts = pd.to_datetime(pending.get("__submitted_at", ""), errors="coerce")
        # If missing/invalid timestamp, treat as "old" so it won't get stuck forever
        ts = ts.fillna(pd.Timestamp("1970-01-01"))

        now_ts = pd.Timestamp.now()
        age_seconds = (now_ts - ts).dt.total_seconds()

        eligible = pending[age_seconds >= float(PENDING_GRACE_SECONDS)].copy()

        new_rows = eligible[~eligible["__submission_id"].astype(str).isin(master_ids)].copy()


        if new_rows.empty:
            log("INTAKE APPLY: no new submissions to apply.")
            return 0, []


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

        # Mark applied rows as APPLIED in intake (so they won't re-apply)
        try:
            applied_ids = set(new_rows["__submission_id"].astype(str).tolist())
            mask = intake["__submission_id"].astype(str).isin(applied_ids)
            intake.loc[mask, "__status"] = "APPLIED"
            intake.to_csv(INTAKE_PATH, index=False, encoding="utf-8")
        except Exception as e:
            log(f"INTAKE APPLY: could not mark APPLIED in intake: {e}")


        with LAST_MASTER_WRITE_LOCK:
            LAST_MASTER_WRITE_BY_INTAKE_AT = time.time()

        after = len(master)
        applied = after - before
        log(f"INTAKE APPLY: applied {applied} new row(s) into MASTER_TRACKER.")
        return applied, applied_items

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

    # NOTE: This is a SEGMENT popup; include segment fields if you want.
    seg_idx = props.get("Segment_idx", "")
    total_segments = props.get("Total_Segments", "")

    loc = props.get("Location", "")
    to_ = props.get("To", "")
    frm = props.get("From", "")

    return f"""
    <div style="font-family:Arial;font-size:13px;line-height:1.25;">
      <b>WO:</b> {html.escape(str(props.get("WO", "")))}<br>
      <b>Segment:</b> {html.escape(str(seg_idx))}<br>
      <b>Total Segments:</b> {html.escape(str(total_segments))}<br>
      <b>Location:</b> {html.escape(str(loc))}<br>
      <b>To:</b> {html.escape(str(to_))}<br>
      <b>From:</b> {html.escape(str(frm))}<br>
      <b>Distance (m):</b> {html.escape(str(wo_m_str))}<br>
      <b>Distance (km):</b> {html.escape(str(wo_km_str))}<br>
      {extra}
      <hr style="margin:6px 0;">
      <b>Supervisor:</b> {sup_html}<br>
      <b>Shift:</b> {shift_html}<br>
    </div>
    """

def build_workorder_popup(props: dict) -> str:
    wo = props.get("WO", "")
    total_segments = props.get("Total_Segments", "")

    loc = props.get("Location", "")
    to_ = props.get("To", "")
    frm = props.get("From", "")

    wo_m_disp = props.get("WO_m_display", "")
    wo_km_disp = props.get("WO_km_display", "")

    route_mode = props.get("route_mode", "")
    supervisor = props.get("Supervisor", "")
    district = props.get("District", "")
    ward = props.get("Ward", "")
    date = props.get("Date", "")
    shift = props.get("Shift", "")
    work_type = props.get("Type", "")

    dump_trucks = props.get("DumpTrucks", "")
    dump_provider = props.get("DumpTruckProvider", "")
    loads = props.get("Loads", "")
    tonnes = props.get("Tonnes", "")
    side = props.get("Side", "")
    road_side = props.get("RoadSide", "")
    snow_dump_site = props.get("SnowDumpSite", "")
    comments = props.get("Comments", "")

    extra = ""
    if route_mode:
        extra = (
            "<div style='margin-top:6px;padding:6px;border-radius:6px;background:#fff3cd;border:1px solid #ffeeba;'>"
            f"<b>Routing:</b> {html.escape(str(route_mode))}"
            "</div>"
        )

    return f"""
    <div style="font-family:Arial;font-size:13px;line-height:1.25;">
      <b>WO:</b> {html.escape(str(wo))}<br>
      <b>Total Segments:</b> {html.escape(str(total_segments))}<br>
      <b>Location:</b> {html.escape(str(loc))}<br>
      <b>To:</b> {html.escape(str(to_))}<br>
      <b>From:</b> {html.escape(str(frm))}<br>
      <b>Distance (m):</b> {html.escape(str(wo_m_disp))}<br>
      <b>Distance (km):</b> {html.escape(str(wo_km_disp))}<br>
      {extra}
      <hr style="margin:6px 0;">
      <b>Supervisor:</b> {html.escape(str(supervisor))}<br>
      <b>District:</b> {html.escape(str(district))}<br>
      <b>Ward:</b> {html.escape(str(ward))}<br>
      <b>Date:</b> {html.escape(str(date))}<br>
      <b>Shift:</b> {html.escape(str(shift))}<br>
      <b>Type:</b> {html.escape(str(work_type))}<br>
      <hr style="margin:6px 0;">
      <b>Dump Trucks:</b> {html.escape(str(dump_trucks))}<br>
      <b>Dump Truck Provider:</b> {html.escape(str(dump_provider))}<br>
      <b>Loads:</b> {html.escape(str(loads))}<br>
      <b>Tonnes:</b> {html.escape(str(tonnes))}<br>
      <b>Side:</b> {html.escape(str(side))}<br>
      <b>Road Side:</b> {html.escape(str(road_side))}<br>
      <b>Snow Dump Site:</b> {html.escape(str(snow_dump_site))}<br>
      <b>Comments:</b> {html.escape(str(comments))}<br>
    </div>
    """

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
                    dy = lat2 - lat1
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
            """
            Compute the length of a MultiLineString in metres.

            - If coordinates look like lon/lat degrees (|lon| <= 180 and |lat| <= 90),
              use haversine (geodesic).
            - Otherwise, treat them as planar (e.g., EPSG:xxxx metres) and use
              simple Euclidean distance in the native units (assumed metres).
            """
            if not coords_multiline:
                return 0.0

            sample_lon = None
            sample_lat = None
            for line in coords_multiline:
                if line:
                    sample_lon, sample_lat = line[0]
                    break

            if sample_lon is None or sample_lat is None:
                return 0.0

            is_degrees = (abs(sample_lon) <= 180.0 and abs(sample_lat) <= 90.0)

            total = 0.0
            if is_degrees:
                for line in coords_multiline:
                    if not line or len(line) < 2:
                        continue
                    for (lon1, lat1), (lon2, lat2) in zip(line, line[1:]):
                        total += haversine_m(lat1, lon1, lat2, lon2)
            else:
                for line in coords_multiline:
                    if not line or len(line) < 2:
                        continue
                    for (x1, y1), (x2, y2) in zip(line, line[1:]):
                        dx = x2 - x1
                        dy = y2 - y1
                        total += math.hypot(dx, dy)

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
            return f"{val:.{decimals}f}"

        intersection_accum = {}

        def clean_text(v) -> str:
            """Safe string: NaN/None -> '' and strip."""
            try:
                if pd.isna(v):
                    return ""
            except Exception:
                pass
            if v is None:
                return ""
            return str(v).strip()

        def normalize_wo_id(v) -> str:
            """
            WO display normalization:
            - NaN/None -> ''
            - 909090.0 -> '909090'
            - keeps alphanumeric IDs intact
            """
            try:
                if pd.isna(v):
                    return ""
            except Exception:
                pass
            if v is None:
                return ""

            # If it's a numeric WO coming in as float, drop .0
            try:
                fv = float(v)
                if math.isfinite(fv) and fv.is_integer():
                    return str(int(fv))
            except Exception:
                pass

            s = str(v).strip()
            if s.endswith(".0"):
                head = s[:-2]
                if head.replace(".", "", 1).isdigit():
                    return head
            return s


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

            def clean_cell(v):
                return "" if pd.isna(v) else str(v)

            for form_key in popup_columns:
                label = popup_labels.get(form_key, form_key)

                # Keep your special formatting for supervisor/shift,
                # but trigger it based on FORM keys now.
                if form_key == "Supervisor__NL":
                    cell_html = supervisor_cell_html
                elif form_key == "Shift__NL":
                    cell_html = shift_cell_html
                else:
                    val = value_for_form_field(row, form_key)
                    cell_html = html.escape(clean_cell(val))

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
              <hr style="margin:6px 0;">
              <b>Dump Trucks:</b> {html.escape(str(props.get("DumpTrucks","")))}<br>
              <b>Dump Truck Provider:</b> {html.escape(str(props.get("DumpTruckProvider","")))}<br>
              <b>Loads:</b> {html.escape(str(props.get("Loads","")))}<br>
              <b>Tonnes:</b> {html.escape(str(props.get("Tonnes","")))}<br>
              <b>Side:</b> {html.escape(str(props.get("Side","")))}<br>
              <b>Road Side:</b> {html.escape(str(props.get("RoadSide","")))}<br>
              <b>Snow Dump Site:</b> {html.escape(str(props.get("SnowDumpSite","")))}<br>
              <b>Comments:</b> {html.escape(str(props.get("Comments","")))}<br>
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
                if (kind === 'intake') {
                  tList.innerHTML = '<div style="color:#666;font-size:12px;">Details not available.</div>';
                }
              }

              toast.style.display = 'block';

              btnReload.onclick = function(){
                safeReload();
              };
              btnDismiss.onclick = function(){
                toast.style.display = 'none';
                if (reloadTimer) { clearTimeout(reloadTimer); reloadTimer = null; }
              };
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

                if (ev.data === 'updated') {
                  showToast({ kind: 'update', count: 0, items: [] });
                  return;
                }

                var payload = null;
                try { payload = JSON.parse(ev.data); } catch(e) {}
                if (payload && payload.event === 'updated') {
                  showToast(payload);
                  return;
                }
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

            forceLinksToBlank(document);

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
        # ✅ FIXED TYPO: f olium -> folium
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

                # ---------------------------------------------------------
        # ✅ Remove Leaflet's default "blue focus box" on click,
        #    and add a slow strobe/pulse on the clicked segment only
        # ---------------------------------------------------------
        wo_click_fx_css = """
        <style>
          /* Leaflet (SVG) can show a blue focus outline rectangle after click */
          .leaflet-container .leaflet-interactive:focus {
            outline: none !important;
          }

          /* Clicked segment pulse (keeps original stroke color) */
          .leaflet-container .leaflet-interactive.wo-active {
            outline: none !important;
            animation: woPulse 1.6s ease-in-out infinite;
          }

          @keyframes woPulse {
            0%   { stroke-opacity: 1;    stroke-width: 10; }
            50%  { stroke-opacity: 0.35; stroke-width: 6; }
            100% { stroke-opacity: 1;    stroke-width: 10; }
          }
        </style>
        """
        m.get_root().html.add_child(folium.Element(wo_click_fx_css))

        wo_click_fx_js = f"""
        <script>
          (function() {{
            function activateTarget(t) {{
              // remove from any previous active path
              document.querySelectorAll('.leaflet-interactive.wo-active').forEach(function(el) {{
                el.classList.remove('wo-active');
              }});

              if (!t || !t.classList) return;
              if (!t.classList.contains('leaflet-interactive')) return;

              // prevent focus outline + apply pulse class
              try {{
                t.setAttribute('tabindex', '-1');
                if (typeof t.blur === 'function') t.blur();
              }} catch (e) {{}}

              t.classList.add('wo-active');
            }}

            var map = {m.get_name()};
            if (!map || !map.on) return;

            map.on('click', function(e) {{
              var t = e && e.originalEvent ? e.originalEvent.target : null;
              activateTarget(t);
            }});
          }})();
        </script>
        """
        m.get_root().html.add_child(folium.Element(wo_click_fx_js))


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

        popup_columns = DISPLAY_FIELDS_FORM[:]  # FORM keys
        popup_labels = {k: k for k in popup_columns}  # EXACT webform names


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

        def add_intersection_points_for_path(
            group_for_points,
            district_color,
            wo_id,
            loc_raw,
            from_raw,
            to_raw,
            node_path
        ):
            """
            Draw intersection points ONLY as visual dots.
            ❌ No popup
            ❌ No tooltip
            """
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

                folium.CircleMarker(
                    location=latlng,
                    radius=INTERSECTION_POINT_RADIUS,
                    color=district_color,
                    weight=2,
                    opacity=INTERSECTION_POINT_OPACITY,
                    fill=True,
                    fill_opacity=INTERSECTION_POINT_FILL_OPACITY,
                    # ❌ popup REMOVED
                    # ❌ tooltip REMOVED
                ).add_to(group_for_points)

                # GeoJSON export kept (silent, no UI noise)
                geojson_features.append({
                    "type": "Feature",
                    "geometry": {
                        "type": "Point",
                        "coordinates": [latlng[1], latlng[0]]
                    },
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
            route_mode="",
            dump_trucks="",
            dump_provider="",
            loads="",
            tonnes="",
            side="",
            road_side="",
            snow_dump_site="",
            comments="",
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

                def clean(v):
                    return "" if pd.isna(v) else str(v)

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

                    # ✅ WEBFORM-style DISPLAY fields (NEW)
                    "WO": str(wo_id),
                    "District__NL": str(district_val),
                    "Ward__NL": str(ward),
                    "Date__NL": str(date_str),
                    "Shift__NL": str(shift_str),
                    "Supervisor__NL": str(supervisor_raw).strip(),
                    "Type__NL": str(work_type),

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
                    "DumpTrucks": clean(dump_trucks),
                    "DumpTruckProvider": clean(dump_provider),
                    "Loads": clean(loads),
                    "Tonnes": clean(tonnes),
                    "Side": clean(side),
                    "RoadSide": clean(road_side),
                    "SnowDumpSite": clean(snow_dump_site),
                    "Comments": clean(comments),
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

            props = {
                "feature_kind": "workorder_line",
                "WO_ID": normalize_wo_id(wo_id),

                # Raw values used in geometry & routing
                "Location": str(loc_raw),
                "From": str(from_raw),
                "To": str(to_raw),
                "Location_resolved": loc_key,
                "From_resolved": from_key,
                "To_resolved": to_key,

                # MASTER-style fields (KEEP – existing logic depends on these)
                "District": district_val,
                "Ward": ward_val,
                "Date": date_val,
                "Shift": shift_val,
                "Supervisor": str(supervisor_raw).strip(),
                "SupervisorKey": sup_key,
                "Type": type_val,

                # ✅ WEBFORM-style DISPLAY fields (NEW – used by popup/tooltips)
                "WO": normalize_wo_id(wo_id),
                "District__NL": str(district_val),
                "Ward__NL": str(ward_val),
                "Date__NL": str(date_val),
                "Shift__NL": str(shift_val),
                "Supervisor__NL": str(supervisor_raw).strip(),
                "Type__NL": str(type_val),
                # --- NEW: equipment fields (from the same row that created this WO) ---
                "DumpTrucks": clean_text(row.get("# of Equipment (Dump Trucks)", "")),
                "DumpTruckProvider": clean_text(row.get("Dump Truck Provider Contractor", "")),
                "Loads": clean_text(row.get("# of Loads", "")),
                "Tonnes": clean_text(row.get("Tonnes", "")),
                "Side": clean_text(row.get("One Side/ Both Sides", "")),
                "RoadSide": clean_text(row.get("Side of Road Cleared", "")),
                "SnowDumpSite": clean_text(row.get("Snow Dumped Site", "")),
                "Comments": clean_text(row.get("Comments", "")),

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
                fields=["WO_ID", "Location", "From", "To", "District__NL", "Supervisor__NL", "Date__NL", "Shift__NL"],
                aliases=["WO", "Location", "From", "To", "District__NL", "Supervisor__NL", "Date__NL", "Shift__NL"],
                sticky=False,
            )

            tooltip.add_to(gj)

            # ✅ ALWAYS define popup_html first
            popup_html = build_workorder_popup(props)

            # Optional: append routing note safely (only if route_mode exists)
            if route_mode:
                popup_html = popup_html.replace(
                    "</table>",
                    f"</table><div style='margin-top:8px;padding:6px;border-radius:6px;background:#fff3cd;border:1px solid #ffeeba;'>"
                    f"<b>Routing:</b> {html.escape(str(route_mode))}</div>"
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

            if start_node is None or end_node is None or start_node == end_node:
                coords_to_use = full_street_multiline(loc_key)
                if coords_to_use:
                    geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
                    add_line_feature(
                        row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                        supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                        loc_key=loc_key, from_key=from_key, to_key=to_key,
                        route_mode="Location Not Found. Mapping Full Street as FALLBACK"
                    )
                    subsegment_count += 1
                    if is_intake_row:
                        intake_mapped_counter += 1
                        record_intake_debug(
                            "MAPPED", submission_id, wo_id,
                            "Location Not Found. Mapping Full Street as FALLBACK",
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

            path = shortest_path_for_street(loc_key, start_node, end_node)

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
                            route_mode="Location Not Found. Mapping Full Street as FALLBACK"
                        )
                        subsegment_count += 1
                        if is_intake_row:
                            intake_mapped_counter += 1
                            record_intake_debug(
                                "MAPPED", submission_id, wo_id,
                                "Location Not Found. Mapping Full Street as FALLBACK",
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
                route_mode="Exact Location found and Mapped"
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
                dump_trucks=row.get("# of Equipment (Dump Trucks)", ""),
                dump_provider=row.get("Dump Truck Provider Contractor", ""),
                loads=row.get("# of Loads", ""),
                tonnes=row.get("Tonnes", ""),
                side=row.get("One Side/ Both Sides", ""),
                road_side=row.get("Side of Road Cleared", ""),
                snow_dump_site=row.get("Snow Dumped Site", ""),
                comments=row.get("Comments", ""),
                route_mode="Exact Location found and Mapped"
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


def format_date_from_picker(val: str) -> str:
    """
    Converts YYYY-MM-DD → 3-Mar-25
    """
    try:
        dt = datetime.strptime(val, "%Y-%m-%d")
        return dt.strftime("%-d-%b-%y")
    except Exception:
        return val

# =========================================================
# 5. LIVE SERVER + SSE EVENTS + DATA ENTRY UI
# =========================================================

app = Flask(__name__)
events = Queue()
latest_build_stats = {"status": "not built yet"}
latest_centre_streets = []
latest_allowed_sets = {}

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
  <title>Add Work Orders (Batch)</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 16px; max-width: 1100px; }
    .card { border: 1px solid #ddd; border-radius: 12px; padding: 14px; margin-bottom: 12px; }
    .help { color:#555; font-size: 13px; margin-top: 6px; }
    .err { background:#ffecec; border:1px solid #ffb2b2; padding:10px; border-radius:10px; }
    .ok  { background:#eaffea; border:1px solid #a6e6a6; padding:12px; border-radius:12px; }
    button {
      padding: 10px 12px; border-radius: 10px;
      border: none; background: #111; color: #fff; font-size: 14px; font-weight: 900;
      cursor: pointer;
    }
    .ghost { background:#f2f2f2; color:#111; }
    input, select {
      width: 100%; padding: 9px 10px; border-radius: 10px;
      border: 1px solid #ccc; font-size: 14px;
    }
    table { width: 100%; border-collapse: collapse; }
    th, td { border-bottom: 1px solid #eee; padding: 8px; vertical-align: top; }
    th { text-align: left; font-size: 12px; color:#333; }
    code { background: #f6f6f6; padding: 2px 6px; border-radius: 6px; }
    a { color:#111; }
    .pill {
      display:inline-block; padding: 3px 8px; border-radius: 999px;
      background:#111; color:#fff; font-size: 12px; font-weight: 900;
    }
    .rowBtns { display:flex; gap:8px; margin-top: 10px; }
    
    /* Countdown agitation */
    .timerWarn {
        border-color: rgba(220, 0, 0, 0.35) !important;
        background: rgba(255, 235, 235, 0.95) !important;
        animation: pulseWarn 0.6s infinite;
    }
    .timerFinal {
        animation: pulseWarn 0.35s infinite, shakeWarn 0.35s infinite;
    }
    #pendingTimer {
        font-variant-numeric: tabular-nums;
    }
    @keyframes pulseWarn {
        0%   { transform: scale(1); }
        50%  { transform: scale(1.02); }
        100% { transform: scale(1); }
    }
    @keyframes shakeWarn {
        0% { transform: translateX(0); }
        25% { transform: translateX(-2px); }
        50% { transform: translateX(2px); }
        75% { transform: translateX(-2px); }
        100% { transform: translateX(0); }
    }
  </style>
</head>
<body>
  <div class="card">
    <h2 style="margin:0 0 6px 0;">Add Work Orders (Batch)</h2>
    <p class="help" style="margin:0;">
      <a href="/">← Back</a> |
      <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">Open Map</a>
    </p>
    <div class="help" style="margin-top:8px;">
      Tip: Add multiple rows and submit once. You can edit any <b>PENDING</b> row instantly before it gets applied.
    </div>
  </div>

  {% if batch and batch_id %}
  <div class="card ok">
    <div style="display:flex;align-items:center;justify-content:space-between;gap:10px;">
        <div id="pendingTimerBox" style="margin-top:12px;padding:12px;border-radius:12px;border:1px solid rgba(0,0,0,0.10);background:rgba(255,255,255,0.85);">
      <div style="font-weight:900;font-size:14px;">
        Editing window: <span id="pendingTimer" style="font-size:18px;">--:--</span>
      </div>
      <div class="help" style="margin-top:6px;">
        You can edit any <b>PENDING</b> row until the timer ends. In the last 10 seconds, the timer will flash.
      </div>
    </div>

      <div>
        <span class="pill">Submitted ✅</span>
        <div style="margin-top:6px;font-weight:900;font-size:14px;">
          Batch saved to intake.
        </div>
        <div style="margin-top:6px;color:#333;font-size:13px;">
          Batch ID: <code>{{ batch_id }}</code>
          &nbsp; • &nbsp;
          Inserted: <code>{{ inserted_count }}</code>
        </div>
      </div>
      <div>
        <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer"
           style="display:inline-block;padding:10px 12px;border-radius:10px;background:#111;color:#fff;text-decoration:none;font-weight:900;">
          Open Map
        </a>
      </div>
    </div>

    <div class="help" style="margin-top:10px;">
      Rows below are in intake. You can edit any row that is still <b>PENDING</b>.
    </div>

    <table style="margin-top:10px;">
      <thead>
        <tr>
            <th>WO</th>
            <th>Date</th>
            <th>District</th>
            <th>Ward</th>
            <th>Supervisor</th>
            <th>Shift</th>
            <th>Type</th>
            <th>Dump Trucks</th>
            <th>Dump Truck Provider</th>
            <th>Loads</th>
            <th>Tonnes</th>
            <th>Side</th>
            <th>Road Side</th>
            <th>Snow Dump Site</th>
            <th>Comments</th>
            <th>Location</th>
            <th>From</th>
            <th>To</th>
            <th>Status</th>
            <th>Edit</th>
        </tr>
      </thead>
      <tbody>
      {% for r in batch %}
        <tr>
          <td>{{ r.get('WO','') }}</td>
          <td>{{ r.get('Date\\n','') }}</td>
          <td>{{ r.get('District\\n','') }}</td>
          <td>{{ r.get('Ward\\n','') }}</td>
          <td>{{ r.get('Supervisor\\n','') }}</td>
          <td>{{ r.get('Shift\\n','') }}</td>
          <td>{{ r.get('Type (Road Class/ School, Bridge)\\n','') }}</td>
          <td>{{ r.get('# of Equipment (Dump Trucks)','') }}</td>
          <td>{{ r.get('Dump Truck Provider Contractor','') }}</td>
          <td>{{ r.get('# of Loads','') }}</td>
          <td>{{ r.get('Tonnes','') }}</td>
          <td>{{ r.get('One Side/ Both Sides','') }}</td>
          <td>{{ r.get('Side of Road Cleared','') }}</td>
          <td>{{ r.get('Snow Dumped Site','') }}</td>
          <td style="max-width:220px;">{{ r.get('Comments','') }}</td>
          <td>{{ r.get('Location','') }}</td>
          <td>{{ r.get('From ','') }}</td>
          <td>{{ r.get('To','') }}</td>
          <td><code>{{ r.get('__status','') }}</code></td>

          <td>
            {% if (r.get('__status','')|upper) == 'PENDING' %}
              <a href="/edit/{{ r.get('__submission_id','') }}">Edit</a>
            {% else %}
              <span style="color:#777;">Locked</span>
            {% endif %}
          </td>
        </tr>
      {% endfor %}
      </tbody>
    </table>
  </div>
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
    <form method="post" action="/new" autocomplete="off" id="batchForm">

      <div class="help" style="margin-bottom:8px;">
        These fields apply per row. Use <b>+ Add Row</b> for multiple WOs.
      </div>

      <table id="woTable">
        <thead>
          <tr>
            <th style="width:110px;">WO</th>
            <th style="width:150px;">Date</th>
            <th style="width:90px;">District</th>
            <th style="width:90px;">Ward</th>
            <th style="width:180px;">Supervisor</th>
            <th style="width:180px;">Shift</th>
            <th style="width:220px;">Type</th>
            <th style="width:140px;">Dump Trucks</th>
            <th style="width:160px;">Dump Truck Provider</th>
            <th style="width:120px;">Loads</th>
            <th style="width:120px;">Tonnes</th>
            <th style="width:140px;">Side</th>
            <th style="width:160px;">Road Side</th>
            <th style="width:180px;">Snow Dump Site</th>
            <th style="width:260px;">Comments</th>
            <th>Location</th>
            <th>From</th>
            <th>To</th>
            <th style="width:80px;">Remove</th>
          </tr>
        </thead>
        <tbody id="woTbody"></tbody>
      </table>

      <datalist id="streets">
        {% for st in streets %}
        <option value="{{ st }}"></option>
        {% endfor %}
      </datalist>

      <datalist id="supervisors_list">
        {% for s in supervisors %}
        <option value="{{ s }}"></option>
        {% endfor %}
      </datalist>

      <div class="rowBtns">
        <button type="button" id="addRowBtn">+ Add Row</button>
        <button type="submit">Submit Batch</button>
      </div>

      <div class="help" style="margin-top:10px;">
        After submit, intake applies automatically every {{ intake_poll_seconds }}s and the map page will toast + refresh.
      </div>
    </form>
  </div>

<script>
(function(){
  var districts = {{ districts_json | safe }};
  var districtToWards = {{ district_to_wards_json | safe }};
  var shifts = {{ shifts_json | safe }};
  var types = {{ types_json | safe }};
  var dumpTruckProvidersOptions = {{ dump_truck_providers_html | tojson | safe }};
  var snowDumpSitesOptions = {{ snow_dump_sites_html | tojson | safe }};


  var tbody = document.getElementById('woTbody');
  var addBtn = document.getElementById('addRowBtn');

  function optList(arr){
    return (arr || []).map(function(x){
      return '<option value="' + escapeHtml(x) + '">' + escapeHtml(x) + '</option>';
    }).join('');
  }

  function escapeHtml(s){
    return (s || '').toString()
      .replaceAll('&','&amp;')
      .replaceAll('<','&lt;')
      .replaceAll('>','&gt;')
      .replaceAll('"','&quot;')
      .replaceAll("'","&#39;");
  }

  function districtSelectHtml(name){
    var o = '<option value="">--</option>';
    (districts||[]).forEach(function(d){
      o += '<option value="' + escapeHtml(d) + '">' + escapeHtml(d) + '</option>';
    });
    return '<select name="' + name + '" class="districtSel" required>' + o + '</select>';
  }

  function wardSelectHtml(name){
    return '<select name="' + name + '" class="wardSel" required><option value="">--</option></select>';
  }

  function shiftSelectHtml(name){
    var o = '<option value="">--</option>' + optList(shifts);
    return '<select name="' + name + '" required>' + o + '</select>';
  }

  function typeSelectHtml(name){
    var o = '<option value="">--</option>' + optList(types);
    return '<select name="' + name + '" required>' + o + '</select>';
  }

  function addRow(){
    var idx = tbody.children.length;
    var tr = document.createElement('tr');

    tr.innerHTML = ''
      + '<td><input name="WO_' + idx + '" required placeholder="12345"></td>'
      + '<td><input type="date" name="Date__NL_' + idx + '" required></td>'
      + '<td>' + districtSelectHtml('District__NL_' + idx) + '</td>'
      + '<td>' + wardSelectHtml('Ward__NL_' + idx) + '</td>'
      + '<td><input name="Supervisor__NL_' + idx + '" list="supervisors_list" required placeholder="Supervisor"></td>'
      + '<td>' + shiftSelectHtml('Shift__NL_' + idx) + '</td>'
      + '<td>' + typeSelectHtml('Type__NL_' + idx) + '</td>'
      + '<td><input name="# of Equipment (Dump Trucks)_' + idx + '" type="number" min="0"></td>'
      + '<td><select name="Dump Truck Provider Contractor_' + idx + '">'
      +   '<option value="">--</option>'
      +   dumpTruckProvidersOptions
      + '</select></td>'
      + '<td><input name="# of Loads_' + idx + '" type="number" min="0"></td>'
      + '<td><input name="Tonnes_' + idx + '" type="number" step="0.01" min="0"></td>'
      + '<td><select name="One Side/ Both Sides_' + idx + '">'
      +   '<option value="">--</option>'
      +   '<option>Both Sides</option>'
      +   '<option>One Side</option>'
      + '</select></td>'
      + '<td><select name="Side of Road Cleared_' + idx + '">'
      +   '<option value="">--</option>'
      +   '<option>North</option><option>South</option>'
      +   '<option>East</option><option>West</option>'
      +   '<option>East/West</option><option>North/South</option>'
      + '</select></td>'
      + '<td><select name="Snow Dumped Site_' + idx + '">'
      +   '<option value="">--</option>'
      +   snowDumpSitesOptions
      + '</select></td>'
      + '<td><textarea name="Comments_' + idx + '" rows="2" '
      +   'style="width:100%;padding:9px 10px;border-radius:10px;border:1px solid #ccc;font-size:14px;resize:vertical;" '
      +   'placeholder="Notes / comments (optional)"></textarea></td>'
      + '<td><input name="Location_' + idx + '" list="streets" required placeholder="Location"></td>'
      + '<td><input name="From_' + idx + '" list="streets" placeholder="From"></td>'
      + '<td><input name="To_' + idx + '" list="streets" placeholder="To"></td>'
      + '<td><button type="button" class="ghost rmBtn">Remove</button></td>';

    tbody.appendChild(tr);

    var rm = tr.querySelector('.rmBtn');
    rm.onclick = function(){
      tr.remove();
      // reindex on remove (simple approach)
      reindex();
    };

    var dsel = tr.querySelector('.districtSel');
    var wsel = tr.querySelector('.wardSel');

    function setWards(d){
      var dd = (d||'').toString().trim().toUpperCase();
      var wards = districtToWards[dd] || [];
      wsel.innerHTML = '<option value="">--</option>';
      wards.forEach(function(w){
        var opt = document.createElement('option');
        opt.value = w; opt.textContent = w;
        wsel.appendChild(opt);
      });
      if (wards.length) wsel.value = wards[0];
    }
    dsel.addEventListener('change', function(){ setWards(dsel.value); });
  }

  function reindex(){
    // Rebuild names so backend can parse 0..N cleanly
    var rows = Array.from(tbody.querySelectorAll('tr'));
    tbody.innerHTML = '';
    rows.forEach(function(_, i){
      addRow();
      // NOTE: simplest: don’t preserve removed row values during reindex.
      // If you want value-preserving reindex, tell me and I’ll upgrade it.
    });
  }

  addBtn.onclick = addRow;

  // start with 1 row
  addRow();
})();
</script>

<script>
(function(){
  // Only runs on the "Submitted ✅" view when batch exists
  var seconds = {{ apply_in_seconds | default(0) }};
  var box = document.getElementById('pendingTimerBox');
  var el = document.getElementById('pendingTimer');
  if (!box || !el) return;

  function fmt(s){
    s = Math.max(0, parseInt(s || 0, 10));
    var m = Math.floor(s / 60);
    var r = s % 60;
    return String(m).padStart(2,'0') + ':' + String(r).padStart(2,'0');
  }

  function tick(){
    el.textContent = fmt(seconds);

    // agitation rules
    box.classList.remove('timerWarn','timerFinal');
    if (seconds <= 10 && seconds > 0){
      box.classList.add('timerFinal');
    } else if (seconds <= 20 && seconds > 0){
      box.classList.add('timerWarn');
    }

    if (seconds <= 0){
      el.textContent = "00:00";
      // Optional: show "submitted" state
      box.classList.remove('timerWarn','timerFinal');
      box.style.background = 'rgba(240,240,240,0.95)';
      return;
    }

    seconds -= 1;
    setTimeout(tick, 1000);
  }

  tick();
})();
</script>

</body>
</html>
"""
EDIT_FORM_HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Edit Intake Work Order</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 16px; max-width: 900px; }
    .card { border: 1px solid #ddd; border-radius: 12px; padding: 14px; margin-bottom: 12px; }
    label { display:block; margin-top: 10px; font-weight: 800; }
    input, select { width: 100%; padding: 10px; border-radius: 10px; border:1px solid #ccc; }
    .help { color:#555; font-size: 13px; margin-top: 6px; }
    .err { background:#ffecec; border:1px solid #ffb2b2; padding:10px; border-radius:10px; }
    .ok  { background:#eaffea; border:1px solid #a6e6a6; padding:12px; border-radius:12px; }
    button { margin-top: 14px; padding: 12px 14px; border-radius: 12px; border:none; background:#111; color:#fff; font-weight:900; cursor:pointer; }
    .ghost { background:#f2f2f2; color:#111; }
    code { background:#f6f6f6; padding:2px 6px; border-radius:6px; }
  </style>
</head>
<body>
  <div class="card">
    <h2 style="margin:0 0 6px 0;">Edit Intake Row</h2>
    <div class="help">
      <a href="/new?bid={{ row.get('__batch_id','') }}">← Back to Batch</a> |
      <a href="/">Home</a> |
      <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">Open Map</a>
    </div>
    <div class="help" style="margin-top:8px;">
      Submission ID: <code>{{ row.get('__submission_id','') }}</code> • Status: <code>{{ row.get('__status','') }}</code>
    </div>
  </div>

  {% if ok %}
  <div class="card ok"><b>Saved ✅</b></div>
  {% endif %}

  {% if errors and errors|length %}
  <div class="card err">
    <b>Fix these:</b>
    <ul>{% for e in errors %}<li>{{ e }}</li>{% endfor %}</ul>
  </div>
  {% endif %}

  <div class="card">
    <form method="post">
      <label>WO</label>
      <input name="WO" required value="{{ row.get('WO','') }}"/>

      <label>Date</label>
      <input name="Date__NL" required value="{{ row.get('Date\\n','') }}"/>

      <label>District</label>
      <select name="District__NL" required>
        <option value="">-- choose --</option>
        {% for d in districts %}
        <option value="{{ d }}" {% if row.get('District\\n','') == d %}selected{% endif %}>{{ d }}</option>
        {% endfor %}
      </select>

      <label>Ward</label>
      <select name="Ward__NL" required>
        <option value="">-- choose --</option>
        {% for w in wards %}
        <option value="{{ w }}" {% if row.get('Ward\\n','') == w %}selected{% endif %}>{{ w }}</option>
        {% endfor %}
      </select>

      <label>Supervisor</label>
      <input name="Supervisor__NL" required value="{{ row.get('Supervisor\\n','') }}"/>

      <label>Shift</label>
      <select name="Shift__NL" required>
        <option value="">-- choose --</option>
        {% for sh in shifts %}
        <option value="{{ sh }}" {% if row.get('Shift\\n','') == sh %}selected{% endif %}>{{ sh }}</option>
        {% endfor %}
      </select>

      <label>Type</label>
      <select name="Type__NL" required>
        <option value="">-- choose --</option>
        {% for t in types %}
        <option value="{{ t }}" {% if row.get('Type (Road Class/ School, Bridge)\\n','') == t %}selected{% endif %}>{{ t }}</option>
        {% endfor %}
      </select>
      
      <label>Dump Trucks</label>
      <input name="# of Equipment (Dump Trucks)" value="{{ row.get('# of Equipment (Dump Trucks)','') }}"/>


      <label>Dump Truck Provider</label>
      <select name="Dump Truck Provider Contractor">
        <option value="">--</option>
        {% for x in dump_truck_providers %}
        <option value="{{ x }}" {% if row.get('Dump Truck Provider Contractor','') == x %}selected{% endif %}>{{ x }}</option>
        {% endfor %}
      </select>

      <label>Loads</label>
      <input name="# of Loads" value="{{ row.get('# of Loads','') }}"/>

      <label>Tonnes</label>
      <input name="Tonnes" value="{{ row.get('Tonnes','') }}"/>

      <label>Side</label>
      <select name="One Side/ Both Sides">
        <option value="">--</option>
        <option {% if row.get('One Side/ Both Sides')=='Both Sides' %}selected{% endif %}>Both Sides</option>
        <option {% if row.get('One Side/ Both Sides')=='One Side' %}selected{% endif %}>One Side</option>
      </select>

      <label>Road Side</label>
      <select name="Side of Road Cleared">
        <option value="">--</option>
        {% for s in ['North','South','East','West','East/West','North/South'] %}
        <option {% if row.get('Side of Road Cleared')==s %}selected{% endif %}>{{ s }}</option>
        {% endfor %}
      </select>

      <label>Snow Dump Site</label>
      <select name="Snow Dumped Site">
        <option value="">--</option>
        {% for s in snow_dump_sites %}
        <option {% if row.get('Snow Dumped Site')==s %}selected{% endif %}>{{ s }}</option>
        {% endfor %}
      </select>

      <label>Comments</label>
      <textarea name="Comments" rows="3">{{ row.get('Comments','') }}</textarea>

      <label>Location</label>
      <input name="Location" required value="{{ row.get('Location','') }}"/>

      <label>From</label>
      <input name="From" value="{{ row.get('From ','') }}"/>

      <label>To</label>
      <input name="To" value="{{ row.get('To','') }}"/>

      <button type="submit">Save changes</button>
      <button type="submit" name="delete" value="1" class="ghost" style="margin-left:8px;">Delete (Pending only)</button>

      <div class="help" style="margin-top:10px;">
        Editing only works while status is <b>PENDING</b>. After it becomes <b>APPLIED</b>, it’s locked to protect the master DB.
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

    bid = (request.args.get("bid") or "").strip()
    batch = get_intake_batch_details(bid) if bid else []
    
    # Countdown calculation for submitted batch (based on earliest submitted_at in batch)
    server_now_epoch = time.time()
    apply_in_seconds = 0

    if batch:
        # Use the earliest submitted_at across the batch so the whole batch shares one timer
        ts_list = []
        for r in batch:
            s = (r.get("__submitted_at", "") or "").strip()
            if s:
                try:
                    ts_list.append(datetime.strptime(s, "%Y-%m-%d %H:%M:%S").timestamp())
                except Exception:
                    pass

        if ts_list:
            earliest = min(ts_list)
            apply_at = earliest + float(PENDING_GRACE_SECONDS)
            apply_in_seconds = max(0, int(round(apply_at - server_now_epoch)))
        else:
            # If timestamps missing, assume it's ready to apply
            apply_in_seconds = 0


    return render_template_string(
        NEW_FORM_HTML,
        errors=[],
        batch=batch,
        batch_id=bid,
        pending_grace_seconds=PENDING_GRACE_SECONDS,
        apply_in_seconds=apply_in_seconds,
        inserted_count=len([r for r in batch if r.get("__status","").strip()]),
        intake_poll_seconds=INTAKE_POLL_SECONDS,
        districts=latest_allowed_sets.get("District\n", []),
        supervisors=latest_allowed_sets.get("Supervisor\n", []),
        shifts=latest_allowed_sets.get("Shift\n", []),
        types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
        streets=latest_centre_streets,
        dump_truck_providers_html="".join(
            f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS
        ),
        snow_dump_sites_html="".join(
            f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES
        ),        
        districts_json=json.dumps(latest_allowed_sets.get("District\n", [])),
        shifts_json=json.dumps(latest_allowed_sets.get("Shift\n", [])),
        types_json=json.dumps(latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", [])),
        district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
    )



@app.post("/new")
def new_submit():
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    form = request.form.to_dict()

    # Parse rows WO_0..WO_n
    rows = []
    idx = 0
    while True:
        key = f"WO_{idx}"
        if key not in form:
            break

        values = {master_key: "" for master_key in MASTER_COLUMNS}
        # map indexed form fields -> master columns
        values["WO"] = form.get(f"WO_{idx}", "")
        values["District\n"] = form.get(f"District__NL_{idx}", "")
        values["Ward\n"] = form.get(f"Ward__NL_{idx}", "")
        values["Date\n"] = form.get(f"Date__NL_{idx}", "")
        values["Shift\n"] = form.get(f"Shift__NL_{idx}", "")
        values["Supervisor\n"] = form.get(f"Supervisor__NL_{idx}", "")
        values["Location"] = form.get(f"Location_{idx}", "")
        values["From "] = form.get(f"From_{idx}", "")
        values["To"] = form.get(f"To_{idx}", "")
        values["Type (Road Class/ School, Bridge)\n"] = form.get(f"Type__NL_{idx}", "")
        values["# of Equipment (Dump Trucks)"] = form.get(f"# of Equipment (Dump Trucks)_{idx}", "")
        values["Dump Truck Provider Contractor"] = form.get(f"Dump Truck Provider Contractor_{idx}", "")
        values["# of Loads"] = form.get(f"# of Loads_{idx}", "")
        values["Tonnes"] = form.get(f"Tonnes_{idx}", "")
        values["One Side/ Both Sides"] = form.get(f"One Side/ Both Sides_{idx}", "")
        values["Side of Road Cleared"] = form.get(f"Side of Road Cleared_{idx}", "")
        values["Snow Dumped Site"] = form.get(f"Snow Dumped Site_{idx}", "")
        values["Comments"] = form.get(f"Comments_{idx}", "")
        values["Date\n"] = format_date_from_picker(values.get("Date\n", ""))

        # Skip fully empty accidental rows (but keep strict required)
        if normalize_blank(values.get("WO")) or normalize_blank(values.get("Location")):
            rows.append(values)

        idx += 1

    if not rows:
        return render_template_string(
            NEW_FORM_HTML,
            errors=["No rows found. Click + Add Row and fill at least one Work Order."],
            batch=[],
            batch_id="",
            inserted_count=0,
            intake_poll_seconds=INTAKE_POLL_SECONDS,
            districts=latest_allowed_sets.get("District\n", []),
            supervisors=latest_allowed_sets.get("Supervisor\n", []),
            shifts=latest_allowed_sets.get("Shift\n", []),
            types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
            streets=latest_centre_streets,
            dump_truck_providers_html="".join(f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS),
            snow_dump_sites_html="".join(f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES),                
            districts_json=json.dumps(latest_allowed_sets.get("District\n", [])),
            shifts_json=json.dumps(latest_allowed_sets.get("Shift\n", [])),
            types_json=json.dumps(latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", [])),
            district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
        )

    streets_set = set(
        s.upper().strip()
        for s in latest_centre_streets
        if isinstance(s, str) and s.strip()
    )

    all_errors = []
    allowed_base = dict(latest_allowed_sets or {})

    # Validate each row independently
    for i, values in enumerate(rows, start=1):
        allowed_sets = dict(allowed_base)
        dval = values.get("District\n", "")
        allowed_sets["Ward\n"] = wards_for_district(dval)

        errs = validate_submission(values, allowed_sets, streets_set)
        for e in errs:
            all_errors.append(f"Row {i}: {e}")

    if all_errors:
        log(f"INTAKE: batch rejected with {len(all_errors)} error(s)")
        return render_template_string(
            NEW_FORM_HTML,
            errors=all_errors,
            batch=[],
            batch_id="",
            inserted_count=0,
            intake_poll_seconds=INTAKE_POLL_SECONDS,
            districts=latest_allowed_sets.get("District\n", []),
            supervisors=latest_allowed_sets.get("Supervisor\n", []),
            shifts=latest_allowed_sets.get("Shift\n", []),
            types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
            streets=latest_centre_streets,
            dump_truck_providers_html="".join(f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS),
            snow_dump_sites_html="".join(f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES),
            districts_json=json.dumps(latest_allowed_sets.get("District\n", [])),
            shifts_json=json.dumps(latest_allowed_sets.get("Shift\n", [])),
            types_json=json.dumps(latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", [])),
            district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
        )

    batch_id, inserted_count, _per = append_batch_to_intake(rows)

    return Response(
        "", 303,
        {"Location": f"/new?bid={batch_id}"}
    )

@app.get("/edit/<sid>")
def edit_form(sid):
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    row = get_intake_row_by_submission_id(sid)
    if not row:
        return Response("Not found", 404)

    return render_template_string(
        EDIT_FORM_HTML,
        row=row,
        ok=False,
        errors=[],
        districts=latest_allowed_sets.get("District\n", []),
        wards=wards_for_district(row.get("District\n", "")) or latest_allowed_sets.get("Ward\n", []),
        supervisors=latest_allowed_sets.get("Supervisor\n", []),
        shifts=latest_allowed_sets.get("Shift\n", []),
        types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
        dump_truck_providers=DUMP_TRUCK_PROVIDERS,
        snow_dump_sites=SNOW_DUMP_SITES,        
    )


@app.post("/edit/<sid>")
def edit_submit(sid):
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    row = get_intake_row_by_submission_id(sid)
    if not row:
        return Response("Not found", 404)

    # Soft delete
    if (request.form.get("delete") or "").strip() == "1":
        ok = delete_intake_row(sid)
        row2 = get_intake_row_by_submission_id(sid)
        return render_template_string(
            EDIT_FORM_HTML,
            row=row2 or row,
            ok=ok,
            errors=[] if ok else ["Cannot delete (only PENDING rows can be deleted)."],
            districts=latest_allowed_sets.get("District\n", []),
            wards=wards_for_district((row2 or row).get("District\n", "")) or latest_allowed_sets.get("Ward\n", []),
            supervisors=latest_allowed_sets.get("Supervisor\n", []),
            shifts=latest_allowed_sets.get("Shift\n", []),
            types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
            dump_truck_providers=DUMP_TRUCK_PROVIDERS,
            snow_dump_sites=SNOW_DUMP_SITES,
        )

    form = request.form.to_dict()

    values = {master_key: "" for master_key in MASTER_COLUMNS}
    for form_key, master_key in FORM_TO_MASTER.items():
        values[master_key] = form.get(form_key, "")

    # Date: allow both picker format and already-formatted
    values["Date\n"] = format_date_from_picker(values.get("Date\n", ""))
    values["# of Equipment (Dump Trucks)"] = form.get("# of Equipment (Dump Trucks)", "")
    values["Dump Truck Provider Contractor"] = form.get("Dump Truck Provider Contractor", "")
    values["# of Loads"] = form.get("# of Loads", "")
    values["Tonnes"] = form.get("Tonnes", "")
    values["One Side/ Both Sides"] = form.get("One Side/ Both Sides", "")
    values["Side of Road Cleared"] = form.get("Side of Road Cleared", "")
    values["Snow Dumped Site"] = form.get("Snow Dumped Site", "")
    values["Comments"] = form.get("Comments", "")


    streets_set = set(
        s.upper().strip()
        for s in latest_centre_streets
        if isinstance(s, str) and s.strip()
    )

    allowed_sets = dict(latest_allowed_sets or {})
    dval = values.get("District\n", "")
    allowed_sets["Ward\n"] = wards_for_district(dval)

    errors = validate_submission(values, allowed_sets, streets_set)
    if errors:
        return render_template_string(
            EDIT_FORM_HTML,
            row=row,
            ok=False,
            errors=errors,
            districts=latest_allowed_sets.get("District\n", []),
            wards=allowed_sets.get("Ward\n", []),
            supervisors=latest_allowed_sets.get("Supervisor\n", []),
            shifts=latest_allowed_sets.get("Shift\n", []),
            types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
            dump_truck_providers=DUMP_TRUCK_PROVIDERS,
            snow_dump_sites=SNOW_DUMP_SITES,
        )

    ok = update_intake_row(sid, values)
    row2 = get_intake_row_by_submission_id(sid)

    return render_template_string(
        EDIT_FORM_HTML,
        row=row2 or row,
        ok=ok,
        errors=[] if ok else ["Cannot edit (only PENDING rows can be edited)."],
        districts=latest_allowed_sets.get("District\n", []),
        wards=wards_for_district((row2 or row).get("District\n", "")) or latest_allowed_sets.get("Ward\n", []),
        supervisors=latest_allowed_sets.get("Supervisor\n", []),
        shifts=latest_allowed_sets.get("Shift\n", []),
        types=latest_allowed_sets.get("Type (Road Class/ School, Bridge)\n", []),
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
def normalize_single_ward(val: str) -> str:
    """
    Accept ONLY a single numeric ward (digits only).
    Rejects: '1&2', '10/11', '1,2', 'Ward 3', etc.
    """
    if not val:
        return ""
    s = str(val).strip()
    if s.isdigit():
        return str(int(s))
    return ""


def recompute_allowed_sets_from_master():
    allowed = {}

    def clean_str(x):
        return str(x).strip()

    def is_junk_number(s):
        return s.isdigit()

    def split_people(s: str):
        if not s:
            return []
        s = clean_str(s)
        if not s:
            return []
        parts = re.split(r"\s*(?:&|/|,)\s*", s)
        out = []
        for p in parts:
            p = clean_str(p)
            if not p:
                continue
            out.append(p)
        return out

    def unique_preserve_order(seq):
        seen = set()
        out = []
        for x in seq:
            x = clean_str(x)
            if not x:
                continue
            if x in seen:
                continue
            seen.add(x)
            out.append(x)
        return out

    def strict_list(lst):
        return unique_preserve_order([clean_str(x) for x in (lst or []) if clean_str(x)])

    allowed["District\n"] = strict_list(STRICT_DISTRICTS)
    allowed["Ward\n"] = strict_list(STRICT_WARDS)
    allowed["Supervisor\n"] = strict_list(STRICT_SUPERVISORS)
    allowed["Shift\n"] = strict_list(STRICT_SHIFTS)
    allowed["Type (Road Class/ School, Bridge)\n"] = strict_list(STRICT_TYPES)

    try:
        df = pd.read_csv(MASTER_TRACKER_PATH, encoding="latin-1")
    except Exception:
        return allowed

    def learn(col):
        if allowed.get(col):
            return

        if col not in df.columns:
            allowed[col] = []
            return

        vals = []

        for v in df[col].fillna("").astype(str):
            v = v.strip()
            if not v:
                continue

            if col == "Ward\n":
                v = normalize_single_ward(v)
                if not v:
                    continue
                vals.append(v)
                continue

            if col == "District\n":
                v = re.split(r"[,&/]", v)[0].strip()
                if v:
                    vals.append(v)
                continue

            if col == "Supervisor\n":
                people = split_people(v)
                for p in people:
                    p2 = p.strip()
                    if not p2:
                        continue
                    if is_junk_number(p2):
                        continue
                    vals.append(p2)
                continue

            vals.append(v)

        vals = unique_preserve_order(vals)

        if col == "Ward\n":
            vals = sorted(vals, key=lambda x: int(x))
        else:
            vals = sorted(vals, key=lambda x: x.casefold())

        if len(vals) > 4000:
            vals = vals[:4000]

        allowed[col] = vals

    learn("District\n")
    learn("Ward\n")
    learn("Supervisor\n")
    learn("Shift\n")
    learn("Type (Road Class/ School, Bridge)\n")

    return allowed


def _emit_updated_event(kind: str, items=None):
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
    if os.environ.get("STATIC_BUILD", "").strip() == "1":
        log("STATIC_BUILD=1 detected — running one-time build only")
        with FILE_LOCK:
            build_everything()
    else:
        main()
