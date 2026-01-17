import os
import json
import html
import math
import re
import difflib
import heapq
import time
import hashlib
import base64
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
    from flask import Flask, Response, send_from_directory, render_template_string, request, redirect
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

# ---------------------------
# Branding: embed CoT logo into landing page (no extra routes needed)
# ---------------------------
COT_LOGO_PATH = os.path.join(BASE_DIR, "COT Logo Screenshot.png")

def _load_png_data_uri(path: str) -> str:
    try:
        with open(path, "rb") as f:
            b64 = base64.b64encode(f.read()).decode("ascii")
        return "data:image/png;base64," + b64
    except Exception:
        return ""

COT_LOGO_DATA_URI = _load_png_data_uri(COT_LOGO_PATH)


MASTER_TRACKER_PATH = os.path.join(BASE_DIR, "Snow_Removal_Master_Tracker.csv")

# Reference intersections (used for Street + From/To picklists and optional IDs)
INTERSECTION_REF_PATH = os.path.join(BASE_DIR, "Centreline Intersection - 4326.csv")

# Routing graph centreline (still used for exact segment plotting)
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
INTERSECTION_POINTS_SHOW_BY_DEFAULT = False

DRAW_WO_SEGMENTS = True
SEGMENT_OPACITY = 0.01
SEGMENT_WEIGHT = 12

# =========================================================
# HARD-CODED DISTRICTS (used in /new and /edit dropdowns)
# =========================================================
DISTRICTS= [
    "EY",
    "NY",
    "SC",
    "TEY",
    # add more here if needed
]


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
INTAKE_EXTRA_COLS = ["__submitted_at", "__edited_at", "__submission_id", "__batch_id", "__status", "__pending_until_epoch"]
PENDING_GRACE_SECONDS = 60  # keep rows editable for 60s before they can be applied


UI_USER = os.environ.get("WO_UI_USER", "").strip()
UI_PASS = os.environ.get("WO_UI_PASS", "").strip()

STRICT_DISTRICTS = ["EY", "NY", "SC", "TEY"]
STRICT_WARDS = []
STRICT_SUPERVISORS = [
    "Adrienne Carnovale",
    "Ahmad Nabavi",
    "Anil Pattali",
    "Antonio Benavidez",
    "Arsalan Saeed",
    "Avinash Singh",
    "Brandon Robinson",
    "Dennis Dionyssiou",
    "Dennis Kelly",
    "Dexta Walker",
    "Donovan Norville",
    "Eduardo Moniz",
    "Florian Osmanaj",
    "Frank Figliano (TW)",
    "Garrett Silveira",
    "Ian MacMillan",
    "Ian McGhee",
    "Ivan Gaitan",
    "Jerry Greco",
    "Joe Disli",
    "Joe Machado",
    "John Alphonso",
    "John Holowczak",
    "John Pezzente",
    "Kevin Bonner",
    "Kim Daniel",
    "Leo Debilio",
    "Les Geroly",
    "Lorenzo Dasilva",
    "Marc Cerqua",
    "Marco Mariani",
    "Marco Roman",
    "Matthew Shaw",
    "Michael Moosaie (TW)",
    "Michael Pokrajac",
    "Mike Grieve",
    "Pasquale Grande",
    "Pat Monardo",
    "Rafiqul Islam",
    "Sami Alani",
    "Sean Scott",
    "Sergio D'Amico",
    "Steve Soria",
    "Tariq Habib",
    "Thomas Bertram",
    "Tomas Chamul",
    "Tran To",
    "Varouj Sorfazlian",
    "Wyatt Cerqua",
]
STRICT_SHIFTS = []
STRICT_TYPES = [
    "Backhoe",
    "Blower",
    "Cameleon",
    "FEL w/Blower",
    "FEL w/Blower & Plow Blade",
    "FEL w/Bucket",
    "FEL w/Claw",
    "FEL w/Plow Blade",
    "Plow/Salt Unit",
    "Shovel",
    "Skid Steer w/Blower",
    "Skidsteer",
    "Unknown",
]


FILE_LOCK = threading.RLock()
BUILD_LOCK = threading.Lock()

LAST_MASTER_WRITE_BY_INTAKE_AT = 0.0
LAST_MASTER_WRITE_LOCK = threading.Lock()
LAST_MASTER_FP_WRITTEN_BY_INTAKE = None


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

# ---------------------------
# Street name normalization (shared)
# ---------------------------
_ABBREV_REPLACEMENTS = [
    # NOTE: We intentionally do NOT globally expand 'ST' because in Toronto
    # it can mean either 'STREET' (suffix) or 'SAINT' (prefix, e.g., ST CLAIR).
    # Prefix handling (ST/SAINT/STREET) is done in normalize_street_name() before these.

    (r"\bAVE\b", "AVENUE"),
    (r"\bRD\b", "ROAD"),
    (r"\bBLVD\b", "BOULEVARD"),
    (r"\bDR\b", "DRIVE"),
    (r"\bCRES\b", "CRESCENT"),
    (r"\bPL\b", "PLACE"),
    (r"\bCRT\b", "COURT"),
    (r"\bPKWY\b", "PARKWAY"),
    (r"\bHWY\b", "HIGHWAY"),
    
    # Normalize directional suffixes (must come after street type expansions)
    (r"\bEAST$", "E"),
    (r"\bWEST$", "W"),
    (r"\bNORTH$", "N"),
    (r"\bSOUTH$", "S"),
]


def normalize_street_name(name: str) -> str:
    """Normalize street/cross-street labels into a consistent uppercase key.

    This is used across:
      - centreline routing graph build
      - Centreline Intersection reference lookup
      - UI cross-street suggestions
    """
    s = str(name or '').upper().strip()
    if not s or s in ('NAN', 'NONE'):
        return ''

    # Strip leading address numbers (e.g., "3409 ST CLAIR AVE" -> "ST CLAIR AVE")
    s = re.sub(r'^\d+\s+', '', s)

    # Collapse whitespace and punctuation variants
    s = s.replace('-', ' ')
    s = re.sub(r"\s+", ' ', s).strip()

    # Drop common prefixes/suffixes that break matching
    s = re.sub(r"^THE\s+", '', s).strip()

    # Normalize abbreviations

    # ---------------------------
    # Toronto-specific ST/SAINT/STREET handling
    #
    # Canonical form (for *SAINT* streets): keep them as prefix "ST <NAME>" (NOT "SAINT").
    # Example: "SAINT CLAIR AVENUE W" -> "ST CLAIR AVENUE W".
    #
    # Suffix road-type abbreviation handling:
    #   - "... ST" or "... ST W" -> "... STREET" / "... STREET W".
    #
    # Also repair the common user mistake where "ST" (Saint) is accidentally expanded to
    # "STREET" as a *prefix name token* (e.g., "STREET CLAIR" -> "ST CLAIR").

    # Canonicalize prefix SAINT to ST
    s = re.sub(r"^SAINT\s+", "ST ", s)

    # Ensure prefix ST variants stay ST
    s = re.sub(r"^ST\.?\s+", "ST ", s)

    # Convert bad expansions like "STREET CLAIR" -> "ST CLAIR" (only when STREET is a prefix name token)
    road_types = {"STREET","ROAD","AVENUE","BOULEVARD","DRIVE","CRESCENT","PLACE","COURT","PARKWAY","HIGHWAY","LANE","TERRACE","CIRCLE","WAY","GROVE","GATE","TRAIL","CLOSE","ROW","SQUARE","PARK","PROMENADE"}
    if s.startswith("STREET "):
        parts = s.split()
        if len(parts) >= 2 and parts[1] not in road_types:
            s = "ST " + " ".join(parts[1:])

    # Normalize suffix street abbreviation " ST" (including before direction tokens)
    # Examples: "BATHURST ST" -> "BATHURST STREET", "QUEEN ST W" -> "QUEEN STREET W"
    s = re.sub(r"\bST\b(?=(\s+[NSEW])?\s*$)", "STREET", s)

    for pat, rep in _ABBREV_REPLACEMENTS:

        s = re.sub(pat, rep, s)

    # Handle slashes used in intersection descriptors (keep tokens clean)
    s = s.replace(' / ', '/').replace('/ ', '/').replace(' /', '/')

    return s

def endpoint_cross_candidates(street_val, endpoint_val):
    """Return candidate cross-street names for an endpoint field.

    Accepts endpoint values like:
      - 'CROSS ST'
      - 'STREET / CROSS'
      - 'A / B / C' (3-way)

    Returns a list of *normalized* street-name tokens to try as the cross street.

    For 3-way values, we treat the token most similar to the selected Street as the
    "main" street, and the remaining two tokens as candidate cross streets.
    """
    s_norm = normalize_street_name(street_val or '')
    raw = ('' if endpoint_val is None else str(endpoint_val)).strip()
    if not raw or raw.lower() == 'nan':
        return []

    # --- Special case (Toronto): same-street E/W variants used as endpoints ---
    # Example seen in the master tracker:
    #   Location: "ST CLAIR AVENUE W"
    #   From:     "ST CLAIR AVENUE E"
    # In reality, this means "start at the E/W split point".
    # In Toronto core, many major streets split at Yonge (Bloor, Queen, King, St Clair, etc.).
    # If the endpoint is the *same base street* as the Location, but with a *different* direction
    # designator, treat the cross street as YONGE STREET.
    def _dir_token(s: str):
        parts = (s or "").split()
        if not parts:
            return None
        last = parts[-1]
        if last in {"E", "W", "N", "S"}:
            return last
        if len(parts) >= 2 and parts[-2] in {"E", "W", "N", "S"}:
            # e.g., "STREET W" already normalized into two tokens
            return parts[-2]
        return None

    def _strip_dir(s: str):
        parts = (s or "").split()
        if parts and parts[-1] in {"E", "W", "N", "S"}:
            parts = parts[:-1]
        return " ".join(parts).strip()

    try:
        ep_norm = normalize_street_name(raw)
        if ep_norm:
            base_loc = _strip_dir(s_norm)
            base_ep = _strip_dir(ep_norm)
            d_loc = _dir_token(s_norm)
            d_ep = _dir_token(ep_norm)
            if base_loc and base_ep and base_loc == base_ep and d_loc and d_ep and d_loc != d_ep:
                # Try both spelling variants for safety
                return [normalize_street_name("YONGE STREET"), normalize_street_name("YONGE ST")]
    except Exception:
        pass

    # Normalize slash spacing but keep tokens
    raw_fixed = raw.replace(' / ', '/').replace('/ ', '/').replace(' /', '/')
    if '/' not in raw_fixed:
        v = normalize_street_name(raw_fixed)
        return [v] if v else []

    toks_raw = [t.strip() for t in raw_fixed.split('/') if t.strip()]
    toks = [normalize_street_name(t) for t in toks_raw]
    toks = [t for t in toks if t]
    if not toks:
        return []

    # 2-token case: prefer the side that isn't the selected Street
    if len(toks) == 2:
        a, b = toks
        if a == s_norm and b:
            return [b]
        if b == s_norm and a:
            return [a]
        # Similarity fallback (handles ST/AVE expansions etc.)
        try:
            if similarity(a, s_norm) >= 0.88 and b:
                return [b]
            if similarity(b, s_norm) >= 0.88 and a:
                return [a]
        except Exception:
            pass
        # Ambiguous: try both
        out = []
        if a:
            out.append(a)
        if b and b not in out:
            out.append(b)
        return out

    # 3+ token case: choose token most similar to Street as the main street, return the rest
    scores = []
    for t in toks:
        try:
            sc = similarity(t, s_norm) if s_norm else 0.0
        except Exception:
            sc = 0.0
        scores.append(sc)

    if s_norm and s_norm in toks:
        main_idx = toks.index(s_norm)
    else:
        main_idx = max(range(len(toks)), key=lambda i: scores[i])

    out = []
    for i, t in enumerate(toks):
        if i == main_idx:
            continue
        if t and t not in out:
            out.append(t)

    return out




# =========================================================
# 3. INTAKE SYSTEM
# =========================================================

MASTER_COLUMNS = [
    # === Snow Removal Master Tracker (CSV) columns ===
    "Work Order Number",
    "District (Where Snow Removed)",
    "Ward (Where Snow Removed)",
    "TOA Area (Where Snow Removed)",
    "Street",
    "From Intersection",
    "To Intersection",
    "One Side / Both Sides Cleared?",
    "Side of Road Cleared",
    "Roadway",
    "Sidewalk",
    "Separated Cycling Infrastructure",
    "Bridge",
    "School Loading Zones",
    "Layby Parking",
    "Equipment Method",
    "# of Equipment (Dump Trucks)",
    "Dump Truck Source (In-House/Contractor)",
    "Snow Dump Site",
    "# of Loads",
    "Tonnes",
    "Shift Start Date",
    "Shift Start Time",
    "Shift End Date",
    "Shift End Time",
    "Hours Worked",
    "Time and Date of Data Entry Input",
    "Supervisor 1",
    "Supervisor 2 (if relevant)",
    "Supervisor 3 (if relevant)",
    "Snow Removal by Contracted Crew or In-House?",
    "Contractor: # of Crews",
    "Contractor: Crew TOA Area Responsibility",
    "Contractor: Crew Number",
    "In-House: Staff Responsibility (Base Yard)",
    "In-House: # of Staff",
    "NOTES",
]

FORM_TO_MASTER = {
    # Core identifiers
    "WO": "Work Order Number",

    # Admin
    "District__NL": "District (Where Snow Removed)",
    "Ward__NL": "Ward (Where Snow Removed)",
    "TOA__NL": "TOA Area (Where Snow Removed)",

    # New address format
    "Street": "Street",
    "FromIntersection": "From Intersection",
    "ToIntersection": "To Intersection",

    # Shift (UI captures a date + start/end time)
    "Date__NL": "Shift Start Date",
    "ShiftStart__NL": "Shift Start Time",
    "ShiftEnd__NL": "Shift End Time",

    # People
    "Supervisor__NL": "Supervisor 1",

    # Ops
    "Equipment Method": "Equipment Method",
    "Dump Truck Source (In-House/Contractor)": "Dump Truck Source (In-House/Contractor)",
    "# of Equipment (Dump Trucks)": "# of Equipment (Dump Trucks)",
    "Snow Dump Site": "Snow Dump Site",
    "# of Loads": "# of Loads",
    "Tonnes": "Tonnes",
    "One Side / Both Sides Cleared?": "One Side / Both Sides Cleared?",
    "Side of Road Cleared": "Side of Road Cleared",
    "NOTES": "NOTES",
}
MASTER_TO_FORM = {v: k for k, v in FORM_TO_MASTER.items()}

DISPLAY_FIELDS_FORM = [
    "Work Order Number",
    "Shift Start Date",
    "District (Where Snow Removed)",
    "Ward (Where Snow Removed)",
    "TOA Area (Where Snow Removed)",
    "Supervisor 1",
    "Supervisor 2 (if relevant)",
    "Supervisor 3 (if relevant)",
    "Shift Start Time",
    "Shift End Date",
    "Shift End Time",
    "Equipment Method",
    "# of Equipment (Dump Trucks)",
    "Dump Truck Source (In-House/Contractor)",
    "Contractor: Crew TOA Area Responsibility",
    "Snow Dump Site",
    "# of Loads",
    "Tonnes",
    "One Side / Both Sides Cleared?",
    "Side of Road Cleared",
    "Snow Removal by Contracted Crew or In-House?",
    "Contractor: # of Crews",
    "Contractor: Crew Number",
    "In-House: Staff Responsibility (Base Yard)",
    "In-House: # of Staff",
    "Street",
    "From Intersection",
    "To Intersection",
    "NOTES",
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
    """Legacy no-op.

    The master tracker is now an Excel workbook (Snow Removal Master Tracker.xlsx)
    with a fixed header row, so we do not patch columns in-place.
    """
    return


def _find_xlsx_header_row(ws, header_key: str = "Work Order Number", scan_rows: int = 30) -> int:
    """Return 1-based row index that contains `header_key` (case-insensitive)."""
    key = (header_key or "").strip().casefold()
    for r in range(1, scan_rows + 1):
        row_vals = [str(c.value).strip() if c.value is not None else "" for c in ws[r]]
        if any(v.casefold() == key for v in row_vals):
            return r
    # Fallback to row 3 (this workbook uses 2 title rows + header row)
    return 3


def read_master_csv() -> pd.DataFrame:
    """Read master rows from the CSV tracker.

    - Returns a DataFrame containing at least MASTER_COLUMNS (missing columns filled with '')
    """
    if not os.path.exists(MASTER_TRACKER_PATH):
        raise FileNotFoundError(f"MASTER_TRACKER_PATH not found: {MASTER_TRACKER_PATH}")

    # Read CSV
    df = pd.read_csv(MASTER_TRACKER_PATH)

    # Drop completely empty rows
    if len(df):
        # If WO is blank, treat as empty row
        wo_col = "Work Order Number"
        if wo_col in df.columns:
            df = df[~df[wo_col].isna()].copy()

    # Ensure required cols
    for c in MASTER_COLUMNS:
        if c not in df.columns:
            df[c] = ""

    return df


def append_rows_to_master_csv(rows: list) -> int:
    """Append list[dict] rows (MASTER_COLUMNS keys) into the CSV tracker.

    Returns number of appended rows.
    """
    if not rows:
        return 0

    if not os.path.exists(MASTER_TRACKER_PATH):
        raise FileNotFoundError(f"MASTER_TRACKER_PATH not found: {MASTER_TRACKER_PATH}")

    with FILE_LOCK:
        # Read existing CSV
        df = pd.read_csv(MASTER_TRACKER_PATH)
        
        now_str = datetime.now().strftime('%Y-%m-%d %H:%M:%S')

        # Process each row
        for row in rows:
            # Auto-fill Data Entry timestamp if missing
            if not str(row.get("Time and Date of Data Entry Input", "")).strip():
                row["Time and Date of Data Entry Input"] = now_str

            # If end date missing, default to start date
            if not str(row.get("Shift End Date", "")).strip():
                row["Shift End Date"] = row.get("Shift Start Date", "")

        # Convert rows to DataFrame and append
        new_df = pd.DataFrame(rows)
        df = pd.concat([df, new_df], ignore_index=True)
        
        # Save back to CSV
        df.to_csv(MASTER_TRACKER_PATH, index=False)

    return len(rows)



# =========================================================
# Intersection reference (Centreline Intersection - 4326.csv)
# =========================================================
_REF_CACHE = {
    "fp": None,
    "street_to_cross": {},
    "pair_to_id": {},
}


def get_intersection_reference():
    """Load and cache the intersection reference file.

    Returns:
        (street_to_cross: dict[str, list[str]], pair_to_id: dict[tuple[str,str], int])

    All street names are normalized with normalize_street_name.
    """
    global _REF_CACHE

    if not os.path.exists(INTERSECTION_REF_PATH):
        return {}, {}

    fp = file_fingerprint(INTERSECTION_REF_PATH)
    if _REF_CACHE.get("fp") == fp and _REF_CACHE.get("street_to_cross") and _REF_CACHE.get("pair_to_id"):
        return _REF_CACHE["street_to_cross"], _REF_CACHE["pair_to_id"]

    try:
        df = pd.read_csv(INTERSECTION_REF_PATH, encoding="latin-1")
    except Exception:
        df = pd.read_csv(INTERSECTION_REF_PATH, encoding="utf-8")

    street_to_cross = {}
    pair_to_id = {}

    # Expect: INTERSECTION_ID, INTERSECTION_DESC, geometry
    for _, r in df.iterrows():
        iid = r.get("INTERSECTION_ID")
        desc = r.get("INTERSECTION_DESC")
        if pd.isna(iid) or not isinstance(desc, str) or "/" not in desc:
            continue
        try:
            iid_int = int(iid)
        except Exception:
            continue

        parts = [p.strip() for p in desc.split("/") if str(p).strip()]
        if len(parts) < 2:
            continue

        # Normalize all parts
        parts_norm = []
        for part in parts:
            norm = normalize_street_name(part)
            if norm:
                parts_norm.append(norm)
        
        if len(parts_norm) < 2:
            continue

        # For 3+ way intersections, create ALL pairwise combinations
        # This ensures that "ST CLAIR AVE E / YONGE ST / ST CLAIR AVE W" creates:
        # - (ST CLAIR AVENUE E, YONGE STREET)
        # - (ST CLAIR AVENUE E, ST CLAIR AVENUE W)
        # - (YONGE STREET, ST CLAIR AVENUE W) ← This was missing before!
        for i in range(len(parts_norm)):
            for j in range(i + 1, len(parts_norm)):
                a_norm = parts_norm[i]
                b_norm = parts_norm[j]
                
                # Store original forms for display
                street_to_cross.setdefault(a_norm, set()).add(parts[j])
                street_to_cross.setdefault(b_norm, set()).add(parts[i])
                
                # pair_to_id uses normalized names for lookup
                if (a_norm, b_norm) not in pair_to_id:
                    pair_to_id[(a_norm, b_norm)] = iid_int
                if (b_norm, a_norm) not in pair_to_id:
                    pair_to_id[(b_norm, a_norm)] = iid_int

    # Sort lists
    street_to_cross_sorted = {
        k: sorted(list(v), key=lambda x: x.casefold())
        for k, v in street_to_cross.items()
    }

    _REF_CACHE = {
        "fp": fp,
        "street_to_cross": street_to_cross_sorted,
        "pair_to_id": pair_to_id,
    }

    return street_to_cross_sorted, pair_to_id

# =========================================================
# 2B. STREET -> ENDPOINT INTERSECTIONS (FROM XLSX)
# =========================================================

_STREET_ENDPOINTS_CACHE = {"fp": None, "street_endpoints": {}}


def get_street_endpoints_index():
    """
    Build a Street -> [IntersectionName...] mapping from the Snow Removal Master Tracker.

    For CSV mode: Creates formatted strings like "Dundas St E / Logan Ave" from intersection reference.
    For XLSX mode: Uses StreetEndPoints sheet if available.

    Keys are normalized to UPPER via normalize_street_name so the browser can do
    fast lookups without API calls.
    """
    global _STREET_ENDPOINTS_CACHE

    if not os.path.exists(MASTER_TRACKER_PATH):
        return {}

    fp = file_fingerprint(MASTER_TRACKER_PATH)
    if _STREET_ENDPOINTS_CACHE.get("fp") == fp and _STREET_ENDPOINTS_CACHE.get("street_endpoints"):
        return _STREET_ENDPOINTS_CACHE["street_endpoints"]

    # CSV mode: build from intersection reference with formatted strings
    if MASTER_TRACKER_PATH.endswith('.csv'):
        street_to_cross, _ = get_intersection_reference()
        
        # Get raw intersection data to find original descriptions
        if not os.path.exists(INTERSECTION_REF_PATH):
            return {}
        
        try:
            int_df = pd.read_csv(INTERSECTION_REF_PATH, dtype=str)
        except Exception:
            return {}
        
        # Build mapping of normalized street -> list of formatted intersection strings
        out = {}
        for _, row in int_df.iterrows():
            desc = str(row.get("INTERSECTION_DESC", "") or "").strip()
            if not desc or desc.lower() == "nan":
                continue
            
            parts = [p.strip() for p in desc.split("/") if str(p).strip()]
            if len(parts) < 2:
                continue
            
            # For each street in the intersection, add the full formatted string
            for part in parts:
                norm_part = normalize_street_name(part)
                if norm_part:
                    out.setdefault(norm_part, set()).add(desc)
        
        # Sort and convert to lists
        out = {k: sorted(list(v), key=lambda x: x.casefold()) for k, v in out.items()}
        _STREET_ENDPOINTS_CACHE = {"fp": fp, "street_endpoints": out}
        return out

    # XLSX mode: try to use StreetEndPoints sheet
    try:
        df = pd.read_excel(MASTER_TRACKER_PATH, sheet_name="StreetEndPoints", dtype=str)
    except Exception:
        # Fallback to intersection reference
        street_to_cross, _ = get_intersection_reference()
        out = {k: v[:] for k, v in (street_to_cross or {}).items()}
        _STREET_ENDPOINTS_CACHE = {"fp": fp, "street_endpoints": out}
        return out

    out = {}
    for _, r in df.iterrows():
        st = normalize_street_name(r.get("linear_name_full", ""))
        inter = str(r.get("intersection_name", "") or "").strip()
        if not st or not inter or inter.lower() == "nan":
            continue
        out.setdefault(st, set()).add(inter)

    out = {k: sorted(list(v), key=lambda x: x.casefold()) for k, v in out.items()}

    _STREET_ENDPOINTS_CACHE = {"fp": fp, "street_endpoints": out}
    return out



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

def normalize_wo_id(v) -> str:
    """
    WO display normalization:
    - NaN/None -> ''
    - 909090.0 -> '909090'
    - keeps alphanumeric IDs intact
    """
    try:
        import pandas as pd
        if pd.isna(v):
            return ""
    except Exception:
        pass

    if v is None:
        return ""

    # If it's a numeric WO coming in as float, drop .0
    try:
        fv = float(v)
        if fv == int(fv):
            return str(int(fv))
    except Exception:
        pass

    s = str(v).strip()
    if s.endswith(".0"):
        s = s[:-2]
    return s



def extract_cross_from_endpoint(street_val, endpoint_val):
    """Backwards-compatible helper that returns a *single* cross-street token.

    For values like 'A / B / C', this returns the first candidate from
    endpoint_cross_candidates(). For routing, prefer endpoint_cross_candidates()
    so we can try multiple candidates.
    """
    cands = endpoint_cross_candidates(street_val, endpoint_val)
    return cands[0] if cands else ''


def validate_submission(values: dict, allowed_sets: dict, streets_set: set, street_endpoints: dict):
    """Validate a single WO row for intake.

    New address format:
      Street + From Intersection + To Intersection

    Note: From/To values may come in as either:
      - pure cross street (e.g., 'BOAKE ST')
      - combined label (e.g., 'ASSINIBOINE RD / BOAKE ST')

    We validate Street against streets_set, and validate From/To against the
    StreetEndPoints list for that Street (when available).
    """
    errors = []

    required = [
        "Work Order Number",
        "District (Where Snow Removed)",
        "Ward (Where Snow Removed)",
        "Shift Start Date",
        "Shift Start Time",
        "Shift End Time",
        "Supervisor 1",
        "Street",
    ]
    for k in required:
        if not normalize_blank(values.get(k)):
            errors.append(f"Missing required field: {k}")

    street_raw = normalize_blank(values.get("Street"))
    from_raw = normalize_blank(values.get("From Intersection"))
    to_raw = normalize_blank(values.get("To Intersection"))

    if street_raw and "ENTIRE STREET" not in street_raw.upper():
        if (not from_raw) and (not to_raw):
            errors.append("Provide at least one of From Intersection or To Intersection (unless Street contains 'ENTIRE STREET').")

    def check_allowed(field, label, allow_custom=False):
        val = normalize_blank(values.get(field))
        if not val:
            return
        if allow_custom:
            return
        allowed = allowed_sets.get(field) or []
        allowed_set = set(str(x).strip() for x in allowed if str(x).strip())
        if allowed_set and val not in allowed_set:
            errors.append(f"{label} not allowed: '{val}'")

    check_allowed("District (Where Snow Removed)", "District")
    check_allowed("Ward (Where Snow Removed)", "Ward")
    check_allowed("Supervisor 1", "Supervisor", allow_custom=True)

    # Shift time range validation
    shift_norm = normalize_shift_time_range(
        "",
        values.get("Shift Start Time", ""),
        values.get("Shift End Time", ""),
    )
    if normalize_blank(values.get("Shift Start Time")) and normalize_blank(values.get("Shift End Time")) and not shift_norm:
        errors.append("Shift times must form a valid range (e.g., 06:30AM - 06:30PM).")

    def norm_key(s: str) -> str:
        return re.sub(r"\s+", " ", str(s).upper().strip())

    def is_special_street(s: str) -> bool:
        u = norm_key(s)
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

    # 1) Validate Street only
    if street_raw and not is_special_street(street_raw):
        u = norm_key(street_raw)
        if not fuzzy_in_set(u, streets_set):
            errors.append(f"Street does not look like a valid street name: '{street_raw}'")

    # 2) Validate From/To as intersections for the chosen Street (when we have endpoints)
    street_norm = normalize_street_name(street_raw)
    endpoints = (street_endpoints or {}).get(street_norm, []) or []

    # Build normalized lookup for endpoints + cross-only options
    endpoints_norm = {norm_key(e): e for e in endpoints}
    cross_norms = set()
    for e in endpoints:
        if not e:
            continue
        if '/' in str(e):
            a, b = [x.strip() for x in str(e).split('/', 1)]
            a_n = normalize_street_name(a)
            b_n = normalize_street_name(b)
            if a_n == street_norm and b:
                cross_norms.add(norm_key(b))
            elif b_n == street_norm and a:
                cross_norms.add(norm_key(a))
            else:
                # If the endpoint label doesn't match the Street cleanly, still add both sides
                if a:
                    cross_norms.add(norm_key(a))
                if b:
                    cross_norms.add(norm_key(b))
        else:
            # sometimes stored as pure cross
            cross_norms.add(norm_key(e))

    def validate_intersection(field_label: str, raw_val: str):
        if not raw_val or is_special_street(raw_val) or "ENTIRE STREET" in (street_raw or "").upper():
            return
        if not endpoints:
            # If we don't have endpoints for this Street, don't block submission
            return

        u = norm_key(raw_val)
        if u in endpoints_norm:
            return

        # If user typed combined "Street / Cross", accept if cross-only matches
        if '/' in raw_val:
            cross_only = extract_cross_from_endpoint(street_raw, raw_val)
            if cross_only and norm_key(cross_only) in cross_norms:
                return

        # If user typed just the cross, accept if in cross list
        if u in cross_norms:
            return

        # Last: fuzzy match to a nearby cross option
        best = 0.0
        for c in list(cross_norms)[:8000]:
            sc = difflib.SequenceMatcher(None, u, c).ratio()
            if sc > best:
                best = sc
                if best >= 0.90:
                    return

        # If invalid, give a helpful message
        ex = endpoints[:3]
        hint = f" Examples: {', '.join([repr(x) for x in ex])}" if ex else ""
        errors.append(f"{field_label} is not a valid intersection for Street '{street_raw}': '{raw_val}'.{hint}")

    validate_intersection("From Intersection", from_raw)
    validate_intersection("To Intersection", to_raw)

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
            out["__pending_until_epoch"] = str(int(time.time() + float(PENDING_GRACE_SECONDS)))
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

    """Apply eligible intake submissions into the Excel master tracker.

    Eligibility:
    - __status == PENDING
    - pending grace period has elapsed (based on __pending_until_epoch or __submitted_at)
    - not already present in master (duplicate-safe)

    Returns:
        (applied_count: int, applied_items: list[dict])
    """
    global LAST_MASTER_WRITE_BY_INTAKE_AT, LAST_MASTER_FP_WRITTEN_BY_INTAKE

    ensure_intake_file()

    if not os.path.exists(MASTER_TRACKER_PATH):
        log("INTAKE APPLY: master tracker missing; cannot apply.")
        return 0, []

    with FILE_LOCK:
        log("INTAKE APPLY: loading intake + master (xlsx)...")
        try:
            intake = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            intake = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        # Ensure intake status columns exist
        if "__status" not in intake.columns:
            intake["__status"] = "PENDING"
        if "__batch_id" not in intake.columns:
            intake["__batch_id"] = ""
        if "__pending_until_epoch" not in intake.columns:
            intake["__pending_until_epoch"] = ""

        intake["__status"] = intake["__status"].fillna("").astype(str)

        pending = intake[intake["__status"].astype(str).str.upper().eq("PENDING")].copy()

        now_epoch = time.time()
        pending_until = pd.to_numeric(pending.get("__pending_until_epoch", ""), errors="coerce")

        ts = pd.to_datetime(pending.get("__submitted_at", ""), errors="coerce")
        ts = ts.fillna(pd.Timestamp("1970-01-01"))
        submitted_epoch = ts.astype("int64") / 1e9

        fallback_until = submitted_epoch + float(PENDING_GRACE_SECONDS)
        pending_until = pending_until.fillna(fallback_until)

        eligible = pending[pending_until <= float(now_epoch)].copy()
        if eligible.empty:
            log("INTAKE APPLY: no eligible submissions to apply yet.")
            return 0, []

        # Build duplicate guard from current master
        try:
            master_df = read_master_csv()
        except Exception as e:
            log(f"INTAKE APPLY: failed to read master xlsx: {e}")
            return 0, []

        existing_sids = set()
        try:
            for _, mr in master_df.iterrows():
                d = {c: (mr.get(c, "") if c in master_df.columns else "") for c in MASTER_COLUMNS}
                existing_sids.add(compute_submission_id(d))
        except Exception:
            existing_sids = set()

        new_rows = []
        applied_items = []

        for _, r in eligible.iterrows():
            row = {c: r.get(c, "") for c in MASTER_COLUMNS}

            # Normalize key fields
            row["Work Order Number"] = normalize_wo_id(row.get("Work Order Number", ""))

            # Shift end date defaults to shift start date
            if not str(row.get("Shift End Date", "")).strip():
                row["Shift End Date"] = row.get("Shift Start Date", "")

            sid = compute_submission_id(row)
            if sid in existing_sids:
                continue

            existing_sids.add(sid)
            new_rows.append(row)

            applied_items.append({
                "__submission_id": str(r.get("__submission_id", "")).strip(),
                "__submitted_at": str(r.get("__submitted_at", "")).strip(),
                "Work Order Number": str(row.get("Work Order Number", "")).strip(),
                "District": str(row.get("District (Where Snow Removed)", "")).strip(),
                "Ward": str(row.get("Ward (Where Snow Removed)", "")).strip(),
                "Street": str(row.get("Street", "")).strip(),
                "From Intersection": str(row.get("From Intersection", "")).strip(),
                "To Intersection": str(row.get("To Intersection", "")).strip(),
            })

        if not new_rows:
            log("INTAKE APPLY: no new submissions to apply (all duplicates or not eligible).")
            return 0, []

        # Append to Excel master
        try:
            appended = append_rows_to_master_csv(new_rows)
        except Exception as e:
            log(f"INTAKE APPLY: failed to append to master xlsx: {e}")
            return 0, []

        # Mark applied rows as APPLIED in intake (so they won't re-apply)
        try:
            applied_ids = set(str(x.get("__submission_id", "")).strip() for x in applied_items if x.get("__submission_id"))
            if applied_ids:
                mask = intake["__submission_id"].astype(str).isin(applied_ids)
                intake.loc[mask, "__status"] = "APPLIED"
                intake.to_csv(INTAKE_PATH, index=False, encoding="utf-8")
        except Exception as e:
            log(f"INTAKE APPLY: could not mark APPLIED in intake: {e}")

        with LAST_MASTER_WRITE_LOCK:
            LAST_MASTER_WRITE_BY_INTAKE_AT = time.time()
            LAST_MASTER_FP_WRITTEN_BY_INTAKE = file_fingerprint(MASTER_TRACKER_PATH)

        log(f"INTAKE APPLY: applied {appended} new row(s) into Excel master tracker.")
        return appended, applied_items


def build_workorder_popup(props: dict) -> str:
    """Build comprehensive popup showing ALL fields for every work order."""
    
    # Helper: only show rows with data
    def row(label, key):
        v = str(props.get(key, "")).strip()
        if not v or v.lower() in ("nan", "none", ""):
            return ""
        return f"<b>{html.escape(label)}:</b> {html.escape(v)}<br>"
    
    route_mode = props.get("Routing_Mode", "")
    extra = ""
    if route_mode:
        extra = (
            "<div style='margin-top:6px;padding:6px;border-radius:6px;background:#fff3cd;border:1px solid #ffeeba;'>"
            f"<b>Routing:</b> {html.escape(str(route_mode))}"
            "</div>"
        )
    
    wo = props.get("Work_Order_Number", "")
    
    return f"""
    <div style='font-family:Arial;font-size:13px;line-height:1.25;max-width:450px;max-height:600px;overflow-y:auto;'>
      <div style='font-size:15px;font-weight:800;margin-bottom:8px;'>Work Order {html.escape(str(wo))}</div>
      
      {row('Street', 'Street')}
      {row('From', 'From_Intersection')}
      {row('To', 'To_Intersection')}
      {extra}
      
      <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
      <div style='font-weight:700;margin-bottom:4px;'>Administrative</div>
      
      {row('Supervisor 1', 'Supervisor_1')}
      {row('Supervisor 2', 'Supervisor_2')}
      {row('Supervisor 3', 'Supervisor_3')}
      {row('District', 'District')}
      {row('Ward', 'Ward')}
      {row('TOA Area', 'TOA_Area')}
      {row('Shift Start Date', 'Shift_Start_Date')}
      {row('Shift Start Time', 'Shift_Start_Time')}
      {row('Shift End Date', 'Shift_End_Date')}
      {row('Shift End Time', 'Shift_End_Time')}
      
      <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
      <div style='font-weight:700;margin-bottom:4px;'>Operational Details</div>
      
      {row('Side Cleared', 'Side_Cleared')}
      {row('Road Side', 'Road_Side')}
      
      <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
      <div style='font-weight:700;margin-bottom:4px;'>Infrastructure</div>
      
      {row('Roadway', 'Roadway')}
      {row('Sidewalk', 'Sidewalk')}
      {row('Cycling', 'Cycling_Infrastructure')}
      {row('Bridge', 'Bridge')}
      {row('School Zones', 'School_Zones')}
      {row('Layby Parking', 'Layby_Parking')}
      
      <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
      <div style='font-weight:700;margin-bottom:4px;'>Equipment & Resources</div>
      
      {row('Equipment Method', 'Equipment_Method')}
      {row('# Dump Trucks', 'Dump_Trucks_Count')}
      {row('Truck Source', 'Dump_Truck_Source')}
      {row('# Loads', 'Number_of_Loads')}
      {row('Tonnes', 'Tonnes')}
      {row('Snow Dump Site', 'Snow_Dump_Site')}
      
      <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
      <div style='font-weight:700;margin-bottom:4px;'>Crew Information</div>
      
      {row('Crew Type', 'Crew_Type')}
      {row('# of Crews', 'Number_of_Crews')}
      {row('Contractor TOA', 'Contractor_TOA')}
      {row('Crew Number', 'Crew_Number')}
      {row('In-House Base', 'InHouse_Base_Yard')}
      {row('# Staff', 'Number_of_Staff')}
      
      <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
      {row('Notes', 'Notes')}
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
        def extract_cross_from_endpoint(street_val, endpoint_val):
            cands = endpoint_cross_candidates(street_val, endpoint_val)
            return cands[0] if cands else ''



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

        master = read_master_csv()
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

        # ---------------------------------------------------------
        # UI helper: Street → Cross-streets (for /new and /edit forms)
        # ---------------------------------------------------------
        # The webforms now use the new address format:
        #   Street + Street/From Intersection + Street/To Intersection
        # We source the dependent cross-street picklists from the Centreline
        # Intersection reference file. Routing still uses the full centreline graph.

        ref_street_to_cross, ref_pair_to_id = get_intersection_reference()

        if ref_street_to_cross:
            street_to_cross = ref_street_to_cross
        else:
            # Fallback to graph-derived cross streets (older behavior)
            street_to_cross = {}
            for _s, _nodes in street_nodes.items():
                try:
                    _cross = set()
                    for _nid in _nodes:
                        _cross.update(intersection_to_streets.get(int(_nid), set()))
                    _cross.discard(_s)
                    street_to_cross[_s] = sorted(
                        [x for x in _cross if x and isinstance(x, str)],
                        key=lambda x: x.casefold()
                    )
                except Exception:
                    street_to_cross[_s] = []

        # Prefer the reference street list for UI if available; otherwise use centreline
        if ref_street_to_cross:
            ALL_CENTRE_STREETS = sorted([s for s in ref_street_to_cross.keys() if s], key=lambda x: x.casefold())


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
            color = props.get("Line_Color", "red")
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
            color = props.get("Line_Color", "red")
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

        def lookup_intersection_id_from_reference(street1_key, street2_key, pair_to_id_dict):
            """
            Look up the intersection ID from the reference file for two streets.
            
            Args:
                street1_key: Normalized street name 1
                street2_key: Normalized street name 2
                pair_to_id_dict: The pair_to_id dictionary from get_intersection_reference()
                
            Returns:
                intersection_id (int) or None
            """
            if not pair_to_id_dict:
                return None
            
            # Try both orderings
            iid = pair_to_id_dict.get((street1_key, street2_key))
            if iid is not None:
                return iid
            
            iid = pair_to_id_dict.get((street2_key, street1_key))
            if iid is not None:
                return iid
            
            return None

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

        def build_segment_popup(props: dict) -> str:
            """Build segment popup with ALL fields matching workorder popup structure."""
            wo = props.get("Work_Order_Number", "")
            date = props.get("Shift_Date", "")
            district = props.get("District", "")
            ward = props.get("Ward", "")
            toa = props.get("TOA_Area", "")
            supervisor = props.get("Supervisor_1", "")
            supervisor_2 = props.get("Supervisor_2", "")
            supervisor_3 = props.get("Supervisor_3", "")
            shift = props.get("Shift_Time", "")
            shift_start_date = props.get("Shift_Start_Date", "")
            shift_start_time = props.get("Shift_Start_Time", "")
            shift_end_date = props.get("Shift_End_Date", "")
            shift_end_time = props.get("Shift_End_Time", "")
            street = props.get("Street", "")
            frm = props.get("From_Intersection", "")
            to_ = props.get("To_Intersection", "")
            side = props.get("Side_Cleared", "")
            road_side = props.get("Road_Side", "")
            roadway = props.get("Roadway", "")    
            sidewalk = props.get("Sidewalk", "")
            cycling = props.get("Cycling_Infrastructure", "")
            bridge = props.get("Bridge", "")
            school = props.get("School_Zones", "")
            layby_parking = props.get("Layby_Parking", "")
            equipment = props.get("Equipment_Method", "")
            dump_trucks = props.get("Dump_Trucks_Count", "")
            dump_source = props.get("Dump_Truck_Source", "")
            contractor_toa = props.get("Contractor_TOA", "")
            snow_site = props.get("Snow_Dump_Site", "")
            loads = props.get("Number_of_Loads", "")
            tonnes = props.get("Tonnes", "")
            crew_type = props.get("Crew_Type", "")
            num_crews = props.get("Number_of_Crews", "")
            crew_num = props.get("Crew_Number", "")
            inhouse = props.get("InHouse_Base_Yard", "")
            num_staff = props.get("Number_of_Staff", "")
            notes = props.get("Notes", "")
            route_mode = props.get("Routing_Mode", "")
            
            # Segment-specific fields
            wo_m_str = props.get("Total_Meters_Display", "")
            wo_km_str = props.get("Total_KM_Display", "")
            segment_count = props.get("Total_Segments", "")
            
            # Helper: only show rows with data
            def row(label, val):
                v = str(val or "").strip()
                if not v or v.lower() in ("nan", "none", ""):
                    return ""
                return f"<b>{html.escape(label)}:</b> {html.escape(v)}<br>"
            
            extra = ""
            if route_mode:
                extra = (
                    "<div style='margin-top:6px;padding:6px;border-radius:6px;background:#fff3cd;border:1px solid #ffeeba;'>"
                    f"<b>Routing:</b> {html.escape(str(route_mode))}"
                    "</div>"
                )
            
            return f"""
            <div style='font-family:Arial;font-size:13px;line-height:1.25;max-width:420px;'>
              <div style='font-size:15px;font-weight:800;margin-bottom:8px;'>Work Order {html.escape(str(wo))}</div>
              
              <b>Street:</b> {html.escape(str(street))}<br>
              <b>From:</b> {html.escape(str(frm))}<br>
              <b>To:</b> {html.escape(str(to_))}<br>
              {extra}
              
              <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
              
              {row('Supervisor 1', supervisor)}
              {row('Supervisor 2', supervisor_2)}
              {row('Supervisor 3', supervisor_3)}
              <b>District:</b> {html.escape(str(district))}<br>
              <b>Ward:</b> {html.escape(str(ward))}<br>
              {row('TOA Area', toa)}
              <b>Start:</b> {html.escape(str(shift_start_date))} {html.escape(str(shift_start_time))}<br>
              <b>End:</b> {html.escape(str(shift_end_date))} {html.escape(str(shift_end_time))}<br>
              
              <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
              
              {row('Side Cleared', side)}
              {row('Road Side', road_side)}
              {row('Roadway', roadway)}
              {row('Sidewalk', sidewalk)}
              {row('Cycling Infra', cycling)}
              {row('Bridge', bridge)}
              {row('School Zones', school)}
              {row('Layby Parking', layby_parking)}
              
              <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
              
              {row('Equipment', equipment)}
              {row('Dump Trucks', dump_trucks)}
              {row('Source', dump_source)}
              {row('Contractor TOA', contractor_toa)}
              {row('Loads', loads)}
              {row('Tonnes', tonnes)}
              {row('Snow Site', snow_site)}
              
              {row('Crew Type', crew_type)}
              {row('# Crews', num_crews)}
              {row('Crew #', crew_num)}
              {row('In-House Base', inhouse)}
              {row('# Staff', num_staff)}
              
              <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
              {row('Notes', notes)}
              
              <hr style='margin:8px 0;border:none;border-top:1px solid #ddd;'>
              <b>Total Segments:</b> {html.escape(str(segment_count))}<br>
              <b>Distance (m):</b> {html.escape(str(wo_m_str))}<br>
              <b>Distance (km):</b> {html.escape(str(wo_km_str))}<br>
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
                    '<div style="margin-top:4px;"><b>Street:</b> ' + escapeHtml(loc) + '</div>' +
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
            shift_start_date="",
            shift_start_time="",
            shift_end_date="",
            shift_end_time="",
            toa="",
            dump_trucks="",
            dump_provider="",
            loads="",
            tonnes="",
            side="",
            road_side="",
            snow_dump_site="",
            comments="",
            roadway="",
            sidewalk="",
            cycling_infra="",
            bridge="",
            school_zones="",
            layby_parking="",
            equipment="",
            contractor_toa="",
            crew_type="",
            num_crews="",
            crew_number="",
            inhouse_base="",
            num_staff="",
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
                    "Feature_Type": "workorder_segment",
                    "Work_Order_Number": str(wo_id),
                    "Street": str(loc_raw),
                    "From_Intersection": str(from_raw),
                    "To_Intersection": str(to_raw),
                    "Street_Normalized": str(street_key),
                    "District": str(district_val),
                    "Ward": str(ward),
                    "Shift_Date": str(date_str),
                    "Shift_Time": str(shift_str),
                    "Shift_Start_Date": str(shift_start_date or date_str),
                    "Shift_Start_Time": str(shift_start_time),
                    "Shift_End_Date": str(shift_end_date or date_str),
                    "Shift_End_Time": str(shift_end_time),
                    "Supervisor_1": str(supervisor_raw),
                    "Supervisor_2": str(supervisor_2_raw),
                    "Supervisor_3": str(supervisor_3_raw),

                    # Segment-specific fields
                    "From_Intersection_ID": int(seg["u"]),
                    "To_Intersection_ID": int(seg["v"]),
                    "Segment_Index": int(idx),
                    "Total_Segments": int(seg_count),
                    "Segment_Distance_Meters": float(seg_m),
                    "Segment_Distance_KM": float(seg_km),
                    "Segment_Meters_Display": fmt_sigfig(seg_m, 2),
                    "Segment_KM_Display": fmt_sigfig(seg_km, 2),
                    "Segment_From_Street": str(seg_from_label),
                    "Segment_To_Street": str(seg_to_label),
                    "Total_Distance_Meters": float(wo_total_m),
                    "Total_Distance_KM": float(wo_total_km),
                    "Total_Meters_Display": fmt_sigfig(wo_total_m, 2),
                    "Total_KM_Display": fmt_sigfig(wo_total_km, 2),

                    "Routing_Mode": route_mode,
                    
                    # All operational fields
                    "TOA_Area": clean(toa),
                    "Side_Cleared": clean(side),
                    "Road_Side": clean(road_side),
                    "Roadway": clean(roadway),
                    "Sidewalk": clean(sidewalk),
                    "Cycling_Infrastructure": clean(cycling_infra),
                    "Bridge": clean(bridge),
                    "School_Zones": clean(school_zones),
                    "Layby_Parking": clean(layby_parking),
                    "Equipment_Method": clean(equipment),
                    "Dump_Trucks_Count": clean(dump_trucks),
                    "Dump_Truck_Source": clean(dump_provider),
                    "Contractor_TOA": clean(contractor_toa),
                    "Number_of_Loads": clean(loads),
                    "Tonnes": clean(tonnes),
                    "Snow_Dump_Site": clean(snow_dump_site),
                    "Crew_Type": clean(crew_type),
                    "Number_of_Crews": clean(num_crews),
                    "Crew_Number": clean(crew_number),
                    "InHouse_Base_Yard": clean(inhouse_base),
                    "Number_of_Staff": clean(num_staff),
                    "Notes": clean(comments),
                    "Line_Color": str(district_color),
                }

                seg_feature = {"type": "Feature", "geometry": seg_geometry, "properties": props}
                geojson_features.append(seg_feature)

                seg_popup = build_segment_popup(props)

                seg_gj = folium.GeoJson(
                    data=seg_feature,
                    style_function=style_for_segment,
                    highlight_function=lambda feat: {
                        "color": feat["properties"].get("Line_Color", "red"),
                        "weight": 8,
                        "opacity": 0.9,
                    },
                    name=f"WO {wo_id} segment",
                )

                seg_tooltip = folium.GeoJsonTooltip(
                    fields=[
                        "Work_Order_Number",
                        "Segment_Index",
                        "Total_Segments",
                        "Street",
                        "Segment_To_Street",
                        "Segment_From_Street",
                        "Segment_Meters_Display",
                        "Segment_KM_Display",
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
                "Street_resolved": loc_key,
                "From_resolved": from_key,
                "To_resolved": to_key,
            })

        def add_line_feature(row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                     supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                     loc_key=None, from_key=None, to_key=None, route_mode="", wo_total_m=0):

            props = {
                "Feature_Type": "workorder_line",
                "Work_Order_Number": normalize_wo_id(wo_id),
                
                # Location fields
                "Street": str(loc_raw),
                "From_Intersection": str(from_raw),
                "To_Intersection": str(to_raw),
                "Street_Normalized": loc_key,
                "From_Normalized": from_key,
                "To_Normalized": to_key,

                # Administrative fields
                "District": district_val,
                "Ward": ward_val,
                "Supervisor_1": str(supervisor_raw).strip(),
                "Supervisor_2": str(supervisor_2_raw).strip(),
                "Supervisor_3": str(supervisor_3_raw).strip(),
                "Shift_Date": date_val,
                "Shift_Time": shift_val,
                "Shift_Start_Date": date_val,
                "Shift_Start_Time": shift_start_t,
                "Shift_End_Date": str(row.get("Shift End Date", "")).strip(),
                "Shift_End_Time": shift_end_t,
                
                # Distance fields (formatted only)
                "Total_Meters": fmt_sigfig(wo_total_m, 2) if wo_total_m > 0 else "0",
                "Total_KM": fmt_sigfig(wo_total_m / 1000.0, 2) if wo_total_m > 0 else "0",
                
                # Operational fields
                "TOA_Area": clean_text(row.get("TOA Area (Where Snow Removed)", "")),
                "Side_Cleared": clean_text(row.get("One Side / Both Sides Cleared?", "")),
                "Road_Side": clean_text(row.get("Side of Road Cleared", "")),
                
                # Infrastructure
                "Roadway": clean_text(row.get("Roadway", "")),
                "Sidewalk": clean_text(row.get("Sidewalk", "")),
                "Cycling_Infrastructure": clean_text(row.get("Separated Cycling Infrastructure", "")),
                "Bridge": clean_text(row.get("Bridge", "")),
                "School_Zones": clean_text(row.get("School Loading Zones", "")),
                "Layby_Parking": clean_text(row.get("Layby Parking", "")),
                
                # Equipment
                "Equipment_Method": clean_text(row.get("Equipment Method", "")),
                "Dump_Trucks_Count": clean_text(row.get("# of Equipment (Dump Trucks)", "")),
                "Dump_Truck_Source": clean_text(row.get("Dump Truck Source (In-House/Contractor)", "")),
                "Number_of_Loads": clean_text(row.get("# of Loads", "")),
                "Tonnes": clean_text(row.get("Tonnes", "")),
                "Snow_Dump_Site": clean_text(row.get("Snow Dump Site", "")),
                
                # Crew information
                "Crew_Type": clean_text(row.get("Snow Removal by Contracted Crew or In-House?", "")),
                "Contractor_TOA": clean_text(row.get("Contractor: Crew TOA Area Responsibility", "")),
                "Number_of_Crews": clean_text(row.get("Contractor: # of Crews", "")),
                "Crew_Number": clean_text(row.get("Contractor: Crew Number", "")),
                "InHouse_Base_Yard": clean_text(row.get("In-House: Staff Responsibility (Base Yard)", "")),
                "Number_of_Staff": clean_text(row.get("In-House: # of Staff", "")),
                
                # Notes and metadata
                "Notes": clean_text(row.get("NOTES", "")),
                "Routing_Mode": route_mode,
                "Line_Color": color,
            }

            feature = {"type": "Feature", "geometry": geometry, "properties": props}
            geojson_features.append(feature)

            gj = folium.GeoJson(
                data=feature,
                style_function=style_for_feature,
                highlight_function=lambda feat: {
                    "color": feat["properties"].get("Line_Color", "red"),
                    "weight": 7,
                    "opacity": 1.0,
                },
                name=f"WO {wo_id}",
            )

            # ✅ FIXED TOOLTIP - Use clear field names
            tooltip = folium.GeoJsonTooltip(
                fields=["Work_Order_Number", "Street", "From_Intersection", "To_Intersection", 
                        "District", "Supervisor_1", "Shift_Date", "Shift_Time"],
                aliases=["WO", "Street", "From", "To", "District", "Supervisor", "Date", "Shift"],
                sticky=False,
            )
            tooltip.add_to(gj)

            # ✅ UPDATED POPUP with all fields
            popup_html = build_workorder_popup(props)
            folium.Popup(popup_html, max_width=420).add_to(gj)
            gj.add_to(work_orders_group)

        for _, row in master.iterrows():
            row_dict = row.to_dict()

            submission_id = str(row.get("__submission_id", "")).strip()
            is_intake_row = bool(submission_id) and (submission_id in intake_ids_set)

            loc_raw = row.get("Street", "")
            from_raw = row.get("From Intersection", "")
            to_raw = row.get("To Intersection", "")
            
            # DEBUG: Log raw values for St Clair
            if "CLAIR" in str(loc_raw).upper():
                log(f"DEBUG RAW: Street='{loc_raw}', From='{from_raw}', To='{to_raw}'")

            # Main street
            loc_core = extract_street_token(loc_raw)
            loc_norm = normalize_street_name(loc_core)

            # ✅ From/To may be 'STREET / CROSS' OR 'A / B / C' (3-way) — collect multiple candidates
            from_candidates_norm = endpoint_cross_candidates(loc_raw, from_raw)
            to_candidates_norm = endpoint_cross_candidates(loc_raw, to_raw)

            # Keep a single primary value for logging/debug, but use candidates for routing
            from_norm = from_candidates_norm[0] if from_candidates_norm else ""
            to_norm = to_candidates_norm[0] if to_candidates_norm else ""


            loc_key, loc_score = resolve_street_name(loc_norm, MIN_SIM_LOCATION)
            
            # DEBUG
            if "CLAIR" in loc_norm:
                log(f"DEBUG: loc_norm='{loc_norm}' -> loc_key='{loc_key}', score={loc_score:.3f}")
                log(f"DEBUG: loc_key in street_graphs: {loc_key in street_graphs if loc_key else 'N/A'}")
            
            if not loc_key:
                reason = f"Location not matched to centreline (core='{loc_core}', norm='{loc_norm}', best_score={loc_score:.2f})"
                row_dict["skip_reason"] = reason
                skipped_records.append(row_dict)
                skipped_count += 1
                skip_reason_counter[reason] += 1
                if is_intake_row:
                    intake_skipped_counter += 1
                    log(f"INTAKE SKIP: WO={row.get('Work Order Number','')} id={submission_id} -> {reason}")
                    record_intake_debug("SKIPPED", submission_id, row.get("Work Order Number", ""), reason, loc_raw, from_raw, to_raw)
                continue

            wo_id = str(row.get("Work Order Number", ""))
            district_val = str(row.get("District (Where Snow Removed)", "Unknown")).strip() or "Unknown"
            color = get_color_for_district(district_val)
            ward_val = str(row.get("Ward (Where Snow Removed)", "")).strip()
            date_val = str(row.get("Shift Start Date", "")).strip()
            shift_start_t = str(row.get("Shift Start Time", "")).strip()
            shift_end_t = str(row.get("Shift End Time", "")).strip()
            shift_val = normalize_shift_time_range("", shift_start_t, shift_end_t) or (f"{shift_start_t} - {shift_end_t}".strip(" -"))
            type_val = ""

            supervisor_raw = row.get("Supervisor 1", "")
            sup_key = make_supervisor_key(supervisor_raw)
            supervisor_2_raw = row.get("Supervisor 2 (if relevant)", "")
            supervisor_3_raw = row.get("Supervisor 3 (if relevant)", "")

            from_is_str = isinstance(from_raw, str)
            to_is_str = isinstance(to_raw, str)
            entire_flag = (
                (from_is_str and "ENTIRE STREET" in from_raw.upper())
                or (to_is_str and "ENTIRE STREET" in to_raw.upper())
            )

            if entire_flag:
                coords_to_use = full_street_multiline(loc_key)
                if not coords_to_use:
                    reason = "Entire Street requested but no geometry found for Street"
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
                wo_total_m = multiline_distance_m(coords_to_use)
                
                add_line_feature(row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                                 supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                                 loc_key=loc_key, route_mode="ENTIRE STREET", wo_total_m=wo_total_m)
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

            # Resolve candidate cross-streets (may be multiple for 3-way endpoints)
            def _resolve_candidates(norm_list):
                out = []
                for norm in (norm_list or []):
                    k, sc = resolve_street_name(norm, MIN_SIM_CROSS)
                    if k:
                        out.append((k, float(sc), norm))
                # Highest score first; de-dupe by key
                out.sort(key=lambda t: t[1], reverse=True)
                seen = set()
                dedup = []
                for k, sc, norm in out:
                    if k in seen:
                        continue
                    seen.add(k)
                    dedup.append((k, sc, norm))
                return dedup

            from_resolved = _resolve_candidates(from_candidates_norm or ([from_norm] if from_norm else []))
            to_resolved   = _resolve_candidates(to_candidates_norm   or ([to_norm]   if to_norm else []))

            # Primary display keys/scores (best candidate)
            from_key, from_score = (from_resolved[0][0], from_resolved[0][1]) if from_resolved else (None, 0.0)
            to_key, to_score     = (to_resolved[0][0],   to_resolved[0][1])   if to_resolved   else (None, 0.0)


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
            # Prefer explicit intersection IDs (if provided in the master), then fall back to name matching

            g_loc = street_graphs.get(loc_key)

            def _parse_int_id(v):
                try:
                    if v is None:
                        return None
                    s = str(v).strip()
                    if not s or s.lower() == "nan":
                        return None
                    return int(float(s))
                except Exception:
                    return None

            from_id = _parse_int_id(row.get("From Intersection ID", ""))
            to_id   = _parse_int_id(row.get("To Intersection ID", ""))

            # Try explicit IDs first (if present and valid for this street graph)
            start_node = from_id if (g_loc and from_id in g_loc["adj"]) else None
            end_node   = to_id   if (g_loc and to_id   in g_loc["adj"]) else None

            # For 3-way endpoints, try multiple candidate cross-streets until we find a valid node
            def _pick_node_from_candidates(resolved_list):
                """Return (node_id, chosen_cross_key, chosen_score) or (None, best_key, best_score)."""
                if not resolved_list:
                    return (None, None, 0.0)

                # Keep best for display even if we fail
                best_key, best_sc, _best_norm = resolved_list[0]

                for cross_key, sc, _norm in resolved_list:
                    # 1) Prefer reference lookup (more authoritative)
                    if ref_pair_to_id:
                        try:
                            ref_id = lookup_intersection_id_from_reference(loc_key, cross_key, ref_pair_to_id)
                        except Exception:
                            ref_id = None
                        if ref_id and g_loc and ref_id in g_loc["adj"]:
                            return (ref_id, cross_key, sc)

                    # 2) Fallback: common-node method
                    nid = find_intersection_node(loc_key, cross_key)
                    if nid is not None:
                        # If we have a street-local graph, ensure membership
                        if (not g_loc) or (nid in g_loc["adj"]):
                            return (nid, cross_key, sc)

                return (None, best_key, best_sc)

            # If explicit IDs missing/invalid, try candidate lists (works for 2-way + 3-way)
            if start_node is None:
                start_node, chosen_from_key, chosen_from_sc = _pick_node_from_candidates(from_resolved)
                if chosen_from_key:
                    from_key, from_score = chosen_from_key, float(chosen_from_sc)

            if end_node is None:
                end_node, chosen_to_key, chosen_to_sc = _pick_node_from_candidates(to_resolved)
                if chosen_to_key:
                    to_key, to_score = chosen_to_key, float(chosen_to_sc)

            # DEBUG LOGGING
            if loc_key == "ST CLAIR AVENUE W":
                log(f"DEBUG St Clair: from_key={from_key}, to_key={to_key}")
                log(f"DEBUG St Clair: start_node={start_node}, end_node={end_node}")
                log(f"DEBUG St Clair: g_loc exists={g_loc is not None}")
                if g_loc:
                    log(f"DEBUG St Clair: g_loc['adj'] has {len(g_loc['adj'])} keys")
            
            if start_node is None or end_node is None or start_node == end_node:
                # More informative fallback message
                route_info = []
                if start_node is None:
                    route_info.append(f"From intersection ({from_key}) not found in centreline")
                if end_node is None:
                    route_info.append(f"To intersection ({to_key}) not found in centreline")
                if start_node == end_node and start_node is not None:
                    route_info.append("Start and end are the same intersection")
                
                reason_detail = "; ".join(route_info) if route_info else "Intersection nodes not found"
                
                coords_to_use = full_street_multiline(loc_key)
                if coords_to_use:
                    geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
                    wo_total_m = multiline_distance_m(coords_to_use)
                    
                    add_line_feature(
                        row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                        supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                        loc_key=loc_key, from_key=from_key, to_key=to_key,
                        route_mode=f"Points not found in centreline. Mapping Full Street as FALLBACK ({reason_detail})",
                        wo_total_m=wo_total_m
                    )
                    subsegment_count += 1
                    if is_intake_row:
                        intake_mapped_counter += 1
                        record_intake_debug(
                            "MAPPED", submission_id, wo_id,
                            f"Points not found in centreline. Mapping Full Street as FALLBACK ({reason_detail})",
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
            
            # DEBUG
            if loc_key == "ST CLAIR AVENUE W" and start_node == 13461271:
                if path:
                    node_path, edge_idx = path
                    log(f"DEBUG: Found path with {len(node_path)} nodes")
                    log(f"DEBUG: First 5 nodes: {node_path[:5]}")
                    log(f"DEBUG: Last 5 nodes: {node_path[-5:]}")
                    if 13460295 in node_path:
                        log(f"DEBUG: ⚠️  Path includes Yonge (13460295)!")
                    else:
                        log(f"DEBUG: ✅ Path does not include Yonge")
                else:
                    log(f"DEBUG: No path found on street")


            if path is None:
                gpath = shortest_path_global(start_node, end_node)
                if gpath is not None:
                    node_path_g, edge_idx_g = gpath
                    coords_to_use = build_path_multiline_global(node_path_g, edge_idx_g)
                    if coords_to_use:
                        geometry = {"type": "MultiLineString", "coordinates": coords_to_use}
                        wo_total_m = multiline_distance_m(coords_to_use)
                        
                        add_line_feature(
                            row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                            supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                            loc_key=loc_key, from_key=from_key, to_key=to_key,
                            route_mode="Path not found on street. Using global routing as FALLBACK",
                            wo_total_m=wo_total_m
                        )
                        subsegment_count += 1
                        if is_intake_row:
                            intake_mapped_counter += 1
                            record_intake_debug(
                                "MAPPED", submission_id, wo_id,
                                "Path not found on street. Using global routing as FALLBACK",
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
            wo_total_m = multiline_distance_m(coords_to_use)
            
            add_line_feature(
                row, wo_id, geometry, color, district_val, ward_val, date_val, shift_val,
                supervisor_raw, sup_key, type_val, loc_raw, from_raw, to_raw,
                loc_key=loc_key, from_key=from_key, to_key=to_key,
                route_mode="Exact Location found and Mapped",
                wo_total_m=wo_total_m
            )
            subsegment_count += 1

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
                shift_display_html=format_shift_with_icons(shift_val),
                wo_total_m=wo_total_m,
                route_mode="Exact Location found and Mapped",
                shift_start_date=row.get("Shift Start Date", ""),
                shift_start_time=row.get("Shift Start Time", ""),
                shift_end_date=row.get("Shift End Date", ""),
                shift_end_time=row.get("Shift End Time", ""),
                toa=row.get("TOA Area (Where Snow Removed)", ""),
                dump_trucks=row.get("# of Equipment (Dump Trucks)", ""),
                dump_provider=row.get("Dump Truck Source (In-House/Contractor)", ""),
                loads=row.get("# of Loads", ""),
                tonnes=row.get("Tonnes", ""),
                side=row.get("One Side / Both Sides Cleared?", ""),
                road_side=row.get("Side of Road Cleared", ""),
                snow_dump_site=row.get("Snow Dump Site", ""),
                comments=row.get("NOTES", ""),
                roadway=row.get("Roadway", ""),
                sidewalk=row.get("Sidewalk", ""),
                cycling_infra=row.get("Separated Cycling Infrastructure", ""),
                bridge=row.get("Bridge", ""),
                school_zones=row.get("School Loading Zones", ""),
                layby_parking=row.get("Layby Parking", ""),
                equipment=row.get("Equipment Method", ""),
                contractor_toa=row.get("Contractor: Crew TOA Area Responsibility", ""),
                crew_type=row.get("Snow Removal by Contracted Crew or In-House?", ""),
                num_crews=row.get("Contractor: # of Crews", ""),
                crew_number=row.get("Contractor: Crew Number", ""),
                inhouse_base=row.get("In-House: Staff Responsibility (Base Yard)", ""),
                num_staff=row.get("In-House: # of Staff", ""),
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
            # Filter to only include work order lines (not individual segments) for ArcGIS export
            workorder_lines_only = [
                f for f in geojson_features 
                if f.get("properties", {}).get("Feature_Type") == "workorder_line"
            ]
            
            # Remove internal attributes from GeoJSON output
            attrs_to_exclude = [
                "Street_Normalized",
                "From_Normalized", 
                "To_Normalized",
                "Shift_Time",
                "Shift_Date",
                "Line_Color"
            ]
            
            # Clean features for export
            cleaned_features = []
            for feature in workorder_lines_only:
                cleaned_feature = {
                    "type": feature["type"],
                    "geometry": feature["geometry"],
                    "properties": {
                        k: v for k, v in feature["properties"].items() 
                        if k not in attrs_to_exclude
                    }
                }
                cleaned_features.append(cleaned_feature)
            
            feature_collection = {"type": "FeatureCollection", "features": cleaned_features}
            with open(OUTPUT_GEOJSON, "w", encoding="utf-8") as f:
                json.dump(feature_collection, f)
            log(f"GeoJSON saved: {OUTPUT_GEOJSON} ({len(cleaned_features)} work order lines)")

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
            "street_to_cross_count": int(len(street_to_cross)),
            "street_to_cross": street_to_cross,
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
    
def _parse_time_token(tok: str):
    """
    Accepts:
      - '18:30'
      - '6:30pm', '6:30 PM'
      - '6pm', '6 PM'
      - '06:30AM'
    Returns (hour24, minute) or None.
    """
    if tok is None:
        return None
    s = str(tok).strip()
    if not s:
        return None

    s = re.sub(r"\s+", "", s).upper()

    # 24h HH:MM
    m = re.match(r"^(\d{1,2}):(\d{2})$", s)
    if m:
        hh = int(m.group(1))
        mm = int(m.group(2))
        if 0 <= hh <= 23 and 0 <= mm <= 59:
            return (hh, mm)
        return None

    # 12h H(:MM)?(AM|PM)
    m = re.match(r"^(\d{1,2})(?::(\d{2}))?(AM|PM)$", s)
    if m:
        h12 = int(m.group(1))
        mm = int(m.group(2) or "00")
        ap = m.group(3)
        if not (1 <= h12 <= 12 and 0 <= mm <= 59):
            return None
        hh = h12 % 12
        if ap == "PM":
            hh += 12
        return (hh, mm)

    return None


def _fmt_hhmm_ampm(hh24: int, mm: int) -> str:
    # Always 2-digit hour as requested (hh:mmAM/PM)
    ap = "AM" if hh24 < 12 else "PM"
    h12 = hh24 % 12
    if h12 == 0:
        h12 = 12
    return f"{h12:02d}:{mm:02d}{ap}"


def normalize_shift_time_range(raw: str, start_24: str = "", end_24: str = "") -> str:
    """
    Returns standardized: 'hh:mmAM - hh:mmPM'
    Input can be:
      - start_24='HH:MM' + end_24='HH:MM'  (from <input type=time>)
      - raw like '06:30AM - 06:30PM' or '6:30pm-6:30pm' or '18:30-06:30'
    """
    # Preferred: two time inputs
    if start_24 and end_24:
        a = _parse_time_token(start_24)
        b = _parse_time_token(end_24)
        if a and b:
            return f"{_fmt_hhmm_ampm(a[0], a[1])} - {_fmt_hhmm_ampm(b[0], b[1])}"

    # Fallback: parse raw range
    s = (raw or "").strip()
    if not s:
        return ""
    # normalize dash variants
    s2 = s.replace("–", "-").replace("—", "-")
    parts = [p.strip() for p in s2.split("-") if p.strip()]
    if len(parts) >= 2:
        a = _parse_time_token(parts[0])
        b = _parse_time_token(parts[1])
        if a and b:
            return f"{_fmt_hhmm_ampm(a[0], a[1])} - {_fmt_hhmm_ampm(b[0], b[1])}"

    # If user typed a single token (rare), treat as invalid (force range)
    return ""



# =========================================================
# 5. LIVE SERVER + SSE EVENTS + DATA ENTRY UI
# =========================================================

app = Flask(__name__)
events = Queue()
latest_build_stats = {"status": "not built yet"}
latest_centre_streets = []
latest_street_to_cross = {}
latest_allowed_sets = {}



INDEX_HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Live Work Orders Map</title>
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">

  <style>
    :root{
      --bg: #f5f7fb;
      --card: #ffffff;
      --stroke: #e5e7eb;
      --text: #111827;
      --muted: #6b7280;
      --brand: #005aa3;  /* CoT-ish blue */
      --brand2:#0ea5e9;
      --shadow: 0 18px 45px rgba(16,24,40,0.10);
      --radius: 18px;
    }
    *{ box-sizing:border-box; }
    html,body{ height:100%; }
    body{
      margin:0;
      font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
      color: var(--text);
      background:
        radial-gradient(900px 450px at 10% 0%, rgba(14,165,233,0.15), transparent 55%),
        radial-gradient(900px 450px at 90% 0%, rgba(0,90,163,0.10), transparent 55%),
        linear-gradient(180deg, #ffffff, var(--bg));
      padding: 28px 18px;
      -webkit-font-smoothing: antialiased;
      -moz-osx-font-smoothing: grayscale;
    }

    .card{
      max-width: 980px;
      margin: 0 auto;
      border: 1px solid var(--stroke);
      background: var(--card);
      border-radius: var(--radius);
      padding: 18px 18px;
      box-shadow: var(--shadow);
      animation: fadeIn .22s ease-out both;
    }
    @keyframes fadeIn{ from{ opacity:0; transform: translateY(6px);} to{ opacity:1; transform:none;} }

    .top{
      display:flex;
      align-items:center;
      justify-content:space-between;
      gap: 14px;
      margin-bottom: 10px;
    }
    .brand{
      display:flex;
      align-items:center;
      gap: 12px;
      min-width: 0;
    }
    .brand img{
      height: 42px;
      width: auto;
      display:block;
      object-fit: contain;
    }
    .titleWrap{ min-width:0; }
    h2{ margin:0; font-size: 20px; font-weight: 950; letter-spacing: -0.02em; }
    .sub{ margin-top:4px; color: var(--muted); font-weight: 650; font-size: 13px; }

    .stats{
      display:grid;
      grid-template-columns: repeat(3, minmax(0, 1fr));
      gap: 10px;
      margin-top: 12px;
    }
    .stat{
      border: 1px solid var(--stroke);
      border-radius: 16px;
      padding: 10px 12px;
      background: #fbfdff;
    }
    .stat .k{ color: var(--muted); font-size: 12px; font-weight: 800; }
    .stat .v{ margin-top: 4px; font-size: 14px; font-weight: 950; }

    a{ color: var(--brand); text-decoration:none; font-weight: 800; }
    a:hover{ text-decoration: underline; }

    a.btn{
      display:inline-flex;
      align-items:center;
      justify-content:center;
      gap:10px;
      padding: 12px 14px;
      border-radius: 14px;
      border: 1px solid rgba(0,90,163,0.20);
      background: linear-gradient(135deg, var(--brand), var(--brand2));
      color: #fff;
      text-decoration:none;
      font-weight: 950;
      box-shadow: 0 14px 34px rgba(0,90,163,0.18);
      transition: transform .12s ease, filter .12s ease;
      user-select:none;
    }
    a.btn:hover{ transform: translateY(-1px); filter: brightness(1.03); text-decoration:none; }
    a.btn:active{ transform: translateY(0px) scale(.99); }

    code{
      background: #f3f4f6;
      border: 1px solid #e5e7eb;
      padding: 2px 8px;
      border-radius: 999px;
      font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
      font-size: 12px;
      color: #111827;
    }

    .muted{ color: var(--muted); font-size: 12px; font-weight: 650; }

    @media (max-width: 820px){
      .stats{ grid-template-columns: 1fr; }
      .top{ flex-direction: column; align-items:flex-start; }
    }
  </style>


</head>
<body>
    <div class="card">
    <div class="top">
      <div class="brand">
        {% if cot_logo_src %}
          <img src="{{ cot_logo_src }}" alt="City of Toronto">
        {% endif %}
        <div class="titleWrap">
          <h2>Live Work Orders Map</h2>
          <div class="sub">Internal operations tool</div>
        </div>
      </div>
    </div>
    <div class="stats">
      <div class="stat"><div class="k">Status</div><div class="v">{{ status }}</div></div>
      <div class="stat"><div class="k">Last build</div><div class="v">{{ last_build }}</div></div>
      <div class="stat"><div class="k">Master / Drawn / Skipped</div><div class="v">{{ master_rows }} / {{ drawn }} / {{ skipped }}</div></div>
    </div>

    <p>
      Open map:
      <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">work_orders_map.html</a>
    </p>
    <p>
      <a class="btn" href="/new">+ Add a New Work Order </a>
    </p>
    <p class="muted">
      Download:
      <a href="/outputs/work_orders.geojson" target="_blank" rel="noopener noreferrer">work_orders.geojson</a>
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
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">
  <style>
    :root{
      --bg:#f5f7fb;
      --card:#ffffff;
      --stroke:#e5e7eb;
      --text:#111827;
      --muted:#6b7280;
      --brand:#005aa3;
      --brand2:#0ea5e9;
      --danger:#dc2626;
      --shadow: 0 18px 45px rgba(16,24,40,0.10);
      --radius: 18px;
    }
    *{ box-sizing:border-box; }
    html,body{ height:100%; }
    body{
      margin:0;
      font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
      color: var(--text);
      background:
        radial-gradient(900px 450px at 10% 0%, rgba(14,165,233,0.15), transparent 55%),
        radial-gradient(900px 450px at 90% 0%, rgba(0,90,163,0.10), transparent 55%),
        linear-gradient(180deg, #ffffff, var(--bg));
      padding: 22px 16px;
      -webkit-font-smoothing: antialiased;
      -moz-osx-font-smoothing: grayscale;
    }

    .card{
      max-width: 1200px;
      margin: 0 auto 14px auto;
      border: 1px solid var(--stroke);
      background: var(--card);
      border-radius: var(--radius);
      padding: 16px 16px;
      box-shadow: var(--shadow);
    }

    h2{ margin:0 0 6px 0; font-size: 20px; font-weight: 950; letter-spacing:-0.02em; }
    .help{ color: var(--muted); font-size: 13px; margin-top: 6px; font-weight: 650; }

    a{ color: var(--brand); text-decoration:none; font-weight: 850; }
    a:hover{ text-decoration: underline; }

    .pill{
      display:inline-flex;
      align-items:center;
      gap:8px;
      padding: 6px 10px;
      border-radius: 999px;
      border: 1px solid rgba(0,90,163,0.22);
      background: rgba(0,90,163,0.08);
      color: #0b2b4a;
      font-size: 12px;
      font-weight: 900;
    }

    .err{
      background: rgba(220,38,38,0.08);
      border: 1px solid rgba(220,38,38,0.22);
      padding: 12px;
      border-radius: 14px;
      color: #7f1d1d;
      font-weight: 750;
      overflow-wrap: anywhere;
    }
    .ok{
      background: rgba(14,165,233,0.06);
      border: 1px solid rgba(14,165,233,0.18);
      padding: 12px;
      border-radius: 14px;
      color: #0b2b4a;
      font-weight: 750;
      overflow: hidden;            /* fixes “not fitting inside borders” */
      overflow-wrap: anywhere;     /* prevents long text overflow */
    }

    button{
      padding: 11px 13px;
      border-radius: 14px;
      border: 1px solid rgba(0,90,163,0.20);
      background: linear-gradient(135deg, var(--brand), var(--brand2));
      color:#fff;
      font-weight: 950;
      cursor:pointer;
      box-shadow: 0 14px 34px rgba(0,90,163,0.18);
      transition: transform .12s ease, filter .12s ease;
      user-select:none;
    }
    button:hover{ transform: translateY(-1px); filter: brightness(1.03); }
    button:active{ transform: translateY(0px) scale(.99); }
    .ghost{
      background:#f3f4f6;
      border: 1px solid #e5e7eb;
      color:#111827;
      box-shadow:none;
    }

    /* Inputs */
    input, select, textarea{
      width: 100%;
      padding: 10px 11px;
      border-radius: 12px;
      border: 1px solid #d1d5db;
      background: #ffffff;
      color: #111827;
      font-size: 14px;
      font-weight: 650;
      outline: none;
      transition: border-color .12s ease, box-shadow .12s ease;
      min-width: 0;
    }
    textarea{
      min-height: 110px; /* bigger comments box */
      resize: vertical;
      line-height: 1.3;
    }
    input:focus, select:focus, textarea:focus{
      border-color: rgba(0,90,163,0.45);
      box-shadow: 0 0 0 4px rgba(14,165,233,0.16);
    }
    select, option{ color:#111827; background:#ffffff; } /* fixes “selected option not showing” */

    /* ===== Timer styling ===== */
    #pendingTimerBox{
      border: 1px solid var(--stroke) !important;
      background: #f9fafb !important;
      border-radius: 16px !important;
    }
    #pendingTimer{
      font-variant-numeric: tabular-nums;
      font-weight: 950;
      color: #6b7280;  /* grey until last 10 seconds */
    }
    #pendingTimer.timerWarn,
    #pendingTimer.timerFinal{
      color: var(--danger); /* red in last 10 seconds */
    }
    .timerWarn{
      animation: pulseWarn 0.9s infinite;
    }
    .timerFinal{
      animation: pulseWarn 0.35s infinite, shakeWarn 0.35s infinite;
    }
    @keyframes pulseWarn{ 0%{transform:scale(1)} 50%{transform:scale(1.03)} 100%{transform:scale(1)} }
    @keyframes shakeWarn{ 0%{transform:translateX(0)} 25%{transform:translateX(-2px)} 50%{transform:translateX(2px)} 75%{transform:translateX(-2px)} 100%{transform:translateX(0)} }

    /* ===== Submitted "batch" table (the top table) — make it wrap and fit ===== */
    table:not(#woTable){
        width: 100%;
        border-collapse: separate;
        border-spacing: 0;
        margin-top: 10px;
        background: #ffffff;
        border: 1px solid var(--stroke);
        border-radius: 16px;
        overflow: hidden;
    }
    table:not(#woTable) thead{ display:none; } /* avoids horizontal scroll */
    table:not(#woTable) tbody tr{
        display:grid;
        grid-template-columns: repeat(4, minmax(0, 1fr));
        gap: 10px 12px;
        padding: 12px;
        border-bottom: 1px solid var(--stroke);
    }
    table:not(#woTable) tbody tr:last-child{ border-bottom:none; }
    table:not(#woTable) tbody td{
        border:none;
        padding:0;
        display:flex;
        flex-direction:column;
        gap: 6px;
        min-width: 0;
    }
    table:not(#woTable) tbody td::before{
        font-size: 11px;
        color: var(--muted);
        font-weight: 900;
        letter-spacing: .04em;
        text-transform: uppercase;
        content: "";
    }
    /* ✅ COMPLETE LABELS - matches 32-column table structure */
    table:not(#woTable) tbody td:nth-child(1)::before{ content:"WO"; }
    table:not(#woTable) tbody td:nth-child(2)::before{ content:"Date"; }
    table:not(#woTable) tbody td:nth-child(3)::before{ content:"District"; }
    table:not(#woTable) tbody td:nth-child(4)::before{ content:"Ward"; }
    table:not(#woTable) tbody td:nth-child(5)::before{ content:"TOA Area"; }
    table:not(#woTable) tbody td:nth-child(6)::before{ content:"Supervisor(s)"; }
    table:not(#woTable) tbody td:nth-child(7)::before{ content:"Shift"; }
    table:not(#woTable) tbody td:nth-child(8)::before{ content:"Street"; }
    table:not(#woTable) tbody td:nth-child(9)::before{ content:"From"; }
    table:not(#woTable) tbody td:nth-child(10)::before{ content:"To"; }
    table:not(#woTable) tbody td:nth-child(11)::before{ content:"Side Cleared"; }
    table:not(#woTable) tbody td:nth-child(12)::before{ content:"Road Side"; }
    table:not(#woTable) tbody td:nth-child(13)::before{ content:"Roadway"; }
    table:not(#woTable) tbody td:nth-child(14)::before{ content:"Sidewalk"; }
    table:not(#woTable) tbody td:nth-child(15)::before{ content:"Cycling"; }
    table:not(#woTable) tbody td:nth-child(16)::before{ content:"Bridge"; }
    table:not(#woTable) tbody td:nth-child(17)::before{ content:"School Zones"; }
    table:not(#woTable) tbody td:nth-child(18)::before{ content:"Layby Parking"; }
    table:not(#woTable) tbody td:nth-child(19)::before{ content:"Equipment"; }
    table:not(#woTable) tbody td:nth-child(20)::before{ content:"Dump Trucks"; }
    table:not(#woTable) tbody td:nth-child(21)::before{ content:"Source"; }
    table:not(#woTable) tbody td:nth-child(22)::before{ content:"Contractor TOA"; }
    table:not(#woTable) tbody td:nth-child(23)::before{ content:"Snow Dump Site"; }
    table:not(#woTable) tbody td:nth-child(24)::before{ content:"Loads"; }
    table:not(#woTable) tbody td:nth-child(25)::before{ content:"Tonnes"; }
    table:not(#woTable) tbody td:nth-child(26)::before{ content:"Crew Type"; }
    table:not(#woTable) tbody td:nth-child(27)::before{ content:"# Crews"; }
    table:not(#woTable) tbody td:nth-child(28)::before{ content:"Crew Number"; }
    table:not(#woTable) tbody td:nth-child(29)::before{ content:"In-House Base"; }
    table:not(#woTable) tbody td:nth-child(30)::before{ content:"# Staff"; }
    table:not(#woTable) tbody td:nth-child(31)::before{ content:"Notes"; }
    table:not(#woTable) tbody td:nth-child(32)::before{ content:"Status"; }
    table:not(#woTable) tbody td:nth-child(33)::before{ content:"Edit"; }

    /* ✅ Make long text fields span full width */
    table:not(#woTable) tbody td:nth-child(8),   /* Street */
    table:not(#woTable) tbody td:nth-child(9),   /* From */
    table:not(#woTable) tbody td:nth-child(10),  /* To */
    table:not(#woTable) tbody td:nth-child(31){  /* Notes */
    grid-column: 1 / -1;
    }

    /* ===== Entry table (woTable) — convert to responsive grid cards, no horizontal scroll ===== */
    #woTable{
      width: 100%;
      border: none;
      border-radius: 0;
      background: transparent;
      margin-top: 10px;
    }
    #woTable thead{ display:none; } /* remove wide header */
    #woTable th[style]{ width:auto !important; } /* ignore inline width styles */

    #woTable tbody tr{
      display:grid;
      grid-template-columns: repeat(6, minmax(0, 1fr));
      gap: 10px 12px;
      padding: 12px;
      margin: 10px 0;
      border: 1px solid var(--stroke);
      border-radius: 16px;
      background: #ffffff;
      box-shadow: 0 10px 26px rgba(16,24,40,0.06);
    }
    #woTable tbody td{
      border:none;
      padding:0;
      display:flex;
      flex-direction:column;
      gap: 6px;
      min-width: 0;
    }
    #woTable tbody td::before{
      font-size: 11px;
      color: var(--muted);
      font-weight: 900;
      letter-spacing: .04em;
      text-transform: uppercase;
      content: "";
    }

    /* Labels by column (MUST match addRow() order below) */
    #woTable tbody td:nth-child(1)::before{ content:"Work Order Number"; }
    #woTable tbody td:nth-child(2)::before{ content:"District (Where Snow Removed)"; }
    #woTable tbody td:nth-child(3)::before{ content:"Ward (Where Snow Removed)"; }
    #woTable tbody td:nth-child(4)::before{ content:"TOA Area (Where Snow Removed)"; }
    #woTable tbody td:nth-child(5)::before{ content:"Street"; }
    #woTable tbody td:nth-child(6)::before{ content:"From Intersection"; }
    #woTable tbody td:nth-child(7)::before{ content:"To Intersection"; }
    #woTable tbody td:nth-child(8)::before{ content:"One Side / Both Sides Cleared?"; }
    #woTable tbody td:nth-child(9)::before{ content:"Side of Road Cleared"; }
    #woTable tbody td:nth-child(10)::before{ content:"Roadway"; }
    #woTable tbody td:nth-child(11)::before{ content:"Sidewalk"; }
    #woTable tbody td:nth-child(12)::before{ content:"Separated Cycling Infrastructure"; }
    #woTable tbody td:nth-child(13)::before{ content:"Bridge"; }
    #woTable tbody td:nth-child(14)::before{ content:"School Loading Zones"; }
    #woTable tbody td:nth-child(15)::before{ content:"Layby Parking"; }
    #woTable tbody td:nth-child(16)::before{ content:"Equipment Method"; }
    #woTable tbody td:nth-child(17)::before{ content:"# of Equipment (Dump Trucks)"; }
    #woTable tbody td:nth-child(18)::before{ content:"Dump Truck Source (In-House/Contractor)"; }
    #woTable tbody td:nth-child(19)::before{ content:"Snow Dump Site"; }
    #woTable tbody td:nth-child(20)::before{ content:"# of Loads"; }
    #woTable tbody td:nth-child(21)::before{ content:"Tonnes"; }
    #woTable tbody td:nth-child(22)::before{ content:"Shift Start Date"; }
    #woTable tbody td:nth-child(23)::before{ content:"Shift Start Time"; }
    #woTable tbody td:nth-child(24)::before{ content:"Shift End Date"; }
    #woTable tbody td:nth-child(25)::before{ content:"Shift End Time"; }
    #woTable tbody td:nth-child(26)::before{ content:"Supervisor 1"; }
    #woTable tbody td:nth-child(27)::before{ content:"Supervisor 2 (if relevant)"; }
    #woTable tbody td:nth-child(28)::before{ content:"Supervisor 3 (if relevant)"; }
    #woTable tbody td:nth-child(29)::before{ content:"Snow Removal by Contracted Crew or In-House?"; }
    #woTable tbody td:nth-child(30)::before{ content:"Contractor: # of Crews"; }
    #woTable tbody td:nth-child(31)::before{ content:"Contractor: Crew TOA Area Responsibility"; }
    #woTable tbody td:nth-child(32)::before{ content:"Contractor: Crew Number"; }
    #woTable tbody td:nth-child(33)::before{ content:"In-House: Staff Responsibility (Base Yard)"; }
    #woTable tbody td:nth-child(34)::before{ content:"In-House: # of Staff"; }
    #woTable tbody td:nth-child(35)::before{ content:"NOTES"; }
    #woTable tbody td:nth-child(36)::before{ content:"Remove"; }

    /* Spans / sizing (optional but recommended) */
    #woTable tbody td:nth-child(1){ grid-column: span 2; }      /* WO bigger */
    #woTable tbody td:nth-child(5){ grid-column: span 2; }      /* Street bigger */
    #woTable tbody td:nth-child(16){ grid-column: span 2; }     /* Equipment Method bigger */
    #woTable tbody td:nth-child(31){ grid-column: span 2; }     /* Crew responsibility bigger */
    #woTable tbody td:nth-child(35){ grid-column: 1 / -1; }     /* NOTES full width */

    #woTable tbody td:nth-child(5),
    #woTable tbody td:nth-child(6),
    #woTable tbody td:nth-child(7){
    grid-column: span 2; /* Street + From/To bigger */
    }


    /* Make dump trucks feel “small”, loads readable */
    #woTable tbody td:nth-child(8) input{ text-align:right; }
    #woTable tbody td:nth-child(10) input{ text-align:right; } /* Loads */
    #woTable tbody td:nth-child(11) input{ text-align:right; } /* Tonnes */

    /* Make WO field monospaced-ish readability */
    #woTable tbody td:nth-child(1) input{
      font-variant-numeric: tabular-nums;
      font-weight: 850;
    }

    /* Remove button */
    .rmBtn{
      width: 100%;
      border-radius: 14px;
      padding: 11px 12px;
      border: 1px solid rgba(220,38,38,0.25);
      background: rgba(220,38,38,0.06);
      color: #7f1d1d;
      font-weight: 950;
      cursor:pointer;
    }
    .rmBtn:hover{ background: rgba(220,38,38,0.10); }

    /* Ensure crosslist host stays hidden */
    #crossLists{ display:none; }

    /* Responsive grid */
    @media (max-width: 1100px){
      #woTable tbody tr{ grid-template-columns: repeat(3, minmax(0, 1fr)); }
      #woTable tbody td:nth-child(15){ grid-column: 1 / -1; }
    }
    @media (max-width: 720px){
      #woTable tbody tr{ grid-template-columns: repeat(2, minmax(0, 1fr)); }
      #woTable tbody td:nth-child(15),
      #woTable tbody td:nth-child(16),
      #woTable tbody td:nth-child(17),
      #woTable tbody td:nth-child(18){ grid-column: 1 / -1; }
    }
    .statusPill{
      display:inline-flex;
      align-items:center;
      padding:6px 10px;
      border-radius:999px;
      font-weight:900;
      font-size:12px;
      border:1px solid rgba(0,0,0,0.10);
      background:#fff;
    }
    .statusPending{
      background: rgba(245, 158, 11, 0.14);
      border-color: rgba(245, 158, 11, 0.35);
      color:#92400e;
    }
    .statusApplied{
      background: rgba(16, 185, 129, 0.14);
      border-color: rgba(16, 185, 129, 0.35);
      color:#065f46;
    }
    /* Force button colors (overrides inline styles if needed) */
    #extendBtn{
      background:#6b7280 !important;
      color:#fff !important;
      border-color: rgba(0,0,0,0.10) !important;
    }
    #dismissSubmitted{
      background:#dc2626 !important;
      color:#fff !important;
      border-color: rgba(220,38,38,0.30) !important;
    }
    
    /* Mac-style close glyph alignment */
    #dismissSubmitted .closeGlyph{
      display:block;
      line-height:1;
      font-size:18px;
      transform: translateY(-1px); /* tiny optical centering */
      user-select:none;
    }
    /* Shift time range inputs */
    .timeRange {
      display: flex;
      align-items: center;
      gap: 6px;
      white-space: nowrap;
    }
    .timeRange input[type="time"]{
      width: 160px;
      padding: 8px 10px;
      border-radius: 10px;
      border: 1px solid #ccc;
      font-size: 13px;
      background: #fff;
    }
    .timeRange .dash{
      font-weight: 900;
      color: #666;
    }


  </style>

</head>
<body>
  <div class="card">
    <div style="display:flex;align-items:center;gap:12px;">
      {% if cot_logo_src %}
      <img src="{{ cot_logo_src }}" alt="City of Toronto"
           style="height:38px;width:auto;object-fit:contain;display:block;" />
      {% endif %}
      <div style="flex:1;">
        <h2 style="margin:0 0 6px 0;">Add Work Orders (Batch)</h2>
        <p class="help" style="margin:0;">
          <a href="/">← Back</a> |
          <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">Open Map</a>
        </p>
        <div class="help" style="margin-top:8px;">
          Tip: Add multiple rows and submit once. You can edit any <b>PENDING</b> row instantly before it gets applied.
        </div>
      </div>
    </div>
  </div>

  {% if batch and batch_id %}
  <div class="card ok" id="submittedPanel">
    <div style="display:flex;align-items:center;justify-content:space-between;gap:10px;">
        <div id="pendingTimerBox" style="margin-top:12px;padding:12px;border-radius:12px;border:1px solid rgba(0,0,0,0.10);background:rgba(255,255,255,0.85);">
      <div style="font-weight:900;font-size:14px;">
        Editing window:
        <span id="pendingTimer" style="font-size:18px;">--:--</span>
        <button type="button" id="extendBtn"
                style="margin-left:10px;display:none;padding:6px 10px;border-radius:999px;border:1px solid rgba(0,0,0,0.10);background:#6b7280;color:#fff;font-weight:900;font-size:12px;cursor:pointer;">
          Extend
        </button>
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
      <div style="display:flex;flex-direction:column;align-items:flex-end;gap:8px;">
        <button type="button" id="dismissSubmitted" title="Dismiss"
                style="width:32px;height:32px;border-radius:999px;border:1px solid rgba(220,38,38,0.30);background:#dc2626;color:#fff;cursor:pointer;font-weight:900;padding:0;display:inline-flex;align-items:center;justify-content:center;">
          <span class="closeGlyph">×</span>
        </button>
        <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer"
           style="display:inline-block;padding:10px 12px;border-radius:12px;background:#111;color:#fff;text-decoration:none;font-weight:900;">
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
        <th>Work Order Number</th>
        <th>Date</th>
        <th>District</th>
        <th>Ward</th>
        <th>TOA Area</th>
        <th>Supervisor(s)</th>
        <th>Shift</th>
        <th>Street</th>
        <th>From Intersection</th>
        <th>To Intersection</th>
        <th>Side Cleared</th>
        <th>Road Side</th>
        <th>Roadway</th>
        <th>Sidewalk</th>
        <th>Cycling</th>
        <th>Bridge</th>
        <th>School Zones</th>
        <th>Layby Parking</th>
        <th>Equipment Method</th>
        <th>Dump Trucks</th>
        <th>Dump Truck Source</th>
        <th>Contractor TOA</th>
        <th>Snow Dump Site</th>
        <th>Loads</th>
        <th>Tonnes</th>
        <th>Snow Removal by...</th>
        <th># Crews</th>
        <th>Crew Number</th>
        <th>In-House Base</th>
        <th># Staff</th>
        <th>Notes</th>
        <th>Status</th>
        <th>Edit</th>
        </tr>
    </thead>
    <tbody>
    {% for r in batch %}
        <tr>
        <td>{{ r.get('Work Order Number','') }}</td>
        <td>{{ r.get('Shift Start Date','') }}</td>
        <td>{{ r.get('District (Where Snow Removed)','') }}</td>
        <td>{{ r.get('Ward (Where Snow Removed)','') }}</td>
        <td>{{ r.get('TOA Area (Where Snow Removed)','') }}</td>
        <td>{{ r.get('Supervisor 1','') }}{% if r.get('Supervisor 2 (if relevant)','') %}<br>{{ r.get('Supervisor 2 (if relevant)','') }}{% endif %}{% if r.get('Supervisor 3 (if relevant)','') %}<br>{{ r.get('Supervisor 3 (if relevant)','') }}{% endif %}</td>
        <td>{{ r.get('Shift Start Date','') }} {{ r.get('Shift Start Time','') }}<br>{{ r.get('Shift End Date','') }} {{ r.get('Shift End Time','') }}</td>
        <td>{{ r.get('Street','') }}</td>
        <td>{{ r.get('From Intersection','') }}</td>
        <td>{{ r.get('To Intersection','') }}</td>
        <td>{{ r.get('One Side / Both Sides Cleared?','') }}</td>
        <td>{{ r.get('Side of Road Cleared','') }}</td>
        <td>{{ r.get('Roadway','') }}</td>
        <td>{{ r.get('Sidewalk','') }}</td>
        <td>{{ r.get('Separated Cycling Infrastructure','') }}</td>
        <td>{{ r.get('Bridge','') }}</td>
        <td>{{ r.get('School Loading Zones','') }}</td>
        <td>{{ r.get('Layby Parking','') }}</td>
        <td>{{ r.get('Equipment Method','') }}</td>
        <td>{{ r.get('# of Equipment (Dump Trucks)','') }}</td>
        <td>{{ r.get('Dump Truck Source (In-House/Contractor)','') }}</td>
        <td>{{ r.get('Contractor: Crew TOA Area Responsibility','') }}</td>
        <td>{{ r.get('Snow Dump Site','') }}</td>
        <td>{{ r.get('# of Loads','') }}</td>
        <td>{{ r.get('Tonnes','') }}</td>
        <td>{{ r.get('Snow Removal by Contracted Crew or In-House?','') }}</td>
        <td>{{ r.get('Contractor: # of Crews','') }}</td>
        <td>{{ r.get('Contractor: Crew Number','') }}</td>
        <td>{{ r.get('In-House: Staff Responsibility (Base Yard)','') }}</td>
        <td>{{ r.get('In-House: # of Staff','') }}</td>
        <td style="max-width:220px;">{{ r.get('NOTES','') }}</td>
        <td>
            {% set st = (r.get('__status','')|string)|upper %}
            <span class="statusPill {{ 'statusApplied' if st=='APPLIED' else 'statusPending' }}"
                    data-sid="{{ r.get('__submission_id','') }}">
                {{ st if st else '—' }}
            </span>
        </td>
        <td>
            {% if (r.get('__status','')|upper) == 'PENDING' %}
            <a href="/edit/{{ r.get('__submission_id','') }}?bid={{ batch_id }}">Edit</a>
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
            <th>Work Order Number</th>
            <th>Shift Start Date</th>
            <th>District (Where Snow Removed)</th>
            <th>Ward (Where Snow Removed)</th>
            <th>TOA Area (Where Snow Removed)</th>
            <th>Supervisor 1</th>
            <th>Shift Start Time - Shift End Time</th>
            <th>Equipment Method</th>
            <th># of Equipment (Dump Trucks)</th>
            <th>Contractor: Crew TOA Area Responsibility</th>
            <th># of Loads</th>
            <th>Tonnes</th>
            <th>One Side / Both Sides Cleared?</th>
            <th>Side of Road Cleared</th>
            <th>Snow Dump Site</th>
            <th>NOTES</th>
            <th>Street</th>
            <th>Street/From Intersection</th>
            <th>Street/To Intersection</th>
            <th>Status</th>
            <th>Edit</th>
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

<div id="crossLists" style="display:none;"></div>

<script>
(function(){
  var districts = {{ districts_json | safe }};
  var supervisors = {{ supervisors_json | safe }};
  var districtToWards = {{ district_to_wards_json | safe }};
  var shifts = {{ shifts_json | safe }};
  var types = {{ types_json | safe }};
  var dumpTruckProvidersOptions = {{ dump_truck_providers_html | tojson | safe }};
  var snowDumpSitesOptions = {{ snow_dump_sites_html | tojson | safe }};
  var STREET_ENDPOINTS = {{ street_endpoints_json | safe }};


  var tbody = document.getElementById('woTbody');
  var addBtn = document.getElementById('addRowBtn');
  var crossListsHost = document.getElementById('crossLists');

  function populateDatalist(dl, arr, excludeVal){
    if (!dl) return;
    var ex = (excludeVal || '').toString().trim().toUpperCase();
    dl.innerHTML = '';
    (arr || []).forEach(function(s){
      var v = (s || '').toString();
      if (!v) return;
      if (ex && v.toUpperCase() === ex) return;
      var opt = document.createElement('option');
      opt.value = v;
      dl.appendChild(opt);
    });
  }

  function endpointsForStreet(streetVal){
    var k = (streetVal || '').toString().trim().toUpperCase();
    if (!k) return [];
    if (STREET_ENDPOINTS && STREET_ENDPOINTS[k]) return STREET_ENDPOINTS[k];
    return [];
  }

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

  function shiftTimeHtml(nameCombined, nameStart, nameEnd){
    return ''
      + '<div class="timeRange">'
      +   '<input type="time" class="tStart" name="' + nameStart + '" required>'
      +   '<span class="dash">-</span>'
      +   '<input type="time" class="tEnd" name="' + nameEnd + '" required>'
      +   '<input type="hidden" class="shiftCombined" name="' + nameCombined + '">'
      + '</div>';
  }

  function fmt12FromTimeInput(v){
    // v = "HH:MM" (24h)
    if(!v) return '';
    var parts = v.split(':');
    if(parts.length < 2) return '';
    var hh = parseInt(parts[0], 10);
    var mm = parts[1];
    if(isNaN(hh)) return '';
    var ap = (hh >= 12) ? 'PM' : 'AM';
    var h12 = hh % 12;
    if(h12 === 0) h12 = 12;
    return String(h12).padStart(2,'0') + ':' + mm + ap;
  }


  function simpleSelectHtml(name, arr){
    var o = '<option value="">--</option>';
    (arr || []).forEach(function(x){
        o += '<option value="' + escapeHtml(x) + '">' + escapeHtml(x) + '</option>';
    });
    return '<select name="' + name + '">' + o + '</select>';
  }

  function yesNoSelectHtml(name){
    return simpleSelectHtml(name, ['Yes','No']);
  }

  function toaSelectHtml(name){
    var toaAreas = ['TOA 1-1', 'TOA 1-2', 'TOA 1-3', 'TOA 1-4', 'TOA 1-5',
                    'TOA 2-1', 'TOA 2-2', 'TOA 2-3', 'TOA 2-4', 'TOA 2-5',
                    'DVP-FGGE'];
    var o = '<option value="">--</option>';
    toaAreas.forEach(function(t){
        o += '<option value="' + escapeHtml(t) + '">' + escapeHtml(t) + '</option>';
    });
    return '<select name="' + name + '">' + o + '</select>';
  }

  function typeSelectHtml(name){
    var o = '<option value="">--</option>';
    (types || []).forEach(function(t){
        o += '<option value="' + escapeHtml(t) + '">' + escapeHtml(t) + '</option>';
    });
    return '<select name="' + name + '" required>' + o + '</select>';
  }



  function addRow(prefill){
    prefill = prefill || {};
    var idx = tbody.children.length;
    var tr = document.createElement('tr');

    tr.innerHTML = ''
        + '<td><input name="Work Order Number_' + idx + '" required placeholder="12345" value="' + escapeHtml(prefill["Work Order Number"] || "") + '"></td>'

        + '<td>' + districtSelectHtml('District (Where Snow Removed)_' + idx) + '</td>'
        + '<td>' + wardSelectHtml('Ward (Where Snow Removed)_' + idx) + '</td>'

        + '<td>' + toaSelectHtml('TOA Area (Where Snow Removed)_' + idx) + '</td>'

        + '<td><input class="streetIn" name="Street_' + idx + '" list="streets" required placeholder="Street" value="' + escapeHtml(prefill["Street"] || "") + '"></td>'
        + '<td><input class="fromIn" name="From Intersection_' + idx + '" placeholder="From Intersection" value="' + escapeHtml(prefill["From Intersection"] || "") + '"></td>'
        + '<td><input class="toIn" name="To Intersection_' + idx + '" placeholder="To Intersection" value="' + escapeHtml(prefill["To Intersection"] || "") + '"></td>'

        + '<td>' + simpleSelectHtml('One Side / Both Sides Cleared?_' + idx, ['Both Sides','One Side']) + '</td>'
        + '<td>' + simpleSelectHtml('Side of Road Cleared_' + idx, ['North','South','East','West','East/West','North/South']) + '</td>'

        + '<td>' + yesNoSelectHtml('Roadway_' + idx) + '</td>'
        + '<td>' + yesNoSelectHtml('Sidewalk_' + idx) + '</td>'
        + '<td>' + yesNoSelectHtml('Separated Cycling Infrastructure_' + idx) + '</td>'
        + '<td>' + yesNoSelectHtml('Bridge_' + idx) + '</td>'
        + '<td>' + yesNoSelectHtml('School Loading Zones_' + idx) + '</td>'
        + '<td>' + yesNoSelectHtml('Layby Parking_' + idx) + '</td>'

        + '<td>' + typeSelectHtml('Equipment Method_' + idx) + '</td>'

        + '<td><input name="# of Equipment (Dump Trucks)_' + idx + '" type="number" min="0" value="' + escapeHtml(prefill["# of Equipment (Dump Trucks)"] || "") + '"></td>'

        + '<td>' + simpleSelectHtml('Dump Truck Source (In-House/Contractor)_' + idx, ['In-House','Contractor']) + '</td>'

        + '<td><select name="Snow Dump Site_' + idx + '">'
        +   '<option value="">--</option>'
        +   snowDumpSitesOptions
        + '</select></td>'

        + '<td><input name="# of Loads_' + idx + '" type="number" min="0" value="' + escapeHtml(prefill["# of Loads"] || "") + '"></td>'
        + '<td><input name="Tonnes_' + idx + '" type="number" step="0.01" min="0" value="' + escapeHtml(prefill["Tonnes"] || "") + '"></td>'

        + '<td><input type="date" name="Shift Start Date_' + idx + '" required value="' + escapeHtml(prefill["Shift Start Date"] || "") + '"></td>'
        + '<td><input type="time" name="Shift Start Time_' + idx + '" required value="' + escapeHtml(prefill["Shift Start Time"] || "") + '"></td>'
        + '<td><input type="date" name="Shift End Date_' + idx + '" value="' + escapeHtml(prefill["Shift End Date"] || "") + '"></td>'
        + '<td><input type="time" name="Shift End Time_' + idx + '" required value="' + escapeHtml(prefill["Shift End Time"] || "") + '"></td>'

        + '<td><select class="sup1" name="Supervisor 1_' + idx + '" required><option value="">-- Select Supervisor 1 --</option>' + optList(supervisors) + '</select></td>'
        + '<td><select class="sup2" name="Supervisor 2 (if relevant)_' + idx + '"><option value="">-- Select Supervisor 2 --</option></select></td>'
        + '<td><select class="sup3" name="Supervisor 3 (if relevant)_' + idx + '"><option value="">-- Select Supervisor 3 --</option></select></td>'

        + '<td>' + simpleSelectHtml('Snow Removal by Contracted Crew or In-House?_' + idx, ['Contracted Crew','In-House']) + '</td>'

        + '<td><input name="Contractor: # of Crews_' + idx + '" type="number" min="0" placeholder="e.g. 2" value="' + escapeHtml(prefill["Contractor: # of Crews"] || "") + '"></td>'

        + '<td><select name="Contractor: Crew TOA Area Responsibility_' + idx + '">'
        +   '<option value="">--</option>'
        +   dumpTruckProvidersOptions
        + '</select></td>'

        + '<td><input name="Contractor: Crew Number_' + idx + '" placeholder="Crew #" value="' + escapeHtml(prefill["Contractor: Crew Number"] || "") + '"></td>'

        + '<td><input name="In-House: Staff Responsibility (Base Yard)_' + idx + '" placeholder="Base Yard" value="' + escapeHtml(prefill["In-House: Staff Responsibility (Base Yard)"] || "") + '"></td>'
        + '<td><input name="In-House: # of Staff_' + idx + '" type="number" min="0" value="' + escapeHtml(prefill["In-House: # of Staff"] || "") + '"></td>'

        + '<td><textarea name="NOTES_' + idx + '" rows="2" placeholder="Notes / comments (optional)">' + escapeHtml(prefill["NOTES"] || "") + '</textarea></td>'

        + '<td><button type="button" class="ghost rmBtn">Remove</button></td>';

    tbody.appendChild(tr);

    // ✅ Set prefill values for select dropdowns
    if (prefill) {
        // Yes/No fields
        var yesNoFields = ['Roadway', 'Sidewalk', 'Separated Cycling Infrastructure', 'Bridge', 'School Loading Zones', 'Layby Parking'];
        yesNoFields.forEach(function(field){
            var val = prefill[field];
            if (val) {
                var sel = tr.querySelector('select[name="' + field + '_' + idx + '"]');
                if (sel) sel.value = String(val);
            }
        });
        
        // Equipment Method
        if (prefill["Equipment Method"]) {
            var typeSel = tr.querySelector('select[name="Equipment Method_' + idx + '"]');
            if (typeSel) typeSel.value = String(prefill["Equipment Method"]);
        }
        
        // Other select fields
        var selectFields = [
            'One Side / Both Sides Cleared?',
            'Side of Road Cleared',
            'Dump Truck Source (In-House/Contractor)',
            'Snow Removal by Contracted Crew or In-House?'
        ];
        selectFields.forEach(function(field){
            var val = prefill[field];
            if (val) {
                var sel = tr.querySelector('select[name="' + field + '_' + idx + '"]');
                if (sel) sel.value = String(val);
            }
        });
        
        // Snow Dump Site
        if (prefill["Snow Dump Site"]) {
            var snowSel = tr.querySelector('select[name="Snow Dump Site_' + idx + '"]');
            if (snowSel) snowSel.value = String(prefill["Snow Dump Site"]);
        }
        
        // Contractor TOA
        if (prefill["Contractor: Crew TOA Area Responsibility"]) {
            var crewSel = tr.querySelector('select[name="Contractor: Crew TOA Area Responsibility_' + idx + '"]');
            if (crewSel) crewSel.value = String(prefill["Contractor: Crew TOA Area Responsibility"]);
        }
    }

    // ✅ Remove row
    tr.querySelector('.rmBtn').onclick = function(){
        tr.remove();
    };

    // ✅ District → Ward dependency
    var dsel = tr.querySelector('.districtSel');
    var wsel = tr.querySelector('.wardSel');

    function setWards(d){
        var dd = (d||'').toString().trim().toUpperCase();
        var wards = (districtToWards && districtToWards[dd]) ? districtToWards[dd] : [];
        wsel.innerHTML = '<option value="">--</option>';
        wards.forEach(function(w){
        var opt = document.createElement('option');
        opt.value = w; opt.textContent = w;
        wsel.appendChild(opt);
        });
    }
    dsel.addEventListener('change', function(){ setWards(dsel.value); });
    
    // Set prefilled district/ward/TOA values
    if (prefill["District (Where Snow Removed)"]) {
        dsel.value = prefill["District (Where Snow Removed)"];
        setWards(dsel.value);
        if (prefill["Ward (Where Snow Removed)"]) {
            wsel.value = prefill["Ward (Where Snow Removed)"];
        }
    }
    var toaSel = tr.querySelector('.toaSel');
    if (toaSel && prefill["TOA Area (Where Snow Removed)"]) {
        toaSel.value = prefill["TOA Area (Where Snow Removed)"];
    }

    // ✅ Street → cross streets
    var streetIn = tr.querySelector('.streetIn');
    var toIn = tr.querySelector('.toIn');
    var fromIn = tr.querySelector('.fromIn');

    var dlTo = document.createElement('datalist');
    dlTo.id = 'cross_to_' + idx;
    crossListsHost.appendChild(dlTo);
    toIn.setAttribute('list', dlTo.id);

    var dlFrom = document.createElement('datalist');
    dlFrom.id = 'cross_from_' + idx;
    crossListsHost.appendChild(dlFrom);
    fromIn.setAttribute('list', dlFrom.id);

    var cachedCross = [];

    function refreshCrossLists(){
        cachedCross = endpointsForStreet(streetIn.value);
        populateDatalist(dlTo, cachedCross, fromIn.value);
        populateDatalist(dlFrom, cachedCross, toIn.value);
    }

    streetIn.addEventListener('change', refreshCrossLists);
    streetIn.addEventListener('blur', refreshCrossLists);

    toIn.addEventListener('change', function(){
        populateDatalist(dlFrom, cachedCross, toIn.value);
    });
    fromIn.addEventListener('change', function(){
        populateDatalist(dlTo, cachedCross, fromIn.value);
    });

    // ✅ Supervisor deduplication for SELECT dropdowns
    var sup1 = tr.querySelector('.sup1');
    var sup2 = tr.querySelector('.sup2');
    var sup3 = tr.querySelector('.sup3');

    function refreshSupervisorLists(){
        var sup1Val = (sup1.value || '').trim();
        var sup2Val = (sup2.value || '').trim();
        var sup3Val = (sup3.value || '').trim();
        
        // Supervisor 2: exclude Supervisor 1
        var sup2Options = supervisors.filter(function(s){ return s !== sup1Val; });
        sup2.innerHTML = '<option value="">-- Select Supervisor 2 --</option>' + optList(sup2Options);
        if (sup2Val && sup2Options.includes(sup2Val)) {
            sup2.value = sup2Val;
        }
        
        // Supervisor 3: exclude both Supervisor 1 and 2
        var excluded = [sup1Val, sup2Val].filter(function(v){ return v; });
        var sup3Options = supervisors.filter(function(s){ return !excluded.includes(s); });
        sup3.innerHTML = '<option value="">-- Select Supervisor 3 --</option>' + optList(sup3Options);
        if (sup3Val && sup3Options.includes(sup3Val)) {
            sup3.value = sup3Val;
        }
    }

    sup1.addEventListener('change', refreshSupervisorLists);
    sup2.addEventListener('change', refreshSupervisorLists);
    
    // Set prefill values
    if (prefill["Supervisor 1"]) sup1.value = prefill["Supervisor 1"];
    if (prefill["Supervisor 2 (if relevant)"]) sup2.value = prefill["Supervisor 2 (if relevant)"];
    if (prefill["Supervisor 3 (if relevant)"]) sup3.value = prefill["Supervisor 3 (if relevant)"];
    
    // Initial population
    refreshSupervisorLists();
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

  addBtn.addEventListener('click', function(){ addRow(); });


  // start with 1 row
  // start with 1 row (or prefill rows if backend returned errors)
  var PREFILL = {{ prefill_rows_json|default("[]")|safe }};
  if (Array.isArray(PREFILL) && PREFILL.length) {
    PREFILL.forEach(function(r){ addRow(r); });
  } else {
    addRow();
  }

})();
</script>

<script>
(function(){
  // Only runs on the "Submitted ✅" view when batch exists
  var bid = "{{ batch_id }}";
  if (!bid) return;

  var timerEl = document.getElementById('pendingTimer');
  var extendBtn = document.getElementById('extendBtn');
  var dismissBtn = document.getElementById('dismissSubmitted');
  var panel = document.getElementById('submittedPanel');

  function fmt(sec){
    sec = Math.max(0, Math.floor(sec || 0));
    var m = Math.floor(sec / 60);
    var s = sec % 60;
    return String(m).padStart(2,'0') + ':' + String(s).padStart(2,'0');
  }

  var serverNow = 0;
  var pendingUntil = 0;
  var remaining = 0;
  var lastPollAt = 0;

  function applyTimerClasses(rem){
    if (!timerEl) return;
    timerEl.classList.remove('timerWarn','timerFinal');
    if (rem <= 10 && rem > 0) timerEl.classList.add('timerFinal');
    else if (rem <= 20 && rem > 0) timerEl.classList.add('timerWarn');
  }

  function updateExtendButton(rem){
    if (!extendBtn) return;
    if (rem <= 20 && rem > 0){
      extendBtn.style.display = 'inline-block';
      extendBtn.disabled = false;
      extendBtn.style.opacity = '1';
      extendBtn.style.cursor = 'pointer';
    } else {
      extendBtn.style.display = 'none';
      extendBtn.disabled = true;
    }
  }

  function updateStatusPills(statuses){
    try{
      var pills = document.querySelectorAll('.statusPill[data-sid]');
      pills.forEach(function(p){
        var sid = p.getAttribute('data-sid') || '';
        var st = (statuses && statuses[sid]) ? String(statuses[sid]).toUpperCase() : String(p.textContent||'').toUpperCase();
        if (!st) return;
        p.textContent = st;
        p.classList.remove('statusPending','statusApplied');
        if (st === 'APPLIED') p.classList.add('statusApplied');
        else if (st === 'PENDING') p.classList.add('statusPending');
      });
    }catch(e){}
  }

  async function poll(){
    var now = Date.now();
    if (now - lastPollAt < 1500) return; // throttle a bit
    lastPollAt = now;

    try{
      var resp = await fetch('/api/pending_status?bid=' + encodeURIComponent(bid) + '&_t=' + now);
      if(!resp.ok) return;
      var j = await resp.json();
      if (!j || !j.ok) return;

      serverNow = Number(j.server_now_epoch || 0);
      pendingUntil = Number(j.pending_until_epoch || 0);

      // compute remaining using server values
      remaining = Math.max(0, pendingUntil - serverNow);

      if (timerEl){
        timerEl.textContent = fmt(remaining);
        applyTimerClasses(remaining);
      }
      updateExtendButton(remaining);
      updateStatusPills(j.statuses || {});
    }catch(e){}
  }

  function tick(){
    // decrement locally between polls for smoothness
    if (remaining > 0){
      remaining -= 1;
      if (timerEl){
        timerEl.textContent = fmt(remaining);
        applyTimerClasses(remaining);
      }
      updateExtendButton(remaining);
    }

    // refresh from server every ~4 seconds to avoid drift and update statuses
    if ((Date.now() - lastPollAt) > 4000){
      poll();
    }

    setTimeout(tick, 1000);
  }

  if (extendBtn && !extendBtn.dataset.bound){
    extendBtn.dataset.bound = "1";
    extendBtn.addEventListener('click', async function(){
      try{
        extendBtn.disabled = true;
        var resp = await fetch('/api/extend_pending', {
          method: 'POST',
          headers: {'Content-Type':'application/json'},
          body: JSON.stringify({bid: bid})
        });
        // even if it fails, just re-poll to reflect truth
        await poll();
      }catch(e){
        await poll();
      }
    });
  }

  if (dismissBtn && panel){
    dismissBtn.addEventListener('click', function(){
      panel.style.display = 'none';
      // focus first WO input for next entry
      var firstWo = document.querySelector('input[name="Work Order Number_0"]');
      if (firstWo) firstWo.focus();
    });
  }

  // initial sync + start ticking
  poll();
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
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">
  <style>
    :root{
      --bg:#f5f7fb;
      --card:#ffffff;
      --stroke:#e5e7eb;
      --text:#111827;
      --muted:#6b7280;
      --brand:#005aa3;
      --brand2:#0ea5e9;
      --danger:#dc2626;
      --shadow: 0 18px 45px rgba(16,24,40,0.10);
      --radius: 18px;
    }
    *{ box-sizing:border-box; }
    html,body{ height:100%; }
    body{
      margin:0;
      font-family: Inter, system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif;
      color: var(--text);
      background:
        radial-gradient(900px 450px at 10% 0%, rgba(14,165,233,0.15), transparent 55%),
        radial-gradient(900px 450px at 90% 0%, rgba(0,90,163,0.10), transparent 55%),
        linear-gradient(180deg, #ffffff, var(--bg));
      padding: 22px 16px;
      -webkit-font-smoothing: antialiased;
      -moz-osx-font-smoothing: grayscale;
    }

    .card{
      max-width: 1200px;
      margin: 0 auto 14px auto;
      border: 1px solid var(--stroke);
      background: var(--card);
      border-radius: var(--radius);
      padding: 16px 16px;
      box-shadow: var(--shadow);
    }

    h2{ margin:0 0 6px 0; font-size: 20px; font-weight: 950; letter-spacing:-0.02em; }
    a{ color: var(--brand); text-decoration:none; font-weight: 850; }
    a:hover{ text-decoration: underline; }

    .help{ color: var(--muted); font-size: 13px; margin-top: 6px; font-weight: 650; }

    .err{
      background: rgba(220,38,38,0.08);
      border: 1px solid rgba(220,38,38,0.22);
      padding: 12px;
      border-radius: 14px;
      color: #7f1d1d;
      font-weight: 750;
      overflow-wrap:anywhere;
    }
    .ok{
      background: rgba(14,165,233,0.06);
      border: 1px solid rgba(14,165,233,0.18);
      padding: 12px;
      border-radius: 14px;
      color: #0b2b4a;
      font-weight: 750;
      overflow-wrap:anywhere;
    }

    button{
      padding: 11px 13px;
      border-radius: 14px;
      border: 1px solid rgba(0,90,163,0.20);
      background: linear-gradient(135deg, var(--brand), var(--brand2));
      color:#fff;
      font-weight: 950;
      cursor:pointer;
      box-shadow: 0 14px 34px rgba(0,90,163,0.18);
      transition: transform .12s ease, filter .12s ease;
      user-select:none;
    }
    button:hover{ transform: translateY(-1px); filter: brightness(1.03); }
    button:active{ transform: translateY(0px) scale(.99); }
    .ghost{
      background:#f3f4f6;
      border: 1px solid #e5e7eb;
      color:#111827;
      box-shadow:none;
    }

    input, select, textarea{
      width: 100%;
      padding: 10px 11px;
      border-radius: 12px;
      border: 1px solid #d1d5db;
      background: #ffffff;
      color: #111827;
      font-size: 14px;
      font-weight: 650;
      outline: none;
      transition: border-color .12s ease, box-shadow .12s ease;
      min-width:0;
    }
    textarea{
      min-height: 110px;
      resize: vertical;
      line-height: 1.3;
    }
    input:focus, select:focus, textarea:focus{
      border-color: rgba(0,90,163,0.45);
      box-shadow: 0 0 0 4px rgba(14,165,233,0.16);
    }
    select, option{ color:#111827; background:#ffffff; }

    /* ===== Timer styling ===== */
    #editTimerBox{
      border: 1px solid var(--stroke) !important;
      background: #f9fafb !important;
      border-radius: 16px !important;
    }
    #editPendingTimer{
      font-variant-numeric: tabular-nums;
      font-weight: 950;
      color: #6b7280;
    }
    #editPendingTimer.timerWarn,
    #editPendingTimer.timerFinal{
      color: var(--danger);
    }
    .timerWarn{ animation: pulseWarn 0.9s infinite; }
    .timerFinal{ animation: pulseWarn 0.35s infinite, shakeWarn 0.35s infinite; }
    @keyframes pulseWarn{ 0%{transform:scale(1)} 50%{transform:scale(1.03)} 100%{transform:scale(1)} }
    @keyframes shakeWarn{ 0%{transform:translateX(0)} 25%{transform:translateX(-2px)} 50%{transform:translateX(2px)} 75%{transform:translateX(-2px)} 100%{transform:translateX(0)} }

    #editExtendBtn{
      background:#6b7280 !important;
      color:#fff !important;
      border-color: rgba(0,0,0,0.10) !important;
      padding:6px 10px !important;
      border-radius:999px !important;
      font-size:12px !important;
      box-shadow:none !important;
    }

    /* ===== Edit “woTable” (single-row) — same grid-card style as NEW ===== */
    #woTable{
      width: 100%;
      border: none;
      border-radius: 0;
      background: transparent;
      margin-top: 10px;
    }
    #woTable thead{ display:none; }

    #woTable tbody tr{
      display:grid;
      grid-template-columns: repeat(6, minmax(0, 1fr));
      gap: 10px 12px;
      padding: 12px;
      margin: 10px 0;
      border: 1px solid var(--stroke);
      border-radius: 16px;
      background: #ffffff;
      box-shadow: 0 10px 26px rgba(16,24,40,0.06);
    }
    #woTable tbody td{
      border:none;
      padding:0;
      display:flex;
      flex-direction:column;
      gap: 6px;
      min-width: 0;
    }
    #woTable tbody td::before{
      font-size: 11px;
      color: var(--muted);
      font-weight: 900;
      letter-spacing: .04em;
      text-transform: uppercase;
      content: "";
    }

    /* Labels by column (must match the addRow() order below) */
    #woTable tbody td:nth-child(1)::before{ content:"Work Order Number"; }
    #woTable tbody td:nth-child(2)::before{ content:"District (Where Snow Removed)"; }
    #woTable tbody td:nth-child(3)::before{ content:"Ward (Where Snow Removed)"; }
    #woTable tbody td:nth-child(4)::before{ content:"TOA Area (Where Snow Removed)"; }
    #woTable tbody td:nth-child(5)::before{ content:"Street"; }
    #woTable tbody td:nth-child(6)::before{ content:"From Intersection"; }
    #woTable tbody td:nth-child(7)::before{ content:"To Intersection"; }
    #woTable tbody td:nth-child(8)::before{ content:"One Side / Both Sides Cleared?"; }
    #woTable tbody td:nth-child(9)::before{ content:"Side of Road Cleared"; }
    #woTable tbody td:nth-child(10)::before{ content:"Roadway"; }
    #woTable tbody td:nth-child(11)::before{ content:"Sidewalk"; }
    #woTable tbody td:nth-child(12)::before{ content:"Separated Cycling Infrastructure"; }
    #woTable tbody td:nth-child(13)::before{ content:"Bridge"; }
    #woTable tbody td:nth-child(14)::before{ content:"School Loading Zones"; }
    #woTable tbody td:nth-child(15)::before{ content:"Layby Parking"; }
    #woTable tbody td:nth-child(16)::before{ content:"Equipment Method"; }
    #woTable tbody td:nth-child(17)::before{ content:"# of Equipment (Dump Trucks)"; }
    #woTable tbody td:nth-child(18)::before{ content:"Dump Truck Source (In-House/Contractor)"; }
    #woTable tbody td:nth-child(19)::before{ content:"Snow Dump Site"; }
    #woTable tbody td:nth-child(20)::before{ content:"# of Loads"; }
    #woTable tbody td:nth-child(21)::before{ content:"Tonnes"; }
    #woTable tbody td:nth-child(22)::before{ content:"Shift Start Date"; }
    #woTable tbody td:nth-child(23)::before{ content:"Shift Start Time"; }
    #woTable tbody td:nth-child(24)::before{ content:"Shift End Date"; }
    #woTable tbody td:nth-child(25)::before{ content:"Shift End Time"; }
    #woTable tbody td:nth-child(26)::before{ content:"Supervisor 1"; }
    #woTable tbody td:nth-child(27)::before{ content:"Supervisor 2 (if relevant)"; }
    #woTable tbody td:nth-child(28)::before{ content:"Supervisor 3 (if relevant)"; }
    #woTable tbody td:nth-child(29)::before{ content:"Snow Removal by Contracted Crew or In-House?"; }
    #woTable tbody td:nth-child(30)::before{ content:"Contractor: # of Crews"; }
    #woTable tbody td:nth-child(31)::before{ content:"Contractor: Crew TOA Area Responsibility"; }
    #woTable tbody td:nth-child(32)::before{ content:"Contractor: Crew Number"; }
    #woTable tbody td:nth-child(33)::before{ content:"In-House: Staff Responsibility (Base Yard)"; }
    #woTable tbody td:nth-child(34)::before{ content:"In-House: # of Staff"; }
    #woTable tbody td:nth-child(35)::before{ content:"NOTES"; }

    /* Spans / sizing */
    #woTable tbody td:nth-child(1){ grid-column: span 2; }
    #woTable tbody td:nth-child(5){ grid-column: span 2; }
    #woTable tbody td:nth-child(15){ grid-column: span 2; }
    #woTable tbody td:nth-child(31){ grid-column: span 2; }

    #woTable tbody td:nth-child(35){ grid-column: 1 / -1; } /* NOTES full width */
    #woTable tbody td:nth-child(5),
    #woTable tbody td:nth-child(6),
    #woTable tbody td:nth-child(7){
      grid-column: span 2; /* Street + From/To bigger */
    }

    @media (max-width: 1100px){
      #woTable tbody tr{ grid-template-columns: repeat(3, minmax(0, 1fr)); }
      #woTable tbody td:nth-child(34){ grid-column: 1 / -1; }
    }
    @media (max-width: 720px){
      #woTable tbody tr{ grid-template-columns: repeat(2, minmax(0, 1fr)); }
      #woTable tbody td:nth-child(34),
      #woTable tbody td:nth-child(5),
      #woTable tbody td:nth-child(6),
      #woTable tbody td:nth-child(7){ grid-column: 1 / -1; }
    }

    .rowBtns{
      display:flex;
      gap:10px;
      flex-wrap:wrap;
      justify-content:flex-end;
      margin-top: 10px;
    }

    #crossLists{ display:none; }
  </style>
</head>

<body>
  <div class="card">
    <div style="display:flex;align-items:center;gap:12px;">
      {% if cot_logo_src %}
      <img src="{{ cot_logo_src }}" alt="City of Toronto"
           style="height:38px;width:auto;object-fit:contain;display:block;" />
      {% endif %}
      <div style="flex:1;">
        <div style="font-weight:950;font-size:18px;letter-spacing:-0.02em;">Edit Intake Row</div>
        <div class="help" style="margin-top:2px;">Internal Operations Tool</div>
      </div>
    </div>

    <div class="help" style="margin-top:8px;">
      <a href="/new?bid={{ row.get('__batch_id','') }}">← Back to Batch</a> |
      <a href="/">Home</a> |
      <a href="/outputs/work_orders_map.html" target="_blank" rel="noopener noreferrer">Open Map</a>
    </div>

    <div class="help" style="margin-top:8px;">
      Submission ID: <code>{{ row.get('__submission_id','') }}</code> • Status: <code>{{ row.get('__status','') }}</code>
    </div>

    <div id="editTimerBox"
         style="margin-top:10px;display:flex;align-items:center;gap:10px;padding:10px 12px;border:1px solid var(--stroke);border-radius:14px;background:#f9fafb;">
      <div style="font-weight:900;font-size:13px;display:flex;align-items:center;gap:10px;">
        <span>Editing window:</span>
        <span id="editPendingTimer" style="font-size:16px;font-variant-numeric:tabular-nums;min-width:56px;display:inline-block;text-align:right;">--:--</span>

        <button type="button" id="editExtendBtn" style="display:none;">
          Extend
        </button>
      </div>
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
    <form method="post" autocomplete="off" id="editForm">

      <div class="help" style="margin-bottom:8px;">
        Edit fields below and click <b>Save changes</b>. (Only works while status is <b>PENDING</b>.)
      </div>

      <table id="woTable">
        <thead><tr><th>edit</th></tr></thead>
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

      <div id="crossLists"></div>

      <div class="rowBtns">
        <button type="submit">Save changes</button>
        <button type="submit" name="delete" value="1" class="ghost">Delete (Pending only)</button>
      </div>

      <div class="help" style="margin-top:10px;">
        After it becomes <b>APPLIED</b>, it’s locked to protect the master DB.
      </div>
    </form>
  </div>

<script>
(function(){
  var districts = {{ districts_json | safe }};
  var supervisors = {{ supervisors_json | safe }};
  var districtToWards = {{ district_to_wards_json | safe }};
  var types = {{ types_json | safe }};
  var dumpTruckProvidersOptions = {{ dump_truck_providers_html | tojson | safe }};
  var snowDumpSitesOptions = {{ snow_dump_sites_html | tojson | safe }};
  var STREET_ENDPOINTS = {{ street_endpoints_json | safe }};

  var tbody = document.getElementById('woTbody');
  var crossListsHost = document.getElementById('crossLists');

  function escapeHtml(s){
    return (s || '').toString()
      .replaceAll('&','&amp;')
      .replaceAll('<','&lt;')
      .replaceAll('>','&gt;')
      .replaceAll('"','&quot;')
      .replaceAll("'","&#39;");
  }

  function optList(arr){
    return (arr || []).map(function(x){
      return '<option value="' + escapeHtml(x) + '">' + escapeHtml(x) + '</option>';
    }).join('');
  }

  function districtSelectHtml(name, current){
    var o = '<option value="">--</option>';
    (districts||[]).forEach(function(d){
      var sel = (String(current||'') === String(d)) ? ' selected' : '';
      o += '<option value="' + escapeHtml(d) + '"' + sel + '>' + escapeHtml(d) + '</option>';
    });
    return '<select name="' + name + '" class="districtSel" required>' + o + '</select>';
  }

  function wardSelectHtml(name){
    return '<select name="' + name + '" class="wardSel" required><option value="">--</option></select>';
  }

  function typeSelectHtml(name, current){
    var o = '<option value="">--</option>' + optList(types);
    var sel = '<select name="' + name + '" required>' + o + '</select>';
    // set later by JS
    return sel;
  }

  function yesNoSelect(name, current){
    var cur = String(current||'');
    return ''
      + '<select name="' + name + '">'
      +   '<option value=""></option>'
      +   '<option' + (cur==='Yes'?' selected':'') + '>Yes</option>'
      +   '<option' + (cur==='No'?' selected':'') + '>No</option>'
      + '</select>';
  }

  function toaSelect(name, current){
    var toaAreas = ['TOA 1-1', 'TOA 1-2', 'TOA 1-3', 'TOA 1-4', 'TOA 1-5',
                    'TOA 2-1', 'TOA 2-2', 'TOA 2-3', 'TOA 2-4', 'TOA 2-5',
                    'DVP-FGGE'];
    var cur = String(current||'');
    var options = '<option value="">--</option>';
    toaAreas.forEach(function(t){
      var sel = (cur === t) ? ' selected' : '';
      options += '<option value="' + escapeHtml(t) + '"' + sel + '>' + escapeHtml(t) + '</option>';
    });
    return '<select name="' + name + '">' + options + '</select>';
  }

  function simpleSelect(name, optionsArr, current){
    var cur = String(current||'');
    var o = '<option value=""></option>';
    (optionsArr||[]).forEach(function(x){
      var sel = (cur===String(x)) ? ' selected' : '';
      o += '<option' + sel + '>' + escapeHtml(x) + '</option>';
    });
    return '<select name="' + name + '">' + o + '</select>';
  }

  function endpointsForStreet(streetVal){
    var k = (streetVal || '').toString().trim().toUpperCase();
    if (!k) return [];
    if (STREET_ENDPOINTS && STREET_ENDPOINTS[k]) return STREET_ENDPOINTS[k];
    return [];
  }

  function populateDatalist(dl, arr, excludeVal){
    if (!dl) return;
    var ex = (excludeVal || '').toString().trim().toUpperCase();
    dl.innerHTML = '';
    (arr || []).forEach(function(s){
      var v = (s || '').toString();
      if (!v) return;
      if (ex && v.toUpperCase() === ex) return;
      var opt = document.createElement('option');
      opt.value = v;
      dl.appendChild(opt);
    });
  }

  // --- Build ONE edit row in the same order as your Excel schema ---
  var row = {{ row_json | safe }};
  console.log("Edit form row data:", row);
  console.log("Shift Start Date:", row["Shift Start Date"]);
  console.log("Shift End Date:", row["Shift End Date"]);
  console.log("Supervisor 2:", row["Supervisor 2 (if relevant)"]);
  console.log("Supervisor 3:", row["Supervisor 3 (if relevant)"]);

  var tr = document.createElement('tr');
  tr.innerHTML =
    ''
    + '<td><input name="Work Order Number" required value="' + escapeHtml(row["Work Order Number"]||"") + '"></td>'
    + '<td>' + districtSelectHtml('District (Where Snow Removed)', row["District (Where Snow Removed)"]||"") + '</td>'
    + '<td>' + wardSelectHtml('Ward (Where Snow Removed)') + '</td>'
    + '<td>' + toaSelect('TOA Area (Where Snow Removed)', row["TOA Area (Where Snow Removed)"]||"") + '</td>'
    + '<td><input class="streetIn" id="streetIn" name="Street" list="streets" required value="' + escapeHtml(row["Street"]||"") + '"></td>'
    + '<td><input class="fromIn" id="fromIn" name="From Intersection" value="' + escapeHtml(row["From Intersection"]||"") + '"></td>'
    + '<td><input class="toIn" id="toIn" name="To Intersection" value="' + escapeHtml(row["To Intersection"]||"") + '"></td>'
    + '<td>' + simpleSelect('One Side / Both Sides Cleared?', ['Both Sides','One Side'], row["One Side / Both Sides Cleared?"]||"") + '</td>'
    + '<td>' + simpleSelect('Side of Road Cleared', ['North','South','East','West','East/West','North/South'], row["Side of Road Cleared"]||"") + '</td>'
    + '<td>' + yesNoSelect('Roadway', row["Roadway"]||"") + '</td>'
    + '<td>' + yesNoSelect('Sidewalk', row["Sidewalk"]||"") + '</td>'
    + '<td>' + yesNoSelect('Separated Cycling Infrastructure', row["Separated Cycling Infrastructure"]||"") + '</td>'
    + '<td>' + yesNoSelect('Bridge', row["Bridge"]||"") + '</td>'
    + '<td>' + yesNoSelect('School Loading Zones', row["School Loading Zones"]||"") + '</td>'
    + '<td>' + yesNoSelect('Layby Parking', row["Layby Parking"]||"") + '</td>'
    + '<td><select name="Equipment Method" required><option value="">--</option>' + optList(types) + '</select></td>'
    + '<td><input name="# of Equipment (Dump Trucks)" type="number" min="0" value="' + escapeHtml(row["# of Equipment (Dump Trucks)"]||"") + '"></td>'
    + '<td>' + simpleSelect('Dump Truck Source (In-House/Contractor)', ['In-House','Contractor'], row["Dump Truck Source (In-House/Contractor)"]||"") + '</td>'
    + '<td><select name="Snow Dump Site"><option value="">--</option>' + snowDumpSitesOptions + '</select></td>'
    + '<td><input name="# of Loads" type="number" min="0" value="' + escapeHtml(row["# of Loads"]||"") + '"></td>'
    + '<td><input name="Tonnes" type="number" step="0.01" min="0" value="' + escapeHtml(row["Tonnes"]||"") + '"></td>'
    + '<td><input type="date" name="Shift Start Date" required value="' + escapeHtml(row["Shift Start Date"]||"") + '"></td>'
    + '<td><input type="time" name="Shift Start Time" required value="' + escapeHtml(row["Shift Start Time"]||"") + '"></td>'
    + '<td><input type="date" name="Shift End Date" value="' + escapeHtml(row["Shift End Date"]||"") + '"></td>'
    + '<td><input type="time" name="Shift End Time" required value="' + escapeHtml(row["Shift End Time"]||"") + '"></td>'
    + '<td><select class="sup1" name="Supervisor 1" required><option value="">-- Select Supervisor 1 --</option>' + optList(supervisors) + '</select></td>'
    + '<td><select class="sup2" name="Supervisor 2 (if relevant)"><option value="">-- Select Supervisor 2 --</option></select></td>'
    + '<td><select class="sup3" name="Supervisor 3 (if relevant)"><option value="">-- Select Supervisor 3 --</option></select></td>'
    + '<td>' + simpleSelect('Snow Removal by Contracted Crew or In-House?', ['Contracted Crew','In-House'], row["Snow Removal by Contracted Crew or In-House?"]||"") + '</td>'
    + '<td><input name="Contractor: # of Crews" type="number" min="0" value="' + escapeHtml(row["Contractor: # of Crews"]||"") + '"></td>'
    + '<td><select name="Contractor: Crew TOA Area Responsibility"><option value="">--</option>' + dumpTruckProvidersOptions + '</select></td>'
    + '<td><input name="Contractor: Crew Number" value="' + escapeHtml(row["Contractor: Crew Number"]||"") + '"></td>'
    + '<td><input name="In-House: Staff Responsibility (Base Yard)" value="' + escapeHtml(row["In-House: Staff Responsibility (Base Yard)"]||"") + '"></td>'
    + '<td><input name="In-House: # of Staff" type="number" min="0" value="' + escapeHtml(row["In-House: # of Staff"]||"") + '"></td>'
    + '<td><textarea name="NOTES" rows="2" placeholder="Notes / comments (optional)">' + escapeHtml(row["NOTES"]||"") + '</textarea></td>';

  tbody.appendChild(tr);

  // set ward options based on district
  var dsel = tr.querySelector('.districtSel');
  var wsel = tr.querySelector('.wardSel');

  function setWards(){
    var dd = (dsel.value||'').toString().trim().toUpperCase();
    var wards = districtToWards[dd] || [];
    var prev = String(row["Ward (Where Snow Removed)"]||"");
    wsel.innerHTML = '<option value="">--</option>';
    wards.forEach(function(w){
      var opt = document.createElement('option');
      opt.value = w; opt.textContent = w;
      wsel.appendChild(opt);
    });
    if (prev && wards.indexOf(prev) !== -1) wsel.value = prev;
    else if (wards.length) wsel.value = wards[0];
  }
  dsel.addEventListener('change', setWards);
  setWards();

  // set equipment type selected
  try{
    var typeSel = tr.querySelector('select[name="Equipment Method"]');
    if (typeSel) typeSel.value = String(row["Equipment Method"]||"");
  }catch(e){}

  // set snow dump site selected
  try{
    var snowSel = tr.querySelector('select[name="Snow Dump Site"]');
    if (snowSel) snowSel.value = String(row["Snow Dump Site"]||"");
  }catch(e){}

  // set contractor responsibility selected
  try{
    var crewSel = tr.querySelector('select[name="Contractor: Crew TOA Area Responsibility"]');
    if (crewSel) crewSel.value = String(row["Contractor: Crew TOA Area Responsibility"]||"");
  }catch(e){}

  // ---- Street -> From/To dependent lists ----
  var streetIn = document.getElementById('streetIn');
  var toIn = document.getElementById('toIn');
  var fromIn = document.getElementById('fromIn');

  var dlTo = document.createElement('datalist');
  dlTo.id = 'cross_to_edit';
  dlTo.setAttribute('data-crosslist','1');
  crossListsHost.appendChild(dlTo);
  toIn.setAttribute('list', dlTo.id);

  var dlFrom = document.createElement('datalist');
  dlFrom.id = 'cross_from_edit';
  dlFrom.setAttribute('data-crosslist','1');
  crossListsHost.appendChild(dlFrom);
  fromIn.setAttribute('list', dlFrom.id);

  var cachedCross = [];

  function refreshCrossLists(){
    cachedCross = endpointsForStreet(streetIn.value);
    populateDatalist(dlTo, cachedCross, fromIn.value);
    populateDatalist(dlFrom, cachedCross, toIn.value);
  }

  streetIn.addEventListener('change', refreshCrossLists);
  streetIn.addEventListener('blur', refreshCrossLists);

  toIn.addEventListener('change', function(){ populateDatalist(dlFrom, cachedCross, toIn.value); });
  fromIn.addEventListener('change', function(){ populateDatalist(dlTo, cachedCross, fromIn.value); });

  refreshCrossLists();

  // ✅ Supervisor deduplication for SELECT dropdowns
  var sup1 = document.querySelector('.sup1');
  var sup2 = document.querySelector('.sup2');
  var sup3 = document.querySelector('.sup3');

  function refreshSupervisorLists(){
    var sup1Val = (sup1.value || '').trim();
    var sup2Val = (sup2.value || '').trim();
    var sup3Val = (sup3.value || '').trim();
    
    // Supervisor 2: exclude Supervisor 1
    var sup2Options = supervisors.filter(function(s){ return s !== sup1Val; });
    sup2.innerHTML = '<option value="">-- Select Supervisor 2 --</option>' + optList(sup2Options);
    if (sup2Val && sup2Options.includes(sup2Val)) {
      sup2.value = sup2Val;
    }
    
    // Supervisor 3: exclude both Supervisor 1 and 2
    var excluded = [sup1Val, sup2Val].filter(function(v){ return v; });
    var sup3Options = supervisors.filter(function(s){ return !excluded.includes(s); });
    sup3.innerHTML = '<option value="">-- Select Supervisor 3 --</option>' + optList(sup3Options);
    if (sup3Val && sup3Options.includes(sup3Val)) {
      sup3.value = sup3Val;
    }
  }

  sup1.addEventListener('change', refreshSupervisorLists);
  sup2.addEventListener('change', refreshSupervisorLists);
  
  // Store target values from row data BEFORE any refresh
  var targetSup1 = String(row["Supervisor 1"]||"");
  var targetSup2 = String(row["Supervisor 2 (if relevant)"]||"");
  var targetSup3 = String(row["Supervisor 3 (if relevant)"]||"");
  
  // Set sup1 first
  if (targetSup1) {
    sup1.value = targetSup1;
  }
  
  // Now refresh to populate sup2 and sup3 options based on sup1
  refreshSupervisorLists();
  
  // After refresh, set sup2 and sup3 values
  // Check if the value exists in the dropdown before setting
  if (targetSup2) {
    var foundSup2 = false;
    for (var i = 0; i < sup2.options.length; i++) {
      if (sup2.options[i].value === targetSup2) {
        foundSup2 = true;
        break;
      }
    }
    if (foundSup2) {
      sup2.value = targetSup2;
    }
  }
  
  if (targetSup3) {
    var foundSup3 = false;
    for (var i = 0; i < sup3.options.length; i++) {
      if (sup3.options[i].value === targetSup3) {
        foundSup3 = true;
        break;
      }
    }
    if (foundSup3) {
      sup3.value = targetSup3;
    }
  }
})();
</script>

<script>
(function(){
  // ---- Edit pending timer + extend ----
  var bid = "{{ row.get('__batch_id','') }}";
  if (!bid) return;

  var timerEl = document.getElementById('editPendingTimer');
  var extendBtn = document.getElementById('editExtendBtn');

  function fmt(sec){
    sec = Math.max(0, Math.floor(sec || 0));
    var m = Math.floor(sec / 60);
    var s = sec % 60;
    return String(m).padStart(2,'0') + ':' + String(s).padStart(2,'0');
  }

  function applyTimerClasses(rem){
    if (!timerEl) return;
    timerEl.classList.remove('timerWarn','timerFinal');
    if (rem <= 10 && rem > 0) timerEl.classList.add('timerFinal');
    else if (rem <= 20 && rem > 0) timerEl.classList.add('timerWarn');
  }

  function updateExtendButton(rem){
    if (!extendBtn) return;
    if (rem <= 20 && rem > 0){
      extendBtn.style.display = 'inline-block';
      extendBtn.disabled = false;
    } else {
      extendBtn.style.display = 'none';
      extendBtn.disabled = true;
    }
  }

  var remaining = 0;
  var lastPollAt = 0;

  async function poll(){
    var now = Date.now();
    if (now - lastPollAt < 1500) return;
    lastPollAt = now;

    try{
      var resp = await fetch('/api/pending_status?bid=' + encodeURIComponent(bid) + '&_t=' + now);
      if(!resp.ok) return;
      var j = await resp.json();
      if (!j || !j.ok) return;

      var serverNow = Number(j.server_now_epoch || 0);
      var pendingUntil = Number(j.pending_until_epoch || 0);

      remaining = Math.max(0, pendingUntil - serverNow);

      if (timerEl){
        timerEl.textContent = fmt(remaining);
        applyTimerClasses(remaining);
      }
      updateExtendButton(remaining);
    }catch(e){}
  }

  function tick(){
    if (remaining > 0){
      remaining -= 1;
      if (timerEl){
        timerEl.textContent = fmt(remaining);
        applyTimerClasses(remaining);
      }
      updateExtendButton(remaining);
    }
    if ((Date.now() - lastPollAt) > 4000){
      poll();
    }
    setTimeout(tick, 1000);
  }

  if (extendBtn){
    extendBtn.addEventListener('click', async function(){
      try{
        extendBtn.disabled = true;
        await fetch('/api/extend_pending', {
          method: 'POST',
          headers: {'Content-Type':'application/json'},
          body: JSON.stringify({bid: bid})
        });
        await poll();
      }catch(e){
        await poll();
      }
    });
  }

  poll();
  tick();
})();
</script>

</body>
</html>
"""


def normalize_wo_id(x: str) -> str:
    """
    Stable normalization for Work Order Number / WO fields.
    Used by intake logic / status checks.
    """
    s = str(x or "").strip()
    if not s:
        return ""
    # keep digits if it's numeric-like, but don't crash on alphas
    s2 = re.sub(r"\s+", "", s)
    return s2


def enqueue_build(reason: str = ""):
    """
    Minimal rebuild trigger used by edit/new flows.
    Fixes: NameError: enqueue_build not defined
    """
    try:
        with FILE_LOCK:
            stats = build_everything()
        # refresh picklists
        try:
            global latest_allowed_sets, latest_centre_streets, latest_street_to_cross, latest_build_stats
            latest_allowed_sets = recompute_allowed_sets_from_master()
            latest_centre_streets = stats.get("centre_streets", [])
            latest_street_to_cross = stats.get("street_to_cross", {})
            latest_build_stats = {
                "status": "ready",
                "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                **{k: v for k, v in stats.items() if k != "centre_streets"},
            }
        except Exception:
            pass

        _emit_updated_event("build", items=[{"reason": reason or "manual"}])
    except Exception as e:
        log(f"enqueue_build error: {e}")


@app.get("/")
def home():
    return render_template_string(
        INDEX_HTML,
        cot_logo_src=COT_LOGO_DATA_URI,
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
        server_now_epoch = time.time()

        pending_untils = []
        for r in batch:
            st = str(r.get("__status", "")).strip().upper()
            if st != "PENDING":
                continue

            pu_raw = str(r.get("__pending_until_epoch", "")).strip()
            try:
                pu = float(pu_raw) if pu_raw else None
            except Exception:
                pu = None

            if pu is None:
                # fallback: __submitted_at + grace
                try:
                    ts = pd.to_datetime(r.get("__submitted_at", ""), errors="coerce")
                    if pd.isna(ts):
                        pu = 0.0
                    else:
                        pu = float(ts.timestamp()) + float(PENDING_GRACE_SECONDS)
                except Exception:
                    pu = 0.0

            pending_untils.append(float(pu))

        if pending_untils:
            apply_in_seconds = int(max(0, min(pending_untils) - float(server_now_epoch)))
        else:
            apply_in_seconds = 0


    street_endpoints = get_street_endpoints_index()

    return render_template_string(
        NEW_FORM_HTML,
        cot_logo_src=COT_LOGO_DATA_URI,
        errors=[],
        batch=batch,
        batch_id=bid,
        pending_grace_seconds=PENDING_GRACE_SECONDS,
        apply_in_seconds=apply_in_seconds,
        inserted_count=len([r for r in batch if r.get("__status","").strip()]),
        intake_poll_seconds=INTAKE_POLL_SECONDS,
        districts=DISTRICTS,
        supervisors=latest_allowed_sets.get("Supervisor 1", []),
        shifts=(STRICT_SHIFTS[:] if STRICT_SHIFTS else []),
        types=(STRICT_TYPES[:] if STRICT_TYPES else []),
        streets=(sorted(street_endpoints.keys(), key=lambda x: x.casefold()) if street_endpoints else latest_centre_streets),
        dump_truck_providers_html="".join(
            f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS
        ),
        snow_dump_sites_html="".join(
            f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES
        ),        
        districts_json=json.dumps(DISTRICTS),
        supervisors_json=json.dumps(latest_allowed_sets.get("Supervisor 1", [])),
        shifts_json=json.dumps((STRICT_SHIFTS[:] if STRICT_SHIFTS else [])),
        types_json=json.dumps((STRICT_TYPES[:] if STRICT_TYPES else [])),
        street_endpoints_json=json.dumps(street_endpoints, ensure_ascii=False),
        district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
    )



@app.post("/new")
def new_submit():
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    form = request.form.to_dict()

    log("NEW_SUBMIT keys sample: " + ", ".join(list(request.form.keys())[:30]))


    # Parse rows WO_0..WO_n
        # -------------------------
    # Parse rows robustly (do NOT assume contiguous 0..N)
    # -------------------------
    rows = []

    # collect all indices present in the submission for Work Order Number_{i}
    idxs = []
    for k in form.keys():
        m = re.match(r"^Work Order Number_(\d+)$", str(k))
        if m:
            try:
                idxs.append(int(m.group(1)))
            except Exception:
                pass
    idxs = sorted(set(idxs))

    for idx in idxs:
        values = {k: "" for k in MASTER_COLUMNS}

        # helper getter
        def g(field_name: str) -> str:
            return (form.get(f"{field_name}_{idx}", "") or "").strip()

        # 1
        values["Work Order Number"] = g("Work Order Number")

        # 2-4
        values["District (Where Snow Removed)"] = g("District (Where Snow Removed)")
        values["Ward (Where Snow Removed)"] = g("Ward (Where Snow Removed)")
        values["TOA Area (Where Snow Removed)"] = g("TOA Area (Where Snow Removed)")

        # 5-7
        values["Street"] = g("Street")
        values["From Intersection"] = g("From Intersection")
        values["To Intersection"] = g("To Intersection")

        # 8-9
        values["One Side / Both Sides Cleared?"] = g("One Side / Both Sides Cleared?")
        values["Side of Road Cleared"] = g("Side of Road Cleared")

        # 10-15 Yes/No fields
        values["Roadway"] = g("Roadway")
        values["Sidewalk"] = g("Sidewalk")
        values["Separated Cycling Infrastructure"] = g("Separated Cycling Infrastructure")
        values["Bridge"] = g("Bridge")
        values["School Loading Zones"] = g("School Loading Zones")
        values["Layby Parking"] = g("Layby Parking")

        # 16-21
        values["Equipment Method"] = g("Equipment Method")
        values["# of Equipment (Dump Trucks)"] = g("# of Equipment (Dump Trucks)")
        values["Dump Truck Source (In-House/Contractor)"] = g("Dump Truck Source (In-House/Contractor)")
        values["Snow Dump Site"] = g("Snow Dump Site")
        values["# of Loads"] = g("# of Loads")
        values["Tonnes"] = g("Tonnes")

        # 21-24 Shift - Keep dates in YYYY-MM-DD format for HTML date inputs
        values["Shift Start Date"] = g("Shift Start Date")
        values["Shift Start Time"] = g("Shift Start Time")

        _end_date = g("Shift End Date")
        values["Shift End Date"] = _end_date if _end_date else values["Shift Start Date"]
        values["Shift End Time"] = g("Shift End Time")

        # If end time is "earlier" than start and end date was blank, assume next day
        try:
            from datetime import datetime, timedelta
            sd = values["Shift Start Date"]
            ed = values["Shift End Date"]
            st = values["Shift Start Time"]
            et = values["Shift End Time"]
            if sd and st and et:
                ds = datetime.strptime(sd, "%Y-%m-%d")
                dt_start = datetime.combine(ds.date(), datetime.strptime(st, "%H:%M").time())
                de_base = datetime.strptime(ed, "%Y-%m-%d") if ed else ds
                dt_end = datetime.combine(de_base.date(), datetime.strptime(et, "%H:%M").time())
                if (not _end_date) and dt_end < dt_start:
                    dt_end += timedelta(days=1)
                    values["Shift End Date"] = dt_end.strftime("%Y-%m-%d")
        except Exception:
            pass

        # 25 Hours Worked (server truth)
        try:
            from datetime import datetime
            sd = values["Shift Start Date"]
            ed = values["Shift End Date"] or sd
            st = values["Shift Start Time"]
            et = values["Shift End Time"]
            if sd and ed and st and et:
                dt1 = datetime.fromisoformat(sd + " " + st + ":00")
                dt2 = datetime.fromisoformat(ed + " " + et + ":00")
                hours = max(0.0, (dt2 - dt1).total_seconds() / 3600.0)
                values["Hours Worked"] = f"{hours:.2f}"
        except Exception:
            values["Hours Worked"] = ""

        # 26 Data entry timestamp
        values["Time and Date of Data Entry Input"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        # 27-29 Supervisors
        values["Supervisor 1"] = g("Supervisor 1")
        values["Supervisor 2 (if relevant)"] = g("Supervisor 2 (if relevant)")
        values["Supervisor 3 (if relevant)"] = g("Supervisor 3 (if relevant)")

        # 30-35 Contractor/In-house fields
        values["Snow Removal by Contracted Crew or In-House?"] = g("Snow Removal by Contracted Crew or In-House?")
        values["Contractor: # of Crews"] = g("Contractor: # of Crews")
        values["Contractor: Crew TOA Area Responsibility"] = g("Contractor: Crew TOA Area Responsibility")
        values["Contractor: Crew Number"] = g("Contractor: Crew Number")
        values["In-House: Staff Responsibility (Base Yard)"] = g("In-House: Staff Responsibility (Base Yard)")
        values["In-House: # of Staff"] = g("In-House: # of Staff")

        # 36 NOTES
        values["NOTES"] = g("NOTES")

        # ✅ Skip accidental fully-empty rows (THIS was backwards in your earlier logic)
        if (not normalize_blank(values.get("Work Order Number"))) and (not normalize_blank(values.get("Street"))):
            continue

        rows.append(values)

        idx += 1

    if not rows:
        street_endpoints = get_street_endpoints_index()
        return render_template_string(
            NEW_FORM_HTML,
            cot_logo_src=COT_LOGO_DATA_URI,
            errors=["No rows found. Click + Add Row and fill at least one Work Order."],
            batch=[],
            batch_id="",
            inserted_count=0,
            intake_poll_seconds=INTAKE_POLL_SECONDS,
            districts=DISTRICTS,            supervisors=latest_allowed_sets.get("Supervisor 1", []),
            shifts=(STRICT_SHIFTS[:] if STRICT_SHIFTS else []),
            types=(STRICT_TYPES[:] if STRICT_TYPES else []),
            streets=(sorted(street_endpoints.keys(), key=lambda x: x.casefold()) if street_endpoints else latest_centre_streets),
            dump_truck_providers_html="".join(f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS),
            snow_dump_sites_html="".join(f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES),                
            districts_json=json.dumps(DISTRICTS),            
            shifts_json=json.dumps((STRICT_SHIFTS[:] if STRICT_SHIFTS else [])),
            types_json=json.dumps((STRICT_TYPES[:] if STRICT_TYPES else [])),
            street_endpoints_json=json.dumps(street_endpoints, ensure_ascii=False),
            district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
        )

    street_endpoints = get_street_endpoints_index()

    streets_set = set(
        s.upper().strip()
        for s in (street_endpoints.keys() if street_endpoints else latest_centre_streets)
        if isinstance(s, str) and s.strip()
    )

    all_errors = []
    allowed_base = dict(latest_allowed_sets or {})

    # Validate each row independently
    for i, values in enumerate(rows, start=1):
        allowed_sets = dict(allowed_base)
        dval = values.get("District (Where Snow Removed)", "")
        allowed_sets["Ward (Where Snow Removed)"] = wards_for_district(dval)

        errs = validate_submission(values, allowed_sets, streets_set, street_endpoints)
        for e in errs:
            all_errors.append(f"Row {i}: {e}")

    if all_errors:
        log(f"INTAKE: batch rejected with {len(all_errors)} error(s)")
        prefill_rows = []

        for v in rows:
            # JS expects these keys (WO/District/Ward/Date/Shift/Supervisor/Street/FromIntersection/ToIntersection...) for repopulating the row grid.
            sh = normalize_shift_time_range("", v.get("Shift Start Time", ""), v.get("Shift End Time", ""))
            prefill_rows.append({
                "Work Order Number": v.get("Work Order Number", ""),
                "District (Where Snow Removed)": v.get("District (Where Snow Removed)", ""),
                "Ward (Where Snow Removed)": v.get("Ward (Where Snow Removed)", ""),
                "TOA Area (Where Snow Removed)": v.get("TOA Area (Where Snow Removed)", ""),
                "Street": v.get("Street", ""),
                "From Intersection": v.get("From Intersection", ""),
                "To Intersection": v.get("To Intersection", ""),
                "One Side / Both Sides Cleared?": v.get("One Side / Both Sides Cleared?", ""),
                "Side of Road Cleared": v.get("Side of Road Cleared", ""),
                "Roadway": v.get("Roadway", ""),
                "Sidewalk": v.get("Sidewalk", ""),
                "Separated Cycling Infrastructure": v.get("Separated Cycling Infrastructure", ""),
                "Bridge": v.get("Bridge", ""),
                "School Loading Zones": v.get("School Loading Zones", ""),
                "Layby Parking": v.get("Layby Parking", ""),
                "Equipment Method": v.get("Equipment Method", ""),
                "# of Equipment (Dump Trucks)": v.get("# of Equipment (Dump Trucks)", ""),
                "Dump Truck Source (In-House/Contractor)": v.get("Dump Truck Source (In-House/Contractor)", ""),
                "Snow Dump Site": v.get("Snow Dump Site", ""),
                "# of Loads": v.get("# of Loads", ""),
                "Tonnes": v.get("Tonnes", ""),
                "Shift Start Date": v.get("Shift Start Date", ""),
                "Shift Start Time": v.get("Shift Start Time", ""),
                "Shift End Date": v.get("Shift End Date", ""),
                "Shift End Time": v.get("Shift End Time", ""),
                "Supervisor 1": v.get("Supervisor 1", ""),
                "Supervisor 2 (if relevant)": v.get("Supervisor 2 (if relevant)", ""),
                "Supervisor 3 (if relevant)": v.get("Supervisor 3 (if relevant)", ""),
                "Snow Removal by Contracted Crew or In-House?": v.get("Snow Removal by Contracted Crew or In-House?", ""),
                "Contractor: # of Crews": v.get("Contractor: # of Crews", ""),
                "Contractor: Crew TOA Area Responsibility": v.get("Contractor: Crew TOA Area Responsibility", ""),
                "Contractor: Crew Number": v.get("Contractor: Crew Number", ""),
                "In-House: Staff Responsibility (Base Yard)": v.get("In-House: Staff Responsibility (Base Yard)", ""),
                "In-House: # of Staff": v.get("In-House: # of Staff", ""),
                "NOTES": v.get("NOTES", ""),
            })

        street_endpoints = get_street_endpoints_index()
        return render_template_string(
            NEW_FORM_HTML,
            cot_logo_src=COT_LOGO_DATA_URI,
            errors=all_errors,
            batch=[],
            batch_id="",
            inserted_count=0,
            intake_poll_seconds=INTAKE_POLL_SECONDS,
            districts=DISTRICTS,
            supervisors=latest_allowed_sets.get("Supervisor 1", []),
            shifts=(STRICT_SHIFTS[:] if STRICT_SHIFTS else []),
            types=(STRICT_TYPES[:] if STRICT_TYPES else []),
            streets=(sorted(street_endpoints.keys(), key=lambda x: x.casefold()) if street_endpoints else latest_centre_streets),
            dump_truck_providers_html="".join(f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS),
            snow_dump_sites_html="".join(f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES),
            districts_json=json.dumps(DISTRICTS),            
            shifts_json=json.dumps((STRICT_SHIFTS[:] if STRICT_SHIFTS else [])),
            types_json=json.dumps((STRICT_TYPES[:] if STRICT_TYPES else [])),
            street_endpoints_json=json.dumps(street_endpoints, ensure_ascii=False),
            prefill_rows_json=json.dumps(prefill_rows),
            district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
        )

    batch_id, inserted_count, _per = append_batch_to_intake(rows)

    return Response(
        "", 303,
        {"Location": f"/new?bid={batch_id}"}
    )

@app.get("/api/cross_streets")
def api_cross_streets():
    """Return cross-street suggestions for a given Street.

    Query params:
      - street (preferred)
      - location (legacy alias)
    """
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    street_raw = (request.args.get("street") or request.args.get("location") or "").strip()

    def _ui_norm(s: str) -> str:
        s = (s or "").upper().strip()
        s = s.replace("-", " ")
        s = re.sub(r"\s+", " ", s).strip()
        return s

    street_key = _ui_norm(street_raw)

    streets = latest_centre_streets or []
    street_set = set(streets)

    matched = ""
    if street_key in street_set:
        matched = street_key
    else:
        # 1) substring
        for st in streets:
            if street_key and street_key in st:
                matched = st
                break
        # 2) difflib fallback
        if not matched and street_key:
            try:
                close = difflib.get_close_matches(street_key, streets, n=1, cutoff=0.72)
                if close:
                    matched = close[0]
            except Exception:
                pass

    cross = list(latest_street_to_cross.get(matched, []) or [])
    payload = {
        "input_street": street_raw,
        "matched_street": matched,
        "count": len(cross),
        "cross_streets": cross,

        # Legacy keys (older JS expects these)
        "input_location": street_raw,
        "matched_location": matched,
    }

    return Response(json.dumps(payload, ensure_ascii=False), mimetype="application/json")

@app.get("/api/pending_status")
def api_pending_status():
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    bid = (request.args.get("bid") or "").strip()
    if not bid:
        return Response(json.dumps({"ok": False, "error": "missing bid"}), mimetype="application/json", status=400)

    ensure_intake_file()

    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

    if "__batch_id" not in df.columns:
        return Response(json.dumps({"ok": False, "error": "intake missing __batch_id"}), mimetype="application/json", status=500)

    sub = df[df["__batch_id"].astype(str) == bid].copy()
    if sub.empty:
        return Response(json.dumps({"ok": True, "bid": bid, "server_now_epoch": time.time(), "pending_until_epoch": 0, "pending_count": 0, "statuses": {}}),
                       mimetype="application/json")

    # statuses map: sid -> status
    statuses = {}
    for _, r in sub.iterrows():
        sid = str(r.get("__submission_id", "")).strip()
        st = str(r.get("__status", "")).strip()
        if sid:
            statuses[sid] = st

    pending = sub[sub["__status"].astype(str).str.upper().eq("PENDING")].copy()

    now_epoch = time.time()
    pending_until_epoch = 0
    pending_count = int(len(pending))

    if not pending.empty:
        pu = pd.to_numeric(pending.get("__pending_until_epoch", ""), errors="coerce")

        ts = pd.to_datetime(pending.get("__submitted_at", ""), errors="coerce")
        ts = ts.fillna(pd.Timestamp("1970-01-01"))
        submitted_epoch = ts.astype("int64") / 1e9

        fallback_until = submitted_epoch + float(PENDING_GRACE_SECONDS)
        pu = pu.fillna(fallback_until)

        try:
            pending_until_epoch = float(pu.min())
        except Exception:
            pending_until_epoch = 0

    return Response(
        json.dumps(
            {
                "ok": True,
                "bid": bid,
                "server_now_epoch": float(now_epoch),
                "pending_until_epoch": float(pending_until_epoch),
                "pending_count": pending_count,
                "statuses": statuses,
            },
            ensure_ascii=False,
        ),
        mimetype="application/json",
    )


@app.post("/api/extend_pending")
def api_extend_pending():
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    payload = request.get_json(silent=True) or {}
    bid = (payload.get("bid") or request.form.get("bid") or "").strip()
    if not bid:
        return Response(json.dumps({"ok": False, "error": "missing bid"}), mimetype="application/json", status=400)

    # Check if it's within the last 20 seconds before allowing extend
    # (server-enforced to match UI behavior)
    ensure_intake_file()

    with FILE_LOCK:
        try:
            df = pd.read_csv(INTAKE_PATH, encoding="utf-8")
        except Exception:
            df = pd.read_csv(INTAKE_PATH, encoding="latin-1")

        if "__batch_id" not in df.columns:
            return Response(json.dumps({"ok": False, "error": "intake missing __batch_id"}), mimetype="application/json", status=500)

        sub = df[df["__batch_id"].astype(str) == bid].copy()
        pending = sub[sub["__status"].astype(str).str.upper().eq("PENDING")].copy()

        now_epoch = time.time()
        if pending.empty:
            return Response(
                json.dumps({"ok": True, "message": "no_pending_noop"}),
                mimetype="application/json",
                status=200,
            )


        pu = pd.to_numeric(pending.get("__pending_until_epoch", ""), errors="coerce")

        ts = pd.to_datetime(pending.get("__submitted_at", ""), errors="coerce")
        ts = ts.fillna(pd.Timestamp("1970-01-01"))
        submitted_epoch = ts.astype("int64") / 1e9

        fallback_until = submitted_epoch + float(PENDING_GRACE_SECONDS)
        pu = pu.fillna(fallback_until)

        current_until = float(pu.min())
        remaining = current_until - float(now_epoch)

        if remaining > 20:
            return Response(
                json.dumps({"ok": False, "error": "too_early", "remaining": remaining}),
                mimetype="application/json",
                status=409,
            )

        new_until = float(now_epoch) + float(PENDING_GRACE_SECONDS)

        mask = df["__batch_id"].astype(str).eq(bid) & df["__status"].astype(str).str.upper().eq("PENDING")
        if "__pending_until_epoch" not in df.columns:
            df["__pending_until_epoch"] = ""
        df["__pending_until_epoch"] = df["__pending_until_epoch"].astype(str)  # ensure column is str type
        df.loc[mask, "__pending_until_epoch"] = str(int(new_until))
        df.to_csv(INTAKE_PATH, index=False, encoding="utf-8")

    return Response(
        json.dumps(
            {
                "ok": True,
                "bid": bid,
                "server_now_epoch": float(now_epoch),
                "pending_until_epoch": float(new_until),
            },
            ensure_ascii=False,
        ),
        mimetype="application/json",
    )



@app.get("/edit/<sid>")
def edit_form(sid):
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    street_endpoints = get_street_endpoints_index()

    row = get_intake_row_by_submission_id(sid)
    if not row:
        return Response("Not found", 404)

    # Derive provider + comments from NOTES (provider is stored as a tagged line)
    raw_notes = str(row.get("NOTES", "") or "").strip()
    provider_val = ""
    notes_val = raw_notes
    tag = "Dump Truck Provider Contractor:"
    if tag in raw_notes:
        parts = raw_notes.split(tag, 1)
        notes_val = parts[0].rstrip() if parts else raw_notes
        provider_val = parts[1].strip() if len(parts) > 1 else ""

    district_val = row.get("District (Where Snow Removed)", "")
    wards = wards_for_district(district_val) or latest_allowed_sets.get("Ward (Where Snow Removed)", [])
    row_json = {k: str(row.get(k, "") or "") for k in MASTER_COLUMNS}

    return render_template_string(
        EDIT_FORM_HTML,
        cot_logo_src=COT_LOGO_DATA_URI,
        row=row,
        row_json=json.dumps(row_json, ensure_ascii=False),
        ok=False,
        errors=[],
        districts=DISTRICTS,
        districts_json=json.dumps(DISTRICTS),
        wards=wards,
        supervisors=latest_allowed_sets.get("Supervisor 1", []),
        supervisors_json=json.dumps(latest_allowed_sets.get("Supervisor 1", [])),
        streets=(sorted(street_endpoints.keys(), key=lambda x: x.casefold()) if street_endpoints else latest_centre_streets),
        district_to_wards_json=json.dumps(DISTRICT_TO_WARDS),
        street_endpoints_json=json.dumps(street_endpoints, ensure_ascii=False),
        types=(STRICT_TYPES[:] if STRICT_TYPES else []),
        types_json=json.dumps((STRICT_TYPES[:] if STRICT_TYPES else [])),
        dump_truck_providers_html="".join(f"<option>{html.escape(x)}</option>" for x in DUMP_TRUCK_PROVIDERS),
        snow_dump_sites_html="".join(f"<option>{html.escape(x)}</option>" for x in SNOW_DUMP_SITES),
    )



@app.post("/edit/<sid>")
def edit_submit(sid):
    auth_resp = require_auth_or_401()
    if auth_resp:
        return auth_resp

    # Load intake rows and locate this submission
    ensure_intake_file()
    intake = pd.read_csv(INTAKE_PATH, dtype=str).fillna("")
    m = intake[intake.get("__submission_id", "") == str(sid)] if "__submission_id" in intake.columns else intake.iloc[0:0]

    form = request.form.to_dict()

    # Build a master-schema row from form values (form now uses exact Excel header names)
    values = {k: "" for k in MASTER_COLUMNS}

    # Copy any direct master keys from the form
    for k in MASTER_COLUMNS:
        if k in form:
            values[k] = form.get(k, "")

    # Keep dates in YYYY-MM-DD format for HTML date inputs
    try:
        _date_picker = values.get("Shift Start Date", "")
        values["Shift Start Date"] = _date_picker if _date_picker else values.get("Shift Start Date", "")
        if not values.get("Shift End Date"):
            values["Shift End Date"] = values.get("Shift Start Date", "")
    except Exception:
        pass

    # Auto compute Shift End Date if crosses midnight
    try:
        sd = values.get("Shift Start Date", "")
        st = values.get("Shift Start Time", "")
        et = values.get("Shift End Time", "")
        if sd and st and et:
            from datetime import datetime, timedelta
            ds = datetime.strptime(sd, "%Y-%m-%d")
            t1 = datetime.strptime(st, "%H:%M").time()
            t2 = datetime.strptime(et, "%H:%M").time()
            dt_start = datetime.combine(ds.date(), t1)
            dt_end = datetime.combine(ds.date(), t2)
            if dt_end < dt_start:
                dt_end += timedelta(days=1)
            values["Shift End Date"] = dt_end.strftime("%Y-%m-%d")
    except Exception:
        pass

    # Intersection IDs (best-effort)
    try:
        _ref_street_to_cross, _pair_to_id = get_intersection_reference()
        _s = normalize_street_name(values.get("Street", ""))
        _f = extract_cross_from_endpoint(values.get("Street", ""), values.get("From Intersection", ""))
        _t = extract_cross_from_endpoint(values.get("Street", ""), values.get("To Intersection", ""))
        values["From Intersection ID"] = _pair_to_id.get((_s, _f), "")
        values["To Intersection ID"] = _pair_to_id.get((_s, _t), "")
    except Exception:
        values["From Intersection ID"] = values.get("From Intersection ID", "")
        values["To Intersection ID"] = values.get("To Intersection ID", "")

    # Data entry timestamp
    try:
        from datetime import datetime as _dt
        values["Time and Date of Data Entry Input"] = _dt.now().strftime("%Y-%m-%d %H:%M:%S")
    except Exception:
        pass

    # Ensure dump-truck source is set if contractor responsibility provided
    try:
        if values.get("Contractor: Crew TOA Area Responsibility", "").strip():
            if not values.get("Dump Truck Source (In-House/Contractor)", "").strip():
                values["Dump Truck Source (In-House/Contractor)"] = "Contractor"
    except Exception:
        pass

    # Persist back to intake file (so map builder sees edits)
    # If intake row exists, update it; else append a new one (rare)
    # --- Persist back to intake (edit only if PENDING) ---
    if "__status" in intake.columns and not m.empty:
        st = str(intake.at[m.index[0], "__status"]).strip().upper()
        if st != "PENDING":
            return Response("Locked (already applied)", 409)

    # Update intake row
    if not m.empty:
        idx0 = m.index[0]
        for k in MASTER_COLUMNS:
            if k in intake.columns:
                intake.at[idx0, k] = values.get(k, "")
        intake.to_csv(INTAKE_PATH, index=False, encoding="utf-8")

    # Rebuild immediately (optional, but makes UI feel instant)
    enqueue_build("edit")

    # Redirect back to batch view
    bid = request.args.get("bid") or str(intake.at[idx0, "__batch_id"]) if (not m.empty and "__batch_id" in intake.columns) else ""
    return redirect(f"/new?bid={bid}" if bid else "/new")


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
    """Build allowed picklists for the webforms.

    With the new Snow Removal Master Tracker.xlsx schema, we keep district/ward
    validation based on DISTRICT_TO_WARDS (hard-coded), and we optionally load
    supervisors from the workbook's "List of Supervisors - Reference" sheet.
    """
    allowed = {}

    # District/Ward come from the hard-coded reference (fast + stable)
    allowed["District (Where Snow Removed)"] = list(STRICT_DISTRICTS) if STRICT_DISTRICTS else list(DISTRICTS)
    allowed["Ward (Where Snow Removed)"] = sorted(list(STRICT_WARDS) if STRICT_WARDS else list({w for ws in DISTRICT_TO_WARDS.values() for w in ws}), key=lambda x: int(x))

    # Supervisors: Start with STRICT_SUPERVISORS, then add any from data
    supervisors = list(STRICT_SUPERVISORS) if STRICT_SUPERVISORS else []
    
    if MASTER_TRACKER_PATH.endswith('.csv'):
        # CSV mode: extract unique supervisors from the actual data and ADD to the list
        try:
            df = read_master_csv()
            if not df.empty:
                sup_cols = ["Supervisor 1", "Supervisor 2 (if relevant)", "Supervisor 3 (if relevant)"]
                for col in sup_cols:
                    if col in df.columns:
                        vals = df[col].fillna("").astype(str).map(lambda x: x.strip()).tolist()
                        supervisors.extend([v for v in vals if v and v.lower() != "nan"])
        except Exception:
            pass  # Keep STRICT_SUPERVISORS
    else:
        # XLSX mode: try to load from reference sheet
        try:
            sup_df = pd.read_excel(MASTER_TRACKER_PATH, sheet_name="List of Supervisors - Reference", header=None)
            if not sup_df.empty:
                col0 = sup_df.iloc[:, 0].fillna("").astype(str).map(lambda x: x.strip()).tolist()
                xlsx_sups = [x for x in col0 if x and x.lower() != "nan"]
                supervisors.extend(xlsx_sups)
        except Exception:
            pass  # Keep STRICT_SUPERVISORS

    # de-dupe + sort
    seen = set()
    out = []
    for s in supervisors:
        if s in seen:
            continue
        seen.add(s)
        out.append(s)
    allowed["Supervisor 1"] = sorted(out, key=lambda x: x.casefold())

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
    global latest_build_stats, latest_centre_streets, latest_street_to_cross, latest_allowed_sets

    last_fp = file_fingerprint(MASTER_TRACKER_PATH)

    try:
        with FILE_LOCK:
            stats = build_everything()
        latest_allowed_sets = recompute_allowed_sets_from_master()
        latest_centre_streets = stats.get("centre_streets", [])
        latest_street_to_cross = stats.get("street_to_cross", {})
        latest_build_stats = {
            "status": "Ready",
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

        with FILE_LOCK:
            cur_fp = file_fingerprint(MASTER_TRACKER_PATH)

        if cur_fp != last_fp:
            fp_intake = LAST_MASTER_FP_WRITTEN_BY_INTAKE
            if fp_intake and cur_fp == fp_intake:
                print("[{}] Watcher: master changed but was written by intake. Skipping watcher rebuild.".format(datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
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

    def _safe_int(x):
        try:
            return int(float(str(x).strip()))
        except Exception:
            return 0

    while True:
        time.sleep(INTAKE_POLL_SECONDS)

        # ---------------------------------------------------------
        # FAST PRE-CHECK: if nothing is PENDING (or none eligible yet),
        # skip heavy apply_intake_to_master() + skip rebuild
        # ---------------------------------------------------------
        try:
            with FILE_LOCK:
                if not os.path.exists(INTAKE_PATH):
                    continue
                try:
                    df0 = pd.read_csv(INTAKE_PATH, dtype=str, encoding="utf-8").fillna("")
                except Exception:
                    df0 = pd.read_csv(INTAKE_PATH, dtype=str, encoding="latin-1").fillna("")

            if "__status" not in df0.columns:
                continue

            now_epoch = int(time.time())

            pend = df0[df0["__status"].astype(str).str.upper() == "PENDING"].copy()
            if pend.empty:
                continue

            # eligibility check by pending-until (or submitted time + grace)
            if "__pending_until_epoch" in pend.columns:
                pu = pend["__pending_until_epoch"].apply(_safe_int)
            else:
                pu = pd.Series([0] * len(pend))

            if pu.max() == 0:
                # fallback to submitted epoch if pending-until missing
                if "__submitted_at_epoch" in pend.columns:
                    sub_epoch = pend["__submitted_at_epoch"].apply(_safe_int)
                    pu = sub_epoch + int(PENDING_GRACE_SECONDS)
                elif "__submitted_at" in pend.columns:
                    ts = pd.to_datetime(pend["__submitted_at"], errors="coerce")
                    ts = ts.fillna(pd.Timestamp("1970-01-01"))
                    sub_epoch = (ts.astype("int64") // 10**9).astype(int)
                    pu = sub_epoch + int(PENDING_GRACE_SECONDS)
                else:
                    # no timestamps -> assume eligible (fall through to heavy apply)
                    pu = pd.Series([0] * len(pend))

            # If *all* pending rows are still inside edit window, do nothing this cycle
            if len(pu) and pu.min() > now_epoch:
                continue

        except Exception:
            # If anything goes weird, fall back to normal behavior (do not block apply)
            pass

        # ---------------------------------------------------------
        # HEAVY WORK only when something might apply
        # ---------------------------------------------------------
        try:
            with FILE_LOCK:
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
                latest_street_to_cross = stats.get("street_to_cross", {})
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