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
from collections import defaultdict

import pandas as pd
import folium
from folium import plugins

# ---------------------------
# Optional web server (for live updates)
# ---------------------------
try:
    from flask import Flask, Response, send_from_directory, render_template_string
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

# NEW: single XLSX that contains BOTH:
# - Data Input (rows to map)
# - midblocks (centreline source / TCL)
TRACKER_XLSX_PATH = os.path.join(BASE_DIR, "Master Tracker Prototype (new TCL) - JL.xlsx")

DATA_INPUT_SHEET = "Data Input"
MIDBLOCKS_SHEET = "midblocks"

# Outputs folder (served by the web app)
OUTPUT_DIR = os.path.join(BASE_DIR, "outputs_work_orders")
os.makedirs(OUTPUT_DIR, exist_ok=True)

OUTPUT_HTML = os.path.join(OUTPUT_DIR, "work_orders_map.html")
OUTPUT_GEOJSON = os.path.join(OUTPUT_DIR, "work_orders.geojson")
OUTPUT_MAPPED_CSV = os.path.join(OUTPUT_DIR, "master_tracker_mapped.csv")
OUTPUT_SKIPPED_CSV = os.path.join(OUTPUT_DIR, "master_tracker_skipped.csv")

# Check every 30 seconds
POLL_INTERVAL_SECONDS = 30

# Similarity thresholds for fuzzy matching
MIN_SIM_LOCATION = 0.80  # for main Location street
MIN_SIM_CROSS = 0.78     # for From / To streets

# Web server config
HOST = "127.0.0.1"
PORT = 8008


# =========================================================
# 1. NOTIFICATIONS
# =========================================================

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
# 2. FILE FINGERPRINTING (detect updates)
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
    """
    Returns a tuple (mtime_int, size_int, sha256_str) for robust change detection.
    """
    if not os.path.exists(path):
        return ("MISSING", 0, "")
    st = os.stat(path)
    mtime = int(st.st_mtime)
    size = int(st.st_size)
    sha = sha256_of_file(path)
    return (mtime, size, sha)


# =========================================================
# 3. HELPERS: XLSX reading + normalization
# =========================================================

def _find_header_row(df_raw: pd.DataFrame, key="WO", max_scan=25) -> int:
    """
    Some Excel sheets have a title row before the true headers.
    We scan the first N rows and find the row containing the column name 'WO'.
    """
    for i in range(min(max_scan, len(df_raw))):
        row = df_raw.iloc[i].astype(str).str.strip().tolist()
        if any(cell == key for cell in row):
            return i
    return 0


def _normalize_ws_cell(s) -> str:
    if not isinstance(s, str):
        return ""
    return re.sub(r"\s+", " ", s).strip()


def _pick_cross_street(intersection_name: str, location_street: str) -> str:
    """
    Intersection strings often look like:
      'Mount Pleasant Rd / Soudan Ave'
      'Avonlea Blvd / Rosevear Ave / Dentonia Park Trl'

    We want the "other" street given the location street.
    """
    if not isinstance(intersection_name, str):
        return ""
    if not isinstance(location_street, str):
        location_street = ""

    parts = [_normalize_ws_cell(p) for p in intersection_name.split("/") if _normalize_ws_cell(p)]
    if not parts:
        return ""

    loc_u = location_street.upper().strip()

    # Prefer a part that is not the location street (case-insensitive)
    for p in parts:
        if p.upper().strip() != loc_u:
            return p

    # Fallback
    return parts[0]


def load_master_from_data_input(xlsx_path: str, sheet_name: str) -> pd.DataFrame:
    """
    Reads the Data Input worksheet and creates the OLD columns your map logic expects:
      Location, From , To, Supervisor\\n, Shift\\n, Date\\n, District\\n, Ward\\n, Type (Road Class/...)\\n
    """
    if not os.path.exists(xlsx_path):
        raise FileNotFoundError(f"XLSX tracker not found: {xlsx_path}")

    raw = pd.read_excel(xlsx_path, sheet_name=sheet_name, header=None)
    hdr_idx = _find_header_row(raw, key="WO")
    df = pd.read_excel(xlsx_path, sheet_name=sheet_name, header=hdr_idx).dropna(how="all").copy()

    if "Street" not in df.columns:
        raise ValueError("Expected column 'Street' not found in Data Input sheet.")

    # OLD Location <- new Street
    df["Location"] = df["Street"]

    # OLD From/To from closest intersection columns (choose "other" street)
    start_col = "Starting Point Closest Intersection"
    end_col = "Ending Point Closest Intersection"

    if start_col not in df.columns or end_col not in df.columns:
        raise ValueError(
            f"Expected columns '{start_col}' and '{end_col}' not found in Data Input sheet."
        )

    df["From "] = df.apply(lambda r: _pick_cross_street(r.get(start_col, ""), r.get("Street", "")), axis=1)
    df["To"] = df.apply(lambda r: _pick_cross_street(r.get(end_col, ""), r.get("Street", "")), axis=1)

    # Supervisor\\n: combine Supervisor 1/2/3
    sup1 = "Supervisor 1"
    sup2 = "Supervisor 2 (if relevant)"
    sup3 = "Supervisor 3 (if relevant)"
    for c in (sup1, sup2, sup3):
        if c not in df.columns:
            df[c] = ""

    def _combine_sup(row):
        vals = [row.get(sup1, ""), row.get(sup2, ""), row.get(sup3, "")]
        vals = [str(v).strip() for v in vals if str(v).strip() and str(v).strip().lower() != "nan"]
        return ", ".join(vals) if vals else ""

    df["Supervisor\n"] = df.apply(_combine_sup, axis=1)

    # Date\\n
    if "Shift Start Date\n" in df.columns:
        df["Date\n"] = df["Shift Start Date\n"]
    elif "Shift Start Date" in df.columns:
        df["Date\n"] = df["Shift Start Date"]
    else:
        df["Date\n"] = ""

    # Shift\\n (display string)
    start_time = "Shift Start Time\n" if "Shift Start Time\n" in df.columns else "Shift Start Time"
    end_time = "Shift End Time" if "Shift End Time" in df.columns else "Shift End Time\n"

    def _shift_str(row):
        a = row.get(start_time, "")
        b = row.get(end_time, "")
        a = "" if str(a).lower() == "nan" else str(a)
        b = "" if str(b).lower() == "nan" else str(b)
        s = f"{a} - {b}".strip(" -")
        return s

    df["Shift\n"] = df.apply(_shift_str, axis=1)

    # Type column mapping
    new_type = "Type (Winter Road Class/ School, Bridge)\n"
    old_type = "Type (Road Class/ School, Bridge)\n"
    if new_type in df.columns:
        df[old_type] = df[new_type]
    elif old_type not in df.columns:
        df[old_type] = ""

    # Ensure District/Ward match old names
    if "District\n" not in df.columns:
        df["District\n"] = df.get("District", "Unknown")
    if "Ward\n" not in df.columns:
        df["Ward\n"] = df.get("Ward", "")

    return df


# =========================================================
# 4. CENTRELINE FROM MIDBLOCKS (NEW)
# =========================================================

def haversine_m(lat1, lon1, lat2, lon2) -> float:
    """
    Haversine distance in meters.
    """
    R = 6371000.0
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)

    a = math.sin(dphi/2)**2 + math.cos(phi1)*math.cos(phi2)*math.sin(dl/2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))
    return R * c


def build_centreline_from_midblocks(xlsx_path: str, sheet_name: str):
    """
    Builds:
      street_edges: {street_name_norm: [edge,...]}
      street_nodes: {street_name_norm: set(intersection_id,...)}
      street_graphs: {street_name_norm: {"edges":[...], "adj":{node:[(neigh, idx, w),...]}}}
      ALL_CENTRE_STREETS: list of street_name_norm

    Geometry note:
    - 'coordinates' column in the workbook is not usable (shows "[List]").
    - We infer intersection coordinates by averaging midblock midpoints incident to each intersection.
    - Then each midblock edge is drawn as a straight segment between inferred intersection coords.
    """
    df = pd.read_excel(xlsx_path, sheet_name=sheet_name).dropna(how="all").copy()

    required = {"linear_name_full", "from_intersection_id", "to_intersection_id", "lat", "lng"}
    missing = [c for c in required if c not in df.columns]
    if missing:
        raise ValueError(f"midblocks sheet missing required columns: {missing}")

    # Coerce types
    df["linear_name_full"] = df["linear_name_full"].astype(str)
    df["lat"] = pd.to_numeric(df["lat"], errors="coerce")
    df["lng"] = pd.to_numeric(df["lng"], errors="coerce")
    df["from_intersection_id"] = pd.to_numeric(df["from_intersection_id"], errors="coerce")
    df["to_intersection_id"] = pd.to_numeric(df["to_intersection_id"], errors="coerce")

    df = df.dropna(subset=["lat", "lng", "from_intersection_id", "to_intersection_id"]).copy()

    # ---------------------------------------------------------
    # Street name normalizer (same behavior as your original)
    # ---------------------------------------------------------
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

    # ---------------------------------------------------------
    # Infer intersection coordinates
    # ---------------------------------------------------------
    points_by_node = defaultdict(list)

    for _, r in df.iterrows():
        u = int(r["from_intersection_id"])
        v = int(r["to_intersection_id"])
        lat = float(r["lat"])
        lon = float(r["lng"])
        points_by_node[u].append((lat, lon))
        points_by_node[v].append((lat, lon))

    node_coord = {}
    for node, pts in points_by_node.items():
        if not pts:
            continue
        lat_avg = sum(p[0] for p in pts) / len(pts)
        lon_avg = sum(p[1] for p in pts) / len(pts)
        node_coord[node] = (lat_avg, lon_avg)

    # ---------------------------------------------------------
    # Build street edges/nodes
    # ---------------------------------------------------------
    street_edges = defaultdict(list)
    street_nodes = defaultdict(set)

    bad_rows = 0
    for _, r in df.iterrows():
        name_raw = r.get("linear_name_full", "")
        street_key = normalize_street_name(str(name_raw))
        if not street_key:
            bad_rows += 1
            continue

        u = int(r["from_intersection_id"])
        v = int(r["to_intersection_id"])

        if u not in node_coord or v not in node_coord:
            bad_rows += 1
            continue

        lat_u, lon_u = node_coord[u]
        lat_v, lon_v = node_coord[v]

        # Build a simple line segment between inferred endpoints
        coords = [[[lon_u, lat_u], [lon_v, lat_v]]]  # MultiLineString with 1 line
        length = haversine_m(lat_u, lon_u, lat_v, lon_v)

        edge = {"from": u, "to": v, "coords": coords, "length": float(length)}
        street_edges[street_key].append(edge)
        street_nodes[street_key].update([u, v])

    # Build graphs
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

    ALL_CENTRE_STREETS = list(street_nodes.keys())

    print(f"Midblocks rows used: {len(df)}")
    print(f"Unique streets in midblocks (normalized): {len(street_edges)}")
    print(f"Bad/ignored midblock rows: {bad_rows}")
    print(f"Intersection nodes inferred: {len(node_coord)}")

    return street_edges, street_nodes, street_graphs, ALL_CENTRE_STREETS, normalize_street_name


# =========================================================
# 5. YOUR MAP BUILD CODE (wrapped into a build function)
# =========================================================

def build_everything():
    """
    Rebuilds:
    - work_orders_map.html
    - work_orders.geojson
    - master_tracker_mapped.csv
    - master_tracker_skipped.csv
    - per-supervisor pages in OUTPUT_DIR
    """

    print("\n" + "=" * 50)
    print(f"BUILD START: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 50)

    if not os.path.exists(TRACKER_XLSX_PATH):
        raise FileNotFoundError(f"TRACKER_XLSX_PATH not found: {TRACKER_XLSX_PATH}")

    print("Loading Data Input + Midblocks from XLSX...")

    # NEW: master rows from Data Input
    master = load_master_from_data_input(TRACKER_XLSX_PATH, DATA_INPUT_SHEET)

    # NEW: centreline graph from midblocks
    street_edges, street_nodes, street_graphs, ALL_CENTRE_STREETS, normalize_street_name = \
        build_centreline_from_midblocks(TRACKER_XLSX_PATH, MIDBLOCKS_SHEET)

    print(f"Master tracker rows (Data Input): {len(master)}")

    # ---------------------------------------------------------
    # Regex-based extraction of the core street name
    # ---------------------------------------------------------
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

    # ---------------------------------------------------------
    # Styling for features
    # ---------------------------------------------------------
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

        return {
            "color": color,
            "weight": weight,
            "opacity": 0.9,
            "dashArray": dash_array,
        }

    # ---------------------------------------------------------
    # Fuzzy resolution of street names to centreline keys
    # ---------------------------------------------------------
    TYPE_TOKENS = {
        " STREET", " AVENUE", " ROAD", " BOULEVARD",
        " DRIVE", " LANE", " CRESCENT", " TRAIL",
        " PARKWAY", " HIGHWAY", " COURT", " PLACE",
        " SQUARE", " CIRCLE"
    }

    DEAD_END_TOKENS = {"DEAD END", "DEAD-END", "DEADEND"}

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

        best_key = None
        best_score = 0.0

        for cand in ALL_CENTRE_STREETS:
            if not cand:
                continue
            if len(norm_name) > 3 and len(cand) > 3 and cand[0] != norm_name[0]:
                continue

            score = similarity(norm_name, cand)
            if cand.startswith(norm_name) or norm_name.startswith(cand):
                score = max(score, 0.9)

            if score > best_score:
                best_score = score
                best_key = cand

        if best_key is not None and best_score >= min_ratio:
            return best_key, best_score
        else:
            return None, best_score

    # ---------------------------------------------------------
    # Intersection & path helpers
    # ---------------------------------------------------------
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

    def find_farthest_endpoint_node(street_key, start_node):
        g = street_graphs.get(street_key)
        if not g:
            return None

        adj = g["adj"]
        if start_node not in adj:
            return None

        dist = {start_node: 0.0}
        heap = [(0.0, start_node)]

        while heap:
            d, u = heapq.heappop(heap)
            if d > dist[u]:
                continue
            for v, edge_idx, w in adj[u]:
                nd = d + w
                if v not in dist or nd < dist[v]:
                    dist[v] = nd
                    heapq.heappush(heap, (nd, v))

        endpoints = [node for node in dist.keys() if len(adj[node]) == 1 and node != start_node]
        if not endpoints:
            endpoints = [node for node in dist.keys() if node != start_node]
        if not endpoints:
            return None

        far_node = max(endpoints, key=lambda n: dist.get(n, 0.0))
        return far_node

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

    def full_street_multiline(street_key):
        edges = street_edges.get(street_key, [])
        all_coords = []
        for e in edges:
            all_coords.extend(e["coords"])
        return all_coords

    # ---------------------------------------------------------
    # UI helpers
    # ---------------------------------------------------------
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
        return f"<a href='{filename}' target='_blank'>{label}</a>"

    def format_shift_with_icons(shift_raw) -> str:
        s = str(shift_raw)
        return html.escape(s)

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

    # ---------------------------------------------------------
    # Folium map & base layers
    # ---------------------------------------------------------
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
        Source: {os.path.basename(TRACKER_XLSX_PATH)} (Data Input + midblocks)
    </div>
    """
    m.get_root().html.add_child(folium.Element(footer_html))

    legend_html = """
    <div style="
        position: fixed;
        bottom: 20px; left: 10px;
        z-index: 9999;
        background-color: rgba(255, 255, 255, 0.9);
        padding: 8px 10px;
        border-radius: 4px;
        font-size: 12px;
        box-shadow: 0 0 4px rgba(0,0,0,0.3);
    ">
        <b>Legend</b><br>
        Colored lines = District-based work segments<br>
        Thicker lines = Higher road class<br>
        Dashed lines = Bridge segments<br>
        <br>
        <b>Live:</b> This page auto-refreshes when new WOs are detected.
    </div>
    """
    m.get_root().html.add_child(folium.Element(legend_html))

    # --- LIVE AUTO-REFRESH VIA SSE ---
    live_js = """
    <script>
      (function() {
        try {
          var es = new EventSource('/events');
          es.onmessage = function(ev) {
            if (!ev || !ev.data) return;
            if (ev.data === 'updated') {
              console.log('Map updated on server. Reloading...');
              window.location.reload(true);
            }
          };
        } catch (e) {
          console.log('Live updates not available:', e);
        }
      })();
    </script>
    """
    m.get_root().html.add_child(folium.Element(live_js))

    # ---------------------------------------------------------
    # District colors/groups
    # ---------------------------------------------------------
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

    district_groups = {}

    all_wo_group = folium.FeatureGroup(name="All Work Orders (search)", show=False)
    all_wo_group.add_to(m)

    # ---------------------------------------------------------
    # Popup/tooltip config
    # ---------------------------------------------------------
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

    # ---------------------------------------------------------
    # Build geometries
    # ---------------------------------------------------------
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

    print("Adding work orders to map...")

    for _, row in master.iterrows():
        row_dict = row.to_dict()

        loc_raw = row.get("Location", "")
        from_raw = row.get("From ", "")
        to_raw = row.get("To", "")

        loc_core = extract_street_token(loc_raw)
        from_core = extract_street_token(from_raw)
        to_core = extract_street_token(to_raw)

        loc_norm = normalize_street_name(loc_core)
        from_norm = normalize_street_name(from_core)
        to_norm = normalize_street_name(to_core)

        row_dict["Location_core"] = loc_core
        row_dict["From_core"] = from_core
        row_dict["To_core"] = to_core
        row_dict["Location_norm"] = loc_norm
        row_dict["From_norm"] = from_norm
        row_dict["To_norm"] = to_norm

        loc_key, loc_score = resolve_street_name(loc_norm, MIN_SIM_LOCATION)
        if not loc_key:
            row_dict["skip_reason"] = (
                f"Location not matched to midblocks centreline (core='{loc_core}', norm='{loc_norm}', best_score={loc_score:.2f})"
            )
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        supervisor_raw = row.get("Supervisor\n", "")
        sup_key = make_supervisor_key(supervisor_raw)
        supervisor_link_html = make_supervisor_link(supervisor_raw, sup_key)
        shift_display_html = format_shift_with_icons(row.get("Shift\n", ""))

        row_dict["SupervisorKey"] = sup_key

        from_is_str = isinstance(from_raw, str)
        to_is_str = isinstance(to_raw, str)
        entire_flag = (
            (from_is_str and "ENTIRE STREET" in from_raw.upper())
            or (to_is_str and "ENTIRE STREET" in to_raw.upper())
        )

        # ------------------ ENTIRE STREET ------------------
        if entire_flag:
            coords_to_use = full_street_multiline(loc_key)
            if not coords_to_use:
                row_dict["skip_reason"] = "Entire Street requested but no geometry found for Location (midblocks)"
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            subsegment_count += 1
            district_val = str(row.get("District\n", "Unknown")).strip() or "Unknown"
            color = get_color_for_district(district_val)
            geometry = {"type": "MultiLineString", "coordinates": coords_to_use}

            popup_html = build_popup_html(
                row, popup_columns, popup_labels, supervisor_link_html, shift_display_html
            )

            props = {
                "WO_ID": str(row.get("WO", "")),
                "Location": str(loc_raw),
                "From": str(from_raw),
                "To": str(to_raw),
                "Location_resolved": loc_key,
                "From_resolved": None,
                "To_resolved": None,
                "District": district_val,
                "Ward": str(row.get("Ward\n", "")).strip(),
                "Date": str(row.get("Date\n", "")).strip(),
                "Shift": str(row.get("Shift\n", "")).strip(),
                "Supervisor": str(supervisor_raw).strip(),
                "SupervisorKey": sup_key,
                "Type": str(row.get("Type (Road Class/ School, Bridge)\n", "")).strip(),
                "stroke_color": color,
            }

            feature = {"type": "Feature", "geometry": geometry, "properties": props}
            geojson_features.append(feature)

            row_dict["Location_resolved"] = loc_key
            row_dict["From_resolved"] = None
            row_dict["To_resolved"] = None
            row_dict["geometry_geojson"] = json.dumps(geometry)
            mapped_records.append(row_dict)
            supervisor_rows[sup_key].append(row_dict)

            if district_val not in district_groups:
                fg = folium.FeatureGroup(name=f"District: {district_val}", show=True)
                fg.add_to(m)
                district_groups[district_val] = fg
            group = district_groups[district_val]

            gj = folium.GeoJson(
                data=feature,
                style_function=style_for_feature,
                highlight_function=lambda feat: {
                    "color": feat["properties"].get("stroke_color", "red"),
                    "weight": 7,
                    "opacity": 1.0,
                },
                name=f"WO {props['WO_ID']}",
            )

            tooltip = folium.GeoJsonTooltip(
                fields=["WO_ID", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
                aliases=["WO", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
                sticky=False,
            )
            tooltip.add_to(gj)
            folium.Popup(popup_html, max_width=350).add_to(gj)
            gj.add_to(group)
            gj.add_to(all_wo_group)

            continue

        # ------------------ DEAD END ------------------
        to_is_dead_end = is_dead_end(to_raw, to_norm)

        if not from_norm and not to_norm:
            row_dict["skip_reason"] = (
                f"Missing usable From/To after extraction (From_raw='{from_raw}', To_raw='{to_raw}')"
            )
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        if to_is_dead_end and from_norm:
            from_key, from_score = resolve_street_name(from_norm, MIN_SIM_CROSS)
            if not from_key:
                row_dict["skip_reason"] = (
                    f"From street (before DEAD END) not matched (From_core='{from_core}', norm='{from_norm}', score={from_score:.2f})"
                )
                row_dict["Location_resolved"] = loc_key
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            start_node = find_intersection_node(loc_key, from_key)
            if start_node is None:
                row_dict["skip_reason"] = f"Could not find intersection node (Location='{loc_key}', From='{from_key}')"
                row_dict["Location_resolved"] = loc_key
                row_dict["From_resolved"] = from_key
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            end_node = find_farthest_endpoint_node(loc_key, start_node)
            if end_node is None or end_node == start_node:
                row_dict["skip_reason"] = f"Could not find far endpoint for DEAD END (Location='{loc_key}', From='{from_key}')"
                row_dict["Location_resolved"] = loc_key
                row_dict["From_resolved"] = from_key
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            path = shortest_path_for_street(loc_key, start_node, end_node)
            if path is None:
                row_dict["skip_reason"] = f"No path for DEAD END (Location='{loc_key}', From='{from_key}')"
                row_dict["Location_resolved"] = loc_key
                row_dict["From_resolved"] = from_key
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            node_path, edge_indices = path
            coords_to_use = build_path_multiline(loc_key, node_path, edge_indices)
            if not coords_to_use:
                row_dict["skip_reason"] = "Empty geometry after path building (DEAD END)"
                row_dict["Location_resolved"] = loc_key
                row_dict["From_resolved"] = from_key
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            subsegment_count += 1
            district_val = str(row.get("District\n", "Unknown")).strip() or "Unknown"
            color = get_color_for_district(district_val)
            geometry = {"type": "MultiLineString", "coordinates": coords_to_use}

            popup_html = build_popup_html(
                row, popup_columns, popup_labels, supervisor_link_html, shift_display_html
            )

            props = {
                "WO_ID": str(row.get("WO", "")),
                "Location": str(loc_raw),
                "From": str(from_raw),
                "To": str(to_raw),
                "Location_resolved": loc_key,
                "From_resolved": from_key,
                "To_resolved": None,
                "District": district_val,
                "Ward": str(row.get("Ward\n", "")).strip(),
                "Date": str(row.get("Date\n", "")).strip(),
                "Shift": str(row.get("Shift\n", "")).strip(),
                "Supervisor": str(supervisor_raw).strip(),
                "SupervisorKey": sup_key,
                "Type": str(row.get("Type (Road Class/ School, Bridge)\n", "")).strip(),
                "stroke_color": color,
            }

            feature = {"type": "Feature", "geometry": geometry, "properties": props}
            geojson_features.append(feature)

            row_dict["Location_resolved"] = loc_key
            row_dict["From_resolved"] = from_key
            row_dict["To_resolved"] = None
            row_dict["geometry_geojson"] = json.dumps(geometry)
            mapped_records.append(row_dict)
            supervisor_rows[sup_key].append(row_dict)

            if district_val not in district_groups:
                fg = folium.FeatureGroup(name=f"District: {district_val}", show=True)
                fg.add_to(m)
                district_groups[district_val] = fg
            group = district_groups[district_val]

            gj = folium.GeoJson(
                data=feature,
                style_function=style_for_feature,
                highlight_function=lambda feat: {
                    "color": feat["properties"].get("stroke_color", "red"),
                    "weight": 7,
                    "opacity": 1.0,
                },
                name=f"WO {props['WO_ID']}",
            )

            tooltip = folium.GeoJsonTooltip(
                fields=["WO_ID", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
                aliases=["WO", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
                sticky=False,
            )
            tooltip.add_to(gj)
            folium.Popup(popup_html, max_width=350).add_to(gj)
            gj.add_to(group)
            gj.add_to(all_wo_group)

            continue

        # ------------------ NORMAL FROM/TO ------------------
        if not from_norm or not to_norm:
            row_dict["skip_reason"] = (
                f"Missing usable From/To after extraction (From_raw='{from_raw}', To_raw='{to_raw}')"
            )
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        from_key, from_score = resolve_street_name(from_norm, MIN_SIM_CROSS)
        to_key, to_score = resolve_street_name(to_norm, MIN_SIM_CROSS)

        if not from_key or not to_key:
            row_dict["skip_reason"] = (
                f"From/To not matched (From='{from_norm}', score={from_score:.2f}; To='{to_norm}', score={to_score:.2f})"
            )
            row_dict["Location_resolved"] = loc_key
            row_dict["From_resolved"] = from_key
            row_dict["To_resolved"] = to_key
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        start_node = find_intersection_node(loc_key, from_key)
        end_node = find_intersection_node(loc_key, to_key)

        if start_node is None or end_node is None or start_node == end_node:
            row_dict["skip_reason"] = (
                f"Could not find both intersection nodes (Location='{loc_key}', From='{from_key}', To='{to_key}')"
            )
            row_dict["Location_resolved"] = loc_key
            row_dict["From_resolved"] = from_key
            row_dict["To_resolved"] = to_key
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        path = shortest_path_for_street(loc_key, start_node, end_node)
        if path is None:
            row_dict["skip_reason"] = (
                f"No path along Location between nodes (Location='{loc_key}', From='{from_key}', To='{to_key}')"
            )
            row_dict["Location_resolved"] = loc_key
            row_dict["From_resolved"] = from_key
            row_dict["To_resolved"] = to_key
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        node_path, edge_indices = path
        coords_to_use = build_path_multiline(loc_key, node_path, edge_indices)
        if not coords_to_use:
            row_dict["skip_reason"] = "Empty geometry after path building"
            row_dict["Location_resolved"] = loc_key
            row_dict["From_resolved"] = from_key
            row_dict["To_resolved"] = to_key
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        subsegment_count += 1
        district_val = str(row.get("District\n", "Unknown")).strip() or "Unknown"
        color = get_color_for_district(district_val)
        geometry = {"type": "MultiLineString", "coordinates": coords_to_use}

        popup_html = build_popup_html(
            row, popup_columns, popup_labels, supervisor_link_html, shift_display_html
        )

        props = {
            "WO_ID": str(row.get("WO", "")),
            "Location": str(loc_raw),
            "From": str(from_raw),
            "To": str(to_raw),
            "Location_resolved": loc_key,
            "From_resolved": from_key,
            "To_resolved": to_key,
            "District": district_val,
            "Ward": str(row.get("Ward\n", "")).strip(),
            "Date": str(row.get("Date\n", "")).strip(),
            "Shift": str(row.get("Shift\n", "")).strip(),
            "Supervisor": str(supervisor_raw).strip(),
            "SupervisorKey": sup_key,
            "Type": str(row.get("Type (Road Class/ School, Bridge)\n", "")).strip(),
            "stroke_color": color,
        }

        feature = {"type": "Feature", "geometry": geometry, "properties": props}
        geojson_features.append(feature)

        row_dict["Location_resolved"] = loc_key
        row_dict["From_resolved"] = from_key
        row_dict["To_resolved"] = to_key
        row_dict["SupervisorKey"] = sup_key
        row_dict["geometry_geojson"] = json.dumps(geometry)
        mapped_records.append(row_dict)
        supervisor_rows[sup_key].append(row_dict)

        if district_val not in district_groups:
            fg = folium.FeatureGroup(name=f"District: {district_val}", show=True)
            fg.add_to(m)
            district_groups[district_val] = fg
        group = district_groups[district_val]

        gj = folium.GeoJson(
            data=feature,
            style_function=style_for_feature,
            highlight_function=lambda feat: {
                "color": feat["properties"].get("stroke_color", "red"),
                "weight": 7,
                "opacity": 1.0,
            },
            name=f"WO {props['WO_ID']}",
        )

        tooltip = folium.GeoJsonTooltip(
            fields=["WO_ID", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
            aliases=["WO", "Location", "From", "To", "District", "Supervisor", "Date", "Shift"],
            sticky=False,
        )
        tooltip.add_to(gj)
        folium.Popup(popup_html, max_width=350).add_to(gj)
        gj.add_to(group)
        gj.add_to(all_wo_group)

    # Search control
    plugins.Search(
        layer=all_wo_group,
        search_label="WO_ID",
        placeholder="Search WO ID...",
        collapsed=False,
    ).add_to(m)

    # Export map
    print(f"Work orders drawn: {subsegment_count}")
    print(f"Work orders skipped: {skipped_count}")

    folium.LayerControl(collapsed=False).add_to(m)
    m.save(OUTPUT_HTML)
    print(f"Map saved: {OUTPUT_HTML}")

    # Export GeoJSON/CSVs
    if geojson_features:
        feature_collection = {"type": "FeatureCollection", "features": geojson_features}
        with open(OUTPUT_GEOJSON, "w", encoding="utf-8") as f:
            json.dump(feature_collection, f)
        print(f"GeoJSON saved: {OUTPUT_GEOJSON}")

    if mapped_records:
        pd.DataFrame(mapped_records).to_csv(OUTPUT_MAPPED_CSV, index=False)
        print(f"Mapped CSV saved: {OUTPUT_MAPPED_CSV}")

    if skipped_records:
        pd.DataFrame(skipped_records).to_csv(OUTPUT_SKIPPED_CSV, index=False)
        print(f"Skipped CSV saved: {OUTPUT_SKIPPED_CSV}")

    # Supervisor pages
    def write_supervisor_page(sup_key: str, rows_for_sup):
        if not sup_key or not rows_for_sup:
            return

        filename = os.path.join(OUTPUT_DIR, f"supervisor_{sup_key}.html")

        sup_name = rows_for_sup[0].get("Supervisor\n", "") or rows_for_sup[0].get("Supervisor", "")
        sup_name = html.escape(str(sup_name))

        header_cols = ["WO", "Date\n", "District\n", "Location", "From ", "To",
                       "Shift\n", "Type (Road Class/ School, Bridge)\n"]
        header_labels = [c.replace("\n", " ").strip() for c in header_cols]

        rows_html = []
        for r in rows_for_sup:
            cells = []
            for c in header_cols:
                val = r.get(c, "")
                cells.append(f"<td>{html.escape(str(val))}</td>")
            rows_html.append("<tr>" + "".join(cells) + "</tr>")

        html_doc = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Work Orders - {sup_name}</title>
<style>
body {{
    font-family: Arial, sans-serif;
    margin: 20px;
}}
table {{
    border-collapse: collapse;
    width: 100%;
}}
th, td {{
    border: 1px solid #ccc;
    padding: 4px 6px;
    font-size: 13px;
}}
th {{
    background-color: #f0f0f0;
}}
</style>
</head>
<body>
<h2>Work Orders for Supervisor: {sup_name}</h2>
<p><a href="work_orders_map.html">← Back to map</a></p>
<table>
<thead>
<tr>{"".join(f"<th>{html.escape(str(lbl))}</th>" for lbl in header_labels)}</tr>
</thead>
<tbody>
{"".join(rows_html)}
</tbody>
</table>
</body>
</html>
"""
        with open(filename, "w", encoding="utf-8") as f:
            f.write(html_doc)

    for sup_key, rows_for_sup in supervisor_rows.items():
        write_supervisor_page(sup_key, rows_for_sup)

    print(f"BUILD DONE: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    return {
        "master_rows": int(len(master)),
        "drawn": int(subsegment_count),
        "skipped": int(skipped_count),
    }


# =========================================================
# 6. LIVE SERVER + SSE EVENTS (unchanged)
# =========================================================

app = Flask(__name__)
events = Queue()
latest_build_stats = {"status": "not built yet"}

INDEX_HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Live Work Orders Map</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 16px; }
    .card { border: 1px solid #ddd; border-radius: 8px; padding: 12px; margin-bottom: 12px; }
    code { background: #f6f6f6; padding: 2px 5px; border-radius: 4px; }
  </style>
</head>
<body>
  <div class="card">
    <h2>Live Work Orders Map</h2>
    <p><b>Status:</b> {{ status }}</p>
    <p><b>Last build:</b> {{ last_build }}</p>
    <p><b>Master rows:</b> {{ master_rows }} | <b>Drawn:</b> {{ drawn }} | <b>Skipped:</b> {{ skipped }}</p>
    <p>
      Open map: <a href="/outputs/work_orders_map.html">work_orders_map.html</a>
    </p>
    <p style="color:#555;">
      This page is live. When new WOs are detected, the map will rebuild and auto-refresh.
    </p>
  </div>

  <div class="card">
    <h3>Outputs</h3>
    <ul>
      <li><a href="/outputs/work_orders.geojson">work_orders.geojson</a></li>
      <li><a href="/outputs/master_tracker_mapped.csv">master_tracker_mapped.csv</a></li>
      <li><a href="/outputs/master_tracker_skipped.csv">master_tracker_skipped.csv</a></li>
    </ul>
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
# 7. WATCHER THREAD (keeps your automation)
# =========================================================

def watcher_loop():
    global latest_build_stats

    # Watch the XLSX (Data Input + midblocks are inside)
    last_fp = file_fingerprint(TRACKER_XLSX_PATH)

    # Build once at startup
    try:
        stats = build_everything()
        latest_build_stats = {
            "status": "ready",
            "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            **stats,
        }
        events.put("updated")
    except Exception as e:
        latest_build_stats = {
            "status": f"build error: {e}",
            "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        notify_user("Build failed", str(e))

    while True:
        time.sleep(POLL_INTERVAL_SECONDS)

        cur_fp = file_fingerprint(TRACKER_XLSX_PATH)

        if cur_fp != last_fp:
            notify_user(
                "Detected change in input data",
                f"Tracker XLSX updated. Rebuilding map...\n{TRACKER_XLSX_PATH}"
            )
            try:
                stats = build_everything()
                latest_build_stats = {
                    "status": "ready",
                    "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    **stats,
                }
                events.put("updated")

                notify_user(
                    "Map updated ✅",
                    f"New tracker detected and map rebuilt.\nDrawn: {stats.get('drawn')} | Skipped: {stats.get('skipped')}",
                )
            except Exception as e:
                latest_build_stats = {
                    "status": f"build error: {e}",
                    "last_build": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                }
                notify_user("Build failed", str(e))

            last_fp = cur_fp
        else:
            print(f"[{datetime.now().strftime('%H:%M:%S')}] No change. Watching... ({TRACKER_XLSX_PATH})")


# =========================================================
# 8. RUN
# =========================================================

def main():
    t = threading.Thread(target=watcher_loop, daemon=True)
    t.start()

    print(f"\nLocal server running at: http://{HOST}:{PORT}/")
    print(f"Map URL: http://{HOST}:{PORT}/outputs/work_orders_map.html")
    print(f"(Serving folder: {OUTPUT_DIR})\n")

    app.run(host=HOST, port=PORT, debug=False, use_reloader=False)

if __name__ == "__main__":
    main()
