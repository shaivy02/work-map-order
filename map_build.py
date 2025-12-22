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

POLL_INTERVAL_SECONDS = 30

MIN_SIM_LOCATION = 0.80
MIN_SIM_CROSS = 0.78

HOST = "127.0.0.1"
PORT = 8008

# ---- Intersection marker settings ----
DRAW_INTERSECTION_POINTS = True
INTERSECTION_POINT_RADIUS = 4
INTERSECTION_POINT_OPACITY = 0.95
INTERSECTION_POINT_FILL_OPACITY = 0.85
INTERSECTION_POINTS_SHOW_BY_DEFAULT = True  # if False, user can toggle layer on

# ---- Segment hover settings ----
DRAW_WO_SEGMENTS = True  # per-intersection-to-intersection mini-segments
SEGMENT_OPACITY = 0.01   # keep visual look the same; still hoverable/clickable
SEGMENT_WEIGHT = 12      # bigger "hit area" so hovering is easy


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
# 3. BUILD EVERYTHING
# =========================================================

def build_everything():
    print("\n" + "=" * 50)
    print(f"BUILD START: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 50)

    # ---------------------------------------------------------
    # Street normalizer
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
    # Core street extraction
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
    # Geometry helpers
    # ---------------------------------------------------------
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

    # Accurate distance along polyline (meters) using haversine
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

    # 2 sig-fig formatting (NO scientific notation)
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

    # intersection_id -> [sum_lon, sum_lat, count]
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

    # ---------------------------------------------------------
    # Load CSVs
    # ---------------------------------------------------------
    print("Loading input files...")
    if not os.path.exists(MASTER_TRACKER_PATH):
        raise FileNotFoundError(f"MASTER_TRACKER_PATH not found: {MASTER_TRACKER_PATH}")
    if not os.path.exists(CENTRELINE_PATH):
        raise FileNotFoundError(f"CENTRELINE_PATH not found: {CENTRELINE_PATH}")

    master = pd.read_csv(MASTER_TRACKER_PATH, encoding="latin-1")
    centre = pd.read_csv(CENTRELINE_PATH, encoding="latin-1")

    print(f"Centreline rows: {len(centre)}")
    print(f"Master tracker rows: {len(master)}")

    # ---------------------------------------------------------
    # Build graph from centreline + build intersection coordinate lookup
    # ---------------------------------------------------------
    street_edges = defaultdict(list)
    street_nodes = defaultdict(set)
    intersection_to_streets = defaultdict(set)  # <-- used to label segment From/To on hover
    bad_geom = 0

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
        edge = {"from": from_id, "to": to_id, "coords": coords, "length": length}
        street_edges[norm_name].append(edge)
        street_nodes[norm_name].update([from_id, to_id])

    print(f"Unique streets in centreline (normalized): {len(street_edges)}")
    print(f"Rows with unusable geometry: {bad_geom}")
    print(f"Intersection coords collected: {len(intersection_accum)}")

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

    TYPE_TOKENS = {
        " STREET", " AVENUE", " ROAD", " BOULEVARD",
        " DRIVE", " LANE", " CRESCENT", " TRAIL",
        " PARKWAY", " HIGHWAY", " COURT", " PLACE",
        " SQUARE", " CIRCLE"
    }

    DEAD_END_TOKENS = {"DEAD END", "DEAD-END", "DEADEND"}

    # Choose a "cross street label" at an intersection, excluding the WO's Location street.
    def pick_cross_street(intersection_id: int, location_street_key: str) -> str:
        try:
            streets = intersection_to_streets.get(int(intersection_id), set())
        except Exception:
            streets = set()
        cands = [s for s in streets if s and s != location_street_key]
        if not cands:
            return ""  # fallback blank
        # pick shortest for readability; tie-break alphabetically
        cands.sort(key=lambda s: (len(s), s))
        return cands[0]

    # ---------------------------------------------------------
    # Styling
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

        return {"color": color, "weight": weight, "opacity": 0.9, "dashArray": dash_array}

    # Invisible-but-hoverable segment style (Option A)
    def style_for_segment(feat):
        props = feat["properties"]
        color = props.get("stroke_color", "red")
        return {
            "color": color,
            "weight": SEGMENT_WEIGHT,
            "opacity": SEGMENT_OPACITY,
            "dashArray": "0",
        }

    # ---------------------------------------------------------
    # Fuzzy resolution
    # ---------------------------------------------------------
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

        return max(endpoints, key=lambda n: dist.get(n, 0.0))

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

    # Per-edge oriented MultiLineString list (one per adjacent-node segment)
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

            segments.append({
                "u": int(u),
                "v": int(v),
                "coords": oriented,
            })
        return segments

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

    # CLICK popup for mini-segment:
    # - From/To are WHOLE WO (props["From"]/props["To"])
    # - Distance is WHOLE WO (props["WO_m_display"]/props["WO_km_display"])
    def build_segment_popup(props: dict) -> str:
        wo_m_str = props.get("WO_m_display", "")
        wo_km_str = props.get("WO_km_display", "")
        sup_html = props.get("Supervisor_link_html", html.escape(str(props.get("Supervisor", ""))))
        shift_html = props.get("Shift_html", html.escape(str(props.get("Shift", ""))))

        return f"""
        <div style="font-family:Arial;font-size:13px;line-height:1.25;">
          <b>WO:</b> {html.escape(str(props.get("WO_ID","")))}<br>
          <b>Segment:</b> {html.escape(str(props.get("Segment_idx","")))}<br>
          <b>Total Segments:</b> {html.escape(str(props.get("Segment_count","")))}<br>
          <b>Location:</b> {html.escape(str(props.get("Location","")))}<br>
          <b>To:</b> {html.escape(str(props.get("To","")))}<br>
          <b>From:</b> {html.escape(str(props.get("From","")))}<br>
          <b>Distance (m):</b> {html.escape(str(wo_m_str))}<br>
          <b>Distance (km):</b> {html.escape(str(wo_km_str))}<br>
          <hr style="margin:6px 0;">
          <b>Supervisor:</b> {sup_html}<br>
          <b>District:</b> {html.escape(str(props.get("District","")))}<br>
          <b>Ward:</b> {html.escape(str(props.get("Ward","")))}<br>
          <b>Date:</b> {html.escape(str(props.get("Date","")))}<br>
          <b>Shift:</b> {shift_html}<br>
          <b>Type:</b> {html.escape(str(props.get("Type","")))}<br>
          <hr style="margin:6px 0;">
          <b>Intersection From:</b> {html.escape(str(props.get("From_Intersection_ID","")))}<br>
          <b>Intersection To:</b> {html.escape(str(props.get("To_Intersection_ID","")))}<br>
        </div>
        """

    # ---------------------------------------------------------
    # Folium base map
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
        Source: MASTER TRACKER(RAW DATA).csv
    </div>
    """
    m.get_root().html.add_child(folium.Element(footer_html))

    # ---------------------------------------------------------
    # Live-refresh JS (SSE)
    # ---------------------------------------------------------
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
    # Google-maps-like FREE search bar (Nominatim via Leaflet-Control-Geocoder)
    # ---------------------------------------------------------
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

    # ---------------------------------------------------------
    # District colors + ONLY ONE map layer ("Work Orders")
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

    work_orders_group = folium.FeatureGroup(name="Work Orders", show=True)
    work_orders_group.add_to(m)

    intersections_group = None
    if DRAW_INTERSECTION_POINTS:
        intersections_group = folium.FeatureGroup(
            name="Intersections",
            show=bool(INTERSECTION_POINTS_SHOW_BY_DEFAULT),
        )
        intersections_group.add_to(m)

    # ---------------------------------------------------------
    # Popup/tooltip config (WO-level popup stays intact)
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

    def add_intersection_points_for_path(
        group_for_points,
        district_color,
        wo_id,
        loc_raw,
        from_raw,
        to_raw,
        node_path
    ):
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

    # Add invisible/hoverable mini-segments for a WO path
    def add_wo_segments(
        street_key,
        node_path,
        edge_indices,
        district_color,
        wo_id,
        loc_raw,
        from_raw,
        to_raw,
        district_val,
        ward,
        date_str,
        shift_str,
        supervisor_raw,
        sup_key,
        work_type,
        supervisor_link_html,
        shift_display_html,
        wo_total_m,
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

            # Segment hover labels: cross streets at the segment's endpoints (exclude the Location street)
            seg_from_label = pick_cross_street(seg["u"], street_key)
            seg_to_label = pick_cross_street(seg["v"], street_key)

            props = {
                "feature_kind": "workorder_segment",

                # WO-level (sheet values)
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

                # segment-level
                "From_Intersection_ID": int(seg["u"]),
                "To_Intersection_ID": int(seg["v"]),
                "Segment_idx": int(idx),
                "Segment_count": int(seg_count),
                "Segment_m": float(seg_m),
                "Segment_km": float(seg_km),

                # display (hover)
                "Segment_m_display": fmt_sigfig(seg_m, 2),
                "Segment_km_display": fmt_sigfig(seg_km, 2),

                # NEW: segment From/To labels for hover (cross streets)
                "Seg_From": str(seg_from_label),
                "Seg_To": str(seg_to_label),

                # NEW: whole WO distance for CLICK popup
                "WO_m": float(wo_total_m),
                "WO_km": float(wo_total_km),
                "WO_m_display": fmt_sigfig(wo_total_m, 2),
                "WO_km_display": fmt_sigfig(wo_total_km, 2),

                # for popup HTML (so supervisor link stays clickable)
                "Supervisor_link_html": supervisor_link_html,
                "Shift_html": shift_display_html,

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

            # HOVER tooltip:
            # - To/From are segment cross-streets (Seg_To / Seg_From)
            # - Distance is segment distance
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

            # CLICK popup uses build_segment_popup() (whole WO distance + whole WO From/To)
            folium.Popup(seg_popup, max_width=420).add_to(seg_gj)

            seg_gj.add_to(work_orders_group)

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
                f"Location not matched to centreline (core='{loc_core}', norm='{loc_norm}', best_score={loc_score:.2f})"
            )
            skipped_records.append(row_dict)
            skipped_count += 1
            continue

        wo_id = str(row.get("WO", ""))

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

        district_val = str(row.get("District\n", "Unknown")).strip() or "Unknown"
        color = get_color_for_district(district_val)

        ward_val = str(row.get("Ward\n", "")).strip()
        date_val = str(row.get("Date\n", "")).strip()
        shift_val = str(row.get("Shift\n", "")).strip()
        type_val = str(row.get("Type (Road Class/ School, Bridge)\n", "")).strip()

        # ------------------ ENTIRE STREET ------------------
        if entire_flag:
            coords_to_use = full_street_multiline(loc_key)
            if not coords_to_use:
                row_dict["skip_reason"] = "Entire Street requested but no geometry found for Location"
                skipped_records.append(row_dict)
                skipped_count += 1
                continue

            subsegment_count += 1
            geometry = {"type": "MultiLineString", "coordinates": coords_to_use}

            popup_html = build_popup_html(row, popup_columns, popup_labels, supervisor_link_html, shift_display_html)

            props = {
                "feature_kind": "workorder_line",
                "WO_ID": wo_id,
                "Location": str(loc_raw),
                "From": str(from_raw),
                "To": str(to_raw),
                "Location_resolved": loc_key,
                "From_resolved": None,
                "To_resolved": None,
                "District": district_val,
                "Ward": ward_val,
                "Date": date_val,
                "Shift": shift_val,
                "Supervisor": str(supervisor_raw).strip(),
                "SupervisorKey": sup_key,
                "Type": type_val,
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
            folium.Popup(popup_html, max_width=350).add_to(gj)
            gj.add_to(work_orders_group)

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

            wo_total_m = multiline_distance_m(coords_to_use)

            subsegment_count += 1
            geometry = {"type": "MultiLineString", "coordinates": coords_to_use}

            popup_html = build_popup_html(row, popup_columns, popup_labels, supervisor_link_html, shift_display_html)

            props = {
                "feature_kind": "workorder_line",
                "WO_ID": wo_id,
                "Location": str(loc_raw),
                "From": str(from_raw),
                "To": str(to_raw),
                "Location_resolved": loc_key,
                "From_resolved": from_key,
                "To_resolved": None,
                "District": district_val,
                "Ward": ward_val,
                "Date": date_val,
                "Shift": shift_val,
                "Supervisor": str(supervisor_raw).strip(),
                "SupervisorKey": sup_key,
                "Type": type_val,
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
            folium.Popup(popup_html, max_width=350).add_to(gj)
            gj.add_to(work_orders_group)

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
                supervisor_link_html=supervisor_link_html,
                shift_display_html=shift_display_html,
                wo_total_m=wo_total_m,
            )

            if DRAW_INTERSECTION_POINTS:
                add_intersection_points_for_path(intersections_group, color, wo_id, loc_raw, from_raw, to_raw, node_path)

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

        wo_total_m = multiline_distance_m(coords_to_use)

        subsegment_count += 1
        geometry = {"type": "MultiLineString", "coordinates": coords_to_use}

        popup_html = build_popup_html(row, popup_columns, popup_labels, supervisor_link_html, shift_display_html)

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
        folium.Popup(popup_html, max_width=350).add_to(gj)
        gj.add_to(work_orders_group)

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
            supervisor_link_html=supervisor_link_html,
            shift_display_html=shift_display_html,
            wo_total_m=wo_total_m,
        )

        if DRAW_INTERSECTION_POINTS:
            add_intersection_points_for_path(intersections_group, color, wo_id, loc_raw, from_raw, to_raw, node_path)

    print(f"Work orders drawn: {subsegment_count}")
    print(f"Work orders skipped: {skipped_count}")

    # ---------------------------------------------------------
    # Legend: district colors only
    # ---------------------------------------------------------
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

    # ---------------------------------------------------------
    # Click on a mini-segment -> flash/highlight the full WO line
    # ---------------------------------------------------------
    highlight_whole_wo_js = f"""
    <script>
      (function() {{
        var map = {m.get_name()};
        if (!map) return;

        function walk(layer, cb) {{
          try {{
            if (!layer) return;
            if (layer.eachLayer) {{
              layer.eachLayer(function(ch) {{ walk(ch, cb); }});
            }}
            cb(layer);
          }} catch (e) {{}}
        }}

        function isFeatureLayer(l) {{
          return l && l.feature && l.feature.properties;
        }}

        var woLines = {{}};

        map.eachLayer(function(root) {{
          walk(root, function(l) {{
            if (!isFeatureLayer(l)) return;
            var p = l.feature.properties || {{}};
            if (p.feature_kind === 'workorder_line' && p.WO_ID) {{
              woLines[String(p.WO_ID)] = l;
            }}
          }});
        }});

        function flashLayer(layer) {{
          if (!layer || !layer.setStyle) return;

          if (layer.__flashTimer) {{
            clearInterval(layer.__flashTimer);
            layer.__flashTimer = null;
          }}
          if (layer.__flashShadow) {{
            try {{
              map.removeLayer(layer.__flashShadow);
            }} catch (e) {{}}
            layer.__flashShadow = null;
          }}

          var orig = {{
            color: layer.options.color,
            weight: layer.options.weight,
            opacity: layer.options.opacity,
            dashArray: layer.options.dashArray,
            lineCap: layer.options.lineCap,
            lineJoin: layer.options.lineJoin
          }};

          try {{
            if (layer.getLatLngs) {{
              var latlngs = layer.getLatLngs();
              var shadow = L.polyline(latlngs, {{
                color: '#FFFF00',
                weight: Math.max((orig.weight || 4) + 14, 18),
                opacity: 0.45,
                dashArray: '0',
                lineCap: 'round',
                lineJoin: 'round',
                interactive: false
              }});
              shadow.addTo(map);
              layer.__flashShadow = shadow;
            }}
          }} catch (e) {{}}

          var on = false;
          var ticks = 0;
          var intervalMs = 120;
          var maxTicks = 20;

          layer.__flashTimer = setInterval(function() {{
            ticks++;

            if (on) {{
              layer.setStyle({{
                weight: Math.max((orig.weight || 4) + 10, 14),
                opacity: 1.0,
                dashArray: '0',
                lineCap: 'round',
                lineJoin: 'round'
              }});
              if (layer.__flashShadow) {{
                layer.__flashShadow.setStyle({{
                  opacity: 0.65,
                  weight: Math.max((orig.weight || 4) + 18, 22)
                }});
              }}
            }} else {{
              layer.setStyle({{
                weight: Math.max((orig.weight || 4) + 2, 6),
                opacity: 0.35,
                dashArray: '10,8',
                lineCap: 'round',
                lineJoin: 'round'
              }});
              if (layer.__flashShadow) {{
                layer.__flashShadow.setStyle({{
                  opacity: 0.25,
                  weight: Math.max((orig.weight || 4) + 12, 16)
                }});
              }}
            }}

            on = !on;

            if (ticks >= maxTicks) {{
              clearInterval(layer.__flashTimer);
              layer.__flashTimer = null;

              try {{ layer.setStyle(orig); }} catch (e) {{}}

              if (layer.__flashShadow) {{
                try {{ map.removeLayer(layer.__flashShadow); }} catch (e) {{}}
                layer.__flashShadow = null;
              }}
            }}
          }}, intervalMs);
        }}

        map.eachLayer(function(root) {{
          walk(root, function(l) {{
            if (!isFeatureLayer(l)) return;
            var p = l.feature.properties || {{}};
            if (p.feature_kind === 'workorder_segment' && p.WO_ID) {{
              if (l.__woClickBound) return;
              l.__woClickBound = true;

              l.on('click', function() {{
                var key = String(p.WO_ID);
                var lineLayer = woLines[key];
                if (lineLayer) {{
                  flashLayer(lineLayer);
                }}
              }});
            }}
          }});
        }});

      }})();
    </script>
    """
    m.get_root().html.add_child(folium.Element(highlight_whole_wo_js))

    folium.LayerControl(collapsed=False).add_to(m)
    m.save(OUTPUT_HTML)
    print(f"Map saved: {OUTPUT_HTML}")

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
# 4. LIVE SERVER + SSE EVENTS
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
# 5. WATCHER THREAD
# =========================================================

def watcher_loop():
    global latest_build_stats

    last_fp = file_fingerprint(MASTER_TRACKER_PATH)

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
        cur_fp = file_fingerprint(MASTER_TRACKER_PATH)

        if cur_fp != last_fp:
            notify_user(
                "Detected change in input data",
                f"Master tracker updated. Rebuilding map...\n{MASTER_TRACKER_PATH}"
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
            print(f"[{datetime.now().strftime('%H:%M:%S')}] No change. Watching... ({MASTER_TRACKER_PATH})")


# =========================================================
# 6. RUN
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
