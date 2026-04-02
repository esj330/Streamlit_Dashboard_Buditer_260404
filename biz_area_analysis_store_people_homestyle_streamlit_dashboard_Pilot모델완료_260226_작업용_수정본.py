# -*- coding: utf-8 -*-
"""
Streamlit 상권 분석 대시보드 (공공데이터포털 SmallShop + SGIS 경계 + 지도)

업데이트(v2.1):
1) 키 입력 보안 강화: UI 마스킹 + 캐시 키에 원문 키를 남기지 않도록 Fingerprint(해시) 사용
2) 중심지(여러 개) 입력 UX 개선:
   - 행 추가(+) / 선택 삭제(-) 버튼 제공 (하단 자동 행추가 바 제거)
   - 스크롤/바로 인한 오작동 완화(num_rows="fixed")
   - 좌표 칼럼을 텍스트 입력으로 변경(숫자 입력 2번 필요 현상 완화)
   - 주소 입력: 자동(도로명→지번), 도로명, 지번 선택 지원
3) 반경별 총 점수 비교: '누적'이 아닌 위치 간 직접 비교가 쉬운 차트(반경 선택 비교 + 그룹형 막대)로 변경

실행:
  pip install -r requirements_streamlit_store_dashboard.txt
  streamlit run streamlit_store_dashboard_v2_multi_centers.py

참고:
- pydeck는 보통 streamlit 설치에 포함되어 있으나, 환경에 따라 누락될 수 있습니다.
  누락 시: pip install pydeck
"""
import os
import re
import math
import json
import hashlib
import urllib.parse
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import numpy as np
import pandas as pd
import requests
import streamlit as st

from pyproj import Transformer
import geopandas as gpd
from shapely.geometry import shape, Point

# Folium (옵션)
import folium
from folium.features import GeoJson
from folium.plugins import HeatMap, Fullscreen
from streamlit_folium import st_folium

# Pydeck (추천 지도)
try:
    import pydeck as pdk
    HAS_PYDECK = True
except Exception:
    HAS_PYDECK = False

# Altair (차트)
try:
    import altair as alt
    HAS_ALTAIR = True
except Exception:
    HAS_ALTAIR = False

# -------------------------
# 상수 (원본과 동일)
# -------------------------
PI_APPROX = 3.14159
DIST_DECAY_M = 345.0
TOLERANCE_M = 10.0

# -------------------------
# Optional: PublicDataReader
# -------------------------
try:
    from PublicDataReader import SmallShop  # pip install PublicDataReader
    HAS_PUBLICDATAREADER = True
except Exception:
    HAS_PUBLICDATAREADER = False



# -------------------------
# CSV 다운로드용 bytes (Excel 한글 깨짐 방지: UTF-8 BOM 포함)
# -------------------------
def df_to_csv_bytes(df: "pd.DataFrame") -> bytes:
    # pandas.to_csv가 문자열을 반환할 때 encoding 인자는 무시되므로,
    # 반드시 bytes로 직접 인코딩해서 BOM(utf-8-sig)을 포함시킵니다.
    return df.to_csv(index=False).encode("utf-8-sig")

# -------------------------
# secrets / env 안전 접근 (secrets.toml 없을 때 StreamlitSecretNotFoundError 방지)
# -------------------------
def get_secret_or_env(key: str, default: str = "") -> str:
    try:
        return str(st.secrets.get(key, os.getenv(key, default)))
    except Exception:
        return str(os.getenv(key, default))


# -------------------------
# 보안/표시 유틸
# -------------------------
def _fingerprint(s: str, n: int = 12) -> str:
    """원문 키를 캐시 키로 쓰지 않기 위한 짧은 fingerprint(비가역 해시)."""
    if not s:
        return ""
    h = hashlib.sha256(str(s).encode("utf-8")).hexdigest()
    return h[:n]

def _redact_text(text: str, secrets: List[str]) -> str:
    """에러/경고 출력에서 키/토큰이 노출되지 않도록 마스킹."""
    t = str(text or "")
    for s in secrets:
        if s:
            t = t.replace(s, "****")
    # URL/query param 패턴 마스킹 (혹시 에러 메시지에 포함될 경우 대비)
    t = re.sub(r"(key=)[^&\s]+", r"\1****", t, flags=re.IGNORECASE)
    t = re.sub(r"(consumer_key=)[^&\s]+", r"\1****", t, flags=re.IGNORECASE)
    t = re.sub(r"(consumer_secret=)[^&\s]+", r"\1****", t, flags=re.IGNORECASE)
    t = re.sub(r"(accessToken=)[^&\s]+", r"\1****", t, flags=re.IGNORECASE)
    return t


# -------------------------
# 유틸
# -------------------------
def _safe_float(x, default=None):
    try:
        return float(x)
    except Exception:
        return default

def _split_csv_list(s: str) -> List[str]:
    return [t.strip() for t in (s or "").split(",") if t.strip()]


# -------------------------
# (추가) Big Data 분석용: mainbiz_mix_table_AFTER_auto_최종결과물 업로드/매핑
# -------------------------
def _read_mix_table(uploaded_file) -> pd.DataFrame:
    """업로드된 파일(xlsx/xls/csv)을 DataFrame으로 읽어 반환합니다."""
    if uploaded_file is None:
        return pd.DataFrame()

    # streamlit UploadedFile 또는 경로 문자열 모두 지원
    name = getattr(uploaded_file, "name", "") or str(uploaded_file)
    ext = os.path.splitext(name)[1].lower()

    try:
        if ext in (".xlsx", ".xls"):
            df = pd.read_excel(uploaded_file)
        else:
            # csv는 인코딩 이슈가 잦아 utf-8-sig → utf-8 → cp949 순으로 시도
            try:
                df = pd.read_csv(uploaded_file, encoding="utf-8-sig")
            except Exception:
                try:
                    df = pd.read_csv(uploaded_file, encoding="utf-8")
                except Exception:
                    df = pd.read_csv(uploaded_file, encoding="cp949")
    except Exception:
        return pd.DataFrame()

    if df is None:
        return pd.DataFrame()

    # 컬럼명 정리
    df.columns = [str(c).strip() for c in df.columns]
    return df


def _parse_sido_sigg_from_address(address: str) -> Tuple[Optional[str], Optional[str]]:
    """주소 문자열에서 (시도명, 시군구명)을 단순 추출합니다. (정확도는 주소 품질에 따라 달라질 수 있음)"""
    addr = str(address or "").strip()
    if not addr:
        return None, None
    # 괄호/쉼표 등 제거 후 공백 분리
    addr = re.sub(r"[\(\)\[\],]", " ", addr)
    toks = [t for t in re.split(r"\s+", addr) if t]
    if len(toks) < 2:
        return None, None
    sido = toks[0]
    sigg = toks[1]
    # '서울', '경기' 같은 축약형은 데이터와 불일치 가능 → 그대로 두되, 필요시 사용자가 주소를 보정하도록 안내
    return sido, sigg


def _build_mix_candidates_for_center(mix_df: pd.DataFrame, sido: str, sigg: str) -> pd.DataFrame:
    """(시도명, 시군구명)으로 mainbiz mix table 후보를 필터링합니다."""
    if mix_df is None or mix_df.empty:
        return pd.DataFrame()
    if not sido or not sigg:
        return pd.DataFrame()

    df = mix_df.copy()
    # 필수 컬럼 확인
    required = ["시도명", "시군구명", "상권명", "mix_type_topgap_v2"]
    if not all(c in df.columns for c in required):
        return pd.DataFrame()

    df = df[df["시도명"].astype(str).str.strip().eq(str(sido).strip())]
    df = df[df["시군구명"].astype(str).str.strip().eq(str(sigg).strip())]
    if df.empty:
        return pd.DataFrame()

    out = df[["시도명", "시군구명", "상권명", "mix_type_topgap_v2"]].copy()
    out.insert(0, "select", False)
    return out.reset_index(drop=True)


def parse_scls_weight_map(weight_str: str, scls_list: List[str]) -> Dict[str, float]:
    """
    - "카페=+3, 편의점=+1, 세탁소=-2" 또는 "3,1,-2" 지원
    """
    scls_list = [str(x).strip() for x in (scls_list or []) if str(x).strip()]
    weight_str = (weight_str or "").strip()
    wmap = {c: 0.0 for c in scls_list}
    if not scls_list or not weight_str:
        return wmap

    if ("=" in weight_str) or (":" in weight_str):
        parts = re.split(r"[,\n]+", weight_str)
        for p in parts:
            p = p.strip()
            if not p:
                continue
            if "=" in p:
                k, v = p.split("=", 1)
            else:
                k, v = p.split(":", 1)
            k = k.strip()
            v = v.strip()
            try:
                w = float(v)
            except Exception:
                continue
            if k in wmap:
                wmap[k] = w
        return wmap

    nums = [t.strip() for t in re.split(r"[,\s]+", weight_str) if t.strip()]
    parsed = []
    for t in nums:
        try:
            parsed.append(float(t))
        except Exception:
            parsed.append(0.0)
    for i, c in enumerate(scls_list):
        wmap[c] = parsed[i] if i < len(parsed) else 0.0
    return wmap


def parse_kv_weight_map(text: str, default_map: Dict[str, float], aliases: Optional[Dict[str, str]] = None) -> Dict[str, float]:
    """
    간단한 key=value 가중치 파서.
    - 줄/쉼표 구분: 20s=2, 30s=1.5 ...
    - aliases: {"20대":"20s"} 처럼 입력 키를 내부키로 매핑
    """
    out = dict(default_map or {})
    txt = (text or "").strip()
    if not txt:
        return out
    aliases = aliases or {}

    parts = re.split(r"[,\n]+", txt)
    for p in parts:
        p = p.strip()
        if not p:
            continue
        if "=" not in p and ":" not in p:
            continue
        k, v = re.split(r"[=:]", p, maxsplit=1)
        k = str(k).strip()
        k = aliases.get(k, k)
        try:
            w = float(str(v).strip())
        except Exception:
            continue
        if k in out:
            out[k] = w
    return out


def build_category_color_map(category_values: List[str]) -> Dict[str, Tuple[int, int, int, int]]:
    """
    - 카페/편의점/세탁소/코인빨래방 고정색
    - 그 외는 팔레트 순환
    """
    fixed = {
        "카페": (230, 57, 70, 235),
        "편의점": (0, 0, 0, 235),
        "세탁소": (69, 123, 157, 235),
        "코인빨래방": (16, 185, 129, 235),
    }
    palette = [
        (29, 53, 87, 235),
        (255, 183, 3, 235),
        (168, 85, 247, 235),
        (0, 172, 193, 235),
        (255, 87, 34, 235),
        (124, 179, 66, 235),
        (141, 110, 99, 235),
        (236, 72, 153, 235),
        (20, 184, 166, 235),
        (132, 204, 22, 235),
    ]
    fixed_colors = set(fixed.values())

    def _match_fixed(v: str):
        vn = (v or "").replace(" ", "")
        if ("코인" in vn) and (("빨래" in vn) or ("세탁" in vn)):
            return "코인빨래방"
        if "세탁소" in vn:
            return "세탁소"
        if "편의점" in vn:
            return "편의점"
        if "카페" in vn:
            return "카페"
        return None

    color_map = {}
    p_idx = 0
    for val in category_values:
        v = str(val)
        key = _match_fixed(v)
        if key:
            color_map[v] = fixed[key]
            continue
        assigned = None
        for _ in range(len(palette)):
            c = palette[p_idx % len(palette)]
            p_idx += 1
            if (c not in fixed_colors) and (c not in set(color_map.values())):
                assigned = c
                break
        if assigned is None:
            assigned = palette[p_idx % len(palette)]
            p_idx += 1
        color_map[v] = assigned
    return color_map


# -------------------------
# 좌표계/거리
# -------------------------
_T_4326_to_3857 = Transformer.from_crs("EPSG:4326", "EPSG:3857", always_xy=True)
_T_3857_to_4326 = Transformer.from_crs("EPSG:3857", "EPSG:4326", always_xy=True)
_T_4326_to_5179 = Transformer.from_crs("EPSG:4326", "EPSG:5179", always_xy=True)
_T_5179_to_4326 = Transformer.from_crs("EPSG:5179", "EPSG:4326", always_xy=True)

def dist_m_4326(lon1, lat1, lon2, lat2) -> float:
    x1, y1 = _T_4326_to_3857.transform(lon1, lat1)
    x2, y2 = _T_4326_to_3857.transform(lon2, lat2)
    return float(math.hypot(x1 - x2, y1 - y2))

def make_circle_path_lonlat(center_lon: float, center_lat: float, radius_m: float, n: int = 96) -> List[List[float]]:
    """
    EPSG:3857에서 원을 만들고 EPSG:4326로 되돌려 path(경로)로 반환
    pydeck PathLayer용
    """
    cx, cy = _T_4326_to_3857.transform(center_lon, center_lat)
    pts = []
    for i in range(n + 1):
        ang = 2.0 * math.pi * (i / n)
        x = cx + radius_m * math.cos(ang)
        y = cy + radius_m * math.sin(ang)
        lon, lat = _T_3857_to_4326.transform(x, y)
        pts.append([float(lon), float(lat)])
    return pts


# -------------------------
# VWorld 지오코딩
# -------------------------
def geocode_vworld(address: str, vworld_key: str, addr_type: str = "ROAD", timeout=12) -> Optional[Tuple[float, float]]:
    if not address or not vworld_key:
        return None
    url = "https://api.vworld.kr/req/address"
    params = {
        "service": "address",
        "request": "getCoord",
        "version": "2.0",
        "format": "json",
        "key": vworld_key,
        "type": addr_type,   # "ROAD" or "PARCEL"
        "address": address,
        "refine": "true",
        "simple": "false",
    }
    r = requests.get(url, params=params, timeout=timeout)
    r.raise_for_status()
    data = r.json() or {}
    resp = data.get("response") or {}
    result = resp.get("result") or {}
    point = result.get("point") or {}
    x = point.get("x"); y = point.get("y")
    if x is None or y is None:
        return None
    return float(x), float(y)


# -------------------------
# SGIS 토큰/경계 (캐시 키에는 Fingerprint만 사용)
# -------------------------
@st.cache_data(ttl=60 * 60, show_spinner=False)
def fetch_sgis_token(sgis_key_fp: str, sgis_secret_fp: str) -> Optional[str]:
    consumer_key = st.session_state.get("_rt_sgis_key", "") or ""
    consumer_secret = st.session_state.get("_rt_sgis_secret", "") or ""
    if not consumer_key or not consumer_secret:
        return None

    urls = [
        "https://sgisapi.mods.go.kr/OpenAPI3/auth/authentication.json",
        "https://sgisapi.kostat.go.kr/OpenAPI3/auth/authentication.json",
    ]
    params = {"consumer_key": consumer_key, "consumer_secret": consumer_secret}
    for url in urls:
        try:
            r = requests.get(url, params=params, timeout=10)
            r.raise_for_status()
            data = r.json() or {}
            if data.get("errCd", -1) == 0:
                token = (data.get("result") or {}).get("accessToken")
                if token:
                    return token
        except Exception:
            continue
    return None

@st.cache_data(ttl=60 * 10, show_spinner=False)
def fetch_sgis_userarea_geojson(access_token_fp: str, center_lon: float, center_lat: float, radius_m: float) -> Optional[dict]:
    access_token = st.session_state.get("_rt_sgis_token", "") or ""
    if not access_token:
        return None

    cx, cy = _T_4326_to_5179.transform(center_lon, center_lat)
    minx = int(round(cx - radius_m))
    miny = int(round(cy - radius_m))
    maxx = int(round(cx + radius_m))
    maxy = int(round(cy + radius_m))

    urls = [
        "https://sgisapi.mods.go.kr/OpenAPI3/boundary/userarea.geojson",
        "https://sgisapi.kostat.go.kr/OpenAPI3/boundary/userarea.geojson",
    ]
    params = {"accessToken": access_token, "minx": minx, "miny": miny, "maxx": maxx, "maxy": maxy, "cd": 3}

    last = None
    for url in urls:
        try:
            r = requests.get(url, params=params, timeout=15)
            r.raise_for_status()
            data = r.json() or {}
            last = data
            if data.get("errCd", 0) == 0:
                return data
        except Exception as e:
            last = {"errCd": -999, "errMsg": str(e)}
    return last



# -------------------------
# SGIS 배후수요/주거유형(행정동) API
#  - pplsummary.json : 거주인구(연령대) 요약
#  - housesummary.json : 거처종류(주거유형) 요약
#  - stats/population.json : 종업원수(employee_cnt), 총가구(tot_family) 등
#
# 주의(확실하지 않음):
#  - SGIS OpenAPI에서 "직장인(연령별)"을 직접 제공하는 엔드포인트는 본 코드 기준으로 확인되지 않아,
#    employee_cnt(종업원수)를 '직장인 수'의 대체 지표로 사용합니다.
#  - 연령별 직장인 분해가 필요하면, (추측입니다) 거주인구 연령분포로 employee_cnt를 비례배분하는 옵션을 제공합니다.
# -------------------------

_SGIS_STARTUPBIZ_URLS = [
    "https://sgisapi.mods.go.kr/OpenAPI3/startupbiz/{name}.json",
    "https://sgisapi.kostat.go.kr/OpenAPI3/startupbiz/{name}.json",
]
_SGIS_STATS_URLS = [
    "https://sgisapi.mods.go.kr/OpenAPI3/stats/{name}.json",
    "https://sgisapi.kostat.go.kr/OpenAPI3/stats/{name}.json",
]

AGE_BANDS = [
    ("u10", "10대미만", "teenage_less_than_cnt"),
    ("10s", "10대", "teenage_cnt"),
    ("20s", "20대", "twenty_cnt"),
    ("30s", "30대", "thirty_cnt"),
    ("40s", "40대", "forty_cnt"),
    ("50s", "50대", "fifty_cnt"),
    ("60s", "60대", "sixty_cnt"),
    ("70p", "70대+", "seventy_more_than_cnt"),
]

HOUSE_TYPES = [
    ("apart", "아파트", "apart_cnt"),
    ("row", "연립/다세대", "row_house_cnt"),
    ("officetel", "오피스텔", "officetel_cnt"),
    ("detach", "단독주택", "detach_house_cnt"),
    ("dorm", "기숙사/사회시설", "dom_soc_fac_cnt"),
    ("etc", "기타", "etc_cnt"),
]


def _safe_int(v, default: int = 0) -> int:
    try:
        if v is None:
            return default
        s = str(v).replace(",", "").strip()
        if s == "" or s.lower() == "n/a":
            return default
        return int(float(s))
    except Exception:
        return default


def _safe_float(v, default: float = 0.0) -> float:
    try:
        if v is None:
            return default
        s = str(v).replace(",", "").strip()
        if s == "" or s.lower() == "n/a":
            return default
        return float(s)
    except Exception:
        return default


@st.cache_data(ttl=60 * 60 * 24, show_spinner=False)
def fetch_sgis_startupbiz_summary(access_token_fp: str, name: str, adm_cd: str) -> dict:
    """startupbiz/*summary.json 공통 호출 (pplsummary/housesummary/ocptnsummary 등)"""
    access_token = st.session_state.get("_rt_sgis_token", "") or ""
    if not access_token:
        return {"errCd": -401, "errMsg": "SGIS accessToken 없음"}

    params = {"accessToken": access_token, "adm_cd": str(adm_cd)}
    last = {}
    for tpl in _SGIS_STARTUPBIZ_URLS:
        url = tpl.format(name=name)
        try:
            r = requests.get(url, params=params, timeout=10)
            r.raise_for_status()
            data = r.json() or {}
            last = data
            if data.get("errCd", -1) == 0:
                return data
        except Exception as e:
            last = {"errCd": -999, "errMsg": str(e)}
            continue
    return last


@st.cache_data(ttl=60 * 60 * 24, show_spinner=False)
def fetch_sgis_stats_population(access_token_fp: str, year: int, adm_cd: str) -> dict:
    """stats/population.json (종업원수/가구수 등)"""
    access_token = st.session_state.get("_rt_sgis_token", "") or ""
    if not access_token:
        return {"errCd": -401, "errMsg": "SGIS accessToken 없음"}

    params = {
        "accessToken": access_token,
        "year": int(year),
        "adm_cd": str(adm_cd),
        "low_search": 0,  # 해당 행정구역만
    }
    last = {}
    for tpl in _SGIS_STATS_URLS:
        url = tpl.format(name="population")
        try:
            r = requests.get(url, params=params, timeout=10)
            r.raise_for_status()
            data = r.json() or {}
            last = data
            if data.get("errCd", -1) == 0:
                return data
        except Exception as e:
            last = {"errCd": -999, "errMsg": str(e)}
            continue
    return last


def _first_result_row(data: dict) -> dict:
    try:
        res = data.get("result") or []
        if isinstance(res, list) and res:
            if isinstance(res[0], dict):
                return res[0]
    except Exception:
        pass
    return {}


def _normalize_values(vals: List[float], method: str) -> List[float]:
    """값 리스트를 0~1 범위로 정규화(전역 비교용)."""
    arr = np.array([float(v) for v in vals], dtype=float)
    if len(arr) == 0:
        return []
    if method == "none":
        return arr.tolist()

    if method == "log1p_minmax":
        arr = np.log1p(np.maximum(arr, 0.0))

    vmin = float(np.nanmin(arr))
    vmax = float(np.nanmax(arr))
    if not np.isfinite(vmin) or not np.isfinite(vmax):
        return [0.0 for _ in arr]
    if abs(vmax - vmin) < 1e-12:
        # 모든 값이 동일한 경우
        if abs(vmin) < 1e-12:
            # 전부 0이면 그대로 0
            return [0.0 for _ in arr]
        # 0이 아닌 상수값이면 1.0으로 통일 (상대 비교는 불가능하지만 '존재'는 반영)
        return [1.0 for _ in arr]
    out = (arr - vmin) / (vmax - vmin)
    out = np.clip(out, 0.0, 1.0)
    return out.tolist()


def _distance_decay(dist_m: float, decay_m: float, mode: str = "exp") -> float:
    d = max(0.0, float(dist_m))
    lam = max(1e-9, float(decay_m))
    if mode == "inv":
        return 1.0 / (1.0 + (d / lam))
    # 기본: exp(-d/lam)
    return float(math.exp(-d / lam))


def compute_demand_housing_raw_by_radius(
    center_lon: float,
    center_lat: float,
    radii: List[int],
    sgis_gdf_4326: "gpd.GeoDataFrame",
    sgis_token_fp: str,
    demand_cfg: dict,
    housing_cfg: dict,
    center_id: str = "",
    center_label: str = "",
    save_detail: bool = True,
) -> Tuple[Dict[int, float], Dict[int, float], "pd.DataFrame"]:
    """
    반경별 배후수요(D_raw) / 주거유형(H_raw) 원점수 산출.

    - (A) 면적겹침(overlap_ratio) × (B) 거리감쇠(decay) = 행정동 기여도(contrib)
    - 연령별 인구(및 선택적으로 직장인 proxy)를 타깃가중치로 합산 → D_raw
    - 주거유형(가구수×유형가중치 합) → H_raw

    반환
    - demand_raw_by_radius: {radius_m: D_raw}
    - housing_raw_by_radius: {radius_m: H_raw}
    - detail_df: (선택) 행정동별 기여도/중간값 테이블
    """
    if sgis_gdf_4326 is None or sgis_gdf_4326.empty:
        return {}, {}, pd.DataFrame()
    if not (demand_cfg.get("enabled") or housing_cfg.get("enabled")):
        return {}, {}, pd.DataFrame()

    # SGIS 경계는 4326 기준으로 들어오므로, 거리/면적 계산을 위해 5179로 변환
    gdf = sgis_gdf_4326.to_crs("EPSG:5179").copy()
    cx, cy = _T_4326_to_5179.transform(center_lon, center_lat)
    center_pt = Point(cx, cy)

    # 1) 행정동별 통계(캐시로 1회만)
    stat_rows = []
    for _, row in gdf.iterrows():
        adm_cd = str(row.get("adm_cd", "") or "").strip()
        if not adm_cd:
            continue

        ppl = fetch_sgis_startupbiz_summary(sgis_token_fp, "pplsummary", adm_cd)
        ppl_row = _first_result_row(ppl) if ppl.get("errCd", -1) == 0 else {}

        house = fetch_sgis_startupbiz_summary(sgis_token_fp, "housesummary", adm_cd)
        house_row = _first_result_row(house) if house.get("errCd", -1) == 0 else {}

        emp_year = int(demand_cfg.get("employee_year", 2023))
        popstat = fetch_sgis_stats_population(sgis_token_fp, emp_year, adm_cd)
        pop_row = _first_result_row(popstat) if popstat.get("errCd", -1) == 0 else {}

        age_counts = {}
        age_total = 0
        for k, _, field in AGE_BANDS:
            c = _safe_int(ppl_row.get(field, 0), 0)
            age_counts[k] = c
            age_total += c

        employee_cnt = _safe_int(pop_row.get("employee_cnt", 0), 0)
        tot_family = _safe_int(pop_row.get("tot_family", 0), 0)

        house_counts = {k: _safe_int(house_row.get(field, 0), 0) for k, _, field in HOUSE_TYPES}
        # housesummary에 total family가 없거나 year mismatch일 수 있어, house_counts 합도 함께 사용
        house_total = int(sum(house_counts.values()))

        stat_rows.append({
            "adm_cd": adm_cd,
            "adm_nm": str(row.get("adm_nm", "") or ""),
            "geom": row.geometry,
            "age_total": age_total,
            "employee_cnt": employee_cnt,
            "tot_family": tot_family,
            "house_total": house_total,
            **{f"age_{k}": int(v) for k, v in age_counts.items()},
            **{f"house_{k}": int(v) for k, v in house_counts.items()},
        })

    if not stat_rows:
        return {}, {}, pd.DataFrame()

    stat_df = pd.DataFrame(stat_rows)

    # 2) 반경별 계산
    decay_m = float(demand_cfg.get("decay_m", DIST_DECAY_M))
    decay_mode = str(demand_cfg.get("decay_mode", "exp"))
    use_employee = bool(demand_cfg.get("use_employee_proxy", True))
    employee_weight = float(demand_cfg.get("employee_weight", 1.0))
    split_employee_by_age = bool(demand_cfg.get("split_employee_by_age", False))
    age_weights = demand_cfg.get("age_weights") or {}
    # default: 모두 1.0
    age_weights = {k: float(age_weights.get(k, 1.0)) for k, _, _ in AGE_BANDS}

    house_weights = housing_cfg.get("house_weights") or {}
    house_weights = {k: float(house_weights.get(k, 0.0)) for k, _, _ in HOUSE_TYPES}
    # 기본(아무 입력 없을 때) : 아파트/연립/오피스텔 +1, 단독 0, 기타 0
    if all(abs(v) < 1e-12 for v in house_weights.values()):
        house_weights.update({"apart": 1.0, "row": 1.0, "officetel": 1.0, "detach": 0.0, "dorm": 0.0, "etc": 0.0})

    demand_raw_by_radius: Dict[int, float] = {}
    housing_raw_by_radius: Dict[int, float] = {}
    detail_rows: List[dict] = []

    # radii 정리
    radii_unique = sorted(list({int(r) for r in radii if int(r) > 0}))

    for radius in radii_unique:
        buf = center_pt.buffer(float(radius))

        D_raw = 0.0
        H_raw = 0.0

        for _, r in stat_df.iterrows():
            geom = r["geom"]
            if geom is None:
                continue
            try:
                inter = geom.intersection(buf)
                if inter.is_empty:
                    continue
                a_geom = float(geom.area) if geom.area else 0.0
                if a_geom <= 0:
                    continue
                overlap_ratio = float(inter.area) / a_geom
            except Exception:
                continue

            if overlap_ratio <= 0:
                continue

            try:
                dist_m = float(center_pt.distance(geom.centroid))
            except Exception:
                dist_m = 0.0

            decay = _distance_decay(dist_m, decay_m, decay_mode)
            contrib = overlap_ratio * decay

            # 배후수요(연령+직장인)
            age_total = float(r.get("age_total", 0.0) or 0.0)
            if age_total < 0:
                age_total = 0.0

            # 연령별 타깃 가중합
            age_score = 0.0
            if age_total > 0:
                for k, _, _ in AGE_BANDS:
                    c = float(r.get(f"age_{k}", 0.0) or 0.0)
                    w = float(age_weights.get(k, 1.0))
                    if c > 0 and w != 0:
                        age_score += c * w

            # 직장인 proxy
            employee_cnt = float(r.get("employee_cnt", 0.0) or 0.0)
            emp_score = 0.0
            if use_employee and employee_cnt > 0:
                if split_employee_by_age and age_total > 0:
                    # 연령 분포로 비례배분
                    for k, _, _ in AGE_BANDS:
                        c = float(r.get(f"age_{k}", 0.0) or 0.0)
                        if c <= 0:
                            continue
                        share = c / age_total
                        w = float(age_weights.get(k, 1.0))
                        emp_score += employee_cnt * share * w
                else:
                    emp_score = employee_cnt

            D_cell = (age_score + employee_weight * emp_score) * contrib

            # 주거유형 점수
            house_total = float(r.get("house_total", 0.0) or 0.0)
            housing_weighted_sum = 0.0
            H_cell = 0.0
            if house_total > 0:
                for k, _, _ in HOUSE_TYPES:
                    c = float(r.get(f"house_{k}", 0.0) or 0.0)
                    w = float(house_weights.get(k, 0.0))
                    if c > 0 and w != 0:
                        housing_weighted_sum += c * w
                H_cell = housing_weighted_sum * contrib

            D_raw += D_cell
            H_raw += H_cell

            if save_detail:
                tot_family_val = float(r.get("tot_family", 0.0) or 0.0)
                detail_rows.append({
                    "center_id": center_id,
                    "center_label": center_label,
                    "radius_m": int(radius),
                    "adm_cd": r.get("adm_cd", ""),
                    "adm_nm": r.get("adm_nm", ""),
                    "dist_m": float(dist_m),
                    "overlap_ratio": float(overlap_ratio),
                    "decay": float(decay),
                    "contrib": float(contrib),
                    "age_total": float(age_total),
                    "employee_cnt": float(employee_cnt),
                    "tot_family": tot_family_val,
                    "house_total": float(house_total),
                    "D_cell": float(D_cell),
                    "H_cell": float(H_cell),
                    "demand_contrib": float(D_cell),
                    "housing_contrib": float(H_cell),
                    "housing_weighted_sum": float(housing_weighted_sum),
                    "D_raw_cum": float(D_raw),
                    "H_raw_cum": float(H_raw),
                })

        demand_raw_by_radius[int(radius)] = float(D_raw)
        housing_raw_by_radius[int(radius)] = float(H_raw)

    detail_df = pd.DataFrame(detail_rows) if (save_detail and detail_rows) else pd.DataFrame()
    return demand_raw_by_radius, housing_raw_by_radius, detail_df


def _build_publicdata_key_candidates(service_key: str) -> List[str]:
    """
    공공데이터포털 서비스키는 환경에 따라 "일반 인증키(Decoding)" / "Encoding" 형태가 섞여 들어올 수 있어
    몇 가지 후보를 순차 재시도합니다.
    """
    raw = str(service_key or "").strip()
    if not raw:
        return []

    cands = []
    for cand in [
        raw,
        urllib.parse.unquote(raw),
        urllib.parse.quote(urllib.parse.unquote(raw), safe=""),
        urllib.parse.quote(raw, safe=""),
    ]:
        cand = str(cand or "").strip()
        if cand and cand not in cands:
            cands.append(cand)
    return cands


def _xml_items_to_df(xml_text: str) -> pd.DataFrame:
    root = ET.fromstring(xml_text)

    result_code = None
    result_msg = None
    header = root.find('.//header')
    if header is not None:
        rc = header.findtext('resultCode') or header.findtext('resultcode')
        rm = header.findtext('resultMsg') or header.findtext('resultmsg')
        result_code = (rc or '').strip()
        result_msg = (rm or '').strip()

    body = root.find('.//body')
    items_parent = None
    if body is not None:
        items_parent = body.find('items')
    if items_parent is None:
        items_parent = root.find('.//items')

    rows = []
    if items_parent is not None:
        for item in items_parent.findall('item'):
            row = {}
            for child in list(item):
                row[str(child.tag)] = (child.text or '').strip()
            if row:
                rows.append(row)

    # 성공 코드인데 데이터가 없는 경우도 빈 DF로 허용
    if result_code in (None, '', '00'):
        return pd.DataFrame(rows)

    raise RuntimeError(f'공공데이터 상가 API 오류(resultCode={result_code}, resultMsg={result_msg or "알 수 없음"})')


def _json_items_to_df(payload: dict) -> pd.DataFrame:
    header = payload.get('header') or {}
    result_code = str(header.get('resultCode') or header.get('resultcode') or '').strip()
    result_msg = str(header.get('resultMsg') or header.get('resultmsg') or '').strip()

    body = payload.get('body') or {}
    items = body.get('items')
    if isinstance(items, dict) and 'item' in items:
        items = items.get('item')
    if items is None:
        items = []
    if isinstance(items, dict):
        items = [items]

    if result_code in ('', '00'):
        return pd.DataFrame(items)

    raise RuntimeError(f'공공데이터 상가 API 오류(resultCode={result_code}, resultMsg={result_msg or "알 수 없음"})')


def _fetch_smallshop_radius_direct(service_key: str, lon: float, lat: float, radius_m: int, timeout: int = 20) -> pd.DataFrame:
    """
    PublicDataReader가 없거나 내부 URL/파싱 문제를 일으킬 때를 대비한 직접 호출 fallback.
    - sdsc2/storeListInRadius 엔드포인트 사용
    - 서비스키 인코딩/디코딩 형태를 순차 재시도
    - XML/JSON 응답 모두 방어적으로 처리
    """
    base_urls = [
        'https://apis.data.go.kr/B553077/api/open/sdsc2/storeListInRadius',
        'http://apis.data.go.kr/B553077/api/open/sdsc2/storeListInRadius',
    ]
    key_candidates = _build_publicdata_key_candidates(service_key)
    if not key_candidates:
        return pd.DataFrame()

    last_err = None
    for base_url in base_urls:
        for key_cand in key_candidates:
            rows_all = []
            for page_no in range(1, 101):
                params = {
                    'serviceKey': key_cand,
                    'radius': str(int(radius_m)),
                    'cx': str(float(lon)),
                    'cy': str(float(lat)),
                    'pageNo': str(page_no),
                    'numOfRows': '1000',
                }
                try:
                    resp = requests.get(base_url, params=params, timeout=timeout)
                    resp.raise_for_status()
                    txt = resp.text or ''
                    stripped = txt.lstrip()
                    if not stripped:
                        raise RuntimeError('공공데이터 상가 API가 빈 응답을 반환했습니다.')

                    if stripped.startswith('{') or stripped.startswith('['):
                        try:
                            payload = resp.json()
                        except Exception as e:
                            raise RuntimeError(f'공공데이터 상가 API JSON 파싱 실패: {e}') from e
                        page_df = _json_items_to_df(payload)
                    elif stripped.startswith('<'):
                        try:
                            page_df = _xml_items_to_df(txt)
                        except ET.ParseError as e:
                            head = stripped[:200].replace('\n', ' ')
                            raise RuntimeError(f'공공데이터 상가 API XML 파싱 실패: {e}; 응답 시작={head}') from e
                    else:
                        head = stripped[:200].replace('\n', ' ')
                        raise RuntimeError(f'공공데이터 상가 API가 XML/JSON이 아닌 응답을 반환했습니다: {head}')

                    if page_df is None or page_df.empty:
                        break
                    rows_all.append(page_df)

                    # 마지막 페이지 추정
                    if len(page_df) < 1000:
                        break
                except Exception as e:
                    last_err = e
                    rows_all = []
                    break

            if rows_all:
                out = pd.concat(rows_all, ignore_index=True)
                return out.copy()

    if last_err is not None:
        raise RuntimeError(str(last_err)) from last_err
    return pd.DataFrame()


def fetch_smallshop_radius(service_key_fp: str, lon: float, lat: float, radius_m: int) -> pd.DataFrame:
    service_key = st.session_state.get("_rt_publicdata_key", "") or ""
    if not service_key:
        return pd.DataFrame()

    # 1차: PublicDataReader 사용 (설치되어 있고 정상 동작하면 그대로 활용)
    if HAS_PUBLICDATAREADER:
        pdr_errors = []
        for key_cand in _build_publicdata_key_candidates(service_key):
            try:
                api = SmallShop(key_cand)
                df = api.get_data(service_name="반경상가", radius=str(int(radius_m)), cx=float(lon), cy=float(lat))
                if df is None:
                    continue
                return df.copy()
            except Exception as e:
                pdr_errors.append(e)

        # PublicDataReader가 URL/파서 이슈를 일으키면 직접 호출로 fallback
        try:
            return _fetch_smallshop_radius_direct(service_key, lon, lat, radius_m)
        except Exception as e2:
            if pdr_errors:
                raise RuntimeError(f'PublicDataReader 호출 실패 후 직접 호출도 실패했습니다. 마지막 오류: {e2}') from e2
            raise

    # 2차: PublicDataReader 미설치 시 직접 호출
    return _fetch_smallshop_radius_direct(service_key, lon, lat, radius_m)


# -------------------------
# 분석 로직
# -------------------------
@dataclass
class AnalysisResult:
    center_id: str
    center_label: str
    center_lon: float
    center_lat: float
    df_master: pd.DataFrame
    df_summary: pd.DataFrame
    sgis_gdf: Optional[gpd.GeoDataFrame]
    meta: Dict

def run_analysis_single(
    center_id: str,
    center_label: str,
    service_key_fp: str,
    center_lon: float,
    center_lat: float,
    radii: List[int],
    lcls: List[str],
    mcls: List[str],
    scls: List[str],
    scls_weights: Dict[str, float],
    sgis_token_fp: Optional[str],
    demand_cfg: Optional[dict] = None,
    housing_cfg: Optional[dict] = None,
) -> AnalysisResult:
    radii = sorted({int(r) for r in radii if int(r) > 0})
    max_radius = int(max(radii))

    df_raw = fetch_smallshop_radius(service_key_fp, center_lon, center_lat, max_radius)
    if df_raw.empty:
        return AnalysisResult(center_id, center_label, center_lon, center_lat,
                              df_master=pd.DataFrame(), df_summary=pd.DataFrame(), sgis_gdf=None,
                              meta={"max_radius": max_radius, "raw_rows": 0, "filtered_rows": 0})

    # 컬럼명 자동 탐색
    col_lon = "경도" if "경도" in df_raw.columns else ("lon" if "lon" in df_raw.columns else None)
    col_lat = "위도" if "위도" in df_raw.columns else ("lat" if "lat" in df_raw.columns else None)
    col_lcls = "상권업종대분류명" if "상권업종대분류명" in df_raw.columns else None
    col_mcls = "상권업종중분류명" if "상권업종중분류명" in df_raw.columns else None
    col_scls = "상권업종소분류명" if "상권업종소분류명" in df_raw.columns else None
    col_id = "상가업소번호" if "상가업소번호" in df_raw.columns else None
    col_name = "상호명" if "상호명" in df_raw.columns else None

    df = df_raw.copy()

    # 분류 필터
    if lcls and col_lcls:
        df = df[df[col_lcls].astype(str).isin(lcls)]
    if mcls and col_mcls:
        df = df[df[col_mcls].astype(str).isin(mcls)]
    if scls and col_scls:
        df = df[df[col_scls].astype(str).isin(scls)]

    # 좌표/거리/반경분기
    rows = []
    dropped_no_coord = 0
    dropped_outside = 0
    for _, r in df.iterrows():
        lon = _safe_float(r.get(col_lon) if col_lon else None)
        lat = _safe_float(r.get(col_lat) if col_lat else None)
        if lon is None or lat is None:
            dropped_no_coord += 1
            continue
        d = dist_m_4326(center_lon, center_lat, lon, lat)
        if d > (max_radius + TOLERANCE_M):
            dropped_outside += 1
            continue
        rows.append({
            "center_id": center_id,
            "center_label": center_label,
            "store_id": str(r.get(col_id, "") or ""),
            "name": str(r.get(col_name, "") or ""),
            "lcls": str(r.get(col_lcls, "") or ""),
            "mcls": str(r.get(col_mcls, "") or ""),
            "scls": str(r.get(col_scls, "") or ""),
            "lon": float(lon),
            "lat": float(lat),
            "dist_m": float(d),
        })
    df_master = pd.DataFrame(rows)

    # 반경별 요약(점수식)
    summary_rows = []
    total_score_by_radius = {}
    for radius in radii:
        sub = df_master[df_master["dist_m"] <= (radius + TOLERANCE_M)].copy()
        if sub.empty:
            total_score_by_radius[int(radius)] = 0.0
            continue

        area_km2 = max(1e-9, PI_APPROX * ((radius / 1000.0) ** 2))
        comp_idx_value = float(len(sub)) / float(area_km2)

        radius_total_score = 0.0
        if scls:
            for cat in scls:
                ss = sub[sub["scls"].astype(str) == str(cat)]
                cnt = int(len(ss))
                w = float(scls_weights.get(cat, 0.0))
                if cnt > 0:
                    avg_dist = float(ss["dist_m"].mean())
                    score = w * cnt * math.exp(-avg_dist / float(DIST_DECAY_M))
                else:
                    avg_dist = np.nan
                    score = 0.0
                radius_total_score += float(score)

                summary_rows.append({
                    "center_id": center_id,
                    "center_label": center_label,
                    "radius_m": int(radius),
                    "scls": str(cat),
                    "count": cnt,
                    "avg_dist_m": avg_dist if not np.isnan(avg_dist) else np.nan,
                    "weight": w,
                    "score": float(score),
                    "comp_idx": comp_idx_value,
                    "total_in_radius": int(len(sub)),
                })
        else:
            summary_rows.append({
                "center_id": center_id,
                "center_label": center_label,
                "radius_m": int(radius),
                "scls": "",
                "count": int(len(sub)),
                "avg_dist_m": float(sub["dist_m"].mean()),
                "weight": 0.0,
                "score": 0.0,
                "comp_idx": comp_idx_value,
                "total_in_radius": int(len(sub)),
            })
        total_score_by_radius[int(radius)] = float(radius_total_score)

    df_summary = pd.DataFrame(summary_rows)

    # SGIS 경계 GeoDataFrame
    sgis_gdf = None
    if sgis_token_fp:
        geo = fetch_sgis_userarea_geojson(sgis_token_fp, center_lon, center_lat, max_radius)
        if geo and isinstance(geo, dict) and geo.get("errCd", 0) == 0:
            feats = geo.get("features") or []
            if feats:
                sgis_gdf = gpd.GeoDataFrame(
                    [{
                        "adm_cd": (f.get("properties") or {}).get("adm_cd", ""),
                        "adm_nm": (f.get("properties") or {}).get("adm_nm", ""),
                        "geometry": shape(f.get("geometry")),
                    } for f in feats if f.get("geometry")],
                    crs="EPSG:5179",
                ).to_crs("EPSG:4326")


    # SGIS 기반 배후수요/주거유형 원점수(반경별)
    demand_cfg = demand_cfg or {}
    housing_cfg = housing_cfg or {}
    demand_raw_by_radius: Dict[int, float] = {}
    housing_raw_by_radius: Dict[int, float] = {}
    dh_detail_df: "pd.DataFrame" = pd.DataFrame()

    if sgis_gdf is not None and sgis_token_fp and (demand_cfg.get("enabled") or housing_cfg.get("enabled")):
        try:
            demand_raw_by_radius, housing_raw_by_radius, dh_detail_df = compute_demand_housing_raw_by_radius(
                center_lon=center_lon,
                center_lat=center_lat,
                radii=radii,
                sgis_gdf_4326=sgis_gdf,
                sgis_token_fp=sgis_token_fp,
                demand_cfg=demand_cfg,
                housing_cfg=housing_cfg,
                center_id=center_id,
                center_label=center_label,
                save_detail=True,
            )
        except Exception as _e:
            # 실패해도 기존 상가 점수는 계속 표시
            demand_raw_by_radius, housing_raw_by_radius, dh_detail_df = {}, {}, pd.DataFrame()

    meta = {
        "max_radius": max_radius,
        "raw_rows": int(len(df_raw)),
        "master_rows": int(len(df_master)),
        "dropped_no_coord": int(dropped_no_coord),
        "dropped_outside": int(dropped_outside),
        "total_score_by_radius": total_score_by_radius,
        "demand_raw_by_radius": demand_raw_by_radius,
        "housing_raw_by_radius": housing_raw_by_radius,
        "dh_detail_df": dh_detail_df,
    }
    return AnalysisResult(center_id, center_label, center_lon, center_lat, df_master, df_summary, sgis_gdf, meta)


# -------------------------
# 지도 렌더링 (folium)
# -------------------------
def _rgba_to_hex(rgba):
    r, g, b, a = rgba
    return "#{:02x}{:02x}{:02x}".format(int(r), int(g), int(b))

def _build_heatmap_points(
    df_master_all: pd.DataFrame,
    weight_mode: str = "uniform",
    scls_weights: Optional[Dict[str, float]] = None,
) -> List[List[float]]:
    """
    HeatMap 입력 포맷: [[lat, lon, weight], ...]
    - folium HeatMap은 weight가 음수일 수 없어서 0 미만은 0으로 클리핑합니다.
    """
    if df_master_all is None or df_master_all.empty:
        return []

    weight_mode = (weight_mode or "uniform").strip().lower()
    scls_weights = scls_weights or {}

    # 기본 weight
    w = np.ones(len(df_master_all), dtype=float)

    if weight_mode in ("distance", "distance_decay", "decay"):
        # 가까울수록 가중↑ (exp(-d/DECAY))
        d = pd.to_numeric(df_master_all.get("dist_m", 0), errors="coerce").fillna(0).astype(float).to_numpy()
        w = np.exp(-d / float(DIST_DECAY_M))

    elif weight_mode in ("scls", "scls_weighted", "category_weighted"):
        # (소분류 가중치) * exp(-d/DECAY)  (음수는 0으로)
        d = pd.to_numeric(df_master_all.get("dist_m", 0), errors="coerce").fillna(0).astype(float).to_numpy()
        decay = np.exp(-d / float(DIST_DECAY_M))
        sw = df_master_all.get("scls", "").astype(str).map(lambda x: float(scls_weights.get(str(x), 0.0))).to_numpy()
        w = sw * decay

    w = np.clip(w, 0.0, None)

    lat = pd.to_numeric(df_master_all.get("lat"), errors="coerce").to_numpy()
    lon = pd.to_numeric(df_master_all.get("lon"), errors="coerce").to_numpy()

    pts = []
    for la, lo, ww in zip(lat, lon, w):
        if np.isnan(la) or np.isnan(lo):
            continue
        pts.append([float(la), float(lo), float(ww)])
    return pts


def _fit_folium_bounds(
    m: folium.Map,
    centers: pd.DataFrame,
    df_master_all: pd.DataFrame,
    sgis_gdf_by_center: Dict[str, gpd.GeoDataFrame],
):
    """folium 지도가 빈 화면처럼 보이지 않도록 표시 범위를 데이터에 맞춰 자동 조정합니다."""
    lats = []
    lons = []

    if centers is not None and not centers.empty:
        lats.extend(pd.to_numeric(centers.get("lat"), errors="coerce").dropna().astype(float).tolist())
        lons.extend(pd.to_numeric(centers.get("lon"), errors="coerce").dropna().astype(float).tolist())

    if df_master_all is not None and not df_master_all.empty:
        lats.extend(pd.to_numeric(df_master_all.get("lat"), errors="coerce").dropna().astype(float).tolist())
        lons.extend(pd.to_numeric(df_master_all.get("lon"), errors="coerce").dropna().astype(float).tolist())

    for _, gdf in (sgis_gdf_by_center or {}).items():
        if gdf is None or gdf.empty:
            continue
        try:
            minx, miny, maxx, maxy = gdf.total_bounds
            lons.extend([float(minx), float(maxx)])
            lats.extend([float(miny), float(maxy)])
        except Exception:
            continue

    if not lats or not lons:
        return

    min_lat = float(np.nanmin(lats))
    max_lat = float(np.nanmax(lats))
    min_lon = float(np.nanmin(lons))
    max_lon = float(np.nanmax(lons))

    # 동일 좌표만 있을 때 Leaflet이 과도하게 확대/축소되는 것을 방지
    if abs(max_lat - min_lat) < 1e-9:
        min_lat -= 0.001
        max_lat += 0.001
    if abs(max_lon - min_lon) < 1e-9:
        min_lon -= 0.001
        max_lon += 0.001

    try:
        m.fit_bounds([[min_lat, min_lon], [max_lat, max_lon]])
    except Exception:
        pass


def render_folium_component_safe(fmap: folium.Map, height: int, map_key: str):
    """streamlit_folium 버전 차이를 흡수하면서 안전하게 렌더링합니다."""
    try:
        return st_folium(fmap, height=int(height), use_container_width=True, key=map_key, returned_objects=[])
    except TypeError:
        try:
            return st_folium(fmap, height=int(height), width=None, key=map_key)
        except TypeError:
            try:
                return st_folium(fmap, height=int(height), use_container_width=True)
            except TypeError:
                return st_folium(fmap, height=int(height), width=1200)


def render_map_folium(
    centers: pd.DataFrame,
    df_master_all: pd.DataFrame,
    radii: List[int],
    scls_for_color: List[str],
    use_vworld: bool,
    vworld_key: str,
    sgis_gdf_by_center: Dict[str, gpd.GeoDataFrame],
    *,
    zoom_start: int = 13,
    enable_fullscreen: bool = True,
    enable_heatmap: bool = True,
    heat_weight_mode: str = "uniform",
    heat_radius_px: int = 18,
    heat_blur_px: int = 15,
    heat_min_opacity: float = 0.2,
    scls_weights: Optional[Dict[str, float]] = None,
) -> folium.Map:
    # 지도 중심: 평균
    if centers.empty:
        center_lon, center_lat = 127.0, 37.5
    else:
        center_lon = float(centers["lon"].mean())
        center_lat = float(centers["lat"].mean())

    # 중요: tiles=None 으로 시작한 뒤 HTTPS 타일을 명시적으로 추가해야
    # Streamlit/브라우저 환경에서 mixed content 또는 중복 base layer 문제를 줄일 수 있습니다.
    m = folium.Map(
        location=[center_lat, center_lon],
        zoom_start=int(zoom_start),
        control_scale=True,
        tiles=None,
        prefer_canvas=True,
    )

    # 배경지도: 항상 OSM(HTTPS)을 기본으로 넣고, VWorld는 선택 시 추가합니다.
    # 기존 http:// VWorld URL은 HTTPS 페이지에서 mixed-content 로 차단될 수 있어 https:// 로 교체합니다.
    folium.TileLayer(
        tiles="https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png",
        attr="© OpenStreetMap contributors",
        name="OSM",
        overlay=False,
        control=True,
        show=not (use_vworld and bool(vworld_key)),
    ).add_to(m)

    if use_vworld and vworld_key:
        tiles = f"https://api.vworld.kr/req/wmts/1.0.0/{vworld_key}/Base/{{z}}/{{y}}/{{x}}.png"
        folium.TileLayer(
            tiles=tiles,
            name="VWorld Base",
            attr="VWorld",
            overlay=False,
            control=True,
            show=True,
        ).add_to(m)

    # (요구사항 3) folium 전체화면/확대 UI
    if enable_fullscreen:
        try:
            Fullscreen(
                position="topleft",
                title="전체화면",
                title_cancel="전체화면 종료",
                force_separate_button=True,
            ).add_to(m)
        except Exception:
            # plugin이 실패해도 지도는 계속 표시
            pass

    # (요구사항 4) Heatmap 레이어
    if enable_heatmap and df_master_all is not None and not df_master_all.empty:
        pts = _build_heatmap_points(df_master_all, weight_mode=heat_weight_mode, scls_weights=scls_weights)
        if pts:
            fg = folium.FeatureGroup(name="Heatmap", overlay=True, show=True)
            HeatMap(
                pts,
                radius=int(heat_radius_px),
                blur=int(heat_blur_px),
                min_opacity=float(heat_min_opacity),
                max_zoom=18,
            ).add_to(fg)
            fg.add_to(m)

    # centers + radii
    for _, c in centers.iterrows():
        clat = float(c["lat"]); clon = float(c["lon"])
        cid = str(c["center_id"]); label = str(c["center_label"])

        # SGIS 경계
        gdf = sgis_gdf_by_center.get(cid)
        if gdf is not None and not gdf.empty:
            gj = json.loads(gdf.to_json())
            GeoJson(
                gj,
                name=f"SGIS {label}",
                style_function=lambda feat: {"fillColor": "#00000000", "color": "#111111", "weight": 2, "fillOpacity": 0.05},
                tooltip=folium.GeoJsonTooltip(fields=["adm_nm", "adm_cd"], aliases=["행정동", "코드"]),
            ).add_to(m)

        # 중심점
        folium.Marker(
            location=[clat, clon],
            tooltip=f"CENTER: {label}",
            icon=folium.Icon(color="orange", icon="star"),
        ).add_to(m)

        # 반경 원
        for r in radii:
            folium.Circle(
                location=[clat, clon],
                radius=float(r),
                color="#555555",
                weight=2,
                fill=False,
                tooltip=f"{label} {int(r)}m",
            ).add_to(m)

    # 점(상가)
    if df_master_all is not None and not df_master_all.empty:
        cats = list(pd.unique(df_master_all["scls"].astype(str)))
        if scls_for_color:
            cats = [c for c in cats if c in set(scls_for_color)]
        color_map = build_category_color_map(cats)

        for _, r in df_master_all.iterrows():
            scls = str(r.get("scls", ""))
            rgba = color_map.get(scls, (0, 0, 0, 235))
            color = _rgba_to_hex(rgba)
            tip = (
                f"{r.get('name','')}"
                f"<br/>{r.get('lcls','')} / {r.get('mcls','')} / {scls}"
                f"<br/>center={r.get('center_label','')}, dist={r.get('dist_m',0):.1f}m"
            )
            folium.CircleMarker(
                location=[float(r["lat"]), float(r["lon"])],
                radius=4,
                color="#ffffff",
                weight=1,
                fill=True,
                fill_color=color,
                fill_opacity=0.9,
                tooltip=folium.Tooltip(tip, sticky=True),
            ).add_to(m)

    _fit_folium_bounds(m, centers=centers, df_master_all=df_master_all, sgis_gdf_by_center=sgis_gdf_by_center)
    folium.LayerControl(position="topright", collapsed=False).add_to(m)
    return m


# -------------------------
# 지도 렌더링 (pydeck 추천)
# -------------------------
def render_map_pydeck(
    centers: pd.DataFrame,
    df_master_all: pd.DataFrame,
    radii: List[int],
    scls_for_color: List[str],
    sgis_gdf_by_center: Dict[str, gpd.GeoDataFrame],
) -> "pdk.Deck":
    if centers.empty:
        view_state = pdk.ViewState(latitude=37.5, longitude=127.0, zoom=12)
    else:
        view_state = pdk.ViewState(
            latitude=float(centers["lat"].mean()),
            longitude=float(centers["lon"].mean()),
            zoom=13,
            pitch=0,
        )

    layers = []

    # centers layer
    centers_df = centers.copy()
    if "color" not in centers_df.columns:
        centers_df["color"] = [[255, 140, 0, 220] for _ in range(len(centers_df))]
    layers.append(
        pdk.Layer(
            "ScatterplotLayer",
            data=centers_df,
            get_position=["lon", "lat"],
            get_fill_color="color",
            get_radius=40,
            radius_units="meters",
            pickable=True,
        )
    )

    # radius circles as PathLayer
    circle_rows = []
    for _, c in centers_df.iterrows():
        clon = float(c["lon"]); clat = float(c["lat"])
        label = str(c["center_label"])
        for r in radii:
            circle_rows.append({
                "name": f"{label} {int(r)}m",
                "path": make_circle_path_lonlat(clon, clat, float(r)),
            })
    if circle_rows:
        layers.append(
            pdk.Layer(
                "PathLayer",
                data=pd.DataFrame(circle_rows),
                get_path="path",
                get_width=2,
                width_units="pixels",
                get_color=[90, 90, 90, 200],
                pickable=False,
            )
        )

    # SGIS boundary as GeoJsonLayer (합쳐서)
    gj_list = []
    for cid, gdf in (sgis_gdf_by_center or {}).items():
        if gdf is None or gdf.empty:
            continue
        try:
            gj_list.append(json.loads(gdf.to_json()))
        except Exception:
            continue
    if gj_list:
        features = []
        for gj in gj_list:
            features.extend(gj.get("features", []) or [])
        gj_merged = {"type": "FeatureCollection", "features": features}
        layers.append(
            pdk.Layer(
                "GeoJsonLayer",
                data=gj_merged,
                stroked=True,
                filled=False,
                get_line_color=[25, 25, 25, 180],
                line_width_min_pixels=1,
                pickable=True,
            )
        )

    # points layer
    if df_master_all is not None and not df_master_all.empty:
        dfp = df_master_all.copy()
        cats = list(pd.unique(dfp["scls"].astype(str)))
        if scls_for_color:
            cats = [c for c in cats if c in set(scls_for_color)]
        color_map = build_category_color_map(cats)

        def _color_of(cat: str):
            rgba = color_map.get(str(cat), (0, 0, 0, 235))
            return [int(rgba[0]), int(rgba[1]), int(rgba[2]), 200]

        dfp["color"] = dfp["scls"].astype(str).map(_color_of)
        dfp["tooltip"] = (
            dfp["name"].astype(str)
            + "\n" + dfp["lcls"].astype(str) + " / " + dfp["mcls"].astype(str) + " / " + dfp["scls"].astype(str)
            + "\ncenter=" + dfp["center_label"].astype(str)
            + ", dist=" + dfp["dist_m"].round(1).astype(str) + "m"
        )

        layers.append(
            pdk.Layer(
                "ScatterplotLayer",
                data=dfp,
                get_position=["lon", "lat"],
                get_fill_color="color",
                get_radius=10,
                radius_units="meters",
                pickable=True,
            )
        )

        tooltip = {"text": "{tooltip}"}
    else:
        tooltip = None

    map_style = "https://basemaps.cartocdn.com/gl/positron-gl-style/style.json"
    return pdk.Deck(layers=layers, initial_view_state=view_state, map_style=map_style, tooltip=tooltip)


# -------------------------
# Streamlit UI
# -------------------------
st.set_page_config(page_title="상권 분석 대시보드 (후보지 비교)", layout="wide")
st.title("상권 경쟁강도 입지분석 Dashboard (멀티 중심지 동시 비교포함)")
# st.title("상권 업종 경쟁강도 분석 (공공데이터포털 + SGIS + 멀티 중심지 비교)")

with st.expander("키 설정(권장: Streamlit secrets / 환경변수)", expanded=False):
    st.code(
        'PUBLICDATA_SERVICE_KEY="..."\nSGIS_KEY="..."\nSGIS_SECRET="..."\nVWORLD_KEY="..."',
        language="toml",
    )
    st.code(
        "set PUBLICDATA_SERVICE_KEY=...\nset SGIS_KEY=...\nset SGIS_SECRET=...\nset VWORLD_KEY=...",
        language="powershell",
    )
    st.caption("입력창은 마스킹(type=password)되며, 캐시 키에는 원문 키 대신 fingerprint(해시 일부)만 사용합니다.")

# 기본값 (secrets/env)
_default_service_key = get_secret_or_env("PUBLICDATA_SERVICE_KEY", "")
_default_sgis_key = get_secret_or_env("SGIS_KEY", "")
_default_sgis_secret = get_secret_or_env("SGIS_SECRET", "")
_default_vworld_key = get_secret_or_env("VWORLD_KEY", "")

left, right = st.columns([0.45, 0.55], gap="small")

with left:
    st.subheader("입력")
    my_business = st.text_input("관심 업종(내 업종) - 라벨용", value="")

        # 🔒 키 입력 UI 제거 (보안): 키는 화면에 표시하지 않고 secrets/env에서만 읽습니다.
    service_key = _default_service_key
    sgis_key = _default_sgis_key
    sgis_secret = _default_sgis_secret
    vworld_key = _default_vworld_key

    st.caption("키 설정 상태(값은 표시하지 않음)")
    st.markdown(
        f"- 공공데이터포털 상가(상권)정보 서비스키: {'✅ 설정됨' if service_key else '⚠️ 미설정'}\n"
        f"- SGIS consumer_key(선택): {'✅ 설정됨' if sgis_key else '➖ 미설정'}\n"
        f"- SGIS consumer_secret(선택): {'✅ 설정됨' if sgis_secret else '➖ 미설정'}\n"
        f"- VWorld key(선택): {'✅ 설정됨' if vworld_key else '➖ 미설정'}"
    )

    if not service_key:
        st.warning("공공데이터포털 상가(상권)정보 서비스키가 설정되지 않았습니다. "
                   "환경변수 PUBLICDATA_SERVICE_KEY 또는 .streamlit/secrets.toml에 PUBLICDATA_SERVICE_KEY를 등록하세요.")

    # 런타임 키(캐시 함수가 session_state에서만 참조하도록)
    st.session_state["_rt_publicdata_key"] = service_key or ""
    st.session_state["_rt_sgis_key"] = sgis_key or ""
    st.session_state["_rt_sgis_secret"] = sgis_secret or ""
    st.session_state["_rt_vworld_key"] = vworld_key or ""

# 에러 표시용 마스킹 리스트
    _secrets_for_redact = [service_key, sgis_key, sgis_secret, vworld_key, st.session_state.get("_rt_sgis_token", "")]

    st.markdown("---")
    # (UI) 제목은 아래 카드에서 표시
    # st.subheader("중심지(여러 개) 입력")
    # st.caption("✅ 행 추가/삭제 버튼을 사용하세요. (하단 자동 행추가 바를 제거했습니다.)")


    # -------------------------
    # 중심지 입력 UI 스타일 (전문가형)
    # -------------------------
    st.markdown(
        """
        <style>
        .center-card{
            background:#ffffff;
            border:1px solid rgba(49, 51, 63, 0.12);
            border-radius:18px;
            padding:18px 18px 12px 18px;
            box-shadow:0 2px 8px rgba(0,0,0,0.04);
            margin-top:8px;
            margin-bottom:6px;
        }
        .center-head{
            display:flex;
            flex-direction:column;
            gap:6px;
            margin-bottom:14px;
        }
        .center-title{
            font-size:24px;
            font-weight:800;
            letter-spacing:-0.3px;
            color:rgba(49, 51, 63, 0.95);
        }
        .center-note{
            background:rgba(2, 132, 199, 0.06);
            border:1px solid rgba(2, 132, 199, 0.18);
            border-radius:14px;
            padding:12px 14px;
            color:rgba(49, 51, 63, 0.78);
            font-size:14px;
            line-height:1.45;
        }
        /* Buttons as pill */
        .center-card button[kind]{
            border-radius:16px !important;
            padding-top:10px !important;
            padding-bottom:10px !important;
            font-weight:700 !important;
        }
        /* Inputs compact */
        .center-card div[data-testid="stTextInput"] input,
        .center-card div[data-testid="stSelectbox"] div[data-baseweb="select"]{
            border-radius:12px !important;
        }
        .center-card div[data-testid="stTextInput"] input{
            padding-top:8px !important;
            padding-bottom:8px !important;
        }

        /* data_editor 가로 스크롤(화면이 좁아질 때 찌그러짐 방지) */
        .center-card div[data-testid="stDataFrame"]{
            overflow-x:auto !important;
        }
        .center-card div[data-testid="stDataFrame"] table{
            min-width: 980px !important;
        }
        </style>
        """,
        unsafe_allow_html=True,
    )

    st.markdown(
        """
        <div class="center-card">
          <div class="center-head">
            <div class="center-title">중심지(여러 개) 입력</div>
          </div>
        """,
        unsafe_allow_html=True,
    )

    # centers_df는 **항상** session_state에 저장/유지합니다.
    if "centers_df" not in st.session_state:
        st.session_state["centers_df"] = pd.DataFrame([
            {"enabled": True, "delete": False, "center_label": "A", "mode": "좌표", "lon": "127.0", "lat": "37.5", "address": ""},
            {"enabled": False, "delete": False, "center_label": "B", "mode": "주소(자동)", "lon": "", "lat": "", "address": ""},
        ])

    # (요구사항 1~2) data_editor의 key를 버전으로 관리해서,
    # - 행 추가/삭제 시 위젯 상태가 "이전 값"으로 되돌아가는 현상을 방지
    # - 입력 후 Enter/셀 이동으로 반영된 값이 rerun 이후에도 유지되도록 보장
    if "centers_editor_ver" not in st.session_state:
        st.session_state["centers_editor_ver"] = 0


    def _coerce_df(obj) -> pd.DataFrame:
        if obj is None:
            return pd.DataFrame()
        if isinstance(obj, pd.DataFrame):
            return obj.copy()
        try:
            return pd.DataFrame(obj).copy()
        except Exception:
            return pd.DataFrame()

    def _editor_state_to_df(ed, base_df: pd.DataFrame) -> pd.DataFrame:
        """st.data_editor 반환값/DataFrame 또는 session_state dict(edited_rows...)를 DataFrame으로 복원"""
        base = _coerce_df(base_df)
        try:
            if isinstance(ed, dict) and any(k in ed for k in ("edited_rows", "added_rows", "deleted_rows")):
                work = base.copy()
                for ridx in ed.get("deleted_rows", []) or []:
                    if isinstance(ridx, int) and 0 <= ridx < len(work):
                        work = work.drop(index=ridx)
                work = work.reset_index(drop=True)

                edits = ed.get("edited_rows", {}) or {}
                if isinstance(edits, dict):
                    for ridx, changes in edits.items():
                        if not isinstance(ridx, int) or ridx < 0 or ridx >= len(work):
                            continue
                        if isinstance(changes, dict):
                            for col, val in changes.items():
                                if col in work.columns:
                                    work.at[ridx, col] = val

                adds = ed.get("added_rows", []) or []
                if isinstance(adds, list) and len(adds) > 0:
                    add_df = pd.DataFrame(adds)
                    for col in work.columns:
                        if col not in add_df.columns:
                            add_df[col] = None
                    add_df = add_df[work.columns]
                    work = pd.concat([work, add_df], ignore_index=True)
                return work
            return ed.copy() if hasattr(ed, "copy") else pd.DataFrame(ed)
        except Exception:
            return base.copy()

    def _current_centers_df() -> pd.DataFrame:
        """현재 centers DF (단일 원본: st.session_state['centers_df'])"""
        return _coerce_df(st.session_state.get("centers_df"))

    def _set_centers_df(df_new: pd.DataFrame):
        df_new = _coerce_df(df_new)
        if df_new.empty:
            df_new = pd.DataFrame(columns=["enabled", "delete", "center_label", "mode", "lon", "lat", "address"])
        # delete 컬럼은 버튼으로만 삭제용으로 쓰고, 기본은 False로 유지
        if "delete" not in df_new.columns:
            df_new["delete"] = False
        df_new["delete"] = df_new["delete"].fillna(False).astype(bool)
        st.session_state["centers_df"] = df_new.reset_index(drop=True).copy()

    def _next_center_label(df: pd.DataFrame) -> str:
        used = set(df.get("center_label", pd.Series(dtype=str)).astype(str).str.strip().tolist())
        for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
            if ch not in used:
                return ch
        return f"C{len(df) + 1}"

    def _bump_editor():
        # data_editor 상태를 초기화하여 행 추가/삭제 후 화면과 데이터가 꼬이지 않도록 함
        for k in list(st.session_state.keys()):
            if str(k).startswith("centers_editor__v") or str(k) == "centers_editor":
                try:
                    del st.session_state[k]
                except Exception:
                    pass
        st.session_state["centers_editor_ver"] = int(st.session_state.get("centers_editor_ver", 0)) + 1

    cbtn1, cbtn2 = st.columns([1, 1], gap="small")
    with cbtn1:
        if st.button("행 추가", use_container_width=True):
            df0 = _current_centers_df()
            df0.loc[len(df0)] = {
                "enabled": True,
                "delete": False,
                "center_label": _next_center_label(df0),
                "mode": "좌표",
                "lon": "",
                "lat": "",
                "address": "",
                "row_id": __import__("uuid").uuid4().hex[:10],
            }
            _set_centers_df(df0)
            _bump_editor()
            st.rerun()

    with cbtn2:
        if st.button("선택 삭제", use_container_width=True):
            df0 = _current_centers_df()
            if "delete" in df0.columns:
                df0 = df0[df0["delete"] != True].copy()  # noqa: E712
            if "delete" in df0.columns:
                df0["delete"] = False
            _set_centers_df(df0)
            _bump_editor()
            st.rerun()
        # (개선) 화면이 좁아져도 컬럼이 과도하게 압축되지 않도록,
    # data_editor + 가로 스크롤(overflow-x) 기반으로 표를 렌더링합니다.
    df_ui = _current_centers_df().copy()
    if df_ui.empty:
        df_ui = pd.DataFrame(
            [
                {"enabled": True, "delete": False, "center_label": "A", "mode": "좌표", "lon": "127.0", "lat": "37.5", "address": "", "row_id": __import__("uuid").uuid4().hex[:10]},
                {"enabled": False, "delete": False, "center_label": "B", "mode": "주소(자동)", "lon": "", "lat": "", "address": "", "row_id": __import__("uuid").uuid4().hex[:10]},
            ]
        )
        _set_centers_df(df_ui)

    # row_id 보정(행 식별용)
    if "row_id" not in df_ui.columns:
        df_ui["row_id"] = [__import__("uuid").uuid4().hex[:10] for _ in range(len(df_ui))]
    else:
        rid = df_ui["row_id"].astype(str).fillna("").str.strip()
        miss = rid.eq("") | rid.eq("nan")
        if miss.any():
            df_ui.loc[miss, "row_id"] = [__import__("uuid").uuid4().hex[:10] for _ in range(int(miss.sum()))]

    display_cols = ["enabled", "delete", "center_label", "mode", "lon", "lat", "address"]
    for c in display_cols:
        if c not in df_ui.columns:
            df_ui[c] = "" if c not in ("enabled", "delete") else False

    df_disp = df_ui[display_cols].copy()

    mode_options = ["좌표", "주소(자동)", "도로명", "지번"]

    col_cfg = {
        "enabled": st.column_config.CheckboxColumn("enabled", width="small", help="분석에 포함할 중심지"),
        "delete": st.column_config.CheckboxColumn("삭제", width="small", help="체크 후 '선택 삭제' 버튼으로 삭제"),
        "center_label": st.column_config.TextColumn("라벨(비교용)", width="small"),
        "mode": st.column_config.SelectboxColumn("입력방식", options=mode_options, width="small"),
        "lon": st.column_config.TextColumn("경도(lon)", width="small"),
        "lat": st.column_config.TextColumn("위도(lat)", width="small"),
        "address": st.column_config.TextColumn("주소(도로명/지번)", width="large"),
    }

    centers_editor_key = f"centers_editor__v{int(st.session_state.get('centers_editor_ver', 0))}"

    def _sync_centers_from_editor():
        """data_editor 편집값을 session_state['centers_df']에 즉시 반영합니다."""
        ed_df = _editor_state_to_df(st.session_state.get(centers_editor_key), df_disp)
        if ed_df is None or getattr(ed_df, "empty", False):
            return
        # row_id는 내부 식별자이므로 원본 순서를 유지
        if "row_id" in df_ui.columns and len(ed_df) == len(df_ui):
            ed_df["row_id"] = df_ui["row_id"].values
        _set_centers_df(ed_df)

    edited = st.data_editor(
        df_disp,
        hide_index=True,
        use_container_width=True,
        num_rows="fixed",
        column_config=col_cfg,
        key=centers_editor_key,
        on_change=_sync_centers_from_editor,
    )

    # (안전장치) 반환값도 동일하게 반영
    try:
        df_new = _editor_state_to_df(edited, df_disp)
        if "row_id" in df_ui.columns and len(df_new) == len(df_ui):
            df_new["row_id"] = df_ui["row_id"].values
        _set_centers_df(df_new)
    except Exception:
        pass

    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown("---")
    # -------------------------
    # 반경 입력 (요구사항: 입력적용 아래, 분석 방식 선택 위)
    # -------------------------
    st.caption("반경은 50m~400m 범위에서 50m 단위로 입력하세요. (예: 50,100,150)")
    if "radii_str" not in st.session_state:
        st.session_state["radii_str"] = "100,200,300"
    radii_str = st.text_input("반경(m) : 50m~400m, 50m단위 입력", key="radii_str")
    _radii_tmp = []
    for t in str(radii_str or "").split(","):
        t = t.strip()
        if not t:
            continue
        try:
            v = int(float(t))
        except Exception:
            continue
        if v < 50 or v > 400:
            continue
        if v % 50 != 0:
            continue
        _radii_tmp.append(v)
    radii = sorted(list(set(_radii_tmp))) if _radii_tmp else [100, 200, 300]
    # BigData 라벨 파일 필터에 사용할 반경 리스트(복수 가능)
    radii_for_bigdata = list(radii) if radii else [100]

    st.subheader("분석 방식 선택")
    analysis_mode = st.radio(
        " ",
        options=["전문가 분석", "Big Data 분석"],
        horizontal=True,
        label_visibility="collapsed",
        key="analysis_mode",
    )
    st.caption("선택된 분석 방식은 화면 표시/리포트 메타정보에 저장됩니다. (분석 로직은 기존과 동일)")

    
    # -------------------------
    # (추가) Big Data 분석: mainbiz_mix_table 업로드 + 전체 라벨 후보 한 번에 보기/선택(선택사항)
    # -------------------------
    if analysis_mode == "Big Data 분석":
        st.markdown("#### Big Data 분석 입력 (mainbiz_mix_table_AFTER_auto_최종결과물)")
        st.caption("엑셀(xlsx/xls) 또는 csv 파일을 업로드하세요. (컬럼: 시도명, 시군구명, 상권명, mix_type_topgap_v2)")

        up = st.file_uploader(
            "mainbiz_mix_table_AFTER_auto_최종결과물 업로드",
            type=["xlsx", "xls", "csv"],
            key="bigdata_mix_uploader",
        )

        # 업로드 파일 변경 감지(중요): 업로드가 바뀌면 라벨별 후보 표(data_editor) 상태를 모두 리셋
        # - Streamlit은 widget key가 같으면 이전 상태를 재사용하므로, 업로드 변경 시점에 key를 '버전'으로 분리합니다.
        upload_name = getattr(up, "name", None) if up is not None else None
        upload_size = getattr(up, "size", None) if up is not None else None
        upload_sig = f"{upload_name}|{upload_size}"

        if "bigdata_upload_sig" not in st.session_state:
            st.session_state["bigdata_upload_sig"] = None
        if "bigdata_upload_rev" not in st.session_state:
            st.session_state["bigdata_upload_rev"] = 0

        if upload_sig != st.session_state["bigdata_upload_sig"]:
            st.session_state["bigdata_upload_sig"] = upload_sig
            st.session_state["bigdata_upload_rev"] = int(st.session_state["bigdata_upload_rev"]) + 1

            # 기존 후보표/선택 결과 초기화 (업로드가 바뀌었는데 과거 표 상태가 남아 있으면 오류/불일치가 발생할 수 있음)
            for k in list(st.session_state.keys()):
                if str(k).startswith("mix_cand_editor__"):
                    try:
                        del st.session_state[k]
                    except Exception:
                        pass
            try:
                st.session_state["bigdata_selected_by_label"] = {}
            except Exception:
                pass

        # 실제 파일 읽기
        mix_df = _read_mix_table(up) if up is not None else pd.DataFrame()
        if mix_df.empty:
            # 업로드가 없으면, (가능한 경우) 로컬 기본 파일을 시도합니다.
            # - Streamlit Cloud에서는 파일이 없을 수 있으므로 실패해도 무시합니다.
            try:
                default_path = os.path.join(os.path.dirname(__file__), "mainbiz_mix_table_AFTER_auto_최종결과물.csv")
                if os.path.exists(default_path):
                    mix_df = pd.read_csv(default_path, encoding="utf-8")
            except Exception:
                mix_df = pd.DataFrame()

        st.session_state["bigdata_mix_df"] = mix_df

        if mix_df.empty:
            st.warning("업로드된 mainbiz_mix_table을 읽지 못했습니다. 파일 형식/인코딩/컬럼명을 확인해주세요.")
        else:
            st.success(f"mainbiz_mix_table 로드 완료: {len(mix_df):,} rows / {len(mix_df.columns)} cols")

        # 라벨별로 주소에서 (시도명, 시군구명) 추출 → 후보 상권 리스트 표시
        centers_all = _current_centers_df()
        enabled_centers = centers_all[centers_all.get("enabled", False) == True].copy()  # noqa: E712
        if enabled_centers.empty:
            st.info("enabled=True 인 중심지가 없어서, 후보를 표시할 수 없습니다.")
        else:
            rev = int(st.session_state.get("bigdata_upload_rev", 0))

            # (추가) 전체 라벨 후보를 한 번에 보기/선택 (선택사항)
            with st.expander("전체 라벨 후보 한 번에 보기 (선택사항)", expanded=False):
                all_rows = []
                for j, rr in enabled_centers.reset_index(drop=True).iterrows():
                    _label = str(rr.get("center_label", "") or f"C{j+1}").strip() or f"C{j+1}"
                    _addr = str(rr.get("address", "") or "").strip()
                    _sido, _sigg = _parse_sido_sigg_from_address(_addr)
                    _cand = _build_mix_candidates_for_center(mix_df, _sido or "", _sigg or "")
                    if _cand is None or _cand.empty:
                        continue
                    _cand2 = _cand.copy()
                    _cand2.insert(0, "label", _label)
                    _cand2.insert(1, "idx", int(j))
                    all_rows.append(_cand2)

                if not all_rows:
                    st.info("표시할 후보가 없습니다. (주소에서 시도/시군구 추출 실패 또는 매칭 후보 없음)")
                else:
                    all_cand = pd.concat(all_rows, ignore_index=True)
                    all_cand["row_key"] = (
                        all_cand["label"].astype(str).str.strip() + "|" +
                        all_cand["시도명"].astype(str).str.strip() + "|" +
                        all_cand["시군구명"].astype(str).str.strip() + "|" +
                        all_cand["상권명"].astype(str).str.strip() + "|" +
                        all_cand["mix_type_topgap_v2"].astype(str).str.strip()
                    )

                    editor_key_all = f"mix_cand_editor__ALL__rev{rev}"
                    data_key_all = f"{editor_key_all}__data"
                    view_cols_all = ["select", "label", "idx", "시도명", "시군구명", "상권명", "mix_type_topgap_v2"]

                    prev_all = _coerce_df(st.session_state.get(data_key_all))
                    if (not prev_all.empty) and ("row_key" in prev_all.columns):
                        prev_pick = (
                            prev_all[["row_key", "select"]]
                            .drop_duplicates(subset=["row_key"], keep="last")
                            .rename(columns={"select": "select_prev"})
                        )
                        all_cand = all_cand.drop(columns=["select"], errors="ignore").merge(prev_pick, on="row_key", how="left")
                        all_cand["select"] = all_cand["select_prev"].fillna(False).astype(bool)
                        all_cand = all_cand.drop(columns=["select_prev"], errors="ignore")
                    else:
                        all_cand["select"] = all_cand.get("select", False)
                        all_cand["select"] = all_cand["select"].fillna(False).astype(bool)

                    st.session_state[data_key_all] = all_cand.copy()
                    display_all = all_cand[view_cols_all].copy()

                    def _sync_all_candidates_from_editor():
                        base_full = _coerce_df(st.session_state.get(data_key_all))
                        edited_df = _editor_state_to_df(st.session_state.get(editor_key_all), base_full[view_cols_all])
                        if edited_df is None or getattr(edited_df, "empty", False):
                            return
                        merged_full = base_full.copy()
                        if len(merged_full) == len(edited_df):
                            for col in view_cols_all:
                                if col in edited_df.columns:
                                    merged_full[col] = edited_df[col].values
                        else:
                            for col in view_cols_all:
                                if col in edited_df.columns and col in merged_full.columns:
                                    merged_full[col] = edited_df[col]
                        merged_full["select"] = merged_full["select"].fillna(False).astype(bool)
                        st.session_state[data_key_all] = merged_full

                    edited_all = st.data_editor(
                        display_all,
                        hide_index=True,
                        use_container_width=True,
                        num_rows="fixed",
                        column_config={
                            "select": st.column_config.CheckboxColumn("선택", width="small"),
                            "label": st.column_config.TextColumn("라벨", width="small"),
                            "idx": st.column_config.NumberColumn("idx", width="small", disabled=True),
                            "시도명": st.column_config.TextColumn("시도명", width="small"),
                            "시군구명": st.column_config.TextColumn("시군구명", width="small"),
                            "상권명": st.column_config.TextColumn("상권명", width="medium"),
                            "mix_type_topgap_v2": st.column_config.TextColumn("mix_type_topgap_v2", width="medium"),
                        },
                        key=editor_key_all,
                        on_change=_sync_all_candidates_from_editor,
                    )

                    edited_all = _editor_state_to_df(edited_all, display_all)
                    full_all = st.session_state[data_key_all].copy()
                    if len(full_all) == len(edited_all):
                        for col in view_cols_all:
                            if col in edited_all.columns:
                                full_all[col] = edited_all[col].values
                    full_all["select"] = full_all["select"].fillna(False).astype(bool)
                    st.session_state[data_key_all] = full_all.copy()
                    sel_all = full_all[full_all["select"] == True].copy()  # noqa: E712
                    st.caption(f"(전체) 후보 {len(full_all):,}개 / 선택 {len(sel_all):,}개")

                    if st.button("전체 선택 결과를 라벨별 선택 결과에 반영", key=f"btn_sync_sel_all__rev{rev}"):
                        st.session_state.setdefault("bigdata_selected_by_label", {})
                        new_map = {}
                        if not sel_all.empty and "label" in sel_all.columns:
                            for lab, g in sel_all.groupby("label"):
                                new_map[str(lab)] = g[["시도명", "시군구명", "상권명", "mix_type_topgap_v2"]].copy()
                        st.session_state["bigdata_selected_by_label"] = new_map
                        # (추가) mix_type_topgap_v2 기준으로 업로드 UI를 만들기 위해 저장
                        mix_types = []
                        if (not sel_all.empty) and ("mix_type_topgap_v2" in sel_all.columns):
                            mix_types = sorted(list({str(x).strip() for x in sel_all["mix_type_topgap_v2"].dropna().astype(str).tolist() if str(x).strip()}))
                        st.session_state["bigdata_selected_mix_types"] = mix_types
                        st.success("라벨별 선택 결과를 업데이트했습니다.")

                # -------------------------
                # (추가) 선택된 mix_type_topgap_v2 값별 BigData 분석파일 업로드 → 후보 업종 조회/선택 → 소분류 가중치 반영
                # -------------------------
                sel_mix_types = st.session_state.get("bigdata_selected_mix_types", []) or []
                if sel_mix_types:
                    st.markdown("---")
                    st.subheader("선택된 상권유형별 BigData 분석파일 업로드 & 후보 업종 선택")

                    if not str(my_business or "").strip():
                        st.warning("먼저 상단의 **관심 업종(내 업종) - 라벨용** 을 입력하세요. (예: 카페)")

                    st.caption('업로드 파일에서 **cat_a(내 업종)** 와 **radius_label(선택 반경)** 를 필터링한 뒤, **w_prior** 내림차순으로 후보를 보여줍니다.')

                    all_selected_rows = []

                    for mt in sel_mix_types:
                        mt_str = str(mt)
                        mt_key = re.sub(r"[^0-9a-zA-Z가-힣_]+", "_", mt_str)

                        st.markdown(f"**{mt_str} 상권특성의 업종간 시너지-경쟁 BigData 분석파일 업로드**")
                        up2 = st.file_uploader(
                            f"{mt_str} 상권특성의 업종간 시너지-경쟁 BigData 분석파일 업로드",
                            type=["xlsx", "xls", "csv"],
                            key=f"bigdata_synergy_uploader__{mt_key}__rev{rev}",
                        )
                        if up2 is None:
                            continue

                        df_raw = _read_mix_table(up2)
                        if df_raw is None or df_raw.empty:
                            st.warning(f"[{mt_str}] 업로드 파일을 읽지 못했습니다. (xlsx/xls/csv 확인)")
                            continue

                        # 필수 컬럼 확인
                        req_cols = ["cat_a", "cat_B", "w_prior", "radius_label", "cand_type"]
                        miss = [c for c in req_cols if c not in df_raw.columns]
                        if miss:
                            st.warning(f"[{mt_str}] 업로드 파일에 필요한 컬럼이 없습니다: {miss}")
                            continue

                        df = df_raw.copy()

                        # 필터: cat_a == my_business
                        myb = str(my_business or "").strip()
                        df["cat_a__norm"] = df["cat_a"].astype(str).str.strip()
                        df = df[df["cat_a__norm"].eq(myb)] if myb else df.iloc[0:0]
                        if df.empty:
                            st.info(f"[{mt_str}] cat_a == '{myb}' 필터 결과가 없습니다.")
                            continue

                        # 필터: radius_label == radius_label_selected
                        def _to_int_radius(v):
                            try:
                                s = str(v).strip()
                                m2 = re.search(r"(\d+)", s)
                                return int(m2.group(1)) if m2 else None
                            except Exception:
                                return None

                        df["radius_label__int"] = df["radius_label"].apply(_to_int_radius)
                        df = df[df["radius_label__int"].isin([int(x) for x in (radii_for_bigdata or [])])]
                        if df.empty:
                            st.info(f"[{mt_str}] radius_label in {sorted([int(x) for x in (radii_for_bigdata or [])])} 필터 결과가 없습니다.")
                            continue

                        df["w_prior__num"] = pd.to_numeric(df["w_prior"], errors="coerce")
                        df = df.dropna(subset=["w_prior__num"]).copy()
                        df = df.sort_values("w_prior__num", ascending=False)

                        show = df.copy()
                        # NOTE: 업로드 파일에 이미 '상권유형' 컬럼이 있을 수 있으므로 insert 중복 오류 방지
                        if "상권유형" in show.columns:
                            show["상권유형"] = mt_str
                        show.insert(0, "select", False)
                        if "상권유형" not in show.columns:
                            show.insert(1, "상권유형", mt_str)

                        show_cols = ["select", "상권유형", "cat_a", "cat_B", "w_prior", "radius_label", "cand_type"]
                        for c in show_cols:
                            if c not in show.columns:
                                show[c] = ""
                        show = show[show_cols].copy()

                        editor_key = f"editor_bigdata_synergy__{mt_key}__rev{rev}"
                        edited = st.data_editor(
                            show,
                            use_container_width=True,
                            hide_index=True,
                            num_rows="fixed",
                            column_config={
                                "select": st.column_config.CheckboxColumn("선택", width="small"),
                                "상권유형": st.column_config.TextColumn("상권유형", width="medium"),
                                "cat_a": st.column_config.TextColumn("cat_a", width="small"),
                                "cat_B": st.column_config.TextColumn("cat_B", width="medium"),
                                "w_prior": st.column_config.NumberColumn("w_prior", width="small"),
                                "radius_label": st.column_config.TextColumn("radius_label", width="small"),
                                "cand_type": st.column_config.TextColumn("cand_type", width="small"),
                            },
                            key=editor_key,
                        )

                        sel2 = edited[edited["select"] == True]  # noqa: E712
                        st.caption(f"[{mt_str}] 후보 {len(edited):,}개 / 선택 {len(sel2):,}개")
                        if not sel2.empty:
                            all_selected_rows.append(sel2.copy())

                    if all_selected_rows:
                        merged = pd.concat(all_selected_rows, ignore_index=True)
                        merged["w_prior__num"] = pd.to_numeric(merged["w_prior"], errors="coerce")
                        merged = merged.dropna(subset=["w_prior__num"]).copy()

                        # cat_B가 여러 반경에서 중복될 수 있으므로(입력 반경이 여러 개일 때) cat_B별 w_prior 평균을 사용
                        best = (
                            merged.groupby("cat_B", as_index=False)["w_prior__num"].mean()
                            .rename(columns={"w_prior__num": "w_prior__num_mean"})
                        )

                        if st.button("✅ 선택한 cat_B/w_prior를 소분류 가중치에 반영", key=f"btn_apply_weights_from_bigdata__rev{rev}"):
                            lines_out = []
                            for _, rr in best.iterrows():
                                cb = str(rr.get("cat_B", "") or "").strip()
                                wv = float(rr.get("w_prior__num_mean", rr.get("w_prior__num", 0.0)) or 0.0)
                                if not cb:
                                    continue
                                lines_out.append(f"{cb}={wv:+.3f}")

                            if lines_out:
                                st.session_state["weight_str_manual"] = "\n".join(lines_out)
                                # 소분류명(관심 카테고리)에 선택된 cat_B를 자동 포함
                                cur = _split_csv_list(st.session_state.get("scls_in_bigdata", ""))
                                add = [str(x).strip() for x in best["cat_B"].astype(str).tolist() if str(x).strip()]
                                union = list(dict.fromkeys(cur + add))
                                st.session_state["scls_in_bigdata"] = ",".join(union)

                                st.success("소분류 가중치가 업데이트되었습니다. (아래 '업종 필터/가중치'에서 확인)")
                                st.rerun()
                            else:
                                st.warning("반영할 선택 결과가 없습니다.")
                    else:
                        st.info("선택한 후보 업종이 없습니다. (각 상권유형 표에서 체크 후 아래 버튼을 누르세요.)")
    # -------------------------
    # (추가 끝)
    # -------------------------


    st.subheader("업종 필터/가중치")
    st.caption("대/중/소분류 필터는 선택입니다. 소분류를 지정하면 그 소분류들에 대해 점수(가중치×개수×거리감쇠)를 계산합니다.")

    lcls_in = st.text_input("대분류명 필터(쉼표, 선택)", value="")
    mcls_in = st.text_input("중분류명 필터(쉼표, 선택)", value="")
    if "scls_in_bigdata" not in st.session_state:
        st.session_state["scls_in_bigdata"] = "카페,편의점,세탁소,코인빨래방"
    scls_in = st.text_input("소분류명(관심 카테고리) (쉼표, 선택)", key="scls_in_bigdata")


    scls_list = _split_csv_list(scls_in)
    lcls_list = _split_csv_list(lcls_in)
    mcls_list = _split_csv_list(mcls_in)

    if "weight_str_manual" not in st.session_state:
        st.session_state["weight_str_manual"] = "카페=+3\\n편의점=+1\\n세탁소=-3\\n코인빨래방=-5"

    st.text_area(
        "소분류 가중치 (예: 카페=+3, 편의점=+1, 세탁소=-2)\\n또는 소분류 순서대로 숫자: 3,1,-2",
        height=120,
        key="weight_str_manual",
    )
    weight_str = st.session_state.get("weight_str_manual", "")
    wmap = parse_scls_weight_map(weight_str, scls_list)


    st.markdown("---")
    use_sgis = st.checkbox("SGIS 행정동 경계 표시", value=bool(sgis_key and sgis_secret))
    map_engine = st.radio("지도 엔진", ["pydeck(추천)", "folium(VWorld/OSM)"], horizontal=True, index=0)
    use_vworld_tiles = st.checkbox("VWorld 배경지도 사용(folium에서만)", value=bool(vworld_key))

    # (요구사항 3~4) folium에서 지도 확대/전체화면 + Heatmap 옵션
    # pydeck 선택 시에도 값은 저장되지만(세션 유지), 실제 적용은 folium에서만 합니다.
    folium_zoom = 13
    folium_height = 650
    folium_fullscreen = True
    folium_heatmap = True
    heat_weight_mode = "uniform"
    heat_radius_px = 18
    heat_blur_px = 15
    heat_min_opacity = 0.2

    if map_engine.startswith("folium"):
        st.markdown("##### folium 표시 옵션")
        folium_zoom = st.slider("지도 초기 확대(zoom)", min_value=10, max_value=19, value=13, step=1)
        folium_height = st.slider("지도 높이(px)", min_value=450, max_value=1300, value=800, step=50)
        folium_fullscreen = st.checkbox("전체화면(Fullscreen) 버튼 추가", value=True)

        folium_heatmap = st.checkbox("Heatmap 레이어 추가", value=True)
        if folium_heatmap:
            heat_weight_mode = st.selectbox(
                "Heatmap 가중치 방식",
                options=["uniform", "distance_decay", "scls_weighted"],
                format_func=lambda x: {
                    "uniform": "균등(점 개수 기반)",
                    "distance_decay": "거리감쇠(exp(-d/DECAY))",
                    "scls_weighted": "소분류 가중치×거리감쇠 (음수는 0 처리)",
                }.get(x, x),
            )
            heat_radius_px = st.slider("Heatmap 반경(radius, px)", min_value=5, max_value=50, value=18, step=1)
            heat_blur_px = st.slider("Heatmap blur(px)", min_value=5, max_value=50, value=15, step=1)
            heat_min_opacity = st.slider("Heatmap 최소투명도", min_value=0.0, max_value=1.0, value=0.2, step=0.05)


    # -------------------------
    # 배후수요(인구/직장인 proxy) + 주거유형 추가 점수 설정
    # -------------------------
    st.markdown("---")
    with st.expander("배후수요/주거유형(행정동) 점수(추가)", expanded=False):
        st.caption("행정동별 (A)면적겹침×(B)거리감쇠 = 기여도로 가중합하여 배후수요/주거유형 점수를 만듭니다.")

        if not (sgis_key and sgis_secret):
            st.info("SGIS 키/시크릿이 없으면 배후수요/주거유형 점수는 계산되지 않습니다.")

        enable_demand = st.checkbox("배후수요(인구/직장인 proxy) 점수 계산", value=True)
        enable_housing = st.checkbox("주거유형(가구수×유형가중치) 점수 계산", value=True)

        demand_decay_m = st.number_input("행정동 기여도 거리감쇠 DECAY(m)", min_value=50.0, max_value=5000.0,
                                         value=float(DIST_DECAY_M), step=10.0)

        decay_mode = st.selectbox("거리감쇠 함수", options=[
            ("exp", "exp(-d/DECAY)"),
            ("inv", "1/(1+d/DECAY)"),
        ], index=0, format_func=lambda x: x[1])[0]

        st.markdown("**직장인(연령별) 처리**")
        use_employee_proxy = st.checkbox("직장인 proxy로 종업원수(employee_cnt) 포함", value=True)
        employee_year = st.number_input("종업원수(employee_cnt) 기준연도(2000~2023)", min_value=2000, max_value=2023, value=2023, step=1)
        employee_weight = st.slider("직장인 proxy 가중치(전체)", min_value=0.0, max_value=3.0, value=1.0, step=0.05)
        split_employee_by_age = st.checkbox("직장인 proxy를 연령별로 분해(추측 옵션)", value=False)
        st.caption("확실하지 않음: SGIS OpenAPI에서 '직장인(연령별)' 직접 제공 엔드포인트를 확인하지 못해, "
                   "employee_cnt(종업원수)를 직장인 proxy로 사용합니다. 연령별 분해는 (추측입니다) 거주인구 연령분포로 비례배분합니다.")

        st.markdown("**연령대 타깃 가중치**")
        age_defaults = {k: 1.0 for k, _, _ in AGE_BANDS}
        age_aliases = {
            "10대미만": "u10", "10미만": "u10", "u10": "u10",
            "10대": "10s", "10s": "10s",
            "20대": "20s", "20s": "20s",
            "30대": "30s", "30s": "30s",
            "40대": "40s", "40s": "40s",
            "50대": "50s", "50s": "50s",
            "60대": "60s", "60s": "60s",
            "70대+": "70p", "70+": "70p", "70p": "70p",
        }
        age_weight_text = st.text_area(
            "예: 20s=2, 30s=1.5 (키: u10,10s,20s,30s,40s,50s,60s,70p)",
            value="20s=1\n30s=1\n40s=1\n50s=1",
            height=120,
        )
        age_weights = parse_kv_weight_map(age_weight_text, age_defaults, aliases=age_aliases)

        st.markdown("**주거유형 가중치**")
        house_defaults = {k: 0.0 for k, _, _ in HOUSE_TYPES}
        house_aliases = {
            "아파트": "apart", "apart": "apart",
            "연립/다세대": "row", "연립": "row", "다세대": "row", "row": "row",
            "오피스텔": "officetel", "officetel": "officetel",
            "단독주택": "detach", "단독": "detach", "detach": "detach",
            "기숙사/사회시설": "dorm", "기숙사": "dorm", "사회시설": "dorm", "dorm": "dorm",
            "기타": "etc", "etc": "etc",
        }
        house_weight_text = st.text_area(
            "예: apart=1, row=0.8, officetel=1.2, detach=0 (키: apart,row,officetel,detach,dorm,etc)",
            value="apart=1\nrow=1\nofficetel=1\ndetach=0",
            height=120,
        )
        house_weights = parse_kv_weight_map(house_weight_text, house_defaults, aliases=house_aliases)

        st.markdown("**스케일 변환/정규화(추천)**")
        norm_method = st.selectbox(
            "정규화 방식(Sstore/D/H → *_norm)",
            options=[
                ("log1p_minmax", "log1p + min-max (추천)"),
                ("minmax", "min-max"),
                ("none", "정규화 안함"),
            ],
            index=0,
            format_func=lambda x: x[1],
        )[0]

        st.markdown("**최종 가중치(공식)**")
        alpha = st.slider("α (상가점수 가중치)", min_value=-10.0, max_value=10.0, value=1.0, step=0.1)
        gamma = st.slider("γ (배후수요 가중치)", min_value=-10.0, max_value=10.0, value=1.0, step=0.1)
        eta = st.slider("η (주거유형 가중치)", min_value=-10.0, max_value=10.0, value=1.0, step=0.1)
        st.caption("Stotal(r) = α·Sstore_norm(r) + γ·D_norm(r) + η·H_norm(r)")

    # 분석 함수로 전달할 config
    demand_cfg = {
        "enabled": bool(enable_demand),
        "decay_m": float(demand_decay_m),
        "decay_mode": str(decay_mode),
        "employee_year": int(employee_year),
        "use_employee_proxy": bool(use_employee_proxy),
        "employee_weight": float(employee_weight),
        "split_employee_by_age": bool(split_employee_by_age),
        "age_weights": dict(age_weights),
        "norm_method": str(norm_method),
    }
    housing_cfg = {
        "enabled": bool(enable_housing),
        "house_weights": dict(house_weights),
        "norm_method": str(norm_method),
    }

    run_btn = st.button("분석 실행", type="primary", use_container_width=True)



def _resolve_centers(centers_df: pd.DataFrame, vworld_key: str, secrets_for_redact: List[str]) -> Tuple[pd.DataFrame, List[str]]:
    """
    centers_df -> enabled & resolved lon/lat
    returns (resolved_df, warnings)
    """
    warns = []
    if centers_df is None or centers_df.empty:
        return pd.DataFrame(columns=["center_id", "center_label", "lon", "lat"]), ["중심지 입력이 없습니다."]

    df = centers_df.copy()
    df = df[df["enabled"] == True].copy()  # noqa: E712
    if df.empty:
        return pd.DataFrame(columns=["center_id", "center_label", "lon", "lat"]), ["enabled=True 인 중심지가 없습니다."]

    resolved = []
    for idx, r in df.reset_index(drop=True).iterrows():
        label = str(r.get("center_label", "") or f"C{idx+1}").strip() or f"C{idx+1}"
        mode = str(r.get("mode", "좌표")).strip()
        lon = _safe_float(r.get("lon"))
        lat = _safe_float(r.get("lat"))
        addr = str(r.get("address", "") or "").strip()

        if mode in ("주소(자동)", "도로명", "지번"):
            if not addr:
                warns.append(f"[{label}] 주소가 비어 있습니다.")
                continue
            if not vworld_key:
                warns.append(f"[{label}] 주소 입력은 VWorld key가 필요합니다.")
                continue

            out = None
            try:
                if mode == "도로명":
                    out = geocode_vworld(addr, vworld_key, "ROAD")
                elif mode == "지번":
                    out = geocode_vworld(addr, vworld_key, "PARCEL")
                else:
                    out = geocode_vworld(addr, vworld_key, "ROAD") or geocode_vworld(addr, vworld_key, "PARCEL")
            except Exception as e:
                warns.append(_redact_text(f"[{label}] 지오코딩 실패: {e}", secrets_for_redact))
                continue

            if not out:
                warns.append(f"[{label}] 지오코딩 결과가 없습니다: {addr}")
                continue
            lon, lat = out

        if lon is None or lat is None:
            warns.append(f"[{label}] 좌표가 올바르지 않습니다.")
            continue
        if not (-180.0 <= lon <= 180.0 and -90.0 <= lat <= 90.0):
            warns.append(f"[{label}] 경도/위도 범위가 올바르지 않습니다: lon={lon}, lat={lat}")
            continue

        resolved.append({
            "center_id": f"C{idx+1}",
            "center_label": label,
            "lon": float(lon),
            "lat": float(lat),
        })

    if not resolved:
        return pd.DataFrame(columns=["center_id", "center_label", "lon", "lat"]), warns or ["유효한 중심지가 없습니다."]
    return pd.DataFrame(resolved), warns


with right:
    st.subheader("결과")

    if not HAS_PUBLICDATAREADER:
        st.warning("PublicDataReader가 설치되어 있어야 공공데이터포털 상가정보를 가져올 수 있습니다. (requirements 파일 참고)")

    if map_engine.startswith("pydeck") and not HAS_PYDECK:
        st.warning("pydeck를 불러오지 못했습니다. 'folium'으로 전환하거나 pip install pydeck 를 실행하세요.")

    # 실행 버튼을 눌렀을 때만 분석을 갱신하고, 그 결과는 session_state에 저장해 계속 표시
    if run_btn:
        if not service_key:
            st.error("공공데이터포털 서비스키가 필요합니다.")
            st.stop()
        if not radii:
            st.error("반경을 1개 이상 입력하세요.")
            st.stop()
        # centers_df는 UI 편집 결과(session_state)를 기준으로 가져옵니다.
        centers_df = _current_centers_df().copy()


        centers_resolved, warns = _resolve_centers(centers_df, vworld_key=vworld_key, secrets_for_redact=_secrets_for_redact)
        if warns:
            for w in warns:
                st.warning(_redact_text(w, _secrets_for_redact))
        if centers_resolved.empty:
            st.error("유효한 중심지가 없습니다. 중심지 입력을 확인하세요.")
            st.stop()

        with st.spinner("데이터 수집/분석 중..."):
            # 캐시 fingerprint
            service_key_fp = _fingerprint(service_key)
            sgis_token_fp = None

            sgis_token = None
            if use_sgis and sgis_key and sgis_secret:
                sgis_token = fetch_sgis_token(_fingerprint(sgis_key), _fingerprint(sgis_secret))
                if sgis_token:
                    st.session_state["_rt_sgis_token"] = sgis_token
                    sgis_token_fp = _fingerprint(sgis_token)

            results: List[AnalysisResult] = []
            errors = []

            for _, c in centers_resolved.iterrows():
                cid = str(c["center_id"])
                label = str(c["center_label"])
                lon = float(c["lon"])
                lat = float(c["lat"])
                try:
                    ar = run_analysis_single(
                        center_id=cid,
                        center_label=label,
                        service_key_fp=service_key_fp,
                        center_lon=lon,
                        center_lat=lat,
                        radii=radii,
                        lcls=lcls_list,
                        mcls=mcls_list,
                        scls=scls_list,
                        scls_weights=wmap,
                        sgis_token_fp=sgis_token_fp,
                        demand_cfg=demand_cfg,
                        housing_cfg=housing_cfg,
                    )
                    ar.meta['analysis_mode'] = analysis_mode
                    results.append(ar)
                except Exception as e:
                    # 에러 메시지에서 키 노출 방지
                    msg = _redact_text(f"[{label}] 분석 실패: {type(e).__name__}: {e}", _secrets_for_redact)
                    errors.append(msg)

            st.session_state["analysis_results"] = results
            st.session_state["analysis_errors"] = errors
            st.session_state["analysis_inputs"] = {
                "my_business": my_business,
                "radii": radii,
                "scls_list": scls_list,
                "scls_weights": wmap,
                "map_engine": map_engine,
                "use_vworld_tiles": use_vworld_tiles,
                "use_sgis": use_sgis,
                "alpha": float(alpha),
                "gamma": float(gamma),
                "eta": float(eta),
                "norm_method": str(norm_method),
                "demand_cfg": demand_cfg,
                "housing_cfg": housing_cfg,

                # folium 옵션
                "folium_zoom": folium_zoom,
                "folium_height": folium_height,
                "folium_fullscreen": folium_fullscreen,
                "folium_heatmap": folium_heatmap,
                "heat_weight_mode": heat_weight_mode,
                "heat_radius_px": heat_radius_px,
                "heat_blur_px": heat_blur_px,
                "heat_min_opacity": heat_min_opacity,
            }

    # ---- 항상 표시 영역 (세션에 결과가 있으면 보여줌) ----
    results: List[AnalysisResult] = st.session_state.get("analysis_results", []) or []
    errors = st.session_state.get("analysis_errors", []) or []
    inputs = st.session_state.get("analysis_inputs", {}) or {}

    if errors:
        st.error("일부 중심지 분석이 실패했습니다.")
        for e in errors:
            st.write("- " + str(e))

    if not results:
        st.info("왼쪽에서 설정 후 **분석 실행**을 누르세요. (실행 후 결과/지도가 계속 유지됩니다.)")
        st.stop()

    # 집계
    centers_out = pd.DataFrame([{
        "center_id": r.center_id,
        "center_label": r.center_label,
        "lon": r.center_lon,
        "lat": r.center_lat,
        "raw_rows": r.meta.get("raw_rows", 0),
        "master_rows": r.meta.get("master_rows", 0),
        "dropped_no_coord": r.meta.get("dropped_no_coord", 0),
        "dropped_outside": r.meta.get("dropped_outside", 0),
    } for r in results])

    df_master_all = pd.concat([r.df_master for r in results if r.df_master is not None and not r.df_master.empty], ignore_index=True) \
        if any((r.df_master is not None and not r.df_master.empty) for r in results) else pd.DataFrame()

    df_summary_all = pd.concat([r.df_summary for r in results if r.df_summary is not None and not r.df_summary.empty], ignore_index=True) \
        if any((r.df_summary is not None and not r.df_summary.empty) for r in results) else pd.DataFrame()

    sgis_gdf_by_center = {r.center_id: r.sgis_gdf for r in results if r.sgis_gdf is not None}

    # 배후수요/주거유형 상세(행정동 기여도) 누적
    _dh_detail_list = []
    for r in results:
        _df = r.meta.get("dh_detail_df", None)
        if isinstance(_df, pd.DataFrame) and not _df.empty:
            _dh_detail_list.append(_df)
    df_dh_detail_all = pd.concat(_dh_detail_list, ignore_index=True) if len(_dh_detail_list) else pd.DataFrame()

    # 배후수요/주거유형 raw → 반경/중심지 단위 집계 (요약/포인트 다운로드 결합용)
    dh_agg_by_radius = pd.DataFrame()
    dh_agg_by_center = pd.DataFrame()
    if isinstance(df_dh_detail_all, pd.DataFrame) and not df_dh_detail_all.empty:
        dh_agg_by_radius = (
            df_dh_detail_all
            .groupby(["center_label", "radius_m"], as_index=False)
            .agg(
                D_raw_from_detail=("demand_contrib", "sum"),
                H_raw_from_detail=("housing_contrib", "sum"),
                age_total_sum=("age_total", "sum"),
                employee_cnt_sum=("employee_cnt", "sum"),
                tot_family_sum=("tot_family", "sum"),
                housing_weighted_sum_sum=("housing_weighted_sum", "sum"),
            )
        )
        dh_agg_by_center = (
            dh_agg_by_radius
            .groupby("center_label", as_index=False)
            .agg(
                D_raw_total=("D_raw_from_detail", "sum"),
                H_raw_total=("H_raw_from_detail", "sum"),
                age_total_total=("age_total_sum", "sum"),
                employee_cnt_total=("employee_cnt_sum", "sum"),
                tot_family_total=("tot_family_sum", "sum"),
                housing_weighted_sum_total=("housing_weighted_sum_sum", "sum"),
            )
        )

    # 상단 KPI
    st.markdown("### 요약 KPI (중심지별)")
    st.dataframe(centers_out, use_container_width=True)

    # 반경별 총 점수 비교표 + 직접 비교 차트
    st.markdown("### 반경별 최종 점수 비교 (Stotal)")
    st.caption("Stotal(r) = α·Sstore_norm(r) + γ·D_norm(r) + η·H_norm(r)")

    score_rows = []
    for r in results:
        sstore_map = (r.meta.get("total_score_by_radius", {}) or {})
        d_raw_map = (r.meta.get("demand_raw_by_radius", {}) or {})
        h_raw_map = (r.meta.get("housing_raw_by_radius", {}) or {})

        for radius_m, sstore in sstore_map.items():
            rm = int(radius_m)
            score_rows.append({
                "center_label": r.center_label,
                "radius_m": rm,
                "Sstore": float(sstore),
                "D_raw": float(d_raw_map.get(rm, 0.0)),
                "H_raw": float(h_raw_map.get(rm, 0.0)),
            })

    df_scores = pd.DataFrame(score_rows)

    if not df_scores.empty:
        method = str(inputs.get("norm_method", "log1p_minmax") or "log1p_minmax")
        alpha_use = float(inputs.get("alpha", 1.0))
        gamma_use = float(inputs.get("gamma", 1.0))
        eta_use = float(inputs.get("eta", 1.0))

        df_scores["Sstore_norm"] = _normalize_values(df_scores["Sstore"].tolist(), method)
        df_scores["D_norm"] = _normalize_values(df_scores["D_raw"].tolist(), method)
        df_scores["H_norm"] = _normalize_values(df_scores["H_raw"].tolist(), method)
        df_scores["Stotal"] = alpha_use * df_scores["Sstore_norm"] + gamma_use * df_scores["D_norm"] + eta_use * df_scores["H_norm"]

        st.markdown("#### (표) Stotal (중심지 × 반경)")
        pivot_total = df_scores.pivot_table(index="center_label", columns="radius_m", values="Stotal", aggfunc="sum", fill_value=0.0)
        st.dataframe(pivot_total, use_container_width=True)

        with st.expander("구성요소(Sstore_raw / Sstore_norm / D_norm / H_norm) 보기", expanded=False):
            c1, c2, c3, c4 = st.columns(4)
            with c1:
                st.markdown("**Sstore (raw)**")
                st.dataframe(
                    df_scores.pivot_table(index="center_label", columns="radius_m", values="Sstore", aggfunc="sum", fill_value=0.0),
                    use_container_width=True,
                )
            with c2:
                st.markdown("**Sstore_norm (0~1)**")
                st.dataframe(
                    df_scores.pivot_table(index="center_label", columns="radius_m", values="Sstore_norm", aggfunc="sum", fill_value=0.0),
                    use_container_width=True,
                )
            with c3:
                st.markdown("**D_norm**")
                st.dataframe(
                    df_scores.pivot_table(index="center_label", columns="radius_m", values="D_norm", aggfunc="sum", fill_value=0.0),
                    use_container_width=True,
                )
            with c4:
                st.markdown("**H_norm**")
                st.dataframe(
                    df_scores.pivot_table(index="center_label", columns="radius_m", values="H_norm", aggfunc="sum", fill_value=0.0),
                    use_container_width=True,
                )

        st.markdown("#### 위치간 직접 비교(반경 선택)")
        radius_options = sorted(df_scores["radius_m"].unique().tolist())
        sel_radius = st.selectbox("비교할 반경(m)", options=radius_options, index=0)
        df_sel = df_scores[df_scores["radius_m"] == int(sel_radius)].copy()
        df_sel = df_sel.sort_values("Stotal", ascending=False)
        st.bar_chart(df_sel.set_index("center_label")[["Stotal"]])

        st.markdown("#### 그룹형 막대(반경별)")
        if HAS_ALTAIR:
            try:
                import altair as alt
                chart = (
                    alt.Chart(df_scores)
                    .mark_bar()
                    .encode(
                        x=alt.X("radius_m:O", title="반경(m)"),
                        y=alt.Y("Stotal:Q", title="Stotal"),
                        xOffset="center_label:N",
                        color=alt.Color("center_label:N", title="중심지"),
                        tooltip=["center_label:N", "radius_m:O", alt.Tooltip("Stotal:Q", format=".3f")],
                    )
                    .properties(height=360)
                )
                st.altair_chart(chart, use_container_width=True)
            except Exception:
                st.info("그룹형 막대그래프(Altair) 렌더링에 실패했습니다. 위의 '반경 선택' 비교 차트를 사용하세요.")
        else:
            st.info("Altair가 없어서 그룹형 막대그래프를 생략했습니다. 위의 '반경 선택' 비교 차트를 사용하세요.")
    else:
        st.info("점수 데이터가 없습니다. (소분류가 비어있거나, 필터 결과가 없을 수 있습니다.)")

    # 후보지 추천 우선순위(3요소 반영: Sstore_norm / D_norm / H_norm)
    if not df_scores.empty:
        st.markdown("#### 후보지 추천 우선순위")

        _r_options = sorted(df_scores["radius_m"].dropna().astype(int).unique().tolist())
        if len(_r_options) > 0:
            _default_r = max(_r_options)
            sel_rank_radius = st.selectbox(
                "추천 기준 반경(m)",
                options=_r_options,
                index=_r_options.index(_default_r),
                key="rank_radius",
            )

            df_rank = df_scores[df_scores["radius_m"] == int(sel_rank_radius)].copy()
            df_rank = df_rank.sort_values("Stotal", ascending=False).reset_index(drop=True)
            df_rank.insert(0, "rank", range(1, len(df_rank) + 1))

            st.markdown("**(반경 선택) 추천 순위**")
            st.dataframe(
                df_rank[["rank", "center_label", "radius_m", "Stotal", "Sstore_norm", "D_norm", "H_norm", "Sstore", "D_raw", "H_raw"]],
                use_container_width=True,
            )

        # 종합: 반경별 Stotal 평균(동일 가중)
        df_overall = (
            df_scores.groupby("center_label", as_index=False)
            .agg(
                Stotal_mean=("Stotal", "mean"),
                Sstore_norm_mean=("Sstore_norm", "mean"),
                D_norm_mean=("D_norm", "mean"),
                H_norm_mean=("H_norm", "mean"),
            )
            .sort_values("Stotal_mean", ascending=False)
            .reset_index(drop=True)
        )
        if not df_overall.empty:
            df_overall.insert(0, "rank", range(1, len(df_overall) + 1))
            st.markdown("**(종합) 반경 평균 기준 추천 순위**")
            st.dataframe(df_overall, use_container_width=True)
            st.caption("※ '종합'은 각 반경의 Stotal을 동일 가중으로 평균낸 값입니다. (반경별 중요도가 다르면 별도 가중 로직으로 바꿀 수 있습니다.)")

    # 지도
    st.markdown("### 지도")
    radii = inputs.get("radii", []) or []
    scls_list = inputs.get("scls_list", []) or []

    if inputs.get("map_engine", "").startswith("pydeck") and HAS_PYDECK:
        deck = render_map_pydeck(
            centers=centers_out[["center_id", "center_label", "lon", "lat"]],
            df_master_all=df_master_all,
            radii=radii,
            scls_for_color=scls_list,
            sgis_gdf_by_center=sgis_gdf_by_center,
        )
        st.pydeck_chart(deck, use_container_width=True)
    else:
        fmap = render_map_folium(
                    centers=centers_out[["center_id", "center_label", "lon", "lat"]],
                    df_master_all=df_master_all,
                    radii=radii,
                    scls_for_color=scls_list,
                    use_vworld=bool(inputs.get("use_vworld_tiles", False)),
                    vworld_key=vworld_key,
                    sgis_gdf_by_center=sgis_gdf_by_center,
                    zoom_start=int(inputs.get("folium_zoom", 13)),
                    enable_fullscreen=bool(inputs.get("folium_fullscreen", True)),
                    enable_heatmap=bool(inputs.get("folium_heatmap", True)),
                    heat_weight_mode=str(inputs.get("heat_weight_mode", "uniform")),
                    heat_radius_px=int(inputs.get("heat_radius_px", 18)),
                    heat_blur_px=int(inputs.get("heat_blur_px", 15)),
                    heat_min_opacity=float(inputs.get("heat_min_opacity", 0.2)),
                    scls_weights=inputs.get("scls_weights", {}) or {},
                )
        map_key_payload = {
            "n_centers": int(len(centers_out)),
            "n_points": int(len(df_master_all)),
            "radii": [int(x) for x in radii],
            "use_vworld": bool(inputs.get("use_vworld_tiles", False)),
            "engine": str(inputs.get("map_engine", "")),
        }
        map_key = "folium_map_" + hashlib.sha1(json.dumps(map_key_payload, sort_keys=True).encode("utf-8")).hexdigest()[:12]
        render_folium_component_safe(
            fmap,
            height=int(inputs.get("folium_height", 650)),
            map_key=map_key,
        )

    # 상세 테이블
    tab1, tab2, tab3, tab4 = st.tabs(["요약(중심지×반경×소분류)", "원본 포인트", "배후수요/주거유형 Raw", "다운로드"])
    with tab1:
        if df_summary_all.empty:
            st.info("요약 데이터가 없습니다.")
        else:
            st.dataframe(
                df_summary_all.sort_values(["center_label", "radius_m", "score"], ascending=[True, True, False]),
                use_container_width=True,
            )

    with tab2:
        if df_master_all.empty:
            st.info("포인트 데이터가 없습니다.")
        else:
            st.dataframe(df_master_all.sort_values(["center_label", "dist_m"]), use_container_width=True)

    with tab3:
        if df_dh_detail_all.empty:
            st.info("배후수요/주거유형 raw 데이터가 없습니다. (SGIS 비활성 또는 계산 미실행일 수 있습니다.)")
        else:
            st.dataframe(
                df_dh_detail_all.sort_values(["center_label", "radius_m", "adm_nm"]),
                use_container_width=True,
            )

    with tab4:
        st.caption("UTF-8-SIG로 저장되어 엑셀에서 한글이 깨지지 않도록 했습니다.")
        if not df_summary_all.empty:
            df_summary_for_dl = df_summary_all.copy()
            try:
                if isinstance(dh_agg_by_radius, pd.DataFrame) and not dh_agg_by_radius.empty:
                    df_summary_for_dl = df_summary_for_dl.merge(
                        dh_agg_by_radius,
                        on=["center_label", "radius_m"],
                        how="left",
                    )
            except Exception:
                pass
            st.download_button(
                "요약 CSV 다운로드",
                data=df_to_csv_bytes(df_summary_for_dl),
                file_name="summary_multi_centers.csv",
                mime="text/csv; charset=utf-8",
            )
        if not df_master_all.empty:
            df_master_for_dl = df_master_all.copy()
            try:
                if isinstance(dh_agg_by_center, pd.DataFrame) and not dh_agg_by_center.empty:
                    df_master_for_dl = df_master_for_dl.merge(
                        dh_agg_by_center,
                        on="center_label",
                        how="left",
                    )
            except Exception:
                pass
            st.download_button(
                "포인트 CSV 다운로드",
                data=df_to_csv_bytes(df_master_for_dl),
                file_name="points_multi_centers.csv",
                mime="text/csv; charset=utf-8",
            )
        if not df_dh_detail_all.empty:
            st.download_button(
                "배후수요_주거유형 Raw CSV 다운로드",
                data=df_to_csv_bytes(df_dh_detail_all),
                file_name="demand_housing_raw_multi_centers.csv",
                mime="text/csv; charset=utf-8",
            )
