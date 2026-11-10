#!/usr/bin/env python3
import argparse
import asyncio
import csv
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
import unittest
import urllib.request
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from types import SimpleNamespace as NS
from typing import Any, Dict, Generator, List, Optional, Set, Tuple

from bleak import BleakScanner

HOME_CACHE_DIR = Path.home() / ".cache" / "fed_detector"
IEEE_OUI_URL = "https://standards-oui.ieee.org/oui/oui.csv"
RANK_HIERARCHY = {"": 0, "low": 1, "medium": 2, "high": 3}
RSSI_LEVELS = {"high": 60, "medium": 30, "low": 15}
LEVEL_COLORS = {"high": "\033[91m", "medium": "\033[93m", "low": "\033[96m"}
RESET_COLOR = "\033[0m"
MAC_REGEX = re.compile(r"^([0-9A-F]{2}:){5}[0-9A-F]{2}$")

VENDORS = [
    (r"^(taser international|axon enterprise)", "Axon", 55, 35),
    (r"^watchguard video", "WatchGuard", 0, 30),
    (r"^digital ally", "DigitalAlly", 0, 30),
    (r"^vievu", "VIEVU", 0, 30),
    (r"^pro-vision", "ProVision", 0, 25),
    (r"^zepcam", "Zepcam", 0, 25),
    (r"^wolfcom", "Wolfcom", 0, 25),
    (r"^coban tech", "Coban", 0, 25),
    (r"^motorola solutions", "Motorola", 20, 12),
    (r"^(harris corp|l3harris)", "Harris", 0, 8),
    (r"^(tait (electronics|international)|sepura)", "Radio", 8, 8),
]
COMPILED_VENDORS = [(re.compile(p, re.I), t, cw, ow) for p, t, cw, ow in VENDORS]
VENDOR_TAG_WEIGHTS = {t: (cw, ow) for _, t, cw, ow in VENDORS}

PIN_COMPANY_IDS = {0x034D: ("Axon", 55), 0x04EC: ("Motorola", 20)}
PIN_OU_IS = {
    "00:25:DF": "Axon",
    "00:1D:96": "WatchGuard",
    "00:23:BD": "DigitalAlly",
    "FC:01:9E": "VIEVU",
    "9C:83:BF": "ProVision",
    "48:46:8D": "Zepcam",
    "00:04:7D": "Motorola",
    "00:1F:92": "Motorola",
    "4C:CC:34": "Motorola",
    "00:18:85": "Motorola",
    "10:74:6F": "Motorola",
    "B8:E2:8C": "Motorola",
    "00:17:F3": "Harris",
    "00:06:EC": "Harris",
    "00:00:C3": "Harris",
    "00:0D:CA": "Radio",
    "00:1E:96": "Radio",
}
LEGACY_OUIS = ["00:50:FA", "00:0C:41", "00:1C:64", "30:83:D2", "AC:CC:8E"]
NAME_PATTERNS = {
    r"\baxon\b": ("Axon", 40),
    r"\btaser\b": ("Taser", 40),
    r"watchguard": ("WatchGuard", 40),
    r"vievu": ("VIEVU", 40),
    r"\bwolfcom\b": ("Wolfcom", 40),
    r"\bcoban\b": ("Coban", 40),
    r"body ?(worn|cam)": ("bodycam", 25),
}

@dataclass
class TrackedDevice:
    first: float
    last: float = 0.0
    ema: float = -100.0
    peak: float = -100.0
    n: int = 0
    pts: int = 0
    alias: int = 0
    lvl: str = ""
    name: str = ""
    hits: Set[str] = field(default_factory=set)
    sent: float = 0.0
    sent_lvl: str = ""
    near: bool = False
    was_near: bool = False
    hist: deque = field(default_factory=lambda: deque(maxlen=64))


def load_json(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return {}


def save_json(path, data):
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True))


def fetch_ieee_database(file_path):
    try:
        file_path.parent.mkdir(parents=True, exist_ok=True)
        req = urllib.request.Request(IEEE_OUI_URL, headers={"User-Agent": "Mozilla/5.0"})
        file_path.write_bytes(urllib.request.urlopen(req, timeout=30).read())
    except Exception as e:
        print(f"IEEE download: {e}")


def get_registered_company_ids():
    try:
        from bluetooth_numbers import company
        return dict(company.items())
    except ImportError:
        return {}


def get_registered_ouis(args):
    try:
        from bluetooth_numbers import oui
        yield from oui.items()
    except ImportError:
        pass

    oui_file = HOME_CACHE_DIR / "oui.csv"
    if args.ieee and not oui_file.exists():
        fetch_ieee_database(oui_file)

    if oui_file.exists():
        with oui_file.open(newline="", encoding="utf-8", errors="ignore") as f:
            for row in csv.reader(f):
                if len(row) > 2 and re.fullmatch(r"[0-9A-Fa-f]{6}", row[1]):
                    prefix = row[1].upper()
                    yield f"{prefix[:2]}:{prefix[2:4]}:{prefix[4:]}", row[2]


def merge_signatures(sig, data):
    for k, e in data.get("company_ids", {}).items():
        sig["cids"][int(k, 0)] = e
    for k, e in data.get("ouis", {}).items():
        sig["ouis"][k.upper()] = e
    for k, e in data.get("uuids", {}).items():
        sig["uuids"][k.lower()] = e
    for k, e in data.get("names", {}).items():
        sig["names"][k] = e
    for k, e in data.get("fps", {}).items():
        sig["fps"][k] = e

def build_signatures(args):
    sig = {"cids": {}, "ouis": {}, "uuids": {}, "fps": {}, "names": {}}
    for cid, (t, w) in PIN_COMPANY_IDS.items():
        sig["cids"][cid] = {"w": w, "tag": t}
    for oui_p, t in PIN_OU_IS.items():
        sig["ouis"][oui_p] = {"w": VENDOR_TAG_WEIGHTS[t][1], "tag": t}
    for l_oui in LEGACY_OUIS:
        sig["ouis"][l_oui] = {"w": 6, "tag": "legacy"}
    for pat, (t, w) in NAME_PATTERNS.items():
        sig["names"][pat] = {"w": w, "tag": t}
    for cid, vname in get_registered_company_ids().items():
        for rx, t, cw, _ in COMPILED_VENDORS:
            if cw and rx.search(vname):
                sig["cids"].setdefault(cid, {"w": cw, "tag": t})
                break
    for oui_p, vname in get_registered_ouis(args):
        for rx, t, _, ow in COMPILED_VENDORS:
            if rx.search(vname):
                sig["ouis"].setdefault(oui_p.upper(), {"w": ow, "tag": t})
                break
    merge_signatures(sig, load_json(args.sigs))
    sig["rx"] = [(re.compile(k, re.I), e) for k, e in sig["names"].items()]
    return sig

def extract_fingerprints(adv):
    fps = {f"{c:04x}:{bytes(v)[:2].hex()}" for c, v in adv.manufacturer_data.items()}
    return fps | {f"u:{u.lower()}" for u in adv.service_uuids}


def score_device(sig, addr, name, adv):
    pts, hits = 0, []
    for c in adv.manufacturer_data:
        e = sig["cids"].get(c)
        if e:
            pts += e["w"]
            hits.append(f"cid:{c:#06x}:{e['tag']}")
    for u in adv.service_uuids:
        e = sig["uuids"].get(u.lower())
        if e:
            pts += e["w"]
            hits.append(f"uuid:{u}:{e['tag']}")
    for rx, e in sig["rx"]:
        if name and rx.search(name):
            pts += e["w"]
            hits.append(f"name:{e['tag']}")
    if MAC_REGEX.match(addr):
        e = sig["ouis"].get(addr[:8])
        if e:
            pts += e["w"]
            hits.append(f"oui:{addr[:8]}:{e['tag']}")
    for f in extract_fingerprints(adv):
        e = sig["fps"].get(f)
        if e:
            pts += e["w"]
            hits.append(f"fp:{f}:{e['tag']}")
    return pts, hits


def evaluate_level(pts):
    for k in ("high", "medium", "low"):
        if pts >= RSSI_LEVELS[k]:
            return k
    return ""

def calculate_distance(rssi, tx=-59, n=2.7):
    return round(10 ** ((tx - rssi) / (10 * n)), 1)
    
def evaluate_trend(tracker, win=10.0, gap=4.0):
    old = next((e for ts, e in tracker.hist if tracker.last - ts <= win), tracker.ema)
    d = tracker.ema - old
    if d >= gap:
        return "approaching"
    if d <= -gap:
        return "leaving"
    return "steady"

def update_tracker(tracker, now, rssi, pts, hits, name, alpha):
    tracker.last = now
    tracker.n += 1
    tracker.ema = rssi if tracker.n == 1 else alpha * rssi + (1 - alpha) * tracker.ema
    tracker.peak = max(tracker.peak, tracker.ema)
    tracker.pts = max(tracker.pts, pts)
    tracker.hits |= set(hits)
    if name:
        tracker.name = name
    tracker.hist.append((now, tracker.ema))

def evaluate_alert_trigger(tracker, now, args):
    if tracker.n < args.hits:
        return None
    if not tracker.sent:
        return "new"
    if RANK_HIERARCHY[tracker.lvl] > RANK_HIERARCHY[tracker.sent_lvl]:
        return "upgraded"
    if tracker.near and not tracker.was_near:
        return "near"
    if now - tracker.sent >= args.cool:
        return "recheck"
    return None

def sanitize_string(s):
    return re.sub(r"[^\w :.\-~/\[\],]", "", s)


def send_notification(title, msg):
    if sys.platform == "darwin":
        cmd = ["osascript", "-e", f'display notification "{sanitize_string(msg)}" with title "{sanitize_string(title)}"']
    elif shutil.which("notify-send"):
        cmd = ["notify-send", sanitize_string(title), sanitize_string(msg)]
    else:
        return
    subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def trigger_hook(cmd, ev):
    env = dict(os.environ, FED_JSON=json.dumps(ev))
    for k, v in ev.items():
        if not isinstance(v, (list, dict)):
            env[f"FED_{k.upper()}"] = str(v)
    subprocess.Popen(shlex.split(cmd), env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


class DeviceDetector:
    def __init__(self, args, sigs):
        self.args = args
        self.sigs = sigs
        self.trackers = {}
        self.fpm = {}
        self.alerts = 0
        self.ign = {x.upper() for x in args.ignore}
        self.log = open(args.log, "a", buffering=1) if args.log else None

    def emit_event(self, ev):
        if self.log:
            self.log.write(json.dumps(ev) + "\n")
        c = LEVEL_COLORS.get(ev.get("lvl", ""), "")
        stamp = ev["t"][11:19]
        if ev["ev"] == "lost":
            line = f"{stamp} LOST       {ev['addr']} seen {ev['secs']}s, peak {ev['peak']} dBm"
        else:
            rot = f" +{ev['alias']}rot" if ev["alias"] else ""
            line = (
                f"{stamp} {ev['why'].upper():<9}{ev['lvl'].upper():<7}{ev['addr']}{rot} "
                f"{ev['name'] or '-':<16} {ev['ema']} dBm ~{ev['dist']}m {ev['trend']} "
                f"[{', '.join(ev['hits'])}]"
            )
        sys.stdout.write(f"\r\033[K{c}{line}{RESET_COLOR}\n")
        if ev["ev"] != "detect":
            return
        if self.args.bell and ev["lvl"] == "high":
            sys.stdout.write("\a")
        if self.args.hook:
            trigger_hook(self.args.hook, ev)
        if self.args.notify and ev["why"] != "recheck":
            send_notification(f"fed_detector {ev['lvl']}", f"{ev['addr']} {ev['name']} ~{ev['dist']}m {ev['trend']}")

    def handle_advertisement(self, dev, adv):
        addr = dev.address.upper()
        if addr in self.ign:
            return
        name = adv.local_name or dev.name or ""
        pts, hits = score_device(self.sigs, addr, name, adv)
        now = time.time()
        fk = tuple(sorted(f for f in extract_fingerprints(adv) if not f.startswith("u:")))
        t = self.trackers.get(addr)
        if not t and pts and fk and self.args.merge:
            o = self.fpm.get(fk)
            ot = self.trackers.get(o) if o else None
            if ot and o != addr and 3 < now - ot.last < self.args.merge:
                t = self.trackers[addr] = self.trackers.pop(o)
                t.alias += 1
        if not pts and not t:
            return
        if not t:
            t = self.trackers[addr] = TrackedDevice(first=now)
        if pts and fk:
            self.fpm[fk] = addr
        rssi = adv.rssi if adv.rssi is not None else -100
        update_tracker(t, now, rssi, pts, hits, name, self.args.alpha)
        t.lvl = evaluate_level(t.pts)
        t.was_near = t.near
        t.near = t.ema >= self.args.near or (t.near and t.ema >= self.args.near - 6)
        if RANK_HIERARCHY[t.lvl] < RANK_HIERARCHY[self.args.min] or t.ema < self.args.floor:
            return
        r = evaluate_alert_trigger(t, now, self.args)
        if not r:
            return
        t.sent, t.sent_lvl = now, t.lvl
        self.alerts += 1
        tx = adv.tx_power if adv.tx_power is not None else -59
        self.emit_event({
            "t": datetime.now().isoformat(timespec="seconds"),
            "ev": "detect",
            "why": r,
            "addr": addr,
            "alias": t.alias,
            "name": t.name,
            "lvl": t.lvl,
            "score": t.pts,
            "hits": sorted(t.hits),
            "rssi": rssi,
            "ema": round(t.ema),
            "dist": calculate_distance(t.ema, tx),
            "trend": evaluate_trend(t),
            "n": t.n,
        })

    def sweep_trackers(self):
        now = time.time()
        for addr, t in list(self.trackers.items()):
            if now - t.last < self.args.lost:
                continue
            if t.sent:
                self.emit_event({
                    "t": datetime.now().isoformat(timespec="seconds"),
                    "ev": "lost",
                    "addr": addr,
                    "secs": round(t.last - t.first),
                    "peak": round(t.peak),
                    "lvl": t.lvl,
                })
            del self.trackers[addr]
        self.fpm = {k: v for k, v in self.fpm.items() if v in self.trackers}

    async def run_ticker(self):
        k = 0
        while True:
            if k % 5 == 0:
                self.sweep_trackers()
            k += 1
            msg = f"Scanning... tracked: {len(self.trackers)} | alerts: {self.alerts}"
            sys.stdout.write(f"\r{msg.ljust(60)}")
            sys.stdout.flush()
            await asyncio.sleep(1)


def create_survey_callback(seen, cn):
    def cb(dev, adv):
        mfr = sorted(adv.manufacturer_data)
        uu = sorted(adv.service_uuids)
        key = (dev.address, tuple(mfr), tuple(uu))
        if key in seen:
            return
        seen.add(key)
        name = adv.local_name or dev.name or "-"
        cids = " ".join(f"{c:#06x}({cn.get(c, '?')})" for c in mfr) or "-"
        print(f"{dev.address:<18}{adv.rssi:>5} dBm  {name:<22} cid: {cids}  uuid: {','.join(uu) or '-'}")
    return cb


def create_learn_callback(d, targets):
    def cb(dev, adv):
        addr = dev.address.upper()
        if addr not in targets:
            return
        name = adv.local_name or dev.name or ""
        tag = f"learned:{name or addr[-5:]}"
        new = [f for f in extract_fingerprints(adv) if f not in d["fps"]]
        for f in new:
            d["fps"][f] = {"w": 50, "tag": tag}
        if name and re.escape(name) not in d["names"]:
            d["names"][re.escape(name)] = {"w": 40, "tag": tag}
            new.append(f"name:{name}")
        if new:
            print(f"{addr} learned {', '.join(new)}")
    return cb


async def run_scanner(args):
    stop = asyncio.Event()
    loop = asyncio.get_running_loop()
    for s in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(s, stop.set)
        except NotImplementedError:
            pass
    tick = det = d = None
    if args.survey:
        print("survey mode: unique advertisers (addr, rssi, name, company ids, service uuids)\n")
        cb = create_survey_callback(set(), get_registered_company_ids())
    elif args.learn:
        d = load_json(args.sigs)
        for k in ("fps", "names"):
            d.setdefault(k, {})
        print(f"Learn mode: waiting for {', '.join(args.learn)}\n")
        cb = create_learn_callback(d, {x.upper() for x in args.learn})
    else:
        det = DeviceDetector(args, build_signatures(args))
        cb = det.handle_advertisement
        tick = asyncio.create_task(det.run_ticker())
    async with BleakScanner(cb):
        await stop.wait()
    if tick:
        tick.cancel()
    if d is not None:
        save_json(args.sigs, d)
        print(f"\nSaved to {args.sigs}")
    if det:
        print(f"\nSession: {det.alerts} alerts, {len(det.trackers)} devices still tracked")
    print("Scanner stopped.")


def parse_arguments(argv=None):
    p = argparse.ArgumentParser(description="jew finder")
    p.add_argument("--sigs", default="learned.json")
    p.add_argument("--log", default="fed_events.jsonl")
    p.add_argument("--floor", type=int, default=-85)
    p.add_argument("--near", type=int, default=-65)
    p.add_argument("--cool", type=int, default=180)
    p.add_argument("--lost", type=int, default=45)
    p.add_argument("--hits", type=int, default=2)
    p.add_argument("--merge", type=int, default=30)
    p.add_argument("--alpha", type=float, default=0.35)
    p.add_argument("--min", choices=["low", "medium", "high"], default="low")
    p.add_argument("--ignore", nargs="*", default=[])
    p.add_argument("--hook")
    p.add_argument("--bell", action="store_true")
    p.add_argument("--notify", action="store_true")
    p.add_argument("--ieee", action="store_true")
    p.add_argument("--survey", action="store_true")
    p.add_argument("--learn", nargs="+")
    p.add_argument("--selftest", action="store_true")
    return p.parse_args(argv)


def create_mock_advertisement(rssi=-60, cids=(), uuids=(), name=None, tx=None):
    return NS(
        rssi=rssi,
        manufacturer_data={c: b"\x01\x02\x03" for c in cids},
        service_uuids=list(uuids),
        local_name=name,
        tx_power=tx,
    )


def create_mock_device(addr, name=None):
    return NS(address=addr, name=name)


class TestFedDetector(unittest.TestCase):
    def setUp(self):
        args = parse_arguments([])
        args.log = None
        args.sigs = "/nonexistent.json"
        self.args = args
        self.signatures = build_signatures(args)
        self.output_events = []

    def setup_detector(self, **kw):
        for k, v in kw.items():
            setattr(self.args, k, v)
        d = DeviceDetector(self.args, self.signatures)
        d.emit_event = self.output_events.append
        return d

    def test_axon_company_id_scoring(self):
        pts, hits = score_device(self.signatures, "random", "", create_mock_advertisement(cids=[0x034D]))
        self.assertEqual(evaluate_level(pts), "medium")
        self.assertTrue(hits[0].startswith("cid:0x034d"))
        pts, _ = score_device(self.signatures, "random", "Axon Body 4", create_mock_advertisement(cids=[0x034D]))
        self.assertEqual(evaluate_level(pts), "high")

    def test_axon_oui_is_medium(self):
        pts, _ = score_device(self.signatures, "00:25:DF:01:02:03", "", create_mock_advertisement())
        self.assertEqual(evaluate_level(pts), "medium")

    def test_unrelated_lookalike_vendors_excluded(self):
        for o in ("00:58:28", "00:90:7F", "00:01:21", "00:03:41"):
            self.assertNotIn(o, self.signatures["ouis"])

    def test_registry_adds_vendors(self):
        self.assertIn("FC:01:9E", self.signatures["ouis"])
        self.assertIn("00:23:BD", self.signatures["ouis"])

    def test_legacy_oui_alone_silent(self):
        pts, _ = score_device(self.signatures, "00:0C:41:AA:BB:CC", "", create_mock_advertisement())
        self.assertEqual(evaluate_level(pts), "")

    def test_non_mac_skips_oui(self):
        pts, _ = score_device(self.signatures, "9F1B2C3D-0000-0000-0000-000000000000", "", create_mock_advertisement())
        self.assertEqual(pts, 0)

    def test_learned_fingerprint(self):
        self.signatures["fps"]["abcd:0102"] = {"w": 50, "tag": "learned"}
        pts, hits = score_device(self.signatures, "random", "", create_mock_advertisement(cids=[0xABCD]))
        self.assertEqual(pts, 50)
        self.assertTrue(hits[0].startswith("fp:"))

    def test_min_hits_and_cooldown(self):
        d = self.setup_detector(hits=2, cool=180)
        for _ in range(8):
            d.handle_advertisement(create_mock_device("00:25:DF:01:02:03"), create_mock_advertisement(-60))
        self.assertEqual([e["why"] for e in self.output_events], ["new"])

    def test_upgrade_and_near(self):
        d = self.setup_detector(hits=2, near=-65)
        a = "00:25:DF:01:02:03"
        for _ in range(3):
            d.handle_advertisement(create_mock_device(a), create_mock_advertisement(-80))
        d.handle_advertisement(create_mock_device(a, "Axon Body 4"), create_mock_advertisement(-80, name="Axon Body 4"))
        for _ in range(8):
            d.handle_advertisement(create_mock_device(a, "Axon Body 4"), create_mock_advertisement(-40, name="Axon Body 4"))
        w = [e["why"] for e in self.output_events]
        self.assertIn("upgraded", w)
        self.assertIn("near", w)

    def test_floor_and_ignore(self):
        d = self.setup_detector(ignore=["00:25:DF:01:02:03"])
        for _ in range(4):
            d.handle_advertisement(create_mock_device("00:25:DF:01:02:03"), create_mock_advertisement(-50))
            d.handle_advertisement(create_mock_device("00:25:DF:09:09:09"), create_mock_advertisement(-95))
        self.assertEqual(self.output_events, [])

    def test_rotation_merge(self):
        d = self.setup_detector(merge=30)
        for _ in range(3):
            d.handle_advertisement(create_mock_device("00:25:DF:01:02:03"), create_mock_advertisement(-60, cids=[0x034D]))
        d.trackers["00:25:DF:01:02:03"].last -= 10
        d.handle_advertisement(create_mock_device("00:25:DF:AA:BB:CC"), create_mock_advertisement(-60, cids=[0x034D]))
        self.assertEqual(list(d.trackers), ["00:25:DF:AA:BB:CC"])
        self.assertEqual(d.trackers["00:25:DF:AA:BB:CC"].alias, 1)

    def test_live_neighbor_not_merged(self):
        d = self.setup_detector(merge=30)
        for _ in range(3):
            d.handle_advertisement(create_mock_device("00:25:DF:01:02:03"), create_mock_advertisement(-60, cids=[0x034D]))
        d.handle_advertisement(create_mock_device("00:25:DF:AA:BB:CC"), create_mock_advertisement(-60, cids=[0x034D]))
        self.assertEqual(len(d.trackers), 2)

    def test_lost_event(self):
        d = self.setup_detector(lost=0)
        for _ in range(2):
            d.handle_advertisement(create_mock_device("00:25:DF:01:02:03"), create_mock_advertisement(-60))
        d.sweep_trackers()
        self.assertEqual(self.output_events[-1]["ev"], "lost")
        self.assertEqual(d.trackers, {})

    def test_ema_and_trend(self):
        t = TrackedDevice(first=0)
        update_tracker(t, 0, -70, 0, [], "", 0.35)
        update_tracker(t, 1, -30, 0, [], "", 0.35)
        self.assertLess(t.ema, -50)
        t = TrackedDevice(first=0)
        for i, r in enumerate([-80, -78, -72, -66, -60]):
            update_tracker(t, i, r, 0, [], "", 0.9)
        self.assertEqual(evaluate_trend(t), "approaching")

    def test_ieee_csv_parse(self):
        import tempfile
        global HOME_CACHE_DIR
        old, HOME_CACHE_DIR = HOME_CACHE_DIR, Path(tempfile.mkdtemp())
        try:
            (HOME_CACHE_DIR / "oui.csv").write_text(
                "Registry,Assignment,Organization Name,Organization Address\n"
                "MA-L,A1B2C3,Axon Enterprise Inc,Scottsdale\n"
                "MA-L,A1B2C4,Axonne Inc,Elsewhere\n"
            )
            self.assertIn("A1:B2:C3", build_signatures(self.args)["ouis"])
            self.assertNotIn("A1:B2:C4", build_signatures(self.args)["ouis"])
        finally:
            HOME_CACHE_DIR = old

    def test_clean_blocks_injection(self):
        self.assertNotIn('"', sanitize_string('x" & do shell script "y'))


def run_selftest():
    r = unittest.TextTestRunner(verbosity=1).run(unittest.defaultTestLoader.loadTestsFromTestCase(TestFedDetector))
    return 0 if r.wasSuccessful() else 1


if __name__ == "__main__":
    args = parse_arguments()
    if args.selftest:
        sys.exit(run_selftest())
    try:
        asyncio.run(run_scanner(args))
    except KeyboardInterrupt:
        print("\nScanner stopped.")
