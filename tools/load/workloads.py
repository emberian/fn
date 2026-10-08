"""Workloads and cells as data: parse tools/load/workloads.json, resolve a cell id.

A cell id is WORKLOAD[@STORE][/variant]: `W2@10k/R16`, `W13`, `smoke`.
WORKLOAD is a matrix id (W1, W2, W13 ...) or a workload name; STORE is a key
of "stores" (1k, 4k, 10k, 40k, 100k) and sets the preload; the variant is a
preset name (post-rate/default), `R<n>` (one reader count) or `A`/`B` (the
idle-GC arm of W13).  No I/O beyond reading the JSON; the driver executes.
"""
from __future__ import annotations

import copy
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PATH = HERE / "workloads.json"

PHASE_KINDS = {
    "post": {"count", "duration_s", "octets", "connections", "rate_per_s", "background_readers"},
    "commands": {"reps"},
    "fresh_start": {"limits_mb"},
    "conn_capacity": {"presets", "max_try"},
    "census": set(),
    "prof": {"article_kib", "reps"},
    "publish": set(),
    "publish_live": {"rate_per_s", "octets", "before_s", "after_s", "max_wait_s"},
    "read": {"readers", "count", "duration_s", "cmd", "poster"},
    "hold": {"steps", "step_settle_s", "close"},
    "idle": {"seconds"},
    "article_sizes": {"sizes_kib", "reps"},
    "reopen": set(),
    "checkpoint": set(),
    "verify": {"count"},
    "peers": {"mode", "rate_per_s", "baseline_s", "posts", "deadline_s", "drain_s", "octets"},
    "unimplemented": {"reason"},
}
COMMON = {"name", "kind", "measure"}


class WorkloadError(ValueError):
    pass


def load(path=PATH):
    with open(path) as f:
        data = json.load(f)
    validate(data)
    return data


def validate(data):
    for key in ("presets", "workloads", "cells", "stores", "sbcl_user_args"):
        if key not in data:
            raise WorkloadError("workloads.json lacks %r" % key)
    for name, w in data["workloads"].items():
        if w.get("preset") not in data["presets"]:
            raise WorkloadError("%s: unknown preset %r" % (name, w.get("preset")))
        if not w.get("phases"):
            raise WorkloadError("%s: no phases" % name)
        seen = set()
        for ph in w["phases"]:
            kind = ph.get("kind")
            if kind not in PHASE_KINDS:
                raise WorkloadError("%s: unknown phase kind %r" % (name, kind))
            extra = set(ph) - PHASE_KINDS[kind] - COMMON
            if extra:
                raise WorkloadError("%s/%s: unknown keys %s" % (name, ph.get("name"), sorted(extra)))
            if not ph.get("name") or ph["name"] in seen:
                raise WorkloadError("%s: phase names must be present and unique" % name)
            seen.add(ph["name"])
            if kind == "post" and not (("count" in ph) ^ ("duration_s" in ph)):
                raise WorkloadError("%s/%s: post needs exactly one of count, duration_s" % (name, ph["name"]))
            if kind == "read" and not (("count" in ph) ^ ("duration_s" in ph)):
                raise WorkloadError("%s/%s: read needs exactly one of count, duration_s" % (name, ph["name"]))
        if sum(1 for ph in w["phases"] if ph.get("measure")) > 1:
            raise WorkloadError("%s: at most one measure phase" % name)
    for cell, wl in data["cells"].items():
        if wl not in data["workloads"]:
            raise WorkloadError("cell %s names unknown workload %s" % (cell, wl))


class Cell:
    """A resolved cell: id, workload name, the workload dict with overrides applied."""

    def __init__(self, cell_id, name, spec, arm=None, store_n=None):
        self.id, self.workload, self.spec, self.arm, self.store_n = cell_id, name, spec, arm, store_n


def resolve(cell_id, data=None):
    data = data or load()
    m = re.fullmatch(r"([A-Za-z0-9-]+)(?:@([0-9a-z]+))?(?:/([A-Za-z0-9]+))?", cell_id)
    if not m:
        raise WorkloadError("bad cell id %r (WORKLOAD[@STORE][/variant])" % cell_id)
    head, store, variant = m.groups()
    name = data["cells"].get(head, head)
    if name not in data["workloads"]:
        raise WorkloadError("unknown workload %r (cells: %s)" % (head, ", ".join(sorted(data["cells"]))))
    spec = copy.deepcopy(data["workloads"][name])
    arm, store_n = None, None
    if store:
        if store not in data["stores"]:
            raise WorkloadError("unknown store %r (one of %s)" % (store, ", ".join(data["stores"])))
        store_n = data["stores"][store]
        spec.setdefault("store", {})["preload"] = store_n
    if variant:
        if variant in spec.get("variants", ()):
            spec["preset"] = variant
            if variant in spec.get("variant_preload", {}):
                spec.setdefault("store", {})["preload"] = spec["variant_preload"][variant]
        elif re.fullmatch(r"R\d+", variant):
            phases = [p for p in spec["phases"] if p["name"] == variant]
            if not phases:
                phases = [dict(copy.deepcopy(spec["phases"][-1]), name=variant, readers=int(variant[1:]))]
            for p in phases:
                p["measure"] = True
            spec["phases"] = phases
        elif variant in ("A", "B"):
            arm = variant
        else:
            raise WorkloadError("unknown variant %r for %s" % (variant, name))
    return Cell(cell_id, name, spec, arm, store_n)


def init_flags(data, preset):
    return list(data["presets"][preset])


def nmem3_clean(data=None):
    """The 128 MiB bar's reference workload as the constants tests/test_native_image_heap.py reads."""
    data = data or load()
    w = data["workloads"]["rss-small-filled"]
    fill = next(p for p in w["phases"] if p["kind"] == "post")
    hold = next(p for p in w["phases"] if p["kind"] == "hold")
    idle = next(p for p in w["phases"] if p["kind"] == "idle")
    return {"posts": fill["count"], "octets": fill["octets"], "idle_connections": tuple(hold["steps"]),
            "idle_seconds": idle["seconds"], "init_flags": tuple(data["presets"][w["preset"]]),
            "groups": tuple(w["groups"]), "sbcl_user_args": data["sbcl_user_args"],
            "settle_s": w["settle_s"], "step_settle_s": hold["step_settle_s"]}
