"""Cells: which numbers of a finished run are the cell's metrics.

`derive(workload, phases)` maps the phase records the driver wrote onto the
flat dotted metric names that tools/load/bars.json checks name, and says why
a metric is absent (`not_measured`).  Pure functions over JSON: laptop-testable.
"""
from __future__ import annotations

import re

from .result import fit_exponent


def _phase(phases, name):
    return next((p for p in phases if p["name"] == name), None)


def _rate(ph):
    return next(iter((ph.get("rate") or {}).values()), None) if ph else None


def _cmd(ph, op):
    return ((ph or {}).get("cmd") or {}).get(op) or {}


def derive(workload, phases):
    m, nm = {}, {}
    measure = next((p for p in phases if p.get("measure")), None)
    if measure and measure.get("mem") and measure.get("status") != "not-implemented":
        for k in ("vmrss", "hwm", "anon", "file"):
            if measure["mem"].get(k) is not None:
                m["rss_kib." + k] = measure["mem"][k]
    gc = [p.get("gc") for p in phases if p.get("gc")]
    if gc:
        m["gc.ms"] = round(sum(g.get("ms") or 0 for g in gc), 1)
        m["gc.count"] = sum(g.get("count") or 0 for g in gc)
    m["posts.admitted"] = sum((p.get("counts") or {}).get("admitted", 0) for p in phases)
    m["posts.refused"] = sum((p.get("counts") or {}).get("refused", 0) for p in phases)
    for p in phases:
        if p.get("status") == "not-implemented":
            nm.setdefault("*", p.get("reason"))
    fn = {"mem-vs-size": _mem_vs_size, "commands": _commands, "post-rate": _post_rate, "readers": _readers, "article-sizes": _sizes, "growth": _growth,
          "m1-durable": _durable, "smoke": _smoke, "fresh-start": _fresh, "conn-capacity": _conncap, "publish-stall": _stall, "prof-ops": _prof}.get(workload)
    if fn:
        fn(phases, m, nm)
    if workload == "rss-small-filled" and "rss_kib.hwm" not in m:
        nm["rss_kib.hwm"] = nm["rss_kib.vmrss"] = "idle phase did not complete"
    out = {k: v for k, v in nm.items() if k != "*"}
    out.update(_expand(workload, nm))
    return m, out


def _expand(workload, nm):
    """A not-implemented phase explains every metric its workload owns."""
    if "*" not in nm:
        return {}
    owned = {"m1-durable": ["durable.exact"], "fresh-start": ["fresh.256.ok", "fresh.1024.ok"],
             "catchup": ["catchup.rate_1000", "catchup.rate_10000"]}.get(workload, [])
    return {k: nm["*"] for k in owned}


def _fresh(phases, m, nm):
    ph = _phase(phases, "limits")
    got = {r["limit_mb"]: r for r in (ph or {}).get("results", [])}
    for limit in (256, 1024):
        r = got.get(limit)
        if r is None:
            nm["fresh.%d.ok" % limit] = "limit %d MB did not run" % limit
            continue
        m["fresh.%d.ok" % limit] = 1 if r.get("served") else 0
        if r.get("at_listening_kib"):
            m["fresh.%d.rss_kib_at_listening" % limit] = r["at_listening_kib"]
        m["fresh.%d.seconds_to_listening_or_exit" % limit] = r["seconds_to_listening_or_exit"]


def _conncap(phases, m, nm):
    ph = _phase(phases, "capacity")
    for preset, r in ((ph or {}).get("capacity") or {}).items():
        m["conn.%s.default_cap" % preset] = r["default_cap"]
        if r["largest_ok"] is not None:
            m["conn.%s.largest_ok" % preset] = r["largest_ok"]
        if r["first_refused"] is not None:
            m["conn.%s.first_refused" % preset] = r["first_refused"]
        per = [t["kib_per_conn"] for t in r["trials"] if t.get("kib_per_conn")]
        if per:
            m["conn.%s.kib_per_conn" % preset] = per[-1]


def parse_prof(text, k):
    """timing.txt of E's prof2.lisp: a window line, then `kind name count ms` rows.  Per command: host-to-ACL2 calls
    (sum of acl2-entry counts), the owner's own barrier/fdatasync count and wall, MB consed, GC ms."""
    lines = text.splitlines()
    w = re.search(r"window_ms ([\d.]+) gc_ms ([\d.]+) consed_mb ([\d.]+)", lines[0]) if lines else None
    calls = 0
    sync_n, sync_ms, entries = 0, 0.0, {}
    for ln in lines[1:]:
        f = ln.split()        # the hook's ~t columns are spaces, not tabs; names may hold spaces
        if len(f) < 4:
            continue
        try:
            kind, name, n, ms = f[0], " ".join(f[1:-2]), int(f[-2]), float(f[-1])
        except ValueError:
            continue
        if kind == "acl2-entry":
            calls += n
            entries[name] = n
        elif kind == "barrier":
            sync_n += n
            sync_ms += ms
    return {"calls_per_cmd": round(calls / k, 3), "entries": entries, "sync_calls_per_cmd": round(sync_n / k, 3),
            "sync_ms_per_cmd": round(sync_ms / k, 3),
            "consed_bytes_per_cmd": round(float(w.group(3)) * 1048576 / k) if w else None,
            "gc_ms": float(w.group(2)) if w else None}


def _prof(phases, m, nm):
    ph = _phase(phases, "prof")
    got = (ph or {}).get("prof") or {}
    dead = bool(got) and all(r["calls_per_cmd"] == 0 and r["sync_calls_per_cmd"] == 0 for r in got.values())
    if dead:
        why = ("E's hook counted 0 fnn-call and 0 barrier calls for every operation: its encapsulations did not fire in this "
               "target (calls compiled direct), so calls and the owner's own sync are NOT-MEASURED here (bytes consed stand)")
        for name in got:
            nm["calls." + name] = nm["sync.own_calls_per_cmd." + name] = nm["sync.own_ms_per_cmd." + name] = why
        nm["sync.own_calls_per_post"] = nm["sync.own_ms_per_post"] = why
    for name, r in got.items():
        if not dead:
            m["calls." + name] = r["calls_per_cmd"]
            m["sync.own_calls_per_cmd." + name] = r["sync_calls_per_cmd"]
            m["sync.own_ms_per_cmd." + name] = r["sync_ms_per_cmd"]
        m["alloc." + name] = r["consed_bytes_per_cmd"]
        if r.get("hooked_cpu_ms_per_cmd") is not None:
            m["hooked_cpu_ms_per_cmd." + name] = r["hooked_cpu_ms_per_cmd"]
    if "POST_2k" in got and not dead:
        m["sync.own_calls_per_post"] = got["POST_2k"]["sync_calls_per_cmd"]
        m["sync.own_ms_per_post"] = got["POST_2k"]["sync_ms_per_cmd"]
    pts = [(int(k.split("_")[1][:-1]) * 1024, v["consed_bytes_per_cmd"]) for k, v in got.items() if k.startswith("ARTICLE_") and v.get("consed_bytes_per_cmd")]
    e = fit_exponent(pts)
    if e is not None:
        m["alloc.article.exponent"] = e
    else:
        nm["alloc.article.exponent"] = "prof phase did not complete"


def _smoke(phases, m, nm):
    rd = _phase(phases, "read")
    m["smoke.articles"] = (_cmd(rd, "ARTICLE")).get("n", 0)


def _post_rate(phases, m, nm):
    for tag in ("c1", "c8", "c1r3", "c8r3"):
        ph = _phase(phases, tag)
        if ph and _rate(ph) is not None:
            m["post.rate_" + tag] = round(_rate(ph), 2)
            st = _cmd(ph, "POST")
            m["post.p50_ms." + tag], m["post.p99_ms." + tag] = st.get("p50_ms"), st.get("p99_ms")
            if ph.get("cpu_ms_per_op") is not None:
                m["post.cpu_ms_per_op." + tag] = ph["cpu_ms_per_op"]
            if st.get("p99_ms") is None and st.get("n") is not None:
                nm["post.p99_ms." + tag] = "fewer than 200 POSTs (%d)" % st["n"]
        elif tag in ("c1", "c8") or ph is not None:
            nm["post.rate_" + tag] = "phase %s did not complete" % tag
        else:
            nm["post.rate_" + tag] = "phase %s not in this cell" % tag


def _readers(phases, m, nm):
    for ph in phases:
        if not ph["name"].startswith("R") or not ph.get("cmd"):
            continue
        tag = ph["name"]
        a = _cmd(ph, "ARTICLE")
        for k in ("p50_ms", "p95_ms", "p99_ms", "max_ms"):
            if a.get(k) is not None:
                m["article.%s.%s" % (k, tag)] = a[k]
        if a.get("p99_ms") is None and a.get("n") is not None:
            nm["article.p99_ms." + tag] = "fewer than 200 ARTICLEs (%d)" % a["n"]
        if _rate(ph) is not None:
            m["reads_per_s." + tag] = round(_rate(ph), 1)
        po = _cmd(ph, "POST")
        if po.get("p50_ms") is not None:
            m["post.p50_ms." + tag] = po["p50_ms"]
        if ph.get("cpu_ms_per_op") is not None:
            m["cpu_ms_per_op." + tag] = ph["cpu_ms_per_op"]
    if m.get("article.p99_ms.R16") is not None and m.get("article.p99_ms.R1"):
        m["article.p99_ratio_16_1"] = round(m["article.p99_ms.R16"] / m["article.p99_ms.R1"], 2)
    elif "article.p99_ms.R1" in m or "article.p99_ms.R16" in m:
        nm["article.p99_ratio_16_1"] = "needs R1 and R16 in one cell"
    else:
        nm["article.p99_ratio_16_1"] = "R1 and R16 phases not run"
    if not any(k.startswith("article.p99_ms.") for k in m) and not any(k.startswith("article.p99_ms.") for k in nm):
        nm["article.p99_ms.R16"] = "R16 phase did not complete"
    if "article.p99_ms.R16" not in m and "article.p99_ms.R16" not in nm:
        nm["article.p99_ms.R16"] = "R16 phase not run in this cell"


def _sizes(phases, m, nm):
    ph = _phase(phases, "sizes")
    t = (ph or {}).get("sizes_ms") or {}
    for kib, ms in t.items():
        m["article.ms.%sk" % kib] = ms
    if "64" in t and "512" in t and t["64"]:
        m["article.ratio_8n_over_n"] = round(t["512"] / t["64"], 2)
    else:
        nm["article.ratio_8n_over_n"] = "sizes 64 KiB and 512 KiB not both served (see refusals)"
    e = fit_exponent([(int(k) * 1024, v) for k, v in t.items() if int(k) >= 16])
    if e is not None:
        m["article.exponent"] = e


def _growth(phases, m, nm):
    done = all(p.get("status") in (None, "ok") for p in phases)
    m["grow.completed"] = 1 if done and phases else 0
    for name, key in (("reopen-checkpoint", "open_s.checkpoint"), ("open", "open_s.replay")):
        ph = _phase(phases, name)
        if ph and ph.get("open_s") is not None:
            m[key] = ph["open_s"]
    ov = _cmd(_phase(phases, "over40"), "OVER40")
    if ov:
        m["over40.p99_ms"] = ov.get("p99_ms")
        m["over40.p50_ms"] = ov.get("p50_ms")
    po = _cmd(_phase(phases, "post"), "POST")
    if po:
        m["post.p99_ms"], m["post.p50_ms"] = po.get("p99_ms"), po.get("p50_ms")


def _durable(phases, m, nm):
    v = _phase(phases, "verify")
    if v and v.get("verified") is not None and v.get("status") == "ok":
        # exactness is only claimed when the reclaim ran; it did not
        rc = _phase(phases, "reclaim")
        if rc and rc.get("status") == "not-implemented":
            nm["durable.exact"] = "reclaim pass not driven (%s); reopen + byte check: %d/%d identical" % (
                rc.get("reason"), v["verified"] - v.get("mismatches", 0), v["verified"])
        else:
            m["durable.exact"] = 1 if v.get("mismatches") == 0 and v["verified"] > 0 else 0
        m["durable.mismatches"] = v.get("mismatches")


ANON_GROUPS = [   # S's grouping of the owner's stobjs (room names them after the stobj)
    ("catalog rows", r"^(FN-CAT\$P|FN-CROW.*|FN-ARENA-PAGE)$"),
    ("message-id table", r"^(FN-MLH|FN-MLG|FN-MLT|FN-MPXT2?)$"),
    ("dense map", r"^(FN-DMAP\$C|FN-DPG)$"),
    ("history", r"^(FN-HIST\$[CP]|FN-HRECS\$[CS])$"),
    ("payload arena", r"^FN-ARENA\$[CLPX]$"),
    ("page pool", r"^(FN-PAGE-READ-POOL|PGS-MEM|PGS-GC|PGS-DIGEST-STATE)$"),
    ("per-connection", r"^FNN-CONNECTION-CUSTODY$"),
]


def parse_census(text):
    """{'raw': {...}, 'live': {...}}: dynamic usage, `groups` (owner structures per S's grouping, octets of
    the instance plus the vectors it points to, from the hook's OWNER lines), and `by_type` (SBCL's own
    per-type totals from `room`, and instance-usage's per-structure totals)."""
    out = {}
    for sect in re.split(r"^=== ", text, flags=re.M)[1:]:
        name = sect.split()[0].lower()
        du = re.search(r"dynamic-usage (\d+)", sect)
        by = {}
        for mo in re.finditer(r"^([A-Z][A-Za-z0-9*$%+() -]*?):\n\s+([\d,]+) bytes, ([\d,]+) objects", sect, flags=re.M):
            if not mo.group(1).startswith("Summary"):
                by["room:" + mo.group(1).strip()] = int(mo.group(2).replace(",", ""))
        inst = sect.split("--- instance-usage", 1)[1].split("--- owner", 1)[0] if "--- instance-usage" in sect else ""
        for mo in re.finditer(r"^\s+(\S+)\s+([\d,]+) bytes,\s+([\d,]+) objects", inst, flags=re.M):
            by["inst:" + mo.group(1)] = int(mo.group(2).replace(",", ""))
        owner, groups = {}, {}
        for mo in re.finditer(r"^OWNER (\S+) slot (\d+) type (\S+) bytes (\d+)", sect, flags=re.M):
            owner["%s.slot%s" % (mo.group(1), mo.group(2))] = int(mo.group(4))
            groups[mo.group(1)] = groups.get(mo.group(1), 0) + int(mo.group(4))
            groups["%s.slot%s:%s" % (mo.group(1), mo.group(2), mo.group(3))] = int(mo.group(4))
        large = {}
        for mo in re.finditer(r"^LARGE (\S+) count (\d+) bytes (\d+) maxlen (\d+)", sect, flags=re.M):
            large[mo.group(1)] = {"count": int(mo.group(2)), "bytes": int(mo.group(3)), "maxlen": int(mo.group(4))}
        out[name] = {"large": large, "dynamic_usage": int(du.group(1)) if du else None, "groups": groups, "owner": owner,
                     "by_type": dict(sorted(by.items(), key=lambda kv: -kv[1])[:40])}
    return out


def _mem_vs_size(phases, m, nm):
    op = _phase(phases, "open")
    if op:
        m["open_s.replay"] = op.get("open_s")
        if op.get("open_cpu_s") is not None:
            m["open_cpu_s.replay"] = op["open_cpu_s"]
    ar = _phase(phases, "at-rest")
    if ar and ar.get("mem"):
        mm = ar["mem"]
        m["rss.at_rest.vmrss"], m["rss.at_rest.anon"], m["rss.at_rest.file"] = mm["vmrss"], mm["anon"], mm["file"]
        m["rss.peak.hwm"] = mm["hwm"]
        m["rss.peak.anon"] = mm.get("peak_anon")
    ce = _phase(phases, "census")
    if ce and ce.get("census"):
        for kind, body in ce["census"].items():
            for g, v in body["groups"].items():
                m["anon.%s.%s" % (kind, g.replace(" ", "_"))] = v
            m["anon.%s.dynamic_usage" % kind] = body["dynamic_usage"]
            for t, v in (body.get("large") or {}).items():
                m["anon.%s.large.%s.bytes" % (kind, t)] = v["bytes"]
            for t, v in list(body["by_type"].items())[:12]:
                m["anon.%s.type.%s" % (kind, t)] = v
    elif ce:
        nm["anon.raw.dynamic_usage"] = ce.get("census_error") or "census produced no file"
    pu = _phase(phases, "publish")
    if pu and pu.get("publish_wall_s") is not None:
        m["publish.wall_s"], m["publish.cpu_s"] = pu["publish_wall_s"], pu["publish_cpu_s"]
        m["publish.write_octets"] = pu["publish_touched_octets"]
        m["store.octets"] = pu["store_octets_after"]
        for comp, v in (pu.get("sizes_after") or {}).items():
            m["size." + comp] = v
    nm["publish.stall_max_s"] = "longest POST stall during an online publication needs W8 (POSTs while a publication runs)"
    rc = _phase(phases, "reopen-checkpoint")
    if rc:
        m["open_s.checkpoint"] = rc.get("open_s")
        if rc.get("open_cpu_s") is not None:
            m["open_cpu_s.checkpoint"] = rc["open_cpu_s"]


def _commands(phases, m, nm):
    ph = _phase(phases, "commands")
    if not ph:
        nm["cmd.p99_ms.max"] = "commands phase did not complete"
        return
    worst = None
    for name, st in (ph.get("cmd") or {}).items():
        for k in ("p50_ms", "p99_ms"):
            if st.get(k) is not None:
                m["cmd.%s.%s" % (k, name)] = st[k]
        if st.get("p99_ms") is not None:
            worst = max(worst or 0, st["p99_ms"])
        elif st.get("n"):
            nm["cmd.p99_ms." + name] = "fewer than 200 samples"
    for name, v in (ph.get("cpu_ms_per_op_by_cmd") or {}).items():
        m["cmd.cpu_ms_per_op." + name] = v
    if worst is not None:
        m["cmd.p99_ms.max"] = worst


def _stall(phases, m, nm):
    ph = _phase(phases, "publish-live")
    if not ph or ph.get("status") not in (None, "ok"):
        nm["publish.stall_max_s"] = (ph or {}).get("reason") or "publish-live phase did not complete"
        return
    m["publish.stall_max_s"] = ph.get("stall_max_s")
    m["publish.window_s"] = ph.get("window_s")
    m["publish.window_posts"] = ph.get("window_posts")
    m["publish.done_gap_max_s"] = ph.get("done_gap_max_s")
    st = (ph.get("cmd") or {}).get("POST") or {}
    if st.get("p99_ms") is not None:
        m["publish.post_p99_ms"] = st["p99_ms"]
    elif st.get("n"):
        nm["publish.post_p99_ms"] = "fewer than 200 POSTs inside the window (n=%d); max reported as publish.stall_max_s" % st["n"]
    if st.get("p50_ms") is not None:
        m["publish.post_p50_ms"] = st["p50_ms"]
    m["publish.hwm_before_kib"], m["publish.hwm_after_kib"] = ph.get("hwm_before_kib"), ph.get("hwm_after_kib")


def merge_sweep(cell_id, workload, subs):
    """Merge sub-cells (key, n, cell result) into the cell the bars judge: metrics suffixed @KEY, and for
    every metric present at 3 or more sizes its fitted exponent against n (`NAME.exponent`)."""
    first = subs[0][2]
    merged = {k: first[k] for k in ("workload", "target", "arm", "rep", "preset", "flags", "git", "image", "hook", "launch",
                                    "heap", "trace", "loopback_only", "max_connections") if k in first}
    merged.update({"cell": cell_id, "members": [c["cell"] for _, _, c in subs], "phases": [],
                   "box": dict(first["box"]), "seconds": round(sum(c.get("seconds") or 0 for _, _, c in subs), 1)})
    merged["box"]["loadavg_end"] = subs[-1][2]["box"].get("loadavg_end")
    merged["box"]["loadavg_start"] = first["box"].get("loadavg_start")
    for key in ("busy_cores_start", "busy_cores_end"):
        vals = [c["box"].get(key) for _, _, c in subs if c["box"].get(key) is not None]
        merged["box"][key] = max(vals) if vals else None
    merged["noisy"] = any(c.get("noisy") for _, _, c in subs)
    ok = all(c.get("status") == "complete" for _, _, c in subs)
    merged["status"] = "complete" if ok else "incomplete: " + ", ".join("%s %s" % (k, c.get("status")) for k, _, c in subs if c.get("status") != "complete")
    metrics, nm, series = {}, {}, {}
    for key, n, c in subs:
        for name, v in (c.get("metrics") or {}).items():
            metrics["%s@%s" % (name, key)] = v
            if isinstance(v, (int, float)):
                series.setdefault(name, []).append((n, v))
        for name, why in (c.get("not_measured") or {}).items():
            nm.setdefault("%s@%s" % (name, key), why)
            nm.setdefault(name, why)
    for name, pts in series.items():
        if len(pts) >= 3 and not name.startswith(("posts.", "gc.")):
            e = fit_exponent(pts)
            if e is not None:
                metrics[name + ".exponent"] = e
    cmd_exp = [v for k, v in metrics.items() if k.startswith("cmd.p99_ms.") and k.endswith(".exponent") and not k.startswith("cmd.p99_ms.max")]
    if cmd_exp:
        metrics["cmd.p99_exponent.max"] = max(cmd_exp)
    for name in ("cmd.p99_ms.max", "publish.stall_max_s"):
        vals = [v for k, v in metrics.items() if k.startswith(name + "@")]
        if vals:
            metrics[name] = max(vals)
    merged["metrics"], merged["not_measured"] = metrics, nm
    merged["refusals"] = {}
    for _, _, c in subs:
        for k, v in (c.get("refusals") or {}).items():
            merged["refusals"][k] = merged["refusals"].get(k, 0) + v
    return merged
