"""Cells: which numbers of a finished run are the cell's metrics.

`derive(workload, phases)` maps the phase records the driver wrote onto the
flat dotted metric names that tools/load/bars.json checks name, and says why
a metric is absent (`not_measured`).  Pure functions over JSON: laptop-testable.
"""
from __future__ import annotations

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
    fn = {"post-rate": _post_rate, "readers": _readers, "article-sizes": _sizes, "growth": _growth,
          "m1-durable": _durable, "smoke": _smoke}.get(workload)
    if fn:
        fn(phases, m, nm)
    if workload == "rss-small-filled" and "rss_kib.vmrss" not in m:
        nm["rss_kib.vmrss"] = "idle phase did not complete"
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


def _smoke(phases, m, nm):
    rd = _phase(phases, "read")
    m["smoke.articles"] = (_cmd(rd, "ARTICLE")).get("n", 0)


def _post_rate(phases, m, nm):
    for tag in ("c1", "c8"):
        ph = _phase(phases, tag)
        if ph and _rate(ph) is not None:
            m["post.rate_" + tag] = round(_rate(ph), 2)
            st = _cmd(ph, "POST")
            m["post.p50_ms." + tag], m["post.p99_ms." + tag] = st.get("p50_ms"), st.get("p99_ms")
        else:
            nm["post.rate_" + tag] = "phase %s did not complete" % tag


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
