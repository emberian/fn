#!/usr/bin/env python3
"""Host loops that make an ACL2 call or take a lock once per iteration (D27's cousin).

D27: bound work, never data.  list_codec_check counts octet LISTS handed to
codecs; nothing counted the access PROTOCOL.  The scalar window borrow made
three ACL2 calls and one mutex acquisition per octet (about 6 us, 75 s a pass
over 12 MiB; PERF-REGRESSION-20261005) and no check noticed, because the loop
lives in the renderer and the call in a host leaf.  This lint is the part of
that class visible in the host source: a loop form (`loop`, `dolist`,
`dotimes`, `do`, `do*`, `mapc`/`mapcar`/`map` over a lambda) inside a `defun`
of a host file whose body, in the loop, dispatches into ACL2 (`fnn-core`,
`fnn-call`, `fnn-core-*`, `fnn-cold-call`, `fnn-state`) or takes a lock
(`fnn-with-observed-mutex`, `sb-thread:with-mutex`).  Such a loop is a site;
what matters is whether its trip count is bounded by a record or by an octet,
which the baseline's per-file counts cannot say, so a NEW site is judged by a
human and either given a batch entry (one call for the range, a span) or
accepted by raising its file's baseline in the same commit with the reason.

`--list` prints the sites; `--write` rewrites tools/loop_call_baseline.json.
The check fails when a file's count exceeds its baseline or a file not in it
has a site.  It only shrinks otherwise.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools import ratchet  # noqa: E402
from tools.ledger import Sym, head  # noqa: E402

BASELINE = ROOT / "tools" / "loop_call_baseline.json"
LOOPS = {"loop", "dolist", "dotimes", "do", "do*", "mapc", "mapcar", "map", "maphash",
         "loop-finish"} - {"loop-finish"}
CALLS_EXACT = {"fnn-core", "fnn-call", "fnn-cold-call", "fnn-state", "fnn-core-state",
               "fnn-core-values", "fnn-core-single"}
LOCKS = {"fnn-with-observed-mutex", "sb-thread:with-mutex", "with-mutex"}


def host_files() -> list[Path]:
    return sorted((ROOT / "host").glob("*.lisp")) + sorted((ROOT / "host" / "native").glob("*.lisp"))


def is_call(name: str) -> bool:
    return name in CALLS_EXACT or name.startswith("fnn-core-")


def hits(form) -> list[str]:
    """Calls and lock acquisitions anywhere under FORM."""
    out: list[str] = []
    if isinstance(form, list) and form:
        if isinstance(form[0], Sym):
            n = str(form[0]).lower()
            if is_call(n):
                out.append("call")
            elif n in LOCKS:
                out.append("lock")
        for y in form:
            out.extend(hits(y))
    return out


def loops(form, acc: list) -> None:
    if not isinstance(form, list) or not form:
        return
    if isinstance(form[0], Sym) and str(form[0]).lower() in LOOPS:
        kinds = sorted(set(hits(form[1:])))
        if kinds:
            acc.append((str(form[0]).lower(), kinds))
    for y in form:
        loops(y, acc)


def scan(files=None) -> list[dict]:
    sites = []
    for path in files or host_files():
        rel = str(path.relative_to(ROOT)) if ROOT in path.resolve().parents else str(path)
        try:
            forms = ledger.Reader(path.read_text()).top_level()
        except Exception as e:
            sites.append({"file": rel, "defun": "?", "error": str(e)})
            continue
        for form, _pos in forms:
            if not (isinstance(form, list) and form and head(form) == "defun" and len(form) > 2):
                continue
            acc: list = []
            loops(form[3:], acc)
            for kind, why in acc:
                sites.append({"file": rel, "defun": str(form[1]), "loop": kind, "does": "+".join(why)})
    return sites


def counts(sites):
    out: dict[str, int] = {}
    for s in sites:
        if "error" not in s:
            out[s["file"]] = out.get(s["file"], 0) + 1
    return dict(sorted(out.items()))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args(argv)
    sites = scan()
    now = counts(sites)
    total = sum(now.values())
    if args.list:
        for s in sites:
            if "error" not in s:
                print(f"{s['file']}:{s['defun']} {s['loop']} [{s['does']}]")
    errors = [s for s in sites if "error" in s]
    for s in errors:
        print(f"loop_call_check: cannot read {s['file']}: {s['error']}")
    if args.write:
        old = json.loads(BASELINE.read_text())["sites"] if BASELINE.exists() else None
        if ratchet.report("loop_call_check", ratchet.refused("loop_call_check", old, now)):
            return 1
        BASELINE.write_text(json.dumps({"_doc": __doc__.splitlines()[0], "total": total,
                                        "sites": now}, indent=1) + "\n")
        print(f"loop_call_check: baseline written: {total} sites in {len(now)} files")
        return 0
    base = json.loads(BASELINE.read_text())
    bad = []
    for f, n in now.items():
        b = base["sites"].get(f)
        if b is None:
            bad.append(f"{f}: {n} per-iteration call/lock loops, not in the baseline")
        elif n > b:
            bad.append(f"{f}: {n} per-iteration call/lock loops, baseline {b}")
    for line in bad:
        print(f"loop_call_check: {line}")
    shrunk = base["total"] - total
    print(f"loop_call_check: {total} host loops that call ACL2 or take a lock per iteration in "
          f"{len(now)} files (baseline {base['total']}{', shrunk by %d: run --write' % shrunk if shrunk > 0 else ''})")
    return 1 if (bad or errors) else 0


if __name__ == "__main__":
    sys.exit(main())
