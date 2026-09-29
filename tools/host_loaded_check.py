#!/usr/bin/env python3
"""Refuse a host file no build loads (Q7k, 2026-09-29).

A file under host/ (host/*.lisp, host/native/*.lisp) is a host line only
when a build loads it: the images (host/native/build.lisp, build-dtn.lisp),
the extraction world the served product comes from
(tools/extract/world-host.lisp) or a test image (build-store-test.lisp) --
tools/reach_check.py's IMAGE_BUILDS and TEST_IMAGE_BUILDS, followed through
`ld' and raw `load' (reach_check.loaded_host_files).  On 2026-09-29 fifteen
host files were loaded by none of them: four the Python host's retirement
(T5b) had deleted and a merge brought back, three hosts of the retired BP
labs, a page-store prototype, and a scenario catalog that belonged in
tests/.  Nothing checked it, so theorems were counted as hosted through
files no running server contains.

KNOWN names a file allowed to stay unloaded, with why; it only shrinks: a
KNOWN file that is now loaded, or gone, is red too (drop the entry).
Mechanical, no ACL2; exit 0 clean, 1 with findings.
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

# path -> why it may stay unloaded.  Shrink-only.
KNOWN: dict[str, str] = {}


def host_files(root: pathlib.Path = ROOT) -> list[str]:
    return sorted(str(p.relative_to(root)) for pattern in ("host/*.lisp", "host/native/*.lisp")
                  for p in root.glob(pattern))


def findings(root: pathlib.Path = ROOT, known: dict[str, str] = KNOWN) -> list[str]:
    import reach_check
    builds = {**reach_check.IMAGE_BUILDS, **reach_check.TEST_IMAGE_BUILDS}
    loaded = reach_check.loaded_host_files(builds, root)
    present = host_files(root)
    out = [f"{path}: no build loads it (reach_check IMAGE_BUILDS/TEST_IMAGE_BUILDS): "
           "wire it into a build, move a test harness to tests/, or delete it and "
           "list it in planning/retired-paths.json"
           for path in present if path not in loaded and path not in known]
    out += [f"{path}: KNOWN as unloaded but a build loads it now: drop its KNOWN entry"
            for path in sorted(known) if path in loaded]
    out += [f"{path}: KNOWN as unloaded but it is gone: drop its KNOWN entry"
            for path in sorted(known) if path not in present]
    return out


def main() -> int:
    found = findings()
    for line in found:
        print("host_loaded_check: " + line)
    if not found:
        print(f"host_loaded_check: every one of {len(host_files())} host files is loaded by a build")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
