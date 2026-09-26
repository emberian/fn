#!/usr/bin/env python3
"""One-dimension scaling rows for the hot-path check's finds (PKT-334).

tools/hot_path_check.py finds suspects statically.  This produces the
measurements that confirm or refute them (answers 2026-09-26 §2: "Hold the
request and profile constant while varying N.  Hold N constant while varying
payload size").  It varies ONE dimension at a time and runs
tools/rep_measure.py once per point on the same image and profile:

  N        retained articles at a fixed request (2 KiB): 1,000 / 4,000 / 10,000
  payload  article octets at a fixed N = 1,000: 2 KiB / 16 KiB / 32 KiB
           (32 KiB is the article bound, books/article.lisp)

Every point records, per operation: the wall time (median of K), the bytes
consed per operation (the heap hook's allocation counter bracketing a batch
of K; allocation is the executed-work proxy used by hot-path-scans), and for
the whole load and the reopen, the seconds.  The table gives each row's ratio
to the first row: a per-operation figure that grows with N at a fixed request
is retained-state work, which is what a find predicts.  The rows cannot name
the walk; a profile does (rep_measure's --profile).  Lock-hold time is not
exposed by the owner, and primitive visits are not counted by this harness:
both are recorded as absent, never estimated.

Usage (the one command, from a lane worktree on the laptop):

    python3 tools/scale_probe.py box REV [--name NAME] [--vary N|payload|both]

ships REV (git archive) to hbox:/tank/fn/scratch/NAME/tree-REV, certifies the
default profile's roots incrementally from the certificate cache, builds the
developer image and its heap-hook twin under swarm-build, and runs every point
under `systemd-run --user --scope -p MemoryMax` (24G; 40G at N >= 10,000) on
tmpfs, detached (nohup).  `fetch` copies the results back and prints the table:

    python3 tools/scale_probe.py fetch REV [--name NAME] [--out DIR]
    python3 tools/scale_probe.py table DIR          # the rows of fetched JSON
    python3 tools/scale_probe.py run ...            # on the box: one sweep

Never touches /tank/fn/node.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HOOK = ROOT / "planning" / "evidence" / "hot-path-checker-2026-09-26" / "hook"
BOX = "hbox"
SCRATCH = "/tank/fn/scratch"
ACL2 = "/tank/fn/toolchains/w28/acl2-literal-4g"
CACHE = "/tank/fn/certcache"
OPENSSL = "/tank/fn/toolchains/openssl-3.5.8"
SWEEPS = {
    "N": [("n1000-2k", 1000, 2048), ("n4000-2k", 4000, 2048), ("n10000-2k", 10000, 2048)],
    "payload": [("n1000-2k", 1000, 2048), ("n1000-16k", 1000, 16384),
                ("n1000-32k", 1000, 32768)],
}

# (label, JSON path) of each per-operation figure in rep_measure's output.
FIGURES = [
    ("POST ms", ("alloc_post", "timing", "median_ms")),
    ("POST bytes", ("alloc_post", "bytes_consed_per_op")),
    ("STAT ms", ("alloc_stat", "timing", "median_ms")),
    ("STAT bytes", ("alloc_stat", "bytes_consed_per_op")),
    ("ARTICLE ms", ("alloc_article", "timing", "median_ms")),
    ("ARTICLE bytes", ("alloc_article", "bytes_consed_per_op")),
    ("OVER ms", ("over_present", "median_ms")),
    ("greeting ms", ("greeting", "median_ms")),
    ("load s", ("load_seconds",)),
    ("reopen s", ("reopen_seconds",)),
]


def dig(data: dict, path: tuple):
    for key in path:
        if not isinstance(data, dict) or key not in data:
            return None
        data = data[key]
    return data


def sweep_points(vary: str) -> list[tuple[str, int, int]]:
    if vary == "both":
        seen, out = set(), []
        for point in SWEEPS["N"] + SWEEPS["payload"]:
            if point[0] not in seen:
                seen.add(point[0])
                out.append(point)
        return out
    return SWEEPS[vary]


# ---------------------------------------------------------------------------
# On the box
# ---------------------------------------------------------------------------


def run(arguments) -> int:
    tree = Path(arguments.tree)
    out = Path(arguments.out)
    out.mkdir(parents=True, exist_ok=True)
    status = 0
    for label, articles, octets in sweep_points(arguments.vary):
        heap = Path(arguments.work) / label / "heap"
        work = Path(arguments.work) / label / "m"
        subprocess.run(["rm", "-rf", str(Path(arguments.work) / label)], check=False)
        heap.mkdir(parents=True, exist_ok=True)
        memory = "40G" if articles >= 10000 else "24G"
        env = dict(os.environ, FN_PROF_LOAD=str(Path(arguments.hook) / "heap.lisp"),
                   FN_HEAP_DIR=str(heap), FN_OPENSSL_PREFIX=OPENSSL,
                   LD_LIBRARY_PATH=f"{OPENSSL}/lib")
        command = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={memory}",
                   sys.executable, str(tree / "tools" / "rep_measure.py"),
                   "--image", str(tree / "build" / "fn-host-developer-prof"),
                   "--heap-dir", str(heap), "--work", str(work),
                   "--articles", str(articles), "--octets", str(octets),
                   "--samples", str(arguments.samples), "--readers", "3",
                   "--skip-checkpoint", "--json", str(out / f"{label}.json")]
        with open(out / f"{label}.log", "w") as log:
            code = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT).returncode
        print(f"{label} rc={code}", flush=True)
        status = status or code
    (out / "done").write_text(f"{status}\n")
    return status


# ---------------------------------------------------------------------------
# The table
# ---------------------------------------------------------------------------


def table(directory: Path, out=sys.stdout) -> list[dict]:
    rows = []
    for vary, points in SWEEPS.items():
        first = None
        print(f"\nvarying {vary}" + (" (octets 2048)" if vary == "N" else " (N 1000)"),
              file=out)
        print("| point | " + " | ".join(label for label, _ in FIGURES) + " |", file=out)
        print("| --- |" + " ---: |" * len(FIGURES), file=out)
        for label, articles, octets in points:
            path = directory / f"{label}.json"
            if not path.exists():
                print(f"| {label} | " + " | ".join("absent" for _ in FIGURES) + " |", file=out)
                continue
            data = json.loads(path.read_text())
            values = [dig(data, figure) for _, figure in FIGURES]
            if first is None:
                first = values
            cells = []
            for value, base in zip(values, first):
                if value is None:
                    cells.append("absent")
                    continue
                ratio = f" (x{value / base:.2f})" if base not in (None, 0) and value is not base else ""
                cells.append(f"{value:,.2f}{ratio}" if isinstance(value, float)
                             else f"{value:,}{ratio}")
            print(f"| {label} | " + " | ".join(cells) + " |", file=out)
            rows.append({"vary": vary, "point": label, "articles": articles, "octets": octets,
                         **{name: value for (name, _), value in zip(FIGURES, values)},
                         "json_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    return rows


# ---------------------------------------------------------------------------
# From the laptop
# ---------------------------------------------------------------------------


def ssh(command: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(["ssh", BOX, command], check=check, text=True,
                          capture_output=True)


def box(arguments) -> int:
    rev = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short=8", arguments.rev],
                         check=True, text=True, capture_output=True).stdout.strip()
    base = f"{SCRATCH}/{arguments.name}"
    tree = f"{base}/tree-{rev}"
    hook = f"{base}/hook"
    results = f"{base}/results-{rev}"
    ssh(f"mkdir -p {shlex.quote(tree)} {shlex.quote(hook)} {shlex.quote(results)}")
    archive = subprocess.Popen(["git", "-C", str(ROOT), "archive", rev], stdout=subprocess.PIPE)
    subprocess.run(["ssh", BOX, f"tar -x -C {shlex.quote(tree)}"], stdin=archive.stdout,
                   check=True)
    archive.wait()
    for name in ("heap.lisp", "prof-raw.lisp"):
        subprocess.run(["scp", "-q", str(HOOK / name), f"{BOX}:{hook}/{name}"], check=True)
    script = f"""#!/bin/sh
set -u
T={tree}; H={hook}; R={results}
export FN_ACL2={ACL2} FN_CERT_CACHE={CACHE} FN_OPENSSL_PREFIX={OPENSSL}
cd $T
printf '(progn! (set-raw-mode t) (load "%s/prof-raw.lisp"))\\n' $H > $H/prof-hook.lisp
python3 tools/proof_artifacts.py roots --profile default 2>/dev/null | grep '^books/\\|^tests/' > $R/roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 900 $(cat $R/roots.txt) > $R/cert.log 2>&1
echo "cert rc=$?" > $R/setup.out
mkdir -p build/freeze
python3 tools/proof_artifacts.py acquire --profile default --acl2 {ACL2} --cache {CACHE} > build/freeze/acquire-default.txt 2>&1 || {{ echo acquire-failed >> $R/setup.out; echo 3 > $R/done; exit 3; }}
python3 tools/proof_artifacts.py validate --profile default --acl2 {ACL2} > build/freeze/validate-default.txt 2>&1 || {{ echo validate-failed >> $R/setup.out; echo 4 > $R/done; exit 4; }}
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh >> $R/setup.out 2>&1 || {{ echo 5 > $R/done; exit 5; }}
awk -v hook=$H/prof-hook.lisp '/^\\(defttag nil\\)/{{while((getline l < hook)>0) print l}} {{print}}' host/native/build.lisp > build/prof-build.lisp
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=build/prof-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-prof FN_NATIVE_LOG=build/freeze/native-build-prof.log swarm-build sh tools/build_native_host.sh >> $R/setup.out 2>&1 || {{ echo 6 > $R/done; exit 6; }}
sha256sum build/fn-host-developer* > $R/image.sha256
python3 tools/scale_probe.py run --tree $T --hook $H --work /dev/shm/{arguments.name}-{rev} --out $R --vary {arguments.vary} --samples {arguments.samples} > $R/runs.out 2>&1
rm -rf /dev/shm/{arguments.name}-{rev}
(cd $R && sha256sum *.json *.log *.out > SHA256SUMS)
"""
    subprocess.run(["ssh", BOX, f"cat > {results}/box.sh"], input=script, text=True, check=True)
    ssh(f"cd {results} && nohup sh box.sh > box.nohup 2>&1 < /dev/null &")
    print(f"started on {BOX}: {results} (wait: tools/wait_for.sh --host {BOX} "
          f"--file {results}/done)")
    return 0


def fetch(arguments) -> int:
    rev = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short=8", arguments.rev],
                         check=True, text=True, capture_output=True).stdout.strip()
    results = f"{SCRATCH}/{arguments.name}/results-{rev}"
    out = Path(arguments.out or ROOT / "build" / "scale-probe" / rev)
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run(["rsync", "-a", f"{BOX}:{results}/", f"{out}/"], check=True)
    table(out)
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    one = sub.add_parser("run", help="on the box: one sweep with an existing tree and image")
    one.add_argument("--tree", required=True)
    one.add_argument("--hook", required=True)
    one.add_argument("--work", required=True)
    one.add_argument("--out", required=True)
    one.add_argument("--vary", choices=("N", "payload", "both"), default="both")
    one.add_argument("--samples", type=int, default=32)
    shown = sub.add_parser("table", help="print the rows of a fetched results directory")
    shown.add_argument("directory")
    shown.add_argument("--json", default=None)
    start = sub.add_parser("box", help="ship REV to hbox, build, run the sweep detached")
    start.add_argument("rev")
    start.add_argument("--name", default="hot-path-checker")
    start.add_argument("--vary", choices=("N", "payload", "both"), default="both")
    start.add_argument("--samples", type=int, default=32)
    back = sub.add_parser("fetch", help="copy a finished sweep back and print its table")
    back.add_argument("rev")
    back.add_argument("--name", default="hot-path-checker")
    back.add_argument("--out", default=None)
    arguments = parser.parse_args(argv)
    if arguments.command == "run":
        return run(arguments)
    if arguments.command == "table":
        rows = table(Path(arguments.directory))
        if arguments.json:
            Path(arguments.json).write_text(json.dumps(rows, indent=1) + "\n")
        return 0
    if arguments.command == "box":
        return box(arguments)
    return fetch(arguments)


if __name__ == "__main__":
    sys.exit(main())
