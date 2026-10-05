#!/usr/bin/env python3
"""The batch gate: the cheapest images that carry HEAD, then the natives HEAD affects, sharded.

    python3 tools/batch.py gate HEAD --base SET [--priority integrator] [--all]
                               [--images LIST] [--build] [--dry-run]
    python3 tools/batch.py fanout SET --from BOX     copy a published set to every box
    python3 tools/batch.py fill SET [--tiers core,e2e,peer,resilience]
                                                     the full suite as boxq fill jobs

`gate` decides, then submits everything through tools/boxq.py (so it is placed
by free capacity like any other job and the integrator's priority wins):

1. Images.  If tools/native_overlay.py can carry HEAD over the published set
   SET into every image the modules read (a host-only batch: no book, build
   script or packaging change), there is no image build: the natives run as an
   OVERLAY job on SET.  Otherwise (or with --build) one image-build job
   certifies, acquires, runs host-ld and saves the images in parallel on the
   rented box with the most room, and publishes HEAD's set there; `fanout`
   then copies it from that box straight to every other rented box and to hbox
   (each pulls from the builder; nothing passes through the laptop).
2. Natives.  The modules are `tools/scenario_suite.py affected` over the files
   SET..HEAD changed: the smoke tier, always, and the modules the change can
   reach (--all: every tier module).  One boxq native job, sharded over the
   boxes holding the set, longest tests first.
3. The verdict table: each stage's wall time, the run ids, the red tests.  One
   json line per gate in build/coordinator/boxq/batches.jsonl.

`fill` queues the whole suite against SET at fill priority: it runs only on
capacity nobody asked for, and its reds land in results.jsonl
(`boxq results --red`) with the test ids, for routing to their lanes.

Exit: 0 green, 1 red natives, 2 refused, 3 a stage failed to run.
"""
from __future__ import annotations

import argparse
import json
import re
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

TOOLS_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import box_table  # noqa: E402
import boxq  # noqa: E402

ALL_IMAGES = "developer,production,dtn,dtn-developer"
SELECTOR_REFS = ("HEAD", "origin/dev", "origin/lane/scenarios-2")
# The opt-in variables the tiers set (tests/scenarios/tiers.tsv `env` rows):
# a gate runs what it selects, with skips allowed for the rest (INN trees).
OPT_IN = ("FN_RUN_CONSUMER_E2E=1", "FN_RUN_CONSUMER_POLL_E2E=1", "FN_RUN_CONSUMER_INSPECT=1",
          "FN_RUN_CONSUMER_PROJECT_BOUNDS=1", "FN_RUN_CONSUMER_EXCHANGE=1", "FN_RUN_HYBRID_E2E=1")


def git(*words, cwd=TOOLS_ROOT) -> str:
    return subprocess.run(["git", "-C", str(cwd), *words], capture_output=True, text=True).stdout.strip()


def full(rev: str) -> str:
    sha = git("rev-parse", "--verify", f"{rev}^{{commit}}")
    if not sha:
        raise SystemExit(f"batch: no commit {rev}")
    return sha


def changed(base: str, head: str) -> list[str]:
    return [p for p in git("diff", "--name-only", base, head).splitlines() if p]


def selector_tree(head: str) -> Path:
    """HEAD's tests and planning, with the first `affected`-capable scenario_suite."""
    out = Path(tempfile.mkdtemp(prefix="batch-select."))
    subprocess.run(f"git -C {TOOLS_ROOT} archive {head} tools tests planning | tar -x -C {out}",
                   shell=True, check=True)
    if "def affected" not in (out / "tools/scenario_suite.py").read_text(errors="replace"):
        for ref in SELECTOR_REFS[1:]:
            text = git("show", f"{ref}:tools/scenario_suite.py")
            if "def affected" in text:
                subprocess.run(f"git -C {TOOLS_ROOT} archive {ref} tools/scenario_suite.py tests/scenarios "
                               f"planning/scenarios-2026-10-04-modules.tsv | tar -x -C {out}",
                               shell=True, check=True)
                break
        else:
            raise SystemExit("batch: no scenario_suite.py with `affected` on HEAD, dev or lane/scenarios-2")
    return out


def runnable(tree: Path, mods: list[str], images: str) -> tuple[list[str], list[str]]:
    """(modules the set's images can run, modules refused: they read an image the set lacks)."""
    if not mods:
        return [], []
    done = subprocess.run([sys.executable, "tools/native_env.py", "plan", "--images", images, "--allow-skips",
                           *mods], cwd=tree, capture_output=True, text=True)
    refused = sorted({m.group(1) for m in re.finditer(r"(tests\.\S+) reads FN_\S+: build the", done.stdout + done.stderr)})
    return [m for m in mods if m not in refused], refused


def affected(head: str, files: list[str], everything: bool, images: str = "") -> list[str]:
    tree = selector_tree(head)
    try:
        if everything:
            mods = []
            for t in ("smoke", "core", "e2e", "peer", "resilience"):
                got = subprocess.run([sys.executable, "tools/scenario_suite.py", "modules", t], cwd=tree,
                                     capture_output=True, text=True).stdout.split()
                mods += [m for m in got if m not in mods]
            return runnable(tree, mods, images)[0] if images else mods
        done = subprocess.run([sys.executable, "tools/scenario_suite.py", "affected", *files], cwd=tree,
                              capture_output=True, text=True)
        if done.returncode:
            raise SystemExit(f"batch: scenario_suite affected failed: {done.stderr.strip()}")
        mods = []
        for m in done.stdout.split():
            if m not in mods and (tree / (m.replace(".", "/") + ".py")).exists():
                mods.append(m)
        if images:
            mods, refused = runnable(tree, mods, images)
            for m in refused:
                print(f"batch: {m} not run: it reads an image the set does not hold", flush=True)
        return mods
    finally:
        shutil.rmtree(tree, ignore_errors=True)


def overlay_carries(base: str, head: str, images: str) -> tuple[bool, str]:
    out = Path(tempfile.mkdtemp(prefix="batch-overlay."))
    try:
        done = subprocess.run([sys.executable, str(TOOLS_ROOT / "tools/native_overlay.py"), "plan",
                               base, head, "--out", str(out)], capture_output=True, text=True)
        if done.returncode:
            return False, (done.stderr or done.stdout).strip().splitlines()[-1:][0] if (done.stderr or done.stdout).strip() else "refused"
        plan = json.loads((out / "plan.json").read_text())
        refused = [i for i in images.split(",") if plan["images"].get(i, {}).get("refused")]
        return (not refused), (f"cannot carry into {', '.join(refused)}" if refused else "overlay plan accepted")
    finally:
        shutil.rmtree(out, ignore_errors=True)


def address(box: str) -> str:
    for line in subprocess.run(["ssh", "-G", box], capture_output=True, text=True).stdout.splitlines():
        if line.startswith("hostname "):
            return line.split()[1]
    raise SystemExit(f"batch: no address for {box}")


def fanout(sha: str, source: str) -> dict[str, str]:
    """Every rented box and hbox pulls SET from SOURCE; {box: 'copied'|'had'|error}."""
    src = address(source)
    boxes = [n for n in box_table.extra_boxes() if n != source] + (["hbox"] if source != "hbox" else [])
    procs = {}
    for box in boxes:
        script = (f"set -e; d=/tank/fn/images/{sha}; if [ -f $d/SHA256SUMS ]; then echo had; exit 0; fi; "
                  f"rsync -a -e 'ssh -o BatchMode=yes -o StrictHostKeyChecking=accept-new' "
                  f"fn@{src}:/tank/fn/images/{sha}/ $d.partial/ && (cd $d.partial && sha256sum -c --quiet SHA256SUMS) "
                  f"&& mv $d.partial $d && echo copied")
        procs[box] = subprocess.Popen(["ssh", "-n", "-o", "BatchMode=yes", box, script],
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    out = {}
    for box, proc in procs.items():
        text, _ = proc.communicate(timeout=3600)
        out[box] = text.strip().splitlines()[-1] if proc.returncode == 0 and text.strip() else f"failed: {text.strip()[-200:]}"
    return out


def boxq_submit(words: list[str]) -> str:
    done = subprocess.run([sys.executable, str(TOOLS_ROOT / "tools/boxq.py"), "submit", *words],
                          capture_output=True, text=True)
    if done.returncode:
        raise SystemExit(f"batch: boxq submit refused: {done.stderr.strip()}")
    return done.stdout.split()[0]


def boxq_wait(job: str) -> dict:
    subprocess.run([sys.executable, str(TOOLS_ROOT / "tools/boxq.py"), "wait", job])
    return boxq.read_state(boxq.state_dir())["jobs"][job]


def gate(args) -> int:
    t0 = time.time()
    head, base = full(args.head), full(args.base)
    files = changed(base, head)
    stages = []
    images = args.images or ALL_IMAGES
    mods = affected(head, files, args.all, images)
    mode = "build" if args.build else None
    why = "--build"
    if mode is None:
        ok, why = overlay_carries(base, head, images)
        mode = "overlay" if ok else "build"
    print(f"batch: {head[:9]} over {base[:9]}: {len(files)} files changed; {mode} ({why}); "
          f"{len(mods)} modules", flush=True)
    if args.dry_run:
        print("\n".join(mods))
        return 0
    common = ["--priority", args.priority, "--lane", args.lane, "--root", str(TOOLS_ROOT)]
    image_set = base
    if mode == "build":
        t = time.time()
        job = boxq_submit(["--kind", "image-build", *common, "--rev", head, "--images", images])
        print(f"batch: image build {job}", flush=True)
        built = boxq_wait(job)
        stages.append(("images", round(time.time() - t), built["verdict"], built.get("run_id")))
        if built["verdict"] != "OK":
            return report(head, base, mode, stages, mods, t0, 3)
        t = time.time()
        copied = fanout(head, built["box"])
        stages.append(("fanout", round(time.time() - t), "OK" if all(v in ("copied", "had") for v in copied.values()) else "PARTIAL", copied))
        image_set = head
    t = time.time()
    kind = "overlay" if mode == "overlay" else "native"
    extra = ["--", "--allow-skips"] + [w for e in OPT_IN for w in ("--env", e)]
    job = boxq_submit(["--kind", kind, *common, "--image-set", image_set, "--rev", head,
                       "--images", images, *mods, *extra])
    print(f"batch: natives {job} ({len(mods)} modules)", flush=True)
    ran = boxq_wait(job)
    stages.append(("natives", round(time.time() - t), ran["verdict"], ran.get("run_id")))
    code = {"OK": 0, "RED": 1}.get(ran["verdict"], 3)
    return report(head, base, mode, stages, mods, t0, code, ran.get("reds") or [])


def report(head, base, mode, stages, mods, t0, code, reds=()) -> int:
    wall = round(time.time() - t0)
    print(f"\n| stage | wall | verdict | run |\n|---|---|---|---|")
    for name, secs, verdict, run in stages:
        print(f"| {name} | {secs // 60}m{secs % 60:02d}s | {verdict} | {run} |")
    print(f"| total | {wall // 60}m{wall % 60:02d}s | {'GREEN' if code == 0 else 'RED' if code == 1 else 'ERROR'} | {mode} |")
    if reds:
        print("red: " + " ".join(reds))
    row = {"head": head, "base": base, "mode": mode, "modules": mods, "wall_s": wall, "exit": code,
           "stages": [list(s[:3]) + [s[3] if isinstance(s[3], (str, list, dict, type(None))) else str(s[3])] for s in stages],
           "reds": list(reds), "finished": boxq.iso(time.time())}
    d = boxq.state_dir()
    d.mkdir(parents=True, exist_ok=True)
    with open(d / "batches.jsonl", "a") as out:
        out.write(json.dumps(row) + "\n")
    return code


def fill(args) -> int:
    sha = full(args.set)
    tree = selector_tree(sha)
    try:
        for t in args.tiers.split(","):
            mods = subprocess.run([sys.executable, "tools/scenario_suite.py", "modules", t], cwd=tree,
                                  capture_output=True, text=True).stdout.split()
            if not mods:
                continue
            job = boxq_submit(["--kind", "native", "--priority", "fill", "--lane", f"fill-{t}",
                               "--root", str(TOOLS_ROOT), "--image-set", sha, "--rev", args.rev or sha,
                               "--images", ALL_IMAGES, *mods, "--", "--allow-skips",
                               *[w for e in OPT_IN for w in ("--env", e)]])
            print(f"batch: fill {t}: {job} ({len(mods)} modules on {sha[:9]})")
    finally:
        shutil.rmtree(tree, ignore_errors=True)
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="batch", description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("gate")
    g.add_argument("head")
    g.add_argument("--base", required=True, help="the published image set the batch starts from")
    g.add_argument("--priority", default="integrator", choices=tuple(boxq.PRIORITIES))
    g.add_argument("--lane", default=os.environ.get("FN_LANE") or "batch")
    g.add_argument("--images")
    g.add_argument("--all", action="store_true", help="every tier module, not only the affected")
    g.add_argument("--build", action="store_true", help="build images even when an overlay would carry HEAD")
    g.add_argument("--dry-run", action="store_true")
    f = sub.add_parser("fanout")
    f.add_argument("set")
    f.add_argument("--from", dest="source", required=True)
    fl = sub.add_parser("fill")
    fl.add_argument("set")
    fl.add_argument("--rev")
    fl.add_argument("--tiers", default="core,e2e,peer,resilience")
    args = p.parse_args(argv)
    if args.cmd == "gate":
        return gate(args)
    if args.cmd == "fanout":
        for box, what in fanout(full(args.set), args.source).items():
            print(f"{box}: {what}")
        return 0
    return fill(args)


if __name__ == "__main__":
    raise SystemExit(main())
