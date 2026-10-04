#!/usr/bin/env python3
"""boxq: one queue for the build boxes, so a lane never picks a box by hand.

    boxq submit --kind KIND [--priority integrator|lane|fill] [--box BOX]
                [--wait] [kind options] [-- EXTRA...]
    boxq wait JOB            block until JOB (and its shards) end; exit 0 OK, 1 RED, 3 error
    boxq status              each box's cores, load, memory and boxq jobs; then the queue
    boxq results [--red] [--since ISO] [--n N]
    boxq cancel JOB          a queued job is dropped; a running one's local side is
                             stopped (a detached box run may go on: its run id says where)
    boxq pump                place what fits now (the daemon does this every 20 s)
    boxq daemon              the placement loop; `submit` starts it when none runs

KIND and what it runs, from the submitting worktree (the lane), with the tools
of the tree boxq.py lives in:

    certify-lane   tools/farm.py submit BOX --root LANE --jobs N EXTRA; farm.py wait
                   (EXTRA: --lane --affected-by books/x.lisp, --recertify ..., roots)
    native         tools/hbox_native.sh --box BOX --image-set SET --images I --wait
                   REV TESTS  (--image-set required: the box must hold the set)
    overlay        the same with --overlay: REV's host change over the published set
    check-lane     tools/remote_check.sh BOX --target check-lane EXTRA, run in LANE
    image-build    tools/hbox_native.sh --build-only --publish --images I REV on a
                   rented box: certify, acquire, host-ld, the saves in parallel, and
                   REV's set published there (tools/batch.py fans it out)
    image-set      EXTRA is the command (run in LANE, $BOXQ_BOX set); hbox only by
                   rule, under hbox's one-certify slot
    cmd            EXTRA is the command, as image-set, on any box (fill kits, probes)

native/overlay options: --image-set SHA, --rev REV (default HEAD of LANE, resolved
at submit), --images LIST (default developer), --mem SIZE, TESTS as positional
words after the options (modules, classes or single test ids).  Without --box a
native job is SHARDED at placement over every rented box that holds the set and
has room: modules longer than the target wall are split into their tests
(timings learned from earlier runs, build/coordinator/boxq/timings.json) and
the units are packed longest-first onto the boxes' slots.

Placement (pump): a box's free cores = cores - (cores boxq has reserved there +
the load not explained by boxq's own ramped jobs); a job needs its slots free and
its memory available, and a native/overlay job needs the image set on the box.
Priority integrator > lane > fill; a fill job never takes a box below a quarter of
its cores free, and none is placed while a higher job waits for room.  hbox takes
only image-set jobs or a job naming --box hbox, one certify-type job at a time at
--jobs 8, and never past load 16 (it is shared).  persvati only by --box.  The
laptop is never a box.

State: build/coordinator/boxq/ under the shared checkout (FN_BOXQ_DIR overrides):
queue.json (flock), results.jsonl (one line per finished job: kind, box, run id,
verdict, red tests, shas at submit and start), jobs/ID.log (the runner's output).
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import fcntl
import json
import math
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import time

TOOLS_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import box_table  # noqa: E402

KINDS = ("certify-lane", "native", "overlay", "check-lane", "image-build", "image-set", "cmd")
PRIORITIES = {"integrator": 0, "lane": 1, "fill": 2}
CERTIFY_KINDS = ("certify-lane", "check-lane", "image-set", "image-build")
HBOX_LOAD_CAP = 16.0
HBOX_JOBS = 8
FILL_RESERVE = 0.25        # a fill job leaves this share of a box's cores free
RAMP_SECONDS = 90          # a job younger than this is not yet in the box's load
PROBE_TTL = 45
MIN_SHARD_SECONDS = 120    # a native job predicted under this is not split
FILL_CHUNK_SECONDS = 600   # a fill shard takes about this much work per slot, so
                           # fill frees its boxes every ~10 min for queued work
CHUNK_SECONDS = 420        # any other native shard: the rest of the job stays queued
                           # and goes, chunk by chunk, to whichever box frees first
UNKNOWN_MODULE_SECONDS = 60.0
# Per-kind defaults: (cores per slot, GiB per slot, default slots)
SHAPE = {
    "certify-lane": (1.0, 4.0, 8),
    "check-lane": (1.0, 2.5, 6),
    "native": (1.5, 3.0, 4),
    "overlay": (1.5, 3.0, 4),
    "image-set": (1.0, 5.0, 8),
    "image-build": (1.0, 4.0, 12),
    "cmd": (1.0, 2.0, 2),
}


# ------------------------------------------------------------------ places

def state_dir(environ=os.environ) -> Path:
    if environ.get("FN_BOXQ_DIR"):
        return Path(environ["FN_BOXQ_DIR"])
    common = subprocess.run(["git", "-C", str(TOOLS_ROOT), "rev-parse", "--git-common-dir"],
                            capture_output=True, text=True).stdout.strip()
    base = Path(common).resolve().parent if common else TOOLS_ROOT
    return base / "build" / "coordinator" / "boxq"


def now() -> float:
    return time.time()


def iso(t: float | None) -> str | None:
    return None if t is None else dt.datetime.fromtimestamp(t, dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


@contextlib.contextmanager
def locked_state(directory: Path):
    """The queue under an exclusive flock; written back atomically on exit."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "jobs").mkdir(exist_ok=True)
    with open(directory / "queue.lock", "a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        path = directory / "queue.json"
        try:
            state = json.loads(path.read_text())
        except (FileNotFoundError, ValueError):
            state = {"jobs": {}, "probes": {}, "seq": 0}
        yield state
        tmp = path.with_suffix(".tmp")
        tmp.write_text(json.dumps(state, indent=1, sort_keys=True))
        os.replace(tmp, path)


def read_state(directory: Path) -> dict:
    try:
        return json.loads((directory / "queue.json").read_text())
    except (FileNotFoundError, ValueError):
        return {"jobs": {}, "probes": {}, "seq": 0}


# ------------------------------------------------------------------ boxes

PROBE_SCRIPT = r'''n=$(getconf _NPROCESSORS_ONLN); l=$(cut -d" " -f1 /proc/loadavg)
m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); a=0
[ -r /proc/spl/kstat/zfs/arcstats ] && a=$(awk '$1=="size"{print int($3/1073741824)}' /proc/spl/kstat/zfs/arcstats)
s=$(ls /tank/fn/images 2>/dev/null | tr '\n' ',')
echo "$n $l $m $a $s"'''


def ssh_probe(box: str) -> dict | None:
    try:
        done = subprocess.run(["ssh", "-n", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10", box,
                               PROBE_SCRIPT], capture_output=True, text=True, timeout=25)
    except subprocess.TimeoutExpired:
        return None
    words = done.stdout.split()
    if done.returncode != 0 or len(words) < 4:
        return None
    return {"cores": int(words[0]), "load": float(words[1]),
            "mem": int(words[2]) + int(words[3]),
            "sets": [s for s in (words[4] if len(words) > 4 else "").split(",") if s]}


# The seam tests replace: box name -> probe dict or None.
PROBE = ssh_probe


def known_boxes(environ=None) -> dict:
    """{name: {"cores", "pick", "rented"}} for hbox, persvati and every live rented row."""
    boxes = {"hbox": {"cores": 24, "pick": False, "rented": False},
             "persvati": {"cores": 24, "pick": False, "rented": False}}
    for name, row in box_table.extra_boxes(environ=environ).items():
        # Only a box tools/box_qualify.sh qualified takes work (by placement or --box).
        if not (row.get("qualified") or {}).get("ok"):
            continue
        boxes[name] = {"cores": row.get("cores"), "pick": bool(row.get("pick", True)), "rented": True}
    return boxes


def probes(state: dict, boxes: dict, ttl: float | None = None) -> dict:
    ttl = PROBE_TTL if ttl is None else ttl
    out = {}
    for name in boxes:
        cached = state["probes"].get(name)
        if cached and now() - cached.get("t", 0) < ttl:
            out[name] = cached
            continue
        got = PROBE(name)
        entry = dict(got, t=now(), ok=True) if got else {"t": now(), "ok": False}
        state["probes"][name] = entry
        out[name] = entry
    return out


def capacity(name: str, box: dict, probe: dict, jobs: dict) -> dict:
    """Free cores and memory on NAME now, from its probe and boxq's own running jobs."""
    cores = box.get("cores") or probe.get("cores") or 1
    if probe.get("cores"):
        cores = min(cores, probe["cores"])
    running = [j for j in jobs.values() if j["state"] == "running" and j.get("box") == name]
    reserved = sum(j["slots"] * SHAPE[j["kind"]][0] for j in running)
    ramped = sum(j["slots"] * SHAPE[j["kind"]][0] for j in running
                 if now() - (j.get("started") or now()) >= RAMP_SECONDS)
    load = probe.get("load", 0.0)
    external = max(0.0, load - ramped)
    free = cores - reserved - external
    if name == "hbox":
        free = min(free, HBOX_LOAD_CAP - load - (reserved - ramped))
    mem = probe.get("mem", 0) - sum(j["slots"] * SHAPE[j["kind"]][1] for j in running
                                    if now() - (j.get("started") or now()) < RAMP_SECONDS)
    return {"cores": cores, "load": load, "reserved": reserved, "free": free, "mem": mem,
            "sets": probe.get("sets", []), "running": [j["id"] for j in running]}


def eligible(job: dict, boxes: dict) -> list[str]:
    if job.get("box"):
        return [job["box"]] if job["box"] in boxes else []
    if job["kind"] == "image-set":
        return ["hbox"] if "hbox" in boxes else []
    return [n for n, b in boxes.items() if b["rented"] and b["pick"]]


def fits(job: dict, name: str, cap: dict, jobs: dict) -> tuple[bool, str]:
    per_core, per_mem, _ = SHAPE[job["kind"]]
    need = job["slots"] * per_core
    if not cap.get("ok", True):
        return False, f"{name} unreachable"
    if job["kind"] in ("native", "overlay") and job.get("image_set") and job["image_set"] not in cap["sets"]:
        return False, f"{name} lacks image set {job['image_set'][:9]}"
    if name == "hbox" and job["kind"] in CERTIFY_KINDS:
        if any(j["state"] == "running" and j.get("box") == "hbox" and j["kind"] in CERTIFY_KINDS
               for j in jobs.values()):
            return False, "hbox runs one certify at a time"
    reserve = cap["cores"] * FILL_RESERVE if job["priority"] == "fill" else 0.0
    if need > cap["free"] - reserve + 1e-9:
        return False, f"{name} has {cap['free']:.1f} cores free, needs {need:.1f}" + (
            f" (+{reserve:.0f} kept free from fill)" if reserve else "")
    if job["slots"] * per_mem > cap["mem"]:
        return False, f"{name} has {cap['mem']} GiB available, needs {job['slots'] * per_mem:.0f}"
    return True, ""


# ------------------------------------------------------------------ native shards

def load_timings(directory: Path) -> dict:
    try:
        return json.loads((directory / "timings.json").read_text())
    except (FileNotFoundError, ValueError):
        return {"tests": {}, "modules": {}}


def predicted(unit: str, timings: dict) -> float:
    if unit in timings["tests"]:
        return timings["tests"][unit]
    if unit in timings["modules"]:
        return timings["modules"][unit]
    prefix = unit + "."
    parts = [s for t, s in timings["tests"].items() if t.startswith(prefix)]
    return sum(parts) if parts else UNKNOWN_MODULE_SECONDS


def expand(tests: list[str], timings: dict, target: float) -> list[tuple[str, float]]:
    """Units to pack: a module (or class) predicted over TARGET becomes its tests."""
    units = []
    for name in tests:
        seconds = predicted(name, timings)
        members = sorted((t, s) for t, s in timings["tests"].items() if t.startswith(name + "."))
        if seconds > target and len(members) > 1:
            units.extend(members)
        else:
            units.append((name, seconds))
    return units


def pack(units: list[tuple[str, float]], slots: dict[str, int]) -> dict[str, list[str]]:
    """Longest-first onto the boxes' slots; {box: [units]} (boxes given no unit left out)."""
    # Slots interleaved across the boxes, so ties spread the work rather than
    # filling the first box listed.
    most = max(max(1, n) for n in slots.values())
    lanes = [[0.0, box] for i in range(most) for box, n in slots.items() if i < max(1, n)]
    out: dict[str, list[str]] = {}
    for name, seconds in sorted(units, key=lambda u: -u[1]):
        lane = min(lanes, key=lambda l: l[0])
        lane[0] += seconds
        out.setdefault(lane[1], []).append(name)
    return out


def chunk(plan: dict[str, list[str]], room: dict[str, int], timings: dict,
          seconds: float = FILL_CHUNK_SECONDS) -> tuple[dict, list[str]]:
    """Keep about SECONDS of work per slot on each box; the rest waits for room."""
    kept, rest = {}, []
    for box, tests in plan.items():
        budget = room[box] * seconds
        used = 0.0
        for t in tests:
            secs = predicted(t, timings)
            if used == 0.0 or used + secs <= budget:
                kept.setdefault(box, []).append(t)
                used += secs
            else:
                rest.append(t)
    return kept, rest


def shard(job: dict, caps: dict, timings: dict) -> tuple[dict[str, list[str]], dict[str, int]] | None:
    """({box: tests}, {box: jobs}) for an unpinned native job over the boxes
    that can take a slot now; a fill job leaves each box its reserve."""
    units_total = sum(predicted(t, timings) for t in job["tests"])
    per_core, per_mem, _ = SHAPE[job["kind"]]
    room = {}
    for name, cap in caps.items():
        ok, _ = fits(dict(job, slots=1), name, cap, {})
        if ok:
            reserve = cap["cores"] * FILL_RESERVE if job["priority"] == "fill" else 0.0
            room[name] = max(1, min(job.get("max_jobs") or 16,
                                    int((cap["free"] - reserve) / per_core),
                                    int(cap["mem"] / per_mem)))
    if not room:
        return None
    if units_total < MIN_SHARD_SECONDS:
        best = max(room, key=lambda n: room[n])
        return {best: list(job["tests"])}, room
    total_slots = sum(room.values())
    target = max(MIN_SHARD_SECONDS / 2, units_total / total_slots)
    return pack(expand(job["tests"], timings, target), room), room


# ------------------------------------------------------------------ the queue

def new_id(state: dict) -> str:
    state["seq"] = state.get("seq", 0) + 1
    return f"bq{dt.datetime.now(dt.timezone.utc):%m%d%H%M}-{state['seq']:04d}"


def blocking(job: dict, jobs: dict) -> bool:
    """A waiting job of a higher priority than JOB holds fill back."""
    rank = PRIORITIES[job["priority"]]
    return any(PRIORITIES[j["priority"]] < rank and j["state"] == "queued" and j.get("parent") is None
               for j in jobs.values())


def pump(directory: Path, launch=None) -> list[str]:
    """Place every queued job that fits now; returns the ids started."""
    launch = launch or spawn_runner
    started = []
    with locked_state(directory) as state:
        jobs = state["jobs"]
        reap(jobs, directory)
        boxes = known_boxes()
        queued = sorted((j for j in jobs.values() if j["state"] == "queued"),
                        key=lambda j: (PRIORITIES[j["priority"]], j["submitted"]))
        if not queued:
            return started
        wanted = {b for j in queued for b in eligible(j, boxes)}
        probed = probes(state, {n: boxes[n] for n in wanted})
        timings = load_timings(directory)
        for job in queued:
            if job["priority"] == "fill" and blocking(job, jobs):
                job["why"] = "fill waits while a higher-priority job waits"
                continue
            names = eligible(job, boxes)
            caps = {n: dict(capacity(n, boxes[n], probed.get(n, {}), jobs), ok=probed.get(n, {}).get("ok", False))
                    for n in names}
            if not names:
                job["why"] = f"no box can take {job['kind']}" + (f" (--box {job['box']} unknown)" if job.get("box") else "")
                continue
            if job["kind"] in ("native", "overlay") and not job.get("box") and not job.get("parent"):
                planned = shard(job, caps, timings)
                if not planned:
                    job["why"] = "; ".join(fits(dict(job, slots=1), n, c, jobs)[1] for n, c in caps.items())
                    continue
                plan, room = planned
                plan, rest = chunk(plan, room, timings,
                                   FILL_CHUNK_SECONDS if job["priority"] == "fill" else CHUNK_SECONDS)
                job["shards"] = job.get("shards") or []
                job["tests"] = rest
                job["state"] = "queued" if rest else "split"
                for box, tests in plan.items():
                    child_id = new_id(state)
                    child = dict(job, id=child_id, label=child_id, parent=job["id"], box=box, tests=tests,
                                 state="queued", shards=None, why=None,
                                 slots=max(1, min(len(tests), room[box])))
                    jobs[child["id"]] = child
                    job["shards"].append(child["id"])
                    if start(child, box, launch, directory):
                        started.append(child["id"])
                continue
            ranked = []
            for name in names:
                cap = caps[name]
                if job["kind"] in ("certify-lane", "check-lane", "image-set", "image-build", "cmd") and not job.get("slots_fixed"):
                    per = SHAPE[job["kind"]][0]
                    room = int((cap["free"] - (cap["cores"] * FILL_RESERVE if job["priority"] == "fill" else 0)) / per)
                    want = HBOX_JOBS if name == "hbox" else job["slots_wanted"]
                    mem_room = int(cap["mem"] / SHAPE[job["kind"]][1])
                    trial = dict(job, slots=max(1, min(want, room, mem_room, cap["cores"])))
                else:
                    trial = job
                ok, why = fits(trial, name, cap, jobs)
                if ok:
                    affinity = 1 if job.get("lane") and any(
                        j.get("lane") == job["lane"] and j.get("box") == name for j in jobs.values()
                        if j["id"] != job["id"]) else 0
                    ranked.append((affinity, cap["free"], name, trial["slots"]))
                else:
                    job["why"] = why
            if not ranked:
                continue
            _, _, box, slots = max(ranked)
            job["slots"] = slots
            if start(job, box, launch, directory):
                started.append(job["id"])
        finish_parents(jobs, directory)
    return started


def start(job: dict, box: str, launch, directory: Path) -> bool:
    job.update(box=box, state="running", started=now(), why=None)
    try:
        job["pid"] = launch(job, directory)
    except OSError as error:
        job.update(state="done", verdict="ERROR", exit=3, finished=now(), why=f"runner did not start: {error}")
        record(job, directory)
        return False
    return True


def reap(jobs: dict, directory: Path) -> None:
    """A running job whose runner is gone without a verdict is lost (never retried)."""
    for job in jobs.values():
        if job["state"] == "running" and job.get("pid") and not alive(job["pid"]):
            job.update(state="done", verdict="LOST", exit=3, finished=now(),
                       why="the runner died without a verdict; its run id (if any) says where the box run is")
            record(job, directory)


def finish_parents(jobs: dict, directory: Path) -> None:
    for job in jobs.values():
        if job["state"] != "split":
            continue
        kids = [jobs[k] for k in job.get("shards") or [] if k in jobs]
        if kids and all(k["state"] == "done" for k in kids):
            verdicts = {k["verdict"] for k in kids}
            job.update(state="done", finished=max(k["finished"] for k in kids),
                       started=min(k.get("started") or k["finished"] for k in kids),
                       verdict="OK" if verdicts == {"OK"} else ("RED" if verdicts <= {"OK", "RED"} else "ERROR"),
                       exit=max(k.get("exit") or 0 for k in kids),
                       run_id=[k.get("run_id") for k in kids],
                       reds=sorted({r for k in kids for r in k.get("reds") or []}))
            record(job, directory)


def alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def record(job: dict, directory: Path) -> None:
    row = {k: job.get(k) for k in ("id", "parent", "kind", "priority", "lane", "box", "verdict", "exit",
                                   "run_id", "reds", "sha_submit", "sha_start", "dirty", "image_set",
                                   "tests", "shards", "why", "label")}
    row.update(submitted=iso(job.get("submitted")), started=iso(job.get("started")),
               finished=iso(job.get("finished")),
               wall_s=round(job["finished"] - job["started"]) if job.get("finished") and job.get("started") else None,
               log=str(directory / "jobs" / f"{job['id']}.log"))
    with open(directory / "results.jsonl", "a") as out:
        out.write(json.dumps(row) + "\n")


# ------------------------------------------------------------------ running one job

def spawn_runner(job: dict, directory: Path) -> int:
    log = open(directory / "jobs" / f"{job['id']}.log", "ab")
    proc = subprocess.Popen([sys.executable, str(Path(job["tools"]) / "tools" / "boxq.py"), "_run", job["id"]],
                            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                            start_new_session=True, env=dict(os.environ, FN_BOXQ_DIR=str(directory)))
    return proc.pid


def git(lane: str, *words) -> str:
    return subprocess.run(["git", "-C", lane, *words], capture_output=True, text=True).stdout.strip()


def command(job: dict) -> tuple[list[str], str]:
    """(argv, cwd) for the job's first (or only) step."""
    tools, lane, box = job["tools"], job["lane_root"], job["box"]
    extra = list(job.get("extra") or [])
    if job["kind"] == "certify-lane":
        jobs_word = [] if "--jobs" in extra else ["--jobs", str(HBOX_JOBS if box == "hbox" else job["slots"])]
        return [sys.executable, f"{tools}/tools/farm.py", "submit", box, "--root", lane, *jobs_word, *extra], lane
    if job["kind"] in ("native", "overlay"):
        argv = ["sh", f"{tools}/tools/hbox_native.sh", "--box", box, "--name", job["lane"],
                "--label", job["label"], "--wait", "--jobs", str(job["slots"]),
                "--image-set", job["image_set"], "--images", job.get("images") or "developer"]
        if job["kind"] == "overlay":
            argv.append("--overlay")
        if job.get("mem"):
            argv += ["--mem", job["mem"]]
        return argv + extra + [job["rev"], *job["tests"]], tools
    if job["kind"] == "image-build":
        return ["sh", f"{tools}/tools/hbox_native.sh", "--box", box, "--name", job["lane"],
                "--label", job["label"], "--wait", "--build-only", "--publish",
                "--certify-jobs", str(job["slots"]),
                "--images", job.get("images") or "developer,production,dtn,dtn-developer",
                *extra, job["rev"]], tools
    if job["kind"] == "check-lane":
        return ["sh", f"{tools}/tools/remote_check.sh", box, *(extra or ["--target", "check-lane"])], lane
    return ["sh", "-c", " ".join(extra)], lane


RUN_ID = re.compile(r"^(run-\d{8}T\d{6}Z-[0-9a-f]+)$", re.MULTILINE)
BUDGET = re.compile(r"FN_TEST_BUDGET_RESULT (\{.*\})")


def run_job(job_id: str, directory: Path) -> int:
    with locked_state(directory) as state:
        job = state["jobs"][job_id]
        job["sha_start"] = git(job["lane_root"], "rev-parse", "HEAD")
        job["dirty"] = bool(git(job["lane_root"], "status", "--porcelain", "--untracked-files=no"))
    print(f"boxq {job_id}: {job['kind']} on {job['box']} ({job['slots']} slots) for {job['lane']}", flush=True)
    argv, cwd = command(job)
    env = dict(os.environ, BOXQ_BOX=job["box"], BOXQ_JOB=job_id, FN_BOX_AS=job["lane"])
    print("boxq: " + " ".join(shlex.quote(w) for w in argv), flush=True)
    done = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    sys.stdout.write(done.stdout)
    code, run_id = done.returncode, None
    if job["kind"] == "certify-lane":
        found = RUN_ID.findall(done.stdout)
        run_id = found[-1] if found else None
        if run_id and code == 0:
            update(directory, job_id, run_id=run_id)
            waited = subprocess.run([sys.executable, f"{job['tools']}/tools/farm.py", "wait", job["box"], run_id,
                                     "--root", job["lane_root"]], cwd=job["lane_root"], env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            sys.stdout.write(waited.stdout)
            code = waited.returncode
    elif job["kind"] in ("native", "overlay", "image-build"):
        run_id = f"{job['box']}:/tank/fn/scratch/{job['lane']}/native-{job['label']}"
    elif job["kind"] == "check-lane":
        run_id = f"{job['box']}:{job['lane']}-check (log build/remote-check/ in {job['lane_root']})"
    reds = sorted(reds_of(done.stdout))
    if job["kind"] in ("native", "overlay"):
        learn(directory, job, done.stdout)
    # What a red is, per tool: hbox_native 1 (a module failed) or 4 (all
    # skipped); farm.py wait 1 (a book failed); make 2.  Anything else (a
    # refusal before running, an unreachable box) is ERROR, never RED.
    red_codes = {"native": (1, 4), "overlay": (1, 4), "certify-lane": (1,), "check-lane": (1, 2)}.get(job["kind"], (1,))
    verdict = "OK" if code == 0 else ("RED" if code in red_codes else "ERROR")
    with locked_state(directory) as state:
        j = state["jobs"][job_id]
        j.update(state="done", exit=code, verdict=verdict, run_id=run_id, reds=reds, finished=now())
        record(j, directory)
        finish_parents(state["jobs"], directory)
    print(f"boxq {job_id}: {verdict} (exit {code}) run {run_id}", flush=True)
    with contextlib.suppress(Exception):
        pump(directory)
    return code


def update(directory: Path, job_id: str, **fields) -> None:
    with locked_state(directory) as state:
        state["jobs"][job_id].update(fields)


def reds_of(output: str) -> set[str]:
    """Failing test ids from hbox_native's run log lines (module FAILED) and farm's failed books."""
    out = set()
    for line in output.splitlines():
        m = re.search(r"test-(tests\.\S+) exit [1-9]\d* \S+: \S+: FAILED", line)
        if m:
            out.add(m.group(1))
        m = re.search(r"^\s*FAILED?:? (books/\S+)", line)
        if m:
            out.add(m.group(1))
    return out


def learn(directory: Path, job: dict, output: str) -> None:
    """Per-test seconds from the box's module logs (FN_TEST_BUDGET_RESULT) into timings.json."""
    run = f"/tank/fn/scratch/{job['lane']}/native-{job['label']}/logs"
    try:
        got = subprocess.run(["ssh", "-n", "-o", "BatchMode=yes", job["box"],
                              f"grep -h FN_TEST_BUDGET_RESULT {run}/test-*.log 2>/dev/null"],
                             capture_output=True, text=True, timeout=60).stdout
    except subprocess.TimeoutExpired:
        return
    merge_timings(directory, got)


def merge_timings(directory: Path, text: str) -> int:
    rows = 0
    with locked_state(directory):
        timings = load_timings(directory)
        for m in BUDGET.finditer(text):
            with contextlib.suppress(ValueError, KeyError):
                row = json.loads(m.group(1))
                total = 0.0
                for test, seconds in row.get("timings", []):
                    timings["tests"][test] = round(float(seconds), 2)
                    total += float(seconds)
                timings["modules"][row["module"]] = round(total, 2)
                rows += 1
        (directory / "timings.json").write_text(json.dumps(timings, indent=1, sort_keys=True))
    return rows


# ------------------------------------------------------------------ commands

def ensure_daemon(directory: Path) -> None:
    lock = directory / "daemon.lock"
    with open(lock, "a+") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return
    subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "daemon"], stdin=subprocess.DEVNULL,
                     stdout=open(directory / "daemon.log", "ab"), stderr=subprocess.STDOUT,
                     start_new_session=True, env=dict(os.environ, FN_BOXQ_DIR=str(directory)))


def daemon(directory: Path, interval: float = 20.0) -> int:
    with open(directory / "daemon.lock", "a+") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("boxq daemon: one is already running", file=sys.stderr)
            return 0
        (directory / "daemon.pid").write_text(f"{os.getpid()}\n")
        idle = 0
        while True:
            with contextlib.suppress(Exception):
                started = pump(directory)
                if started:
                    print(f"{iso(now())} started {' '.join(started)}", flush=True)
            st = read_state(directory)
            live = [j for j in st["jobs"].values() if j["state"] in ("queued", "running", "split")]
            idle = 0 if live else idle + 1
            if idle * interval > 1800:   # nothing for 30 min: exit; the next submit restarts it
                return 0
            time.sleep(interval)


def submit(args, directory: Path) -> str:
    lane_root = git(os.getcwd(), "rev-parse", "--show-toplevel") or os.getcwd()
    if args.root:
        lane_root = str(Path(args.root).resolve())
    lane = args.lane or os.environ.get("FN_LANE") or Path(lane_root).name
    job = {"kind": args.kind, "priority": args.priority, "box": args.box, "lane": lane,
           "lane_root": lane_root, "tools": str(TOOLS_ROOT), "extra": args.extra,
           "submitted": now(), "state": "queued", "parent": None,
           "sha_submit": git(lane_root, "rev-parse", "HEAD"), "note": args.note}
    _, _, default_slots = SHAPE[args.kind]
    job["slots_wanted"] = args.slots or default_slots
    job["slots"] = args.slots or default_slots
    job["slots_fixed"] = bool(args.slots)
    if args.box == "hbox" and args.kind in ("native", "overlay") and not args.image_set:
        raise SystemExit("boxq: a native job needs --image-set")
    if args.kind in ("native", "overlay"):
        if not args.image_set or not args.tests:
            raise SystemExit("boxq: native/overlay need --image-set SHA and at least one test module")
        rev = args.rev or "HEAD"
        full = git(lane_root, "rev-parse", "--verify", f"{rev}^{{commit}}")
        if not full:
            raise SystemExit(f"boxq: no commit {rev} in {lane_root} (a queued run needs a commit, not `.`)")
        image_set = git(lane_root, "rev-parse", "--verify", f"{args.image_set}^{{commit}}") or args.image_set
        job.update(rev=full, image_set=image_set, tests=args.tests, images=args.images, mem=args.mem,
                   max_jobs=args.slots)
    elif args.kind == "image-build":
        full = git(lane_root, "rev-parse", "--verify", f"{args.rev or 'HEAD'}^{{commit}}")
        if not full:
            raise SystemExit(f"boxq: no commit {args.rev or 'HEAD'} in {lane_root}")
        job.update(rev=full, images=args.images)
    elif args.tests:
        job["extra"] = list(args.tests) + list(args.extra)
    if args.kind in ("image-set", "cmd") and not job["extra"]:
        raise SystemExit(f"boxq: --kind {args.kind} runs the command after --")
    if args.box and args.box not in known_boxes():
        raise SystemExit(f"boxq: unknown box {args.box} (known: {', '.join(known_boxes())})")
    with locked_state(directory) as state:
        job["id"] = new_id(state)
        job["label"] = job["id"]
        state["jobs"][job["id"]] = job
    return job["id"]


def wait(job_id: str, directory: Path, poll: float = 5.0, out=sys.stdout) -> int:
    said = set()
    while True:
        st = read_state(directory)
        job = st["jobs"].get(job_id)
        if job is None:
            print(f"boxq: no job {job_id}", file=sys.stderr)
            return 3
        family = [job] + [st["jobs"][k] for k in job.get("shards") or [] if k in st["jobs"]]
        for j in family:
            key = (j["id"], j["state"], j.get("box"), str(j.get("run_id")))
            if key not in said and j["state"] in ("running", "done"):
                said.add(key)
                if j["state"] == "running":
                    print(f"boxq {j['id']}: running on {j['box']} ({j['slots']} slots)"
                          + (f", {len(j.get('tests') or [])} tests" if j.get("tests") else ""), file=out, flush=True)
                elif j is not job:
                    print(f"boxq {j['id']}: {j['verdict']} on {j['box']} run {j.get('run_id')}", file=out, flush=True)
        if job["state"] == "done":
            print(f"boxq {job_id}: {job['verdict']} exit {job.get('exit')} run {job.get('run_id')}"
                  + (f" reds {' '.join(job['reds'])}" if job.get("reds") else "")
                  + f" (log {directory / 'jobs' / (job_id + '.log')})", file=out, flush=True)
            return {"OK": 0, "RED": 1}.get(job["verdict"], 3)
        if job["state"] == "cancelled":
            print(f"boxq {job_id}: cancelled", file=out)
            return 3
        time.sleep(poll)


def status(directory: Path, out=sys.stdout) -> None:
    with locked_state(directory) as state:
        jobs = state["jobs"]
        reap(jobs, directory)
        boxes = known_boxes()
        probed = probes(state, {n: b for n, b in boxes.items() if b["rented"] or n == "hbox"}, ttl=min(20, PROBE_TTL))
        print(f"{'box':9} {'cores':>5} {'load':>6} {'boxq':>5} {'free':>5} {'mem':>5}  running", file=out)
        for name in probed:
            p = probed[name]
            if not p.get("ok"):
                print(f"{name:9} unreachable", file=out)
                continue
            cap = capacity(name, boxes[name], p, jobs)
            run = ", ".join(f"{j} {jobs[j]['kind']}/{jobs[j]['lane']}" for j in cap["running"])
            print(f"{name:9} {cap['cores']:>5} {cap['load']:>6.1f} {cap['reserved']:>5.0f} {cap['free']:>5.1f} "
                  f"{cap['mem']:>4}G  {run or '-'}", file=out)
        queued = sorted((j for j in jobs.values() if j["state"] == "queued"),
                        key=lambda j: (PRIORITIES[j["priority"]], j["submitted"]))
        print(f"queue: {len(queued)} waiting", file=out)
        for j in queued:
            print(f"  {j['id']} {j['priority']:10} {j['kind']:12} {j['lane']:22} {j.get('why') or ''}", file=out)
        split = [j for j in jobs.values() if j["state"] == "split"]
        for j in split:
            kids = [jobs[k] for k in j.get("shards") or [] if k in jobs]
            print(f"  {j['id']} sharded: " + ", ".join(f"{k['id']}@{k['box']}:{k['state']}" for k in kids), file=out)


def results(directory: Path, red: bool, since: str | None, n: int, out=sys.stdout) -> None:
    try:
        rows = [json.loads(l) for l in (directory / "results.jsonl").read_text().splitlines() if l.strip()]
    except FileNotFoundError:
        rows = []
    if red:
        rows = [r for r in rows if r.get("verdict") != "OK"]
    if since:
        rows = [r for r in rows if (r.get("finished") or "") >= since]
    for r in rows[-n:]:
        print(json.dumps(r), file=out)


def cancel(job_id: str, directory: Path) -> int:
    with locked_state(directory) as state:
        job = state["jobs"].get(job_id)
        if not job:
            print(f"boxq: no job {job_id}", file=sys.stderr)
            return 2
        family = [job] + [state["jobs"][k] for k in job.get("shards") or [] if k in state["jobs"]]
        for j in family:
            if j["state"] == "queued":
                j["state"] = "cancelled"
            elif j["state"] == "running" and j.get("pid"):
                with contextlib.suppress(ProcessLookupError, PermissionError):
                    os.killpg(j["pid"], signal.SIGTERM)
                j.update(state="done", verdict="CANCELLED", exit=3, finished=now())
                record(j, directory)
        if job["state"] == "split":
            job["state"] = "cancelled"
    print(f"boxq: cancelled {job_id}")
    return 0


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    extra: list[str] = []
    if "--" in argv:
        cut = argv.index("--")
        argv, extra = argv[:cut], argv[cut + 1:]
    p = argparse.ArgumentParser(prog="boxq", description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("submit")
    s.add_argument("--kind", required=True, choices=KINDS)
    s.add_argument("--priority", default="lane", choices=tuple(PRIORITIES))
    s.add_argument("--box")
    s.add_argument("--wait", action="store_true")
    s.add_argument("--slots", type=int, help="cores/jobs to use (default per kind; native: max jobs per shard)")
    s.add_argument("--image-set")
    s.add_argument("--rev")
    s.add_argument("--images")
    s.add_argument("--mem")
    s.add_argument("--root", help="the lane's worktree (default: the one you are in)")
    s.add_argument("--lane", help="the lane's name (default $FN_LANE, else the worktree's basename)")
    s.add_argument("--note")
    s.add_argument("tests", nargs="*")
    w = sub.add_parser("wait")
    w.add_argument("job")
    sub.add_parser("status")
    r = sub.add_parser("results")
    r.add_argument("--red", action="store_true")
    r.add_argument("--since")
    r.add_argument("--n", type=int, default=20)
    c = sub.add_parser("cancel")
    c.add_argument("job")
    sub.add_parser("pump")
    sub.add_parser("daemon")
    t = sub.add_parser("learn", help="merge FN_TEST_BUDGET_RESULT lines from files into timings.json")
    t.add_argument("files", nargs="+")
    run = sub.add_parser("_run")
    run.add_argument("job")
    args = p.parse_args(argv)
    args.extra = extra
    directory = state_dir()
    directory.mkdir(parents=True, exist_ok=True)
    if args.cmd == "submit":
        job_id = submit(args, directory)
        print(job_id, flush=True)
        pump(directory)
        ensure_daemon(directory)
        return wait(job_id, directory) if args.wait else 0
    if args.cmd == "wait":
        ensure_daemon(directory)
        return wait(args.job, directory)
    if args.cmd == "status":
        status(directory)
        return 0
    if args.cmd == "results":
        results(directory, args.red, args.since, args.n)
        return 0
    if args.cmd == "cancel":
        return cancel(args.job, directory)
    if args.cmd == "pump":
        print(" ".join(pump(directory)) or "boxq: nothing placed")
        return 0
    if args.cmd == "daemon":
        return daemon(directory)
    if args.cmd == "learn":
        n = merge_timings(directory, "\n".join(Path(f).read_text(errors="replace") for f in args.files))
        print(f"boxq: {n} module timing rows merged")
        return 0
    if args.cmd == "_run":
        return run_job(args.job, directory)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
