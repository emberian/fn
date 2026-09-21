#!/usr/bin/env python3
"""One commit, every gate this tree has, one verdict.

`verdict.py` does not certify anything itself and does not drive a socket
itself.  It ships one commit to a farm box, runs the box's own gate over it
(`make certify`, the Python suite, `tools/gate_publish.sh`), then runs each
harness that already exists -- the deploy gate, the two-node gate, the INN
lab, the scale gate -- against that same commit, and writes one evidence
record whose table is a fiber per row and whose last line is the single
sentence this tree is entitled to say.

    python3 tools/verdict.py HEAD --host persvati

Each harness keeps its own evidence file; this one cites them and adds
nothing to them.  A fiber that did not run is a row saying so, never an
absence: `--skip inn` is recorded in the table and in the claim.

Two gates must never overlap on one box -- a gate is a fresh directory
certified once, and a second `make certify` against the same cache while the
first is publishing gives the second a cache it cannot vouch for.  **There is
exactly one lock per box and it is the `flock` file the hand-written gate
scripts already take**: `$HOME/fn-gates/.gate.lock` on persvati,
`/tank/fn/gates/.lock` on hbox.  This tool used to keep a second scheme of its
own -- an atomic `mkdir` on `.verdict.lock` beside the same directories --
and two schemes that cannot see each other are not a lock: a verdict run and
a hand gate could certify on one box at the same time.  So the gate script
this tool writes opens the same file and holds `flock` on it for its whole
certification phase, exactly as the hand gates do, and before launching
anything this tool asks the box whether that lock is free and refuses rather
than queueing behind it.  `--wait-for-lock` queues instead.  The lock is a
CERTIFICATION lock: it is not a reservation of the box, and the deploy,
two-node, INN and scale fibers do not hold it.

`--reuse-gate [REV]` reads a gate directory that already exists -- one this
tool made, or one of the hand gates, which have the same shape (`certify.log`,
`pytests.log`, `publish.log`, `build/acl2/certify-*/manifest.json`) and no
`gate.done` -- and builds the per-fiber table from it.  It never ships and
never launches: a gate directory that is not there is a row saying so.

Nothing here establishes a proof.  A green certify row means ACL2 read the
books named in that run's manifest and produced the certificates whose
digests the manifest records; a green harness row means that harness's steps
exited as that harness expected them to.
"""

import argparse
import datetime as dt
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import evidence_manifests  # noqa: E402
from deploy_gate import (GATE_ROOT, evidence_path,       # noqa: E402
                         repo_root, resolve)
from farm import HOSTS as FARM_HOSTS                      # noqa: E402

DEFAULT_HOST = "persvati"
DEFAULT_INN_HOST = "hbox"
# One lock per box, and it is the file the hand-written gate scripts take.
# Two names, because the two scripts were written apart; both are what is
# really on the boxes, and matching them is the whole point.
GATE_LOCKS = {"hbox": "/tank/fn/gates/.lock"}
DEFAULT_GATE_LOCK = "$HOME/fn-gates/.gate.lock"
# The files a finished gate directory holds, whoever wrote it.
GATE_ARTEFACTS = ("certify.log", "pytests.log", "publish.log")

# Book-name prefix -> the deputy that owns the row, from
# `planning/deputies/CLUSTERS.md`.  Longest prefix wins, so `bp-primary` goes
# to bp and `store-config` to codecs.  A book matching nothing is `unassigned`
# and says so in the table: an unowned failing root is a finding, not a blank.
OWNERS: tuple[tuple[str, str], ...] = (
    ("acceptance", "core"), ("retention", "core"), ("node", "core"),
    ("replay", "core"), ("exchange", "core"), ("node-config", "core"),
    ("store-files", "store"), ("store-node", "store"), ("store-observed", "store"),
    ("store-sweep", "store"), ("checkpoint", "store"), ("index", "store"),
    ("journal", "store"), ("byte-store", "store"),
    ("cbor", "codecs"), ("records", "codecs"), ("frame", "codecs"),
    ("identity", "codecs"), ("store-config", "codecs"), ("bp-adu", "codecs"),
    ("bp-primary-cbor", "codecs"), ("container", "codecs"),
    ("wire", "nntp"), ("article", "nntp"), ("wildmat", "nntp"), ("nntp", "nntp"),
    ("transfer", "nntp"), ("injection", "nntp"), ("served", "nntp"),
    ("owner", "nntp"), ("ideal", "nntp"), ("peer", "nntp"),
    ("bp-", "bp"), ("relay", "bp"), ("clock", "bp"), ("scheduler", "bp"),
    ("anchor", "bp"),
    ("crypto-seam", "substrate"), ("principal", "substrate"),
    ("statement", "substrate"), ("lace", "substrate"), ("policy", "substrate"),
    ("membership-epochs", "substrate"), ("assumptions", "substrate"),
    ("stx", "substrate"), ("tcpcl", "substrate"), ("config", "core"),
)


def gate_root(host: str) -> str:
    """Where this box keeps its gate directories.

    hbox puts them on its pool (`/tank/fn/gates`), which is also what
    `tools/inn_lab.py` uses; everywhere else it is `$HOME/fn-gates`. The lock
    lives beside the gates it protects, so an operator finds it where the
    thing it guards already is.
    """
    return "/tank/fn/gates" if host == "hbox" else GATE_ROOT


def gate_lock(host: str) -> str:
    """The one lock file this box's gates take, hand-written or generated."""
    return GATE_LOCKS.get(host, DEFAULT_GATE_LOCK)


def owner_of(book: str) -> str:
    """The deputy row a Makefile root belongs to."""
    name = book.split("/")[-1]
    for suffix in ("-tests", "-teeth-tests", "-guards-tests"):
        if name.endswith(suffix):
            name = name[: -len(suffix)]
            break
    best = ""
    found = "unassigned"
    for prefix, deputy in OWNERS:
        if name.startswith(prefix) and len(prefix) > len(best):
            best, found = prefix, deputy
    return found


class Fiber:
    """One harness run: what it was asked to do and what came back."""

    def __init__(self, name: str, host: str, tool: str, note: str = ""):
        self.name = name
        self.host = host
        self.tool = tool
        self.note = note
        self.rc: int | None = None
        self.seconds = 0.0
        self.steps = 0
        self.failed = 0
        self.skipped = 0
        self.violated = 0
        self.inconclusive = 0
        self.evidence = ""
        self.summary = ""
        self.failures: list[str] = []
        self.command = ""

    @property
    def state(self) -> str:
        """Four states, because three outcomes stay distinct all the way out.

        A harness exits 3 when nothing it stated was violated but something
        it meant to decide it could not (tools/deploy_gate.py's `Finding`).
        Collapsing that into `fail` loses the distinction the gates were just
        taught to keep, and collapsing it into `pass` is what F1 was."""
        if self.rc is None:
            return "not run"
        if self.rc == 0:
            return "pass"
        if self.rc == 3:
            return "inconclusive"
        return "fail"


def run(command: list[str], timeout: int, cwd: Path | None = None) -> tuple[int, str]:
    try:
        done = subprocess.run(command, cwd=str(cwd) if cwd else None,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=timeout)
        return done.returncode, done.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return 124, "timed out after {}s".format(timeout)


def ssh(host: str, script: str, timeout: int = 300) -> tuple[int, str]:
    try:
        done = subprocess.run(["ssh", "-o", "BatchMode=yes", host, "bash", "-s"],
                              input=script.encode(), stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=timeout)
        return done.returncode, done.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return 124, "timed out after {}s".format(timeout)


# --------------------------------------------------------------------------
# the lock


class GateLock:
    """The one lock per box, checked before anything is launched on it.

    The hold itself is a `flock` inside the gate script, which is what the
    hand-written gates on both boxes do (`exec 9>LOCK; flock 9`) and what
    keeps the exclusion structural: the lock lives as long as the process
    that certifies and dies with it, so it cannot be left behind and cannot
    go stale.  There is nothing here to force-unlock.

    What this class does is ask, before launching, whether that lock is free,
    so an operator gets a refusal naming the file instead of a gate that
    silently queues for an hour.  `--wait-for-lock` says to queue: the gate
    script blocks on `flock 9` and starts when the other gate finishes.
    """

    def __init__(self, hosts: list[str], wait: bool):
        self.hosts = sorted(set(hosts))
        self.wait = wait

    def path(self, host: str) -> str:
        return gate_lock(host)

    def check(self) -> None:
        for host in self.hosts:
            script = """
mkdir -p {root}
lock={lock}
: >> "$lock" 2>/dev/null
if flock -n "$lock" true 2>/dev/null; then
  echo FREE
else
  echo "HELD $(fuser -v "$lock" 2>&1 | tr '\\n' ' ')"
fi
""".format(root=gate_root(host), lock=self.path(host))
            code, output = ssh(host, script)
            last = output.strip().splitlines()[-1] if output.strip() else "?"
            if code == 0 and last.startswith("FREE"):
                continue
            if self.wait and last.startswith("HELD"):
                print("verdict: {} is certifying under {}; this gate will "
                      "queue behind it ({})".format(host, self.path(host), last),
                      flush=True)
                continue
            raise SystemExit(
                "verdict: {} already has a gate certifying: {}\n"
                "  the lock is {} and it is held by that gate's own process,\n"
                "  so it cannot be stale and there is nothing to remove.\n"
                "  wait for it, or re-run with --wait-for-lock to queue."
                .format(host, last, self.path(host)))


# --------------------------------------------------------------------------
# fiber 1: the box's own gate


GATE_SH = """#!/bin/bash
cd {gate}
# One gate at a time per box: the same flock file the hand-written gate
# scripts take, held for the whole certification phase and released when this
# script exits.  A second scheme beside this one is not a lock.
exec 9>{lock}
flock 9
export FN_ACL2={acl2} FN_ACL2_TIMEOUT_SECONDS={timeout} FN_CERTIFY_JOBS={jobs} \\
       FN_CERT_CACHE={cache}
make certify > certify.log 2>&1; echo exit=$? >> certify.log
( time python3 -m unittest discover -s tests -p 'test_*.py' ) > pytests.log 2>&1
echo exit=$? >> pytests.log
sh tools/gate_publish.sh > publish.log 2>&1; echo exit=$? >> publish.log
date -u +%Y-%m-%dT%H:%M:%SZ > gate.done
"""


def ship(repo: Path, commit: str, host: str, gate: str, timeout: int) -> tuple[int, str]:
    archive = subprocess.run(["git", "-C", str(repo), "archive", commit],
                             stdout=subprocess.PIPE, check=True).stdout
    done = subprocess.run(
        ["ssh", "-o", "BatchMode=yes", host,
         "rm -rf {g} && mkdir -p {g} && tar -x -C {g}".format(g=gate)],
        input=archive, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=timeout)
    return done.returncode, done.stdout.decode("utf-8", "replace")


def exit_line(text: str) -> int | None:
    found = re.findall(r"^exit=(\d+)$", text, re.M)
    return int(found[-1]) if found else None


def suite_counts(log: str) -> dict:
    """`Ran N tests`, the verdict word, and the failure/error tallies."""
    ran = re.search(r"^Ran (\d+) tests? in ([0-9.]+)s", log, re.M)
    out = {"ran": int(ran.group(1)) if ran else 0,
           "seconds": float(ran.group(2)) if ran else 0.0,
           "failures": 0, "errors": 0, "skipped": 0, "verdict": "unknown"}
    if re.search(r"^OK(\s|$)", log, re.M):
        out["verdict"] = "OK"
    tail = re.search(r"^(OK|FAILED)\s*\((.*)\)\s*$", log, re.M)
    if tail:
        out["verdict"] = tail.group(1)
        for key, value in re.findall(r"(\w+)=(\d+)", tail.group(2)):
            if key in out:
                out[key] = int(value)
    elif out["verdict"] == "unknown" and re.search(r"^FAILED", log, re.M):
        out["verdict"] = "FAILED"
    return out


SURVEY = """
gate={gate}
test -d "$gate" || {{ echo ABSENT; exit 0; }}
echo PRESENT
printf 'DONE %s\\n' "$(tail -1 "$gate/gate.done" 2>/dev/null)"
for name in {artefacts}; do
  if [ -f "$gate/$name" ]; then
    printf 'HAS %s %s\\n' "$name" "$(tail -1 "$gate/$name")"
  else
    printf 'ABSENT %s\\n' "$name"
  fi
done
printf 'MANIFESTS %s\\n' "$(ls -d "$gate"/build/acl2/certify-*/manifest.json \
  2>/dev/null | wc -l | tr -d ' ')"
"""


def survey(host: str, gate: str) -> dict:
    """What a gate directory holds, without assuming who wrote it.

    A hand-written gate never writes `gate.done`, so asking for that file and
    nothing else made every hand gate unreadable and sent `--reuse-gate`
    down the path that ships and certifies.  This reads the shape both kinds
    share and reports each artefact as present or absent, so an incomplete
    gate is a row that says which part is missing rather than a refusal or a
    silent pass.
    """
    _, output = ssh(host, SURVEY.format(
        gate=gate, artefacts=" ".join(GATE_ARTEFACTS)))
    found: dict = {"present": False, "artefacts": {}, "manifests": 0,
                   "finished": ""}
    for line in output.splitlines():
        if line.strip() == "PRESENT":
            found["present"] = True
        elif line.startswith("DONE ") and line[5:].strip():
            found["finished"] = line[5:].strip()
        elif line.startswith("HAS "):
            parts = line.split(" ", 2)
            found["artefacts"][parts[1]] = parts[2] if len(parts) > 2 else ""
        elif line.startswith("ABSENT ") and line[7:].strip():
            found["artefacts"][line[7:].strip()] = None
        elif line.startswith("MANIFESTS "):
            try:
                found["manifests"] = int(line[10:].strip())
            except ValueError:
                pass
    return found


def certify_gate(fiber: Fiber, repo: Path, commit: str, rev: str, tree: str,
                 jobs: int, cache: str, acl2: str, wait_seconds: int,
                 reuse: str | None) -> dict:
    """Ship the commit, run the box's gate detached, wait for `gate.done`.

    Detached on purpose: a `make certify` of this tree is measured in tens of
    minutes and an ssh that drops would otherwise take the gate with it.  The
    poll reads one file; it never greps a log for progress and never touches
    another run's processes.

    With `reuse` set this ships nothing and launches nothing: it reads the
    named gate directory and harvests it.  `reuse` is the empty string for
    this commit's own gate, or a revision naming another one -- including a
    hand gate, which has the same shape and no `gate.done`.
    """
    gate = "{}/{}-{}".format(gate_root(fiber.host), tree, reuse or rev)
    started = time.monotonic()
    facts: dict = {"gate": gate, "reused": False}
    if reuse is not None:
        found = survey(fiber.host, gate)
        facts["reused"] = True
        facts["artefacts"] = found["artefacts"]
        if found["finished"]:
            facts["finished"] = found["finished"]
        fiber.seconds = time.monotonic() - started
        if not found["present"]:
            fiber.rc = None
            fiber.summary = ("no gate directory {} on {}; nothing was reused "
                             "and nothing was started".format(gate, fiber.host))
            return facts
        if not found["manifests"]:
            fiber.rc = 1
            fiber.summary = ("gate {} holds no certification manifest, so it "
                             "certified nothing this can read".format(gate))
            return facts
        missing = sorted(name for name, tail in found["artefacts"].items()
                         if tail is None)
        facts["missing_artefacts"] = missing
        harvested = facts | harvest(fiber, gate, repo)
        if missing:
            fiber.summary += "; absent from this gate: " + ", ".join(missing)
        return harvested
    code, output = ssh(fiber.host, "test -f {}/gate.done && cat {}/gate.done".format(
        gate, gate))
    if code == 0 and output.strip():
        facts["reused"] = True
        facts["finished"] = output.strip().splitlines()[-1]
    else:
        code, output = ship(repo, commit, fiber.host, gate, timeout=1800)
        if code != 0:
            fiber.rc, fiber.summary = code, "ship failed: " + output[:300]
            fiber.seconds = time.monotonic() - started
            return facts
        script = GATE_SH.format(gate=gate, acl2=acl2, timeout=5400, jobs=jobs,
                                cache=cache, lock=gate_lock(fiber.host))
        launch = ("cat > {g}/gate.sh <<'VERDICT_GATE_SH'\n{s}VERDICT_GATE_SH\n"
                  "chmod +x {g}/gate.sh\n"
                  "cd {g} && setsid nohup ./gate.sh > gate.out 2>&1 < /dev/null &\n"
                  "echo LAUNCHED $!\n").format(g=gate, s=script)
        code, output = ssh(fiber.host, launch, timeout=900)
        if code != 0:
            # The launch is fire-and-forget, so whether its ssh returned is
            # not evidence about the gate. Measured on persvati 2026-09-20:
            # the ssh did not close inside 300 s while `gate.sh` was already
            # certifying, and the run reported `launch failed` over a gate
            # that went on to finish. Ask the box instead.
            alive = ssh(fiber.host, "ls -d {}/build/acl2/certify-* 2>/dev/null "
                                    "| head -1\n".format(gate))[1].strip()
            if not alive:
                fiber.rc, fiber.summary = code, "launch failed: " + output[:300]
                fiber.seconds = time.monotonic() - started
                return facts
            facts["launch"] = ("the launch ssh returned {} but {} is certifying, "
                               "so the gate was followed rather than failed"
                               .format(code, alive))
        deadline = time.monotonic() + wait_seconds
        while time.monotonic() < deadline:
            time.sleep(60)
            code, output = ssh(fiber.host, "cat {}/gate.done 2>/dev/null".format(gate))
            if code == 0 and output.strip():
                facts["finished"] = output.strip().splitlines()[-1]
                break
        else:
            fiber.rc = 124
            fiber.summary = ("the gate did not finish inside {}s; it is still "
                             "running at {}".format(wait_seconds, gate))
            fiber.seconds = time.monotonic() - started
            return facts
    fiber.seconds = time.monotonic() - started
    return facts | harvest(fiber, gate, repo)


HARVEST = r"""
python3 - "$1" <<'VERDICT_HARVEST'
import glob, json, os, re, sys
gate = sys.argv[1]
out = {}
runs = sorted(glob.glob(os.path.join(gate, "build/acl2/certify-*/manifest.json")))
if runs:
    m = json.load(open(runs[-1]))
    out["manifest"] = os.path.relpath(runs[-1], gate)
    # The gate directory is the most perishable evidence this project keeps:
    # a gate reaper deletes stale gates, and the verdict record cites
    # this path.  Carry the manifest itself home, not only a path to it.
    out["manifest_json"] = m
    out["manifest_dir"] = os.path.dirname(runs[-1])
    out["status"] = m.get("status")
    out["acl2_version"] = m.get("acl2_version")
    out["platform"] = m.get("platform")
    out["wall"] = m.get("certify_wall_seconds")
    out["jobs"] = m.get("jobs_effective")
    codes = m.get("acl2_exit_codes") or {}
    # The per-book verdict, NOT the exit code.  The certify driver ends in
    # `(quit)`, which ACL2 reaches whether or not the inner `ld` returned on
    # a failed `certify-book`, so a book that failed in 0.2 s still exits 0.
    # Measured on persvati 2026-09-20 against gate dev-909e055: exit codes
    # name 1 bad root, `book_results` names 25.  An older manifest carries no
    # `book_results`, and then the exit codes are all there is.
    results = m.get("book_results") or {}
    out["roots"] = len(results or codes)
    out["verdict_source"] = "book_results" if results else "acl2_exit_codes"
    out["bad"] = (sorted(k for k, v in results.items() if v != "passed")
                  if results else sorted(k for k, v in codes.items() if v != 0))
    out["failure"] = m.get("failure")
    out["failure_markers"] = m.get("failure_markers")
    out["certificates"] = len(m.get("certificate_digests_sha256") or {})
for name in ("certify", "pytests", "publish"):
    path = os.path.join(gate, name + ".log")
    out[name] = open(path, errors="replace").read()[-4000:] if os.path.exists(path) else ""
print(json.dumps(out))
VERDICT_HARVEST
"""


def harvest(fiber: Fiber, gate: str, repo: Path) -> dict:
    code, output = ssh(fiber.host, "set -- {}\n".format(gate) + HARVEST, timeout=300)
    try:
        data = json.loads(output.strip().splitlines()[-1])
    except (ValueError, IndexError):
        fiber.rc, fiber.summary = 2, "could not read the gate: " + output[:300]
        return {}
    # File the gate's manifest where a reader of the repository can see it.
    # `manifest_json` is not returned to the caller: the evidence table takes
    # the fields it renders from the keys below.
    body = data.pop("manifest_json", None)
    where = data.pop("manifest_dir", "")
    if isinstance(body, dict):
        run_id = evidence_manifests.run_id_of(Path(where) / "manifest.json")
        if run_id:
            evidence_manifests.write_manifest(
                run_id, json.dumps(body), "{}:{}".format(fiber.host, where), repo)
    certify_rc = exit_line(data.get("certify", ""))
    pytest_rc = exit_line(data.get("pytests", ""))
    publish_rc = exit_line(data.get("publish", ""))
    suite = suite_counts(data.get("pytests", ""))
    bad = data.get("bad") or []
    fiber.steps = data.get("roots", 0)
    fiber.failed = len(bad)
    fiber.failures = ["{} ({})".format(b, owner_of(b)) for b in bad]
    # `certify_books.py` writes "passed" or "failed"; nothing has ever
    # written "certified", so this row read `fail` for a perfect gate.
    fiber.rc = 0 if (not bad and data.get("status") == "passed"
                     and suite["verdict"] == "OK") else 1
    fiber.summary = ("roots {}/{} certified, suite {} of {} ({}), "
                     "certify rc={} suite rc={} publish rc={}".format(
                         fiber.steps - fiber.failed, fiber.steps,
                         suite["verdict"], suite["ran"],
                         "f={} e={}".format(suite["failures"], suite["errors"]),
                         certify_rc, pytest_rc, publish_rc))
    return {"certify_rc": certify_rc, "pytest_rc": pytest_rc,
            "publish_rc": publish_rc, "suite": suite,
            "manifest": data.get("manifest"), "status": data.get("status"),
            "verdict_source": data.get("verdict_source"),
            "acl2_version": data.get("acl2_version"), "platform": data.get("platform"),
            "certify_wall": data.get("wall"), "jobs": data.get("jobs"),
            "roots": data.get("roots"), "bad": bad,
            "certificates": data.get("certificates"),
            "manifest_failure": data.get("failure"),
            "publish_tail": (data.get("publish") or "").strip().splitlines()[-3:],
            "pytest_tail": [line for line in (data.get("pytests") or "").splitlines()
                            if line.startswith(("FAIL:", "ERROR:"))][:40]}


# --------------------------------------------------------------------------
# fibers 2..5: the harnesses, each run as its own process


SUMMARY = re.compile(r"^steps=(\d+) failed=(\d+) not-exercised=(\d+)"
                     r"(?: violated=(\d+) inconclusive=(\d+))?", re.M)
EVIDENCE = re.compile(r"^evidence: (.+)$", re.M)


def harness(fiber: Fiber, command: list[str], repo: Path, timeout: int) -> None:
    fiber.command = " ".join(command)
    started = time.monotonic()
    fiber.rc, output = run(command, timeout=timeout, cwd=repo)
    fiber.seconds = time.monotonic() - started
    found = SUMMARY.search(output)
    if found:
        fiber.steps = int(found.group(1))
        fiber.failed = int(found.group(2))
        fiber.skipped = int(found.group(3))
        fiber.violated = int(found.group(4) or 0)
        fiber.inconclusive = int(found.group(5) or 0)
    where = EVIDENCE.search(output)
    if where:
        path = Path(where.group(1).strip())
        try:
            fiber.evidence = str(path.relative_to(repo))
        except ValueError:
            fiber.evidence = str(path)
    fiber.failures = [line.strip() for line in output.splitlines()
                      if line.strip().startswith(("FAILED", "INCONCLUSIVE"))][:12]
    tail = [line for line in output.strip().splitlines() if line.strip()]
    fiber.summary = ("steps {} ok, {} failed, {} not exercised; assertions "
                     "{} violated, {} inconclusive".format(
                         fiber.steps - fiber.failed - fiber.skipped, fiber.failed,
                         fiber.skipped, fiber.violated, fiber.inconclusive)
                     if found else (tail[-1][:200] if tail else "no output"))


# --------------------------------------------------------------------------
# the claim


def claim(fibers: list[Fiber], gate_facts: dict) -> str:
    """One sentence, and it is allowed to be a small one.

    The rule this follows: a claim names only what a fiber that actually ran
    and passed supports, and every fiber that did not run or did not pass is
    named in the same sentence as a limit on it.
    """
    by_name = {f.name: f for f in fibers}
    passed = [f.name for f in fibers if f.state == "pass"]
    failed = [f.name for f in fibers if f.state == "fail"]
    unsure = [f.name for f in fibers if f.state == "inconclusive"]
    absent = [f.name for f in fibers if f.state == "not run"]
    gate = by_name.get("gate")
    roots = gate_facts.get("roots") or 0
    bad = len(gate_facts.get("bad") or [])
    suite = gate_facts.get("suite") or {}
    if gate is None or gate.state == "not run":
        return ("This tree claims nothing: the certify gate did not run, so no "
                "book on this commit has a certificate this run established.")
    acl2 = str(gate_facts.get("acl2_version") or "an unrecorded ACL2")
    acl2 = acl2.replace("ACL2 Version ", "ACL2 ").strip()
    head = ("On this commit {} of {} Makefile roots certified under {} and "
            "the Python suite ran {} tests ({})".format(
                roots - bad, roots, acl2,
                suite.get("ran", 0), suite.get("verdict", "unknown")))
    lived = [n for n in ("deploy", "twonode", "inn", "scale") if n in passed]
    if lived:
        head += ("; the {} harness{} drove a server built from it and returned "
                 "every step at its expected code".format(
                     ", ".join(lived), "es" if len(lived) > 1 else ""))
    limits = []
    if bad:
        limits.append("anything in the {} root{} that did not certify ({})".format(
            bad, "s" if bad != 1 else "",
            ", ".join(sorted({owner_of(b) for b in gate_facts.get("bad") or []}))))
    if suite.get("failures") or suite.get("errors"):
        limits.append("whatever the {} suite failures and {} errors cover".format(
            suite.get("failures"), suite.get("errors")))
    if failed:
        limits.append("the steps the {} harness{} reported failing".format(
            ", ".join(failed), "es" if len(failed) > 1 else ""))
    if unsure:
        limits.append("everything the {} harness{} could not decide: those runs "
                      "violated nothing and established nothing either".format(
                          ", ".join(unsure), "es" if len(unsure) > 1 else ""))
    if absent:
        limits.append("anything {} would have shown, which did not run".format(
            " or ".join(absent)))
    if limits:
        head += "; it claims nothing about " + ", nor ".join(limits)
    return head + "."


# --------------------------------------------------------------------------
# evidence


def evidence(path: Path, rev: str, commit: str, host: str, inn_host: str,
             started: str, elapsed: float, fibers: list[Fiber],
             gate_facts: dict, sentence: str) -> Path:
    suite = gate_facts.get("suite") or {}
    lines = [
        "# Verdict: {} across every gate".format(rev),
        "",
        "One commit through the box gate (`make certify`, the Python suite,",
        "`tools/gate_publish.sh`), then every harness this tree has, then this",
        "table.  Produced by `tools/verdict.py`; the per-harness evidence files",
        "cited below are the primary records and this one adds nothing to them.",
        "",
        "## What ran",
        "",
        "| fact | value |",
        "| --- | --- |",
        "| commit | `{}` ({}) |".format(rev, commit),
        "| gate host | `{}` |".format(host),
        "| INN host | `{}` |".format(inn_host),
        "| started | {} |".format(started),
        "| wall time | {:.0f} s ({:.1f} h) |".format(elapsed, elapsed / 3600.0),
        "| gate directory | `{}` |".format(gate_facts.get("gate", "-")),
        "| gate lock | `{}` (the one lock this box's gates take) |".format(
            gate_lock(host)),
        "| gate reused | {} |".format("yes" if gate_facts.get("reused") else "no"),
        "| gate artefacts absent | {} |".format(
            ", ".join("`{}`".format(name)
                      for name in gate_facts.get("missing_artefacts") or [])
            or "none"),
        "| certify manifest | `{}` |".format(gate_facts.get("manifest", "-")),
        "| manifest status | {} |".format(gate_facts.get("status", "-")),
        "| per-root verdict from | `{}` |".format(
            gate_facts.get("verdict_source", "-")),
        "| acl2 | {} |".format(gate_facts.get("acl2_version", "-")),
        "| platform | {} |".format(gate_facts.get("platform", "-")),
        "| certify wall | {} s at {} jobs |".format(
            gate_facts.get("certify_wall", "-"), gate_facts.get("jobs", "-")),
        "| certificates written | {} |".format(gate_facts.get("certificates", "-")),
        "| python suite | {} of {} tests, failures={} errors={} skipped={} |".format(
            suite.get("verdict", "-"), suite.get("ran", 0), suite.get("failures", 0),
            suite.get("errors", 0), suite.get("skipped", 0)),
        "",
        "## Fibers",
        "",
        "| fiber | host | tool | state | rc | steps | failed | not run | s | evidence |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for fiber in fibers:
        lines.append("| {} | `{}` | `{}` | {} | {} | {} | {} | {} | {:.0f} | {} |".format(
            fiber.name, fiber.host, fiber.tool, fiber.state,
            "-" if fiber.rc is None else fiber.rc, fiber.steps or "-",
            fiber.failed, fiber.skipped, fiber.seconds,
            "`{}`".format(fiber.evidence) if fiber.evidence else "-"))
    lines += ["", "Per fiber, in its own words:", ""]
    for fiber in fibers:
        lines.append("- **{}** ({}): {}".format(
            fiber.name, fiber.state, fiber.summary or fiber.note or "-"))
        for failure in fiber.failures:
            lines.append("  - {}".format(failure))
        if fiber.command:
            lines.append("  - `{}`".format(fiber.command))
    bad = gate_facts.get("bad") or []
    lines += ["", "## Certify roots by owner", "",
              "| owner | roots failing | which |", "| --- | --- | --- |"]
    if bad:
        by_owner: dict[str, list[str]] = {}
        for book in bad:
            by_owner.setdefault(owner_of(book), []).append(book)
        for deputy in sorted(by_owner):
            lines.append("| {} | {} | {} |".format(
                deputy, len(by_owner[deputy]),
                ", ".join("`{}`".format(b) for b in sorted(by_owner[deputy]))))
    else:
        lines.append("| - | 0 | every requested root exited 0 |")
    lines += ["",
              "Owners are the rows of `planning/deputies/CLUSTERS.md`, matched by",
              "book-name prefix in `tools/verdict.py`; a root matching no row is",
              "reported as `unassigned` rather than silently dropped.", ""]
    if gate_facts.get("manifest_failure"):
        lines += ["Manifest failure line: `{}`".format(
            gate_facts["manifest_failure"]), ""]
    if gate_facts.get("pytest_tail"):
        lines += ["## Python suite: the failing and erroring cases", "", "```"]
        lines += gate_facts["pytest_tail"]
        lines += ["```", ""]
    lines += [
        "## What this run does NOT establish",
        "",
        "- A certificate records that ACL2 read a book and admitted its events.",
        "  It is not a claim that the theorem in that book is the property its",
        "  name suggests, nor that the host calls the function it is about.",
        "- The harness rows are live runs against real sockets and real kill",
        "  signals. None of them is an RFC conformance audit, none qualifies",
        "  storage hardware, and a SIGKILL is not a power loss.",
        "- Fibers marked `not run` establish nothing at all; they are in the",
        "  table so their absence is visible in the claim.",
        "- This file is generated. Its numbers come from the gate manifest and",
        "  from each harness's own stdout summary, never from typing.",
        "- A reused gate is a reading of a directory that was already there.",
        "  This run did not certify it, did not ship the commit that made it,",
        "  and cannot say the tree beside those logs is the commit named above",
        "  beyond the gate directory's own name.",
        "",
        "## The claim",
        "",
        sentence,
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines))
    return path


# --------------------------------------------------------------------------


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("commit", help="the commit-ish to put through every gate")
    parser.add_argument("--host", default=DEFAULT_HOST,
                        help="the box that certifies, deploys, pairs and measures")
    parser.add_argument("--inn-host", default=DEFAULT_INN_HOST,
                        help="the box with a real INN; the INN lab runs there")
    parser.add_argument("--tree", default="dev", help="gate directory prefix")
    parser.add_argument("--repo", default=None,
                        help="the fn worktree to read the commit from and "
                             "write evidence into (default: the one this "
                             "command was invoked from)")
    parser.add_argument("--jobs", type=int, default=10)
    parser.add_argument("--cache", default="$HOME/fn-certcache")
    parser.add_argument("--acl2", default=None,
                        help="the host's ACL2 image; the default is tools/farm.py's")
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--skip", action="append", default=[],
                        choices=["gate", "deploy", "twonode", "inn", "scale"],
                        help="a fiber to leave out; it is still a row saying so")
    parser.add_argument("--only", action="append", default=[],
                        choices=["gate", "deploy", "twonode", "inn", "scale"])
    parser.add_argument("--reuse-gate", nargs="?", const="", default=None,
                        metavar="REV",
                        help="read a gate directory that already exists and "
                             "build the table from it, shipping nothing and "
                             "certifying nothing.  Bare: this commit's own "
                             "gate.  With a revision: `<tree>-<REV>` on the "
                             "host, which may be a hand-written gate")
    parser.add_argument("--gate-wait", type=int, default=4 * 3600,
                        help="seconds to wait for the box gate to finish")
    parser.add_argument("--harness-timeout", type=int, default=3 * 3600)
    parser.add_argument("--wait-for-lock", action="store_true",
                        help="queue behind a gate that is already certifying "
                             "on the box instead of refusing")
    parser.add_argument("--no-lock", action="store_true",
                        help="do not check the box's gate lock (for a dry "
                             "read only); the gate script still takes it")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve() if args.repo else repo_root()
    commit, rev = resolve(repo, args.commit)
    acl2 = args.acl2 or FARM_HOSTS.get(args.host, {}).get("acl2", "acl2")

    wanted = set(args.only) if args.only else {
        "gate", "deploy", "twonode", "inn", "scale"} - set(args.skip)
    plan = [
        Fiber("gate", args.host, "make certify + unittest + gate_publish.sh"),
        Fiber("deploy", args.host, "tools/deploy_gate.py"),
        Fiber("twonode", args.host, "tools/twonode_gate.py"),
        Fiber("inn", args.inn_host, "tools/inn_lab.py"),
        Fiber("scale", args.host, "tools/scale_gate.py"),
    ]
    for fiber in plan:
        if fiber.name not in wanted:
            fiber.note = "skipped by --skip/--only"

    # The lock is the box's CERTIFICATION lock, so only a run that is going
    # to certify checks it: a `--reuse-gate` read starts no ACL2 at all.
    certifying = "gate" in wanted and args.reuse_gate is None
    hosts = sorted({f.host for f in plan if f.name in wanted and f.name == "gate"})
    lock = GateLock(hosts, args.wait_for_lock)
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    gate_facts: dict = {}
    if certifying and not args.no_lock and hosts:
        lock.check()
        print("verdict: {} free to certify ({})".format(
            ", ".join(hosts), ", ".join(lock.path(h) for h in hosts)), flush=True)
    for fiber in plan:
        if fiber.name not in wanted:
            print("verdict: {} skipped".format(fiber.name), flush=True)
            continue
        print("verdict: {} starting on {}".format(fiber.name, fiber.host),
              flush=True)
        if fiber.name == "gate":
            gate_facts = certify_gate(fiber, repo, commit, rev, args.tree,
                                      args.jobs, args.cache, acl2,
                                      args.gate_wait, args.reuse_gate)
        else:
            command = [sys.executable, "tools/{}.py".format(
                {"deploy": "deploy_gate", "twonode": "twonode_gate",
                 "inn": "inn_lab", "scale": "scale_gate"}[fiber.name]),
                commit, "--host", fiber.host, "--tree", args.tree]
            if fiber.name == "scale":
                command += ["--reuse"]
            if fiber.name == "inn":
                command += ["--jobs", str(args.jobs)]
            harness(fiber, command, repo, args.harness_timeout)
        print("verdict: {} {} rc={} {:.0f}s -- {}".format(
            fiber.name, fiber.state, fiber.rc, fiber.seconds, fiber.summary),
            flush=True)

    elapsed = time.monotonic() - clock
    sentence = claim([f for f in plan], gate_facts)
    date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    target = evidence_path(args.evidence, repo,
                           "verdict-{}-{}.md".format(rev, date))
    evidence(target, rev, commit, args.host, args.inn_host, started, elapsed,
             plan, gate_facts, sentence)
    print("evidence: {}".format(target))
    print(sentence)
    bad = [f for f in plan if f.state == "fail"]
    unsure = [f for f in plan if f.state == "inconclusive"]
    absent = [f for f in plan if f.state == "not run"]
    print("fibers={} pass={} fail={} inconclusive={} not-run={}".format(
        len(plan), len(plan) - len(bad) - len(unsure) - len(absent),
        len(bad), len(unsure), len(absent)))
    # An inconclusive fiber establishes nothing, so it is not a pass; it
    # violated nothing either, so it is not a failure.  3 is D13's uncertain
    # and is the same code the harnesses themselves use.
    if bad:
        return 1
    return 3 if unsure else 0


if __name__ == "__main__":
    sys.exit(main())
