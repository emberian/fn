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
first is publishing gives the second a cache it cannot vouch for.  So every
host this run touches is locked (an atomic `mkdir` beside that box's
gate directories)
before the first fiber starts and unlocked in a `finally`.  A lock older than
`--stale-hours` is reported, not stolen; `--force-unlock` is the deliberate
act.

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
from deploy_gate import (GATE_ROOT, evidence_path,       # noqa: E402
                         repo_root, resolve)
from farm import HOSTS as FARM_HOSTS                      # noqa: E402

DEFAULT_HOST = "persvati"
DEFAULT_INN_HOST = "hbox"
LOCK_NAME = ".verdict.lock"

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
        self.evidence = ""
        self.summary = ""
        self.failures: list[str] = []
        self.command = ""

    @property
    def state(self) -> str:
        if self.rc is None:
            return "not run"
        if self.rc == 0:
            return "pass"
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


class Lock:
    """An atomic `mkdir` on each host, held for the whole run.

    `mkdir` is the atomic primitive every POSIX shell has; a lock directory
    holds one `owner` file naming who took it and when, so a stale lock is
    attributable.  Hosts are locked in sorted order: two verdict runs on the
    same pair of boxes then queue rather than deadlock.
    """

    def __init__(self, hosts: list[str], rev: str, stale_hours: float,
                 force: bool):
        self.hosts = sorted(set(hosts))
        self.rev = rev
        self.stale_hours = stale_hours
        self.force = force
        self.held: list[str] = []

    def path(self, host: str) -> str:
        return "{}/{}".format(gate_root(host), LOCK_NAME)

    def acquire(self) -> None:
        stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        for host in self.hosts:
            script = """
mkdir -p {root}
lock={lock}
if [ -n "{force}" ]; then rm -rf "$lock"; fi
if mkdir "$lock" 2>/dev/null; then
  printf 'verdict %s %s %s\\n' "{rev}" "{stamp}" "$(hostname)" > "$lock/owner"
  echo TAKEN
else
  age=$(( $(date +%s) - $(stat -c %Y "$lock" 2>/dev/null || echo 0) ))
  echo "HELD age=${{age}}s $(cat "$lock/owner" 2>/dev/null)"
fi
""".format(root=gate_root(host), lock=self.path(host), rev=self.rev, stamp=stamp,
           force="1" if self.force else "")
            code, output = ssh(host, script)
            last = output.strip().splitlines()[-1] if output.strip() else "?"
            if code != 0 or not last.startswith("TAKEN"):
                self.release()
                raise SystemExit(
                    "verdict: {} is locked by another gate: {}\n"
                    "  release it with: ssh {} rm -rf {}\n"
                    "  or re-run with --force-unlock if that lock is stale."
                    .format(host, last, host, self.path(host)))
            self.held.append(host)

    def release(self) -> None:
        for host in self.held:
            ssh(host, "rm -rf {}\n".format(self.path(host)), timeout=120)
        self.held = []


# --------------------------------------------------------------------------
# fiber 1: the box's own gate


GATE_SH = """#!/bin/bash
cd {gate}
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


def certify_gate(fiber: Fiber, repo: Path, commit: str, rev: str, tree: str,
                 jobs: int, cache: str, acl2: str, wait_seconds: int,
                 reuse: bool) -> dict:
    """Ship the commit, run the box's gate detached, wait for `gate.done`.

    Detached on purpose: a `make certify` of this tree is measured in tens of
    minutes and an ssh that drops would otherwise take the gate with it.  The
    poll reads one file; it never greps a log for progress and never touches
    another run's processes.
    """
    gate = "{}/{}-{}".format(gate_root(fiber.host), tree, rev)
    started = time.monotonic()
    facts: dict = {"gate": gate, "reused": False}
    code, output = ssh(fiber.host, "test -f {}/gate.done && cat {}/gate.done".format(
        gate, gate))
    if reuse and code == 0 and output.strip():
        facts["reused"] = True
        facts["finished"] = output.strip().splitlines()[-1]
    else:
        code, output = ship(repo, commit, fiber.host, gate, timeout=1800)
        if code != 0:
            fiber.rc, fiber.summary = code, "ship failed: " + output[:300]
            fiber.seconds = time.monotonic() - started
            return facts
        script = GATE_SH.format(gate=gate, acl2=acl2, timeout=5400, jobs=jobs,
                                cache=cache)
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
    return facts | harvest(fiber, gate)


HARVEST = r"""
python3 - "$1" <<'VERDICT_HARVEST'
import glob, json, os, re, sys
gate = sys.argv[1]
out = {}
runs = sorted(glob.glob(os.path.join(gate, "build/acl2/certify-*/manifest.json")))
if runs:
    m = json.load(open(runs[-1]))
    out["manifest"] = os.path.relpath(runs[-1], gate)
    out["status"] = m.get("status")
    out["acl2_version"] = m.get("acl2_version")
    out["platform"] = m.get("platform")
    out["wall"] = m.get("certify_wall_seconds")
    out["jobs"] = m.get("jobs_effective")
    codes = m.get("acl2_exit_codes") or {}
    out["roots"] = len(codes)
    out["bad"] = sorted(k for k, v in codes.items() if v != 0)
    out["failure"] = m.get("failure")
    out["failure_markers"] = m.get("failure_markers")
    out["certificates"] = len(m.get("certificate_digests_sha256") or {})
for name in ("certify", "pytests", "publish"):
    path = os.path.join(gate, name + ".log")
    out[name] = open(path, errors="replace").read()[-4000:] if os.path.exists(path) else ""
print(json.dumps(out))
VERDICT_HARVEST
"""


def harvest(fiber: Fiber, gate: str) -> dict:
    code, output = ssh(fiber.host, "set -- {}\n".format(gate) + HARVEST, timeout=300)
    try:
        data = json.loads(output.strip().splitlines()[-1])
    except (ValueError, IndexError):
        fiber.rc, fiber.summary = 2, "could not read the gate: " + output[:300]
        return {}
    certify_rc = exit_line(data.get("certify", ""))
    pytest_rc = exit_line(data.get("pytests", ""))
    publish_rc = exit_line(data.get("publish", ""))
    suite = suite_counts(data.get("pytests", ""))
    bad = data.get("bad") or []
    fiber.steps = data.get("roots", 0)
    fiber.failed = len(bad)
    fiber.failures = ["{} ({})".format(b, owner_of(b)) for b in bad]
    fiber.rc = 0 if (not bad and data.get("status") == "certified"
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


SUMMARY = re.compile(r"^steps=(\d+) failed=(\d+) not-exercised=(\d+)", re.M)
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
    where = EVIDENCE.search(output)
    if where:
        path = Path(where.group(1).strip())
        try:
            fiber.evidence = str(path.relative_to(repo))
        except ValueError:
            fiber.evidence = str(path)
    fiber.failures = [line.strip() for line in output.splitlines()
                      if line.strip().startswith("FAILED")][:12]
    tail = [line for line in output.strip().splitlines() if line.strip()]
    fiber.summary = ("steps {} ok, {} failed, {} not exercised".format(
        fiber.steps - fiber.failed - fiber.skipped, fiber.failed, fiber.skipped)
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
        "| gate reused | {} |".format("yes" if gate_facts.get("reused") else "no"),
        "| certify manifest | `{}` |".format(gate_facts.get("manifest", "-")),
        "| manifest status | {} |".format(gate_facts.get("status", "-")),
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
    parser.add_argument("--reuse-gate", action="store_true",
                        help="take a finished gate for this exact revision if the "
                             "host already has one")
    parser.add_argument("--gate-wait", type=int, default=4 * 3600,
                        help="seconds to wait for the box gate to finish")
    parser.add_argument("--harness-timeout", type=int, default=3 * 3600)
    parser.add_argument("--stale-hours", type=float, default=6.0)
    parser.add_argument("--force-unlock", action="store_true",
                        help="remove an existing lock before taking it")
    parser.add_argument("--no-lock", action="store_true",
                        help="do not lock the hosts (for a dry read only)")
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

    hosts = sorted({f.host for f in plan if f.name in wanted})
    lock = Lock(hosts, rev, args.stale_hours, args.force_unlock)
    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    gate_facts: dict = {}
    if not args.no_lock and hosts:
        lock.acquire()
        print("verdict: locked {}".format(", ".join(lock.held)), flush=True)
    try:
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
    finally:
        if not args.no_lock:
            lock.release()

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
    absent = [f for f in plan if f.state == "not run"]
    print("fibers={} pass={} fail={} not-run={}".format(
        len(plan), len(plan) - len(bad) - len(absent), len(bad), len(absent)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
