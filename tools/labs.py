#!/usr/bin/env python3
"""Run the integration labs, each under its own budget, and say what ran.

Two integration labs were dead on `dev` for a day and every `make check` was
green for all of it.  One host signature change -- `receive_bpa_request`
gaining a required keyword-only `bundle` -- killed the four-node lab at its
first receive, and that lab carries the only end-to-end evidence for the
carried-media and crash-recovery rows of milestone M3.  A lane recorded a
22-of-22 run from a branch that predated the change, so the evidence record
looked current and was not, and `tests/ltp/run_fn_ltp_lab.py` was broken the
same way for as long again.  Nothing in the tree ran a lab, so nothing
noticed.

This is what runs them.  Three outcomes, kept distinct all the way out to the
exit code, in the shape D13 asks for everywhere else:

* ``passed``       -- the lab ran here and its own assertions held.
* ``failed``       -- the lab ran here and something it asserts did not hold,
                      or it exited 0 and produced no evidence file.
* ``not-runnable`` -- a dependency this machine does not have.  The row
                      always says *what* is missing and how to get it.  A
                      not-runnable lab is never a pass, is never silent, and
                      never contributes to a claim.

The exit code is 1 when any lab failed and 0 otherwise; ``--require`` turns a
named lab's absence into a failure, which is how a box that is supposed to be
able to run a lab says so.

    python3 tools/labs.py                 # everything runnable on this machine
    python3 tools/labs.py --tier quick    # the subset a lane can afford
    python3 tools/labs.py --tier box --host hbox
    python3 tools/labs.py --only four-node --json build/labs/report.json

`tests/README.md` carries the table of which lab is in which tier and what
each one costs.  Nothing here is wired into `make check`: a lab takes minutes
and `make check` takes seconds, and a gate nobody can afford to run is a gate
nobody runs.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import datetime as dt
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

PASSED = "passed"
FAILED = "failed"
NOT_RUNNABLE = "not-runnable"
# A harness that exits 3 violated nothing it stated and decided nothing it
# meant to decide (tools/deploy_gate.py's `Finding`, D13's uncertain).  It is
# not a pass, because it establishes no claim, and it is not a failure,
# because nothing came out false; folding it into either loses the
# distinction the gates keep.
INCONCLUSIVE = "inconclusive"
GATE_INCONCLUSIVE_EXIT = 3


def repo_root(start: Path | None = None) -> Path:
    """The fn worktree this command was INVOKED from, not the one it lives in.

    Same rule and the same reason as `tools/deploy_gate.py`: a lane running
    the main checkout's copy of a harness must measure, and write under, the
    lane's own tree.
    """
    try:
        out = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                             cwd=str(start or Path.cwd()), check=True,
                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        return Path(out.stdout.decode().strip())
    except Exception:
        return Path(__file__).resolve().parents[1]


def revision(root: Path, args=None) -> str:
    """What this run is evidence about, without asking git twice.

    `--commit` when the caller named one that is not a moving reference,
    `FN_GATE_REVISION` when a gate set it, else this worktree's HEAD, else
    the empty string -- and a lab that needs one refuses on the empty string
    rather than writing "unknown".
    """
    named = getattr(args, "commit", None)
    if named and named not in ("HEAD", "dev"):
        return named
    from_gate = os.environ.get("FN_GATE_REVISION", "").strip()
    if from_gate:
        return from_gate
    try:
        out = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(root),
                             check=True, stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL)
        return out.stdout.decode().strip()
    except Exception:
        return ""


def acl2_executable() -> str | None:
    """The ACL2 this tree would use, or None."""
    named = os.environ.get("FN_ACL2")
    if named:
        return named if Path(named).is_file() and os.access(named, os.X_OK) else None
    return shutil.which("acl2")


def certificate_closure(root: Path, hosts: tuple[str, ...]):
    """Every book those host files transitively include, and its certificate.

    A host file is `ld`ed, never certified, so nothing else in the tree reads
    it; the books under it are what an `include-book` inside it needs a
    certificate for.

    Presence only. A certificate here is content-keyed
    (`ACL2_BOOK_HASH_ALISTP=NIL`) and `tools/certs.py install` copies pairs
    out of the cache with their original timestamps, so a file date says
    nothing about whether a pair matches -- an mtime staleness proxy calls
    every book in a freshly installed worktree stale. Whether an installed
    pair is still VALID is ACL2's answer and nobody else's, and when it is not
    the lab does not fail honestly: `include-book` treats a stale certificate
    as an ERROR where an absent one is only a warning, and the bridge dies
    with `ACL2 bridge call marker did not precede its prompt`. `DIAGNOSES`
    below says so on the failing row, which is where it is useful.

    Returns (missing, reader error).
    """
    try:
        from tools import ledger
    except Exception as error:  # pragma: no cover - a broken tree, not a lab
        return [], "the book reader did not load: {!r}".format(error)
    try:
        books = {relative: ledger.analyze_book(path, relative)
                 for path, relative in ledger.book_paths()}
        pending, seen = [], set()
        for relative in hosts:
            path = root / relative
            if not path.is_file():
                return [], "{} is not in this tree".format(relative)
            host = ledger.analyze_host(path, relative)
            pending.extend(ledger.resolve(reference + ".lisp")
                           for reference in host.includes)
        missing = []
        while pending:
            target = pending.pop()
            if target in seen:
                continue
            seen.add(target)
            book = books.get(target)
            if book is None:
                continue  # a system book: ACL2's own certificate, not ours
            if not (root / target).with_suffix(".cert").is_file():
                missing.append(target)
            pending.extend(ledger.included_path(book, reference)
                           for reference in book.includes)
        return sorted(missing), None
    except Exception as error:  # pragma: no cover
        return [], "the book reader failed: {!r}".format(error)


# --------------------------------------------------------------------------
# the registry
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Lab:
    """One integration lab: how to run it, what it costs, what it needs."""

    name: str
    # "lab" is fn meeting something; "dry" is a lab's own harness run against
    # fakes with no ssh and no box.  A dry run establishes that the harness
    # still parses, sequences and renders -- and nothing whatever about fn.
    # It is reported in its own section so the two can never be read as one.
    kind: str
    tier: str
    script: str
    budget: float
    cost: str
    carries: str
    argv: Callable[[Path, Path, argparse.Namespace], list[str]]
    unmet: Callable[[Path, argparse.Namespace], str | None]
    env: dict = field(default_factory=dict)


def _git_repository(root: Path) -> str | None:
    if not (root / ".git").exists():
        return ("the gate harness exports the tree with `git archive` and this "
                "checkout is not a git repository")
    return None


# The host files `tools/run_store.py`, `tools/run_bp_receive.py`,
# `tools/workflow_bridge.py` and `tools/bundle_bridge.py` `ld` on the lab's
# path.  Their include closure is what needs certificates in this worktree.
FOUR_NODE_HOSTS = (
    "host/store-host.lisp", "host/spike-storage-fast-host.lisp", "host/store-node-host.lisp",
    "host/config-host.lisp", "host/anchor-host.lisp",
    "host/checkpoint-host.lisp", "host/bp-ingress-host.lisp",
    "host/bp-receive-host.lisp", "host/bp-receipt-journal-host.lisp",
    "host/workflow-host.lisp")


def _four_node_unmet(root: Path, args) -> str | None:
    if acl2_executable() is None:
        return ("no ACL2: FN_ACL2 names none and `acl2` is not on PATH "
                "(the lab's every acceptance, receipt and local number is ACL2's)")
    missing, error = certificate_closure(root, FOUR_NODE_HOSTS)
    if error:
        return error
    if missing:
        return ("{} of the books under the lab's host files have no certificate "
                "in this worktree ({}{}); run `python3 tools/certs.py install`, "
                "or certify them".format(
                    len(missing), ", ".join(missing[:4]),
                    ", ..." if len(missing) > 4 else ""))
    return None


def _tcpcl_image(root: Path, args) -> Path:
    return Path(args.image).expanduser() if args.image else root / "build" / "fn-host"


def _tcpcl_unmet(root: Path, args) -> str | None:
    image = _tcpcl_image(root, args)
    if not image.exists():
        return ("no native fn image at {}: `sh tools/build_native_host.sh` builds "
                "one, and that needs a certified tree first (it refuses to load an "
                "uncertified book)".format(image))
    return None


def _ltp_unmet(root: Path, args) -> str | None:
    ion = Path(args.ion_root).expanduser()
    for binary in ("bpsendfile", "fn_ltp_stage"):
        if not (ion / "install" / "bin" / binary).is_file():
            return ("no pinned ION build at {}: {} is not there.  The build "
                    "recorded in tests/ltp/pin.json lives on hbox at /tank/fn/ltp, "
                    "and the two ION nodes must already be started "
                    "(tests/ltp/start_node.sh)".format(ion, binary))
    if acl2_executable() is None:
        return "no ACL2: FN_ACL2 names none and `acl2` is not on PATH"
    return None


def _box_unmet(root: Path, args) -> str | None:
    if not args.host:
        return ("needs a farm box: pass --host (persvati or hbox).  This lab ships "
                "a commit to a machine that is not the laptop and drives it there")
    return _git_repository(root)


def _inn_unmet(root: Path, args) -> str | None:
    unmet = _box_unmet(root, args)
    if unmet:
        return unmet.replace("--host (persvati or hbox)",
                             "--host, naming a box with the pinned INN build "
                             "(tests/inn/pin.json; /tank/fn/inn/2.7.4 on hbox)")
    if not getattr(args, "native_image", None):
        return ("the INN lab's fn side is the native image or the lab does not "
                "run (D07): give --native-image, the image's path on the box")
    return None


def _dry_unmet(root: Path, args) -> str | None:
    return _git_repository(root)


def _commit(args) -> str:
    return args.commit


LABS: tuple[Lab, ...] = (
    Lab(name="four-node", kind="lab", tier="quick",
        script="tests/bp-dtn7/run_four_node_lab.py",
        budget=600.0, cost="about 65 s and one ACL2 on this laptop",
        carries="the only end-to-end evidence for the carried-media and "
                "crash-recovery rows of M3: 22 assertions over four nodes, "
                "non-overlapping contacts, a SIGKILLed relay, a lost receipt, "
                "an expiry and a reordered duplicate pair",
        # `--revision` explicitly: the lab refuses to write an evidence file
        # it cannot name a revision for, and a gate tree is a `git archive`
        # extract with no repository to ask.
        argv=lambda root, run, args: [
            sys.executable, str(root / "tests/bp-dtn7/run_four_node_lab.py"),
            "--run-base", str(run), "--revision", revision(root, args)],
        unmet=_four_node_unmet),
    Lab(name="tcpcl", kind="lab", tier="local",
        script="tools/tcpcl_lab.py",
        budget=900.0, cost="a few minutes once build/fn-host exists; the image "
                           "itself costs a certified tree and an SBCL save",
        carries="two fn native hosts exchanging bundles over TCPCLv4 on "
                "loopback: contact, two-segment transfers both ways, a refused "
                "MRU, keepalives, a SIGKILL inside a transfer, a whole-bundle "
                "ADU and the listener's trace folded back through the image",
        argv=lambda root, run, args: [
            sys.executable, str(root / "tools/tcpcl_lab.py"),
            "--image", str(_tcpcl_image(root, args)), "--work", str(run),
            "--scenario", "all"],
        unmet=_tcpcl_unmet),
    Lab(name="ltp", kind="lab", tier="box",
        script="tests/ltp/run_fn_ltp_lab.py",
        budget=900.0, cost="a couple of minutes on the box that holds ION",
        carries="fn's request ADU across an actual ION BP-over-LTP link and "
                "back into fn's own acceptance: feasibility evidence for one "
                "adapter route, not interoperability qualification",
        argv=lambda root, run, args: [
            sys.executable, str(root / "tests/ltp/run_fn_ltp_lab.py"),
            "--ion-root", str(Path(args.ion_root).expanduser()),
            "--run", str(run)],
        unmet=_ltp_unmet),
    Lab(name="deploy", kind="lab", tier="box",
        script="tools/deploy_gate.py",
        budget=5400.0, cost="tens of minutes on a box, and a certification if "
                            "the box holds no gate for the tree",
        carries="one commit unpacked on a machine that is not the laptop, "
                "serving a real socket to an independent client, SIGKILLed "
                "mid-session and reopened through the real recovery path",
        argv=lambda root, run, args: [
            sys.executable, str(root / "tools/deploy_gate.py"), _commit(args),
            "--host", args.host or "", "--jobs", str(args.jobs)],
        unmet=_box_unmet),
    Lab(name="twonode", kind="lab", tier="box",
        script="tools/twonode_gate.py",
        budget=5400.0, cost="tens of minutes on a box",
        carries="two fn nodes beside each other: what A accepts is A's, an "
                "IHAVE offer from A to B, and B SIGKILLed mid-transfer and "
                "reread",
        argv=lambda root, run, args: [
            sys.executable, str(root / "tools/twonode_gate.py"), _commit(args),
            "--host", args.host or "", "--jobs", str(args.jobs)],
        unmet=_box_unmet),
    Lab(name="inn", kind="lab", tier="box",
        script="tools/inn_lab.py",
        budget=1800.0, cost="about a minute on the box that holds INN (52 s on "
                            "hbox, 2026-09-22)",
        carries="the only question whose answer does not come from our own "
                "code: the native fn owner against a real InterNetNews, its "
                "feed into innd, innfeed into fn, duplicates and loops both "
                "ways, and a cut on each side",
        argv=lambda root, run, args: [
            sys.executable, str(root / "tools/inn_lab.py"), _commit(args),
            "--host", args.host or "", "--native-image", args.native_image or "",
            "--evidence", str(Path(run) / "inn-lab.md")],
        unmet=_inn_unmet),
    Lab(name="scale", kind="lab", tier="box",
        script="tools/scale_gate.py",
        budget=10800.0, cost="hours on a box; it doubles a store until a post "
                             "or a recover crosses its ceiling",
        carries="the number that has to ship beside `one commit serves`: at "
                "what store size a post stops returning, at what size recover "
                "becomes an outage, and what a reader pays per command",
        argv=lambda root, run, args: [
            sys.executable, str(root / "tools/scale_gate.py"), _commit(args),
            "--host", args.host or "", "--jobs", str(args.jobs)],
        unmet=_box_unmet),
    # The dry runs.  Each drives the real gate script through bash on this
    # machine with HOME redirected, fakes over the entry points and no ssh at
    # all.  They establish that the harness parses, sequences, classifies and
    # renders.  They establish NOTHING about fn, and they are printed apart
    # from the labs so that they cannot be read as a lab result.
    Lab(name="deploy-dry", kind="dry", tier="quick",
        script="tests/test_deploy_gate.py",
        budget=600.0, cost="about 30 s",
        carries="tools/deploy_gate.py's sequencing, certificate choice, port "
                "parsing, kill/recover cut, exit-code classification and "
                "evidence rendering, against fakes",
        argv=lambda root, run, args: [
            sys.executable, "-m", "unittest", "tests.test_deploy_gate"],
        unmet=_dry_unmet),
    Lab(name="twonode-dry", kind="dry", tier="quick",
        script="tests/test_twonode_gate.py",
        budget=600.0, cost="about 20 s",
        carries="tools/twonode_gate.py's two-node sequencing, peer records, "
                "feed and kill scenarios and evidence, against fakes",
        argv=lambda root, run, args: [
            sys.executable, "-m", "unittest", "tests.test_twonode_gate"],
        unmet=_dry_unmet),
    Lab(name="scale-dry", kind="dry", tier="quick",
        script="tests/test_scale_gate.py",
        budget=600.0, cost="about 15 s",
        carries="tools/scale_gate.py's series, stop rule, comparison and "
                "tables, against fake series, generate, measure and server "
                "entry points",
        argv=lambda root, run, args: [
            sys.executable, "-m", "unittest", "tests.test_scale_gate"],
        unmet=_dry_unmet),
    Lab(name="inn-dry", kind="dry", tier="quick",
        script="tests/test_inn_lab.py",
        budget=600.0, cost="about 20 s",
        carries="tools/inn_lab.py's scenario sequencing, relay parsing, header "
                "comparison, port scheme, configuration writing and evidence, "
                "against a stand-in INN and a stand-in image (tests/inn_lab_fake)",
        argv=lambda root, run, args: [
            sys.executable, "-m", "unittest", "tests.test_inn_lab"],
        unmet=_dry_unmet),
)

TIERS = {"quick": ("quick",), "local": ("quick", "local"),
         "box": ("box",), "all": ("quick", "local", "box")}


# --------------------------------------------------------------------------
# running one
# --------------------------------------------------------------------------


# Failures whose cause is not in the lab at all.  A row that matches one says
# so, because the alternative is a lane spending an afternoon in the lab.
DIAGNOSES = (
    ("ACL2 bridge call marker did not precede its prompt",
     "this is almost always a STALE certificate, not a defect of the lab: "
     "`include-book` treats a stale pair as an ERROR where an absent one is "
     "only a warning, so the bridge dies before the lab runs. Run "
     "`python3 tools/certs.py install`, or certify the closure, and try "
     "again."),
    ("Uncertified",
     "a book in the closure was included uncertified. Run "
     "`python3 tools/certs.py install`, or certify the closure."),
    ("AF_UNIX path too long",
     "the run directory is too deep for a unix socket (104 bytes on darwin). "
     "Pass a shorter --run."),
    ("ACL2 executable is unavailable",
     "set FN_ACL2 to the ACL2 this box has; on hbox that is "
     "/tank/fn/acl2-8.7/saved_acl2."),
)


def diagnosis(output: str) -> str:
    for marker, advice in DIAGNOSES:
        if marker in output:
            return " [{}]".format(advice)
    return ""


def last_json_object(text: str) -> dict | None:
    """The last line of output that is a JSON object.

    Every lab here ends by printing one; it is where the evidence path and the
    lab's own verdict live.
    """
    for line in reversed(text.splitlines()):
        line = line.strip()
        if line.startswith("{") and line.endswith("}"):
            try:
                value = json.loads(line)
            except ValueError:
                continue
            if isinstance(value, dict):
                return value
    return None


def run_one(lab: Lab, root: Path, run: Path, args) -> dict:
    row = {"lab": lab.name, "kind": lab.kind, "tier": lab.tier,
           "script": lab.script, "budget_seconds": lab.budget,
           "carries": lab.carries, "cost": lab.cost}
    unmet = lab.unmet(root, args)
    if unmet is not None:
        row.update(outcome=NOT_RUNNABLE, reason=unmet, seconds=0.0)
        return row
    run.mkdir(parents=True, exist_ok=True)
    argv = lab.argv(root, run, args)
    environment = dict(os.environ, **lab.env)
    environment.setdefault("PYTHONPATH", str(root))
    row["command"] = " ".join(argv)
    start = time.monotonic()
    try:
        done = subprocess.run(argv, cwd=str(root), env=environment,
                              timeout=lab.budget, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        rc, output = done.returncode, done.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired as expired:
        rc = 124
        output = (expired.output or b"").decode("utf-8", "replace")
        output += "\n[labs] killed at the {} s budget".format(lab.budget)
    seconds = time.monotonic() - start
    row.update(rc=rc, seconds=round(seconds, 1))
    (run / "output.txt").write_text(output, encoding="utf-8")
    row["output"] = str(run / "output.txt")
    record = last_json_object(output)
    if record:
        row["record"] = record
        if record.get("evidence"):
            row["evidence"] = record["evidence"]
    tail = [line for line in output.splitlines() if line.strip()][-1:]
    row["last_line"] = tail[0][:300] if tail else ""
    if rc == GATE_INCONCLUSIVE_EXIT and lab.kind in ("lab", "dry"):
        row.update(outcome=INCONCLUSIVE,
                   reason="exit 3: the run violated nothing and decided "
                          "nothing it meant to decide: {}".format(
                              row["last_line"] or "no output"))
        return row
    if rc != 0:
        row.update(outcome=FAILED,
                   reason="exit {}: {}{}".format(
                       rc, row["last_line"] or "no output", diagnosis(output)))
        return row
    # A lab that exits 0 and leaves no evidence file has not run: that is the
    # shape the four-node record took while the lab could not start at all.
    evidence = row.get("evidence")
    if lab.kind == "lab" and evidence and not Path(evidence).is_file():
        row.update(outcome=FAILED,
                   reason="exit 0 and no evidence at {}".format(evidence))
        return row
    if lab.kind == "lab" and record is None:
        row.update(outcome=FAILED,
                   reason="exit 0 and no JSON record on stdout; a lab reports "
                          "its own verdict and this one printed none")
        return row
    row["outcome"] = PASSED
    return row


# --------------------------------------------------------------------------
# reporting
# --------------------------------------------------------------------------


def render(rows: list[dict], tier: str) -> str:
    lines = []
    for kind, title in (("lab", "labs"),
                        ("dry", "harness dry runs (the harness, not fn)")):
        chosen = [row for row in rows if row["kind"] == kind]
        if not chosen:
            continue
        lines.append("")
        lines.append(title)
        width = max(len(row["lab"]) for row in chosen)
        for row in chosen:
            lines.append("  {name:<{width}}  {outcome:<13} {seconds:>7.1f}s  {detail}".format(
                name=row["lab"], width=width, outcome=row["outcome"],
                seconds=row.get("seconds", 0.0),
                detail=row.get("reason") or row.get("evidence")
                or row.get("last_line", "")))
    counts = {name: sum(1 for row in rows if row["outcome"] == name)
              for name in (PASSED, FAILED, INCONCLUSIVE, NOT_RUNNABLE)}
    lines.append("")
    lines.append(
        "labs[{}]: {} passed, {} failed, {} inconclusive, {} not-runnable".format(
            tier, counts[PASSED], counts[FAILED], counts[INCONCLUSIVE],
            counts[NOT_RUNNABLE]))
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tier", default="local", choices=sorted(TIERS),
                        help="quick: what a lane can afford. local: everything "
                             "runnable off a box. box: the shipped gates. "
                             "all: every row.")
    parser.add_argument("--only", default="",
                        help="comma-separated lab names, whatever their tier")
    parser.add_argument("--require", default="",
                        help="comma-separated lab names whose absence is a "
                             "failure rather than a not-runnable row")
    parser.add_argument("--host", default="",
                        help="the farm box for the shipped gates")
    parser.add_argument("--commit", default="HEAD",
                        help="the commit-ish the shipped gates deploy")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--image", default=None,
                        help="the native fn image for the TCPCL lab "
                             "(default: build/fn-host under this worktree)")
    parser.add_argument("--native-image", default=None,
                        help="the saved native image's path on the box, for the "
                             "INN lab (its fn side is the image, D07)")
    parser.add_argument("--ion-root", default=os.environ.get("FN_ION_ROOT", "/tank/fn/ltp"),
                        help="the pinned ION install for the LTP lab")
    parser.add_argument("--run", default=None,
                        help="where the run directories go "
                             "(default: build/labs/<utc timestamp> under this worktree)")
    parser.add_argument("--json", default=None, help="write the rows here too")
    parser.add_argument("--list", action="store_true",
                        help="print the registry and exit")
    args = parser.parse_args(argv)

    root = repo_root()
    if args.list:
        for lab in LABS:
            print("{:<14} {:<4} {:<6} {:<34} {}".format(
                lab.name, lab.kind, lab.tier, lab.script, lab.cost))
        return 0

    only = {name.strip() for name in args.only.split(",") if name.strip()}
    required = {name.strip() for name in args.require.split(",") if name.strip()}
    known = {lab.name for lab in LABS}
    for name in only | required:
        if name not in known:
            parser.error("no lab named {!r}; known: {}".format(
                name, ", ".join(sorted(known))))
    if only:
        chosen = [lab for lab in LABS if lab.name in only]
    else:
        chosen = [lab for lab in LABS if lab.tier in TIERS[args.tier]]

    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    base = Path(args.run).expanduser() if args.run else root / "build/labs" / stamp
    rows = []
    for lab in chosen:
        row = run_one(lab, root, base / lab.name, args)
        if row["outcome"] == NOT_RUNNABLE and lab.name in required:
            row["outcome"] = FAILED
            row["reason"] = "--require {}: {}".format(lab.name, row["reason"])
        rows.append(row)
        print("  {:<14} {:<13} {:>7.1f}s  {}".format(
            row["lab"], row["outcome"], row.get("seconds", 0.0),
            (row.get("reason") or row.get("evidence") or "")[:160]), flush=True)

    report = {"schema": 1, "tier": args.tier, "root": str(root),
              "started": stamp, "runs": str(base), "rows": rows}
    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(render(rows, args.tier))
    print("run directories: {}".format(base))
    if any(row["outcome"] == FAILED for row in rows):
        return 1
    return 3 if any(row["outcome"] == INCONCLUSIVE for row in rows) else 0


if __name__ == "__main__":
    sys.exit(main())
