"""Actual issued-page I/O scenario; native verdict requires a matching image.

The delayed token is cancelled and its immutable file incarnation retired.
Its observed completion must discard, then the retired file may close. A
different retained article read proves productivity; a new socket does not
prove native CID reuse. These observations do not prove worker thread death.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
import unittest

from tests.native_harness import Client
from tests.test_native_expiry import (ExpiryMixin, DeveloperExpiryTests, GROUP,
                                     article, msgid)
from tools.resilience import checker
from tools.resilience.adapters.native_cuts import ACTORS, healing_bound, served_matches
from tools.resilience.journal import Journal
from tools.resilience.scenario import Scenario, Operation, Fault, check as validate

ROOT = Path(__file__).resolve().parents[3]
TOKEN = rb"\(([0-9]+)\s+([0-9]+)\s+([0-9]+)\s+([0-9]+)\s+([0-9]+)\s+([0-9]+)\)"
EVENTS = re.compile(
    rb"PAGE-IO (?:(held) token=" + TOKEN + rb" file=([0-9]+)|"
    rb"(cancelled|settled) token=" + TOKEN +
    rb"(?: answer=(:PUBLISH|:CANCELLED|\(:FAULT :(?:READ|ERROR|DIGEST|TRAILER)\)))?|"
    rb"(close-held|closed) file=([0-9]+)|"
    rb"(stale|duplicate) answer=(:STALE))")


def example() -> Scenario:
    return validate(Scenario(
        id="schedule-page-read-outstanding",
        title="cancel an issued page read, retire its file, settle it, then read retained bytes",
        contract="page-io-ownership", requirements=["STO-017", "STO-002"],
        initial={"recipe": "page-io", "groups": [GROUP],
                 "prior": [{"id": "p0", "groups": [GROUP]},
                           {"id": "n0", "groups": [GROUP]}]}, actors=ACTORS,
        operations=[Operation("read-prior", "client", "read", {"article": "p0"}),
                    Operation("cancel", "nemesis", "cancel-reader", {"reader": "read-prior"}),
                    Operation("retire", "nemesis", "retire-generation"),
                    Operation("deliver", "nemesis", "deliver-delayed-page", {"article": "p0"}),
                    Operation("read-retained", "client", "read", {"article": "n0"})],
        faults=[Fault("read-prior", "page-read-outstanding", "interleave",
                      "contract-admissible", "issued", "served-post", ("cancel", "retire"))],
        healing=["deliver", "read-retained"],
        witnesses=["issued-read-held", "cancelled-read-settled", "retired-file-closed",
                   "read-completed"], healing_bound=healing_bound()))


def events(stderr: bytes) -> list[dict]:
    """Parse decimal token fields without the Lisp reader, including wrapped tokens."""
    rows = []
    for match in EVENTS.finditer(stderr):
        g = match.groups()
        if g[0]:
            token = [int(x) for x in g[1:7]]
            rows.append(dict(phase="held", token=token, file=int(g[7])))
        elif g[8]:
            rows.append(dict(phase=g[8].decode(), token=[int(x) for x in g[9:15]],
                             answer=g[15].decode() if g[15] else None))
        elif g[16]:
            rows.append(dict(phase=g[16].decode(), file=int(g[17])))
        else:
            rows.append(dict(phase=g[18].decode(), answer=g[19].decode()))
    return rows


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


class HarnessFailure(Exception):
    pass


class Fixture(ExpiryMixin, unittest.TestCase):
    """Reuse native Store setup; the scenario's verdict is the journal checker."""
    recorded_base = DeveloperExpiryTests.recorded_base
    copy_of = DeveloperExpiryTests.copy_of


def run_scenario(scenario, image, work, fault_hook=True):
    work = Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    j = Journal(scenario.id)
    fixture = Fixture()
    fixture.root, fixture.image = work, Path(image).resolve()
    owner = None
    observed_stderr_bytes = 0
    release = work / "page-io-release"
    old = new = None

    def observed():
        if owner.stderr.dropped:
            raise HarnessFailure("page-io-history-truncated")
        return events(owner.stderr.since(0))

    def wait(predicate, missing):
        deadline = time.monotonic() + 120
        while time.monotonic() < deadline:
            rows = observed()
            if predicate(rows):
                return rows
            if owner.poll() is not None:
                raise HarnessFailure("page-io-owner-died:" + missing)
            time.sleep(0.1)
        raise HarnessFailure(missing)

    try:
        j.stage("setup", "begun")
        base = fixture.recorded_base()
        node = fixture.copy_of(base, "issued-page")
        j.stage("setup", "ended")
        j.stage("workload", "begun")
        env = {"FN_NATIVE_PAGE_IO_HOLD": str(release)} if fault_hook else {}
        owner = node.start(timeout=600, env=env)
        old = Client(node.port, timeout=120, greeting=None)
        old.send(("ARTICLE " + msgid("p0") + "\r\n").encode("ascii"))
        status = old.line()
        j.client("io-request", operation="read-prior", status=status.decode("ascii", "replace"))
        if status.startswith(b"220"):
            raise HarnessFailure("fault-never-occurred:read-prior@page-read-outstanding:interleave")
        rows = wait(lambda rs: any(r["phase"] == "held" for r in rs),
                    "page-io-hold-unobserved:FN_NATIVE_PAGE_IO_HOLD issued-token boundary")
        token = next(r["token"] for r in rows if r["phase"] == "held")
        wait(lambda rs: any(r["phase"] == "cancelled" and r["token"] == token for r in rs),
             "page-io-cancellation-unobserved")
        old.close(False)
        old = None
        j.client("io-cancel", operation="cancel", token=token)
        new = Client(node.port, timeout=120, greeting=None)
        retired = fixture.reclaim(node, "--recorded", expect=None)
        j.client("io-retire", operation="retire", returncode=retired.returncode,
                 installed=b"installed" in retired.stdout)
        rows = wait(lambda rs: any(r["phase"] == "close-held" and r["file"] == token[2]
                                  for r in rs), "page-io-retired-hold-unobserved")
        # Only the observed issued token, cancellation and blocked retirement
        # activate this interleave. Configuring a selector is insufficient.
        j.environment("fault-fired", operation="read-prior", boundary="page-read-outstanding",
                      action="interleave", stage="issued", token=token)
        j.stage("workload", "ended")
        healing_started = time.monotonic()
        j.stage("healing", "begun")
        release.write_bytes(b"release")
        j.client("io-release", operation="deliver", token=token)
        wait(lambda rs: any(r["phase"] == "closed" and r["file"] == token[2] for r in rs),
             "page-io-settlement-unobserved")
        data = new.article(msgid("n0"))
        j.client("read", operation="read-retained", article="n0",
                 result="match" if data is not None and served_matches(data, article("n0")) else "other")
        rows = wait(lambda rs: any(r["phase"] == "settled" and r.get("answer") == ":PUBLISH"
                                  and r["token"][0] > token[0] for r in rs),
                    "page-io-productive-completion-unobserved")
        observed_stderr_bytes = len(owner.stderr.since(0))
        for row in rows:
            j.environment("page-io", **row)
        j.environment("io-terminal", token=token)
        j.stage("healing", "ended", elapsed=time.monotonic() - healing_started)
        verdict = checker.check(scenario, j)
    except Exception as error:
        verdict = checker.harness_failure(scenario, j, str(error)[:500])
    finally:
        release.write_bytes(b"cleanup release")
        for client in (old, new):
            if client is not None:
                client.close(False)
        fixture.doCleanups()
        if owner is not None:
            (work / "owner.stderr").write_bytes(owner.stderr.since(0))
    j.write(work / "journal.jsonl")
    (work / "scenario.json").write_text(json.dumps(scenario.to_json(), indent=2) + "\n")
    (work / "verdict.json").write_text(json.dumps(verdict.to_json(), indent=2) + "\n")
    (work / "manifest.json").write_text(json.dumps(dict(
        source_revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                                text=True).strip(),
        image=str(fixture.image), image_sha256=file_hash(fixture.image),
        observed_stderr_bytes=observed_stderr_bytes,
        inputs={p: file_hash(ROOT / p) for p in (
            "tools/resilience/adapters/page_io.py", "tools/resilience/checker.py",
            "tools/resilience/adapters/native_cuts.py", "tests/campaign/native_operator_campaign.py",
            "tools/resilience/scenario.py", "tools/resilience/journal.py",
            "tests/test_native_expiry.py", "tests/native_harness.py",
            "tools/outcome_codes.py", "books/outcome-class.lisp",
            "host/native/extent.lisp", "host/native/owner.lisp",
            "books/page-read-ownership.lisp", "books/page-read-resources.lisp")},
        scenario=scenario.id, scope="issued-token cancellation/settlement and retained article; thread death unclaimed"),
        indent=2) + "\n")
    return j, verdict


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--image", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--no-fault", action="store_true")
    args = ap.parse_args()
    _, verdict = run_scenario(example(), args.image, args.out, not args.no_fault)
    print(json.dumps(verdict.to_json(), sort_keys=True))
    return 0 if verdict.green else 1


if __name__ == "__main__":
    raise SystemExit(main())
