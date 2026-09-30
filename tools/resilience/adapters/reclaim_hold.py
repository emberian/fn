"""Reclaim captures first; a new independent live response then prevents swap.

This uses the actual OVER quantum hold after response ownership acquisition,
reads the candidate's full article during competing work, observes readers
deferral, drains the response and observes its named settlement. Reclaim
then installs and a retained article remains productive. No plan-only hold.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import time

from tests.native_harness import Client, start
from tests.test_native_expiry import GROUP, PAST, article, msgid
from tools.resilience import checker
from tools.resilience.checker import Verdict
from tools.resilience.adapters.native_cuts import ACTORS, healing_bound, served_matches
from tools.resilience.adapters.page_io import Fixture, file_hash, HarnessFailure
from tools.resilience.journal import Journal
from tools.resilience.scenario import Scenario, Operation, Fault, check as validate

ROOT = Path(__file__).resolve().parents[3]
PATTERN = re.compile(
    rb"RECLAIM held at=(captured)|OVER quantum-held cid=([0-9]+)|"
    rb"RECLAIM deferred reason=(readers)|OVER response-settled cid=([0-9]+) status=(released)|"
    rb"RECLAIM installed records=([0-9]+) reclaimed=([0-9]+) dropped=([0-9]+)")


def events(stderr):
    rows = []
    for match in PATTERN.finditer(stderr):
        captured, held, deferred, settled, released, records, reclaimed, dropped = match.groups()
        if captured:
            rows.append(dict(phase="captured"))
        elif held:
            rows.append(dict(phase="held", cid=int(held)))
        elif deferred:
            rows.append(dict(phase="deferred", reason="readers"))
        elif settled:
            rows.append(dict(phase="settled", cid=int(settled), status=released.decode()))
        else:
            rows.append(dict(phase="installed", records=int(records), reclaimed=int(reclaimed),
                             dropped=int(dropped)))
    return rows


def example():
    return validate(Scenario(
        id="schedule-reclaim-candidate-selected",
        title="capture reclaim, acquire independent response ownership, settle it and make progress",
        contract="reclaim-response-hold", requirements=["STO-017", "HST-023"],
        initial={"recipe": "reclaim-response-hold", "fixture": "recorded-expiry-five", "groups": [GROUP],
                 "prior": [{"id": "p0", "groups": [GROUP]}, {"id": "n0", "groups": [GROUP]}]},
        actors=ACTORS,
        operations=[Operation("reclaim-1", "client", "reclaim"),
                    Operation("hold", "nemesis", "acquire-hold", {"article": "p0"}),
                    Operation("read-prior", "client", "read", {"article": "p0"}),
                    Operation("release", "nemesis", "release-hold", {"article": "p0"}),
                    Operation("reclaim-heal", "client", "reclaim"),
                    Operation("read-retained", "client", "read", {"article": "n0"})],
        faults=[Fault("reclaim-1", "reclaim-candidate-selected", "interleave",
                      "contract-admissible", "performed", "served-post", ("hold", "read-prior"))],
        healing=["release", "reclaim-heal", "read-retained"],
        witnesses=["independent-response-held", "response-hold-settled", "reclaim-freed",
                   "read-during-competing-work", "read-completed"], healing_bound=healing_bound()))


def run_scenario(scenario, image, work, fault_hook=True):
    work = Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    fixture = Fixture()
    fixture.root, fixture.image = work, Path(image).resolve()
    j = Journal(scenario.id)
    j.bind("p0", msgid("p0"))
    j.bind("n0", msgid("n0"))
    owner = reclaim = response = None
    capture_release, response_stall = work / "reclaim-release", work / "response-stall"
    observed_stderr_bytes = 0
    primary = None
    cleanup_errors = []

    def observed():
        if owner.stderr.dropped:
            raise HarnessFailure("reclaim-hold-history-truncated")
        return events(owner.stderr.since(0))

    def wait(predicate, cause):
        deadline = time.monotonic() + 120
        while time.monotonic() < deadline:
            rows = observed()
            if predicate(rows):
                return rows
            if owner.poll() is not None:
                raise HarnessFailure("reclaim-hold-owner-died:" + cause)
            time.sleep(0.1)
        raise HarnessFailure(cause)

    try:
        if not fixture.image.is_file():
            raise HarnessFailure("reclaim-image-unavailable")
        canonical = example()
        for field in ("contract", "initial", "operations", "faults", "healing", "witnesses"):
            if getattr(scenario, field) != getattr(canonical, field):
                raise HarnessFailure("unsupported-reclaim-hold-recipe:" + field)
        j.stage("setup", "begun")
        node = fixture.copy_of(fixture.recorded_base(), "capture-first")
        response_stall.touch()
        env = {"FN_NATIVE_OVER_WINDOW": "1",
               "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM": str(response_stall)}
        if fault_hook:
            env["FN_NATIVE_RECLAIM_HOLD"] = "captured:" + str(capture_release)
        owner = node.start(timeout=600, env=env)
        j.stage("setup", "ended")
        j.stage("workload", "begun")
        reclaim = start(node.argv(None, ["operator", node.config, "store", "reclaim", "--recorded"]),
                        cwd=ROOT, env=node.environment())
        rows = wait(lambda rows: any(r["phase"] in ("captured", "installed") for r in rows),
                    "reclaim-capture-hold-unobserved")
        if not any(r["phase"] == "captured" for r in rows):
            raise HarnessFailure("fault-never-occurred:reclaim-1@reclaim-candidate-selected:interleave")
        response = Client(node.port, timeout=300, greeting=None)
        group = response.command("GROUP " + GROUP)
        response.send(b"OVER 1-100\r\n")
        rows = wait(lambda rows: any(r["phase"] == "held" for r in rows),
                    "independent-response-hold-unobserved")
        cid = next(r["cid"] for r in rows if r["phase"] == "held")
        j.bind("held-response-cid", cid)
        j.client("response-hold", operation="hold", cid=cid, group=group.decode("ascii", "replace"))
        with Client(node.port, timeout=300, greeting=None) as reader:
            data = reader.article(msgid("p0"))
        j.client("read", operation="read-prior", article="p0", during_competing_work=True,
                 result="match" if data is not None and served_matches(data, article("p0", expires=PAST)) else "other")
        capture_release.write_bytes(b"release capture")
        stdout, stderr = reclaim.communicate(timeout=1200)
        j.client("reclaim", operation="reclaim-1", returncode=reclaim.returncode,
                 installed=b"installed" in stdout)
        wait(lambda rows: any(r["phase"] == "deferred" for r in rows),
             "captured-reclaim-did-not-defer-for-new-reader")
        j.environment("fault-fired", operation="reclaim-1", boundary="reclaim-candidate-selected",
                      action="interleave", stage="performed", cid=cid)
        j.stage("workload", "ended")
        healing_started = time.monotonic()
        j.stage("healing", "begun")
        response_stall.unlink()
        status = response.line()
        body = response.block()
        numbers = [int(row.split(b"\t", 1)[0]) for row in body.splitlines()]
        response.close()
        response = None
        j.client("response-drain", operation="release", cid=cid,
                 status=status.decode("ascii", "replace"), numbers=numbers)
        wait(lambda rows: any(r["phase"] == "settled" and r["cid"] == cid for r in rows),
             "independent-response-settlement-unobserved")
        result = fixture.reclaim(node, "--recorded", expect=None)
        j.client("reclaim", operation="reclaim-heal", returncode=result.returncode,
                 installed=b"installed" in result.stdout)
        rows = wait(lambda rows: any(r["phase"] == "installed" for r in rows),
                    "released-reclaim-install-unobserved")
        with Client(node.port, timeout=300, greeting=None) as reader:
            reclaimed_status = reader.command("STAT " + msgid("p0"))
            data = reader.article(msgid("n0"))
        j.client("read", operation="read-retained", article="n0",
                 expired_status=reclaimed_status.decode("ascii", "replace"),
                 result="match" if data is not None and served_matches(data, article("n0")) else "other")
        for row in rows:
            j.environment("response-reclaim", **row)
        observed_stderr_bytes = len(owner.stderr.since(0))
        j.environment("response-terminal", cid=cid)
        j.stage("healing", "ended", elapsed=time.monotonic() - healing_started)
        verdict = checker.check(scenario, j)
    except Exception as error:
        primary = dict(exception=type(error).__name__, diagnostic=str(error))
        verdict = checker.harness_failure(scenario, j, str(error)[:500])
    finally:
        # Each owned cleanup is attempted even when another fails. Retain the
        # original outcome independently; cleanup never supplies a cut receipt.
        def cleanup(name, action):
            try:
                action()
            except Exception as error:
                detail = dict(action=name, exception=type(error).__name__, diagnostic=str(error))
                cleanup_errors.append(detail)
                j.environment("reclaim-cleanup-failed", **detail)
        cleanup("release-capture", lambda: capture_release.write_bytes(b"cleanup release"))
        cleanup("release-response-stall", lambda: response_stall.unlink(missing_ok=True))
        if response is not None:
            cleanup("close-response", lambda: response.close(False))
        if reclaim is not None:
            cleanup("stop-reclaim", reclaim.stop)
        def fixture_cleanup():
            if fixture.doCleanups() is False:
                raise RuntimeError("unittest fixture reported cleanup failure")
        cleanup("fixture-cleanups", fixture_cleanup)
        if owner is not None:
            cleanup("retain-owner-stderr", lambda: (work / "owner.stderr").write_bytes(owner.stderr.since(0)))
    (work / "primary-outcome.json").write_text(json.dumps(
        dict(failure=primary, verdict=verdict.to_json(), cleanup_errors=cleanup_errors), indent=2) + "\n")
    if cleanup_errors:
        cause = "reclaim-cleanup-incomplete"
        if verdict.cause:
            cause = verdict.cause + ";" + cause
        verdict = Verdict("harness-failure", scenario_id=scenario.id, journal_digest=j.digest(),
                          cause=cause, explanation="Owned cleanup failed; original outcome retained.").sign()
    j.write(work / "journal.jsonl")
    (work / "scenario.json").write_text(json.dumps(scenario.to_json(), indent=2) + "\n")
    (work / "verdict.json").write_text(json.dumps(verdict.to_json(), indent=2) + "\n")
    inputs = ("tools/resilience/adapters/reclaim_hold.py", "tools/resilience/checker.py",
              "tools/resilience/scenario.py", "tools/resilience/journal.py",
              "tools/resilience/adapters/page_io.py", "tools/resilience/adapters/native_cuts.py",
              "tests/test_native_expiry.py", "tests/native_harness.py",
              "tests/campaign/native_operator_campaign.py", "host/native/owner.lisp",
              "books/response-plan-pins.lisp", "books/owner-reclaim-pass.lisp")
    (work / "manifest.json").write_text(json.dumps(dict(
        source_revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        image=str(fixture.image), image_sha256=file_hash(fixture.image) if fixture.image.is_file() else None,
        image_present=fixture.image.is_file(), cleanup_complete=not cleanup_errors,
        inputs={p: file_hash(ROOT / p) for p in inputs}, observed_stderr_bytes=observed_stderr_bytes,
        scenario=scenario.id, scope="capture-first independent response ownership; physical sector release unclaimed"),
        indent=2) + "\n")
    return j, verdict
