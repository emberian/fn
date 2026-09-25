#!/usr/bin/env python3
"""Deterministic crash campaign over the integrated host.

For every (scenario, cut) pair the campaign copies a prepared scenario
template, runs the real host operation in its own process group, SIGKILLs it
at the named cut, reopens the store and the journals through the real recovery
path, and then checks:

  * content acknowledged before the operation began, and the pins that belong
    to it, are intact;
  * the interrupted operation is absent or complete, never partial -- the
    expectation per cut is the `fn-sf-crash` record choice recorded in
    `cuts.py`;
  * a retry through the real entry point reaches exactly the state a run with
    no kill reaches (the per-scenario *reference* run): one article, its pins,
    one receipt;
  * the receipt ADU regenerates byte-identically, including against the bytes
    the killed process had already produced;
  * what the host had told the caller or the transport before the kill is
    consistent with the recovered state: an acknowledged receipt implies a
    durable record, and a cut that acknowledges nothing may recover either way.

A failure is recorded as a minimal trace: scenario, cut, the digest of the
durable state before and after the kill, the ACL2 replay result, and the
checks that failed.  The campaign kills only process groups it created.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
import hashlib
import json
import os
from pathlib import Path
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import zlib
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tests.campaign import child as child_module  # noqa: E402
from tests.campaign import cuts as cuts_module
from tests.campaign import model_images as model_images_module  # noqa: E402
from tools import run_bp_ingress, run_bp_receive, run_store, workflow_journal  # noqa: E402
from tools import deploy_gate  # noqa: E402
from tools.deploy_gate import evidence_path  # noqa: E402
from tools.workflow_bridge import Acl2WorkflowReplay  # noqa: E402

BASELINE_BID = "bid-baseline"
CHILD_READY_SECONDS = 180.0
DIGEST_TREES = ("store/config.json", "store/allocation-frontier.json",
                "store/transactions", "inbox/inbound", "receipts/records",
                "workflow/records")
BP_SCENARIOS = ("bp-receive", "bp-retry", "capacity-refusal")


def article(name: str) -> bytes:
    return ("Message-ID: <{}@fn.example>\r\nNewsgroups: fn.letters\r\n\r\n"
            "body for {}\r\n".format(name, name)).encode("ascii")


def digest(root: Path) -> str:
    """One digest over every durable name the campaign reasons about."""
    parts = []
    for relative in DIGEST_TREES:
        path = root / relative
        if path.is_dir():
            for item in sorted(path.rglob("*")):
                if item.is_file():
                    parts.append("{}:{}".format(
                        item.relative_to(root),
                        hashlib.sha256(item.read_bytes()).hexdigest()))
        elif path.is_file():
            parts.append("{}:{}".format(
                relative, hashlib.sha256(path.read_bytes()).hexdigest()))
    return hashlib.sha256("\n".join(parts).encode("utf-8")).hexdigest()


@dataclass
class StoreState:
    records: int
    articles: int
    pins: int
    baseline_present: bool
    campaign_present: bool
    replay: str


@dataclass
class Reference:
    """The state a scenario reaches with no kill at all."""
    outcome: str
    state: StoreState
    receipt_sha256: str | None


@dataclass
class Failure:
    scenario: str
    cut: str
    path: str
    model: str
    checks: list[str]
    before_digest: str
    after_digest: str
    acl2_replay: str
    observed: dict
    seconds: float

    def as_json(self) -> dict:
        return asdict(self)


@dataclass
class Report:
    pairs: int = 0
    failures: list[Failure] = field(default_factory=list)
    seconds: float = 0.0
    timings: dict = field(default_factory=dict)
    uncovered: list[str] = field(default_factory=list)
    model_gaps: list[str] = field(default_factory=list)

    def as_json(self) -> dict:
        return {"pairs": self.pairs, "seconds": round(self.seconds, 1),
                "timings": {key: round(value, 1)
                            for key, value in self.timings.items()},
                "uncovered": self.uncovered, "model_gaps": self.model_gaps,
                "failures": [failure.as_json() for failure in self.failures]}


class Campaign:
    def __init__(self, workdir: Path, quick: bool = False,
                 only: tuple[str, ...] | None = None,
                 scenarios: tuple[str, ...] | None = None,
                 log=lambda message: None, model_images: bool = False):
        self.workdir = Path(workdir)
        self.quick = quick
        self.only = only
        self.scenarios = scenarios
        self.log = log
        self.templates: dict[str, Path] = {}
        self.references: dict[str, Reference] = {}
        self.template_states: dict[str, StoreState] = {}
        self.model_images = model_images
        self.model_bridge = None
        self.model_sets: dict[str, model_images_module.ModelImages] = {}

    # -- configuration ------------------------------------------------------
    @staticmethod
    def max_transactions(scenario: str) -> int | None:
        # The 129th record would make every later reopen fault, so the bound
        # is what the refusal protects.  The number is reduced, not the guard.
        return 1 if scenario == "capacity-refusal" else None

    @contextmanager
    def configured(self, scenario: str):
        bound = self.max_transactions(scenario)
        if bound is None:
            yield
            return
        # The bound is ACL2's (`fn-sbud-verdict`); the scenario stands in a
        # verdict that refuses after BOUND admissions.
        admitted = [0]
        original = run_store.publication_admissible

        def publication_admissible(store, bridge=None, kind="article"):
            admitted[0] += 1
            return admitted[0] <= bound

        run_store.publication_admissible = publication_admissible
        try:
            yield
        finally:
            run_store.publication_admissible = original

    # -- host entry points --------------------------------------------------
    @staticmethod
    def post(root: Path, message_id: str, payload: bytes, groups) -> int:
        target = root / "article-{}".format(hashlib.sha256(payload).hexdigest()[:8])
        target.write_bytes(payload)
        return run_store.command_post(SimpleNamespace(
            store=root / "store", message_id=message_id, payload=target,
            group=list(groups), charge=None, inject_fault=None))

    @staticmethod
    def build_bundles(root: Path, bids) -> None:
        """Write the BPv7 bundle octets the BPA holds for each carried BID.

        Nothing here spells a BPv7 field: `fn-bpi-host-bundle-prefix` returns
        the indefinite-array head and the certified primary-block encoding,
        and the break stop code stands in for the blocks the boundary never
        interprets.  Distinct creation sequences make these distinct bundles
        one agent happens to carry, which is what the "same ADU under a fresh
        BID is a duplicate" check needs.
        """
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            def eid(ssp: bytes) -> str:
                return "(cons :dtn '" + bridge.literal(ssp) + ")"

            for bid in bids:
                form = ("(fn-bpi-host-bundle-prefix (fn-bpp-make-block 0 0 {} {} {} "
                        "1000 {} {} nil nil))".format(
                            eid(b"//fn.lab/inbox"), eid(b"//sender.lab/"),
                            eid(b"//fn.lab/report"),
                            zlib.crc32(bid.encode("ascii")) + 1, 10 ** 15))
                child_module.bundle_path(root, bid).write_bytes(
                    run_store.acl2_octets(bridge.call(form)) + b"\xff")
        finally:
            bridge.close()

    @staticmethod
    def build_request(name: str) -> bytes:
        body = article(name)
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-adu")')
            msgid = bridge.extract_message_id(body)
            _archive, subject, _evidence = run_store.metadata(msgid, body)

            def text(value: bytes) -> str:
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = ["work:{}".format(name).encode("ascii"), subject,
                      child_module.SOURCE_EID.encode("ascii"),
                      run_bp_receive.DESTINATION.encode("ascii"),
                      run_bp_receive.POLICY_ID.encode("ascii"), b"origin:1",
                      b"wire-auth", b"terms:1"]
            form = ("(fn-bpa-encode (fn-bpa-make-request "
                    + " ".join(text(value) for value in fields)
                    + " '" + bridge.literal(body) + "))")
            return run_store.acl2_octets(bridge.call(form))
        finally:
            bridge.close()

    @staticmethod
    def receive(root: Path, bid: str, inventory: dict, *, deleter=None,
                pending_outcome=None):
        deleted: list[str] = []

        def delete(found: str) -> None:
            if deleter is not None:
                deleter(found)
            deleted.append(found)
            inventory.pop(found, None)

        result = run_bp_receive.receive_bpa_request(
            store_root=root / "store", inbox_root=root / "inbox",
            receipt_root=root / "receipts", bid=bid,
            inventory=lambda: list(inventory),
            download=lambda found: inventory[found], delete=delete,
            bundle=lambda found: child_module.bundle_for(root, found),
            source_eid=child_module.SOURCE_EID, pending_outcome=pending_outcome)
        return result, deleted

    def store_state(self, root: Path) -> StoreState:
        """Reopen through the real recovery path and read the recovered state."""
        try:
            store, bridge, records = run_bp_ingress.open_live_bp_store(
                root / "store", False)
        except Exception as error:
            return StoreState(-1, -1, -1, False, False,
                              "{}: {}".format(type(error).__name__, error))
        try:
            return StoreState(
                len(records), bridge.article_count(), bridge.pin_count(),
                bridge.lookup(child_module.BASELINE_MSGID.encode("ascii")) != b"",
                bridge.lookup(child_module.CAMPAIGN_MSGID.encode("ascii")) != b"",
                "recovering")
        finally:
            bridge.close()
            store.close()

    # -- templates and reference runs ---------------------------------------
    def template(self, scenario: str) -> Path:
        if scenario in self.templates:
            return self.templates[scenario]
        root = self.workdir / "templates" / scenario
        root.mkdir(parents=True)
        started = time.monotonic()
        with self.configured(scenario):
            run_store.Store(root / "store", True).initialize()
            if scenario in BP_SCENARIOS:
                (root / "request.adu").write_bytes(self.build_request("campaign"))
                self.build_bundles(root, (BASELINE_BID, child_module.CAMPAIGN_BID,
                                          child_module.RETRY_BID, "bid-again"))
                baseline = self.build_request("baseline")
                # The baseline receive installs the receiver journal's config
                # record, so a cut inside a journal publish lands on the
                # campaign request's own record rather than on configuration.
                result, deleted = self.receive(root, BASELINE_BID,
                                               {BASELINE_BID: baseline})
                assert result.outcome == "accepted" and deleted == [BASELINE_BID], result
                if scenario == "bp-retry":
                    # A complete receive whose BPA delete reply was lost: the
                    # receipt is committed and the BID is still in inventory.
                    request = (root / "request.adu").read_bytes()
                    try:
                        self.receive(root, child_module.CAMPAIGN_BID,
                                     {child_module.CAMPAIGN_BID: request},
                                     deleter=self.lost_delete_reply)
                    except run_bp_receive.BpReceiveDeletePending as pending:
                        assert pending.outcome == "accepted", pending.outcome
                    else:
                        raise AssertionError("bp-retry template deleted the BID")
            else:
                assert self.post(root, child_module.BASELINE_MSGID,
                                 child_module.BASELINE_PAYLOAD,
                                 child_module.GROUPS) == run_store.EXIT_OK
            if scenario == "sender-enqueue":
                assert self.post(root, child_module.CAMPAIGN_MSGID,
                                 child_module.CAMPAIGN_PAYLOAD,
                                 child_module.GROUPS) == run_store.EXIT_OK
                store, bridge, _records = run_store.open_live_store(root / "store", True)
                try:
                    journal = workflow_journal.WorkflowJournal(
                        root / "workflow", Acl2WorkflowReplay(bridge))
                    journal.open()
                    journal.initialize(child_module.WORKFLOW_CONFIG)
                    journal.close()
                finally:
                    bridge.close()
                    store.close()
        self.log("template {} built in {:.1f}s".format(
            scenario, time.monotonic() - started))
        self.templates[scenario] = root
        return root

    @staticmethod
    def lost_delete_reply(_bid: str) -> None:
        raise OSError("BPA delete reply was lost")

    def reference(self, scenario: str) -> Reference:
        """Run the scenario once with no kill; its result is the target state."""
        if scenario in self.references:
            return self.references[scenario]
        case = self.case_root(scenario, "reference")
        with self.configured(scenario):
            receipt = None
            if scenario in BP_SCENARIOS:
                request = (case / "request.adu").read_bytes()
                result, _deleted = self.receive(
                    case, child_module.CAMPAIGN_BID,
                    {child_module.CAMPAIGN_BID: request})
                outcome = result.outcome
                receipt = (hashlib.sha256(result.receipt_adu).hexdigest()
                           if result.receipt_adu else None)
            elif scenario == "sender-enqueue":
                self.enqueue(case)
                outcome = "accepted"
            else:
                code = self.post(case, child_module.CAMPAIGN_MSGID,
                                 child_module.CAMPAIGN_PAYLOAD, child_module.GROUPS)
                outcome = "accepted" if code == run_store.EXIT_OK else "refused"
            state = self.store_state(case)
        self.references[scenario] = Reference(outcome, state, receipt)
        self.log("reference {}: {} {}".format(scenario, outcome, state))
        return self.references[scenario]

    @staticmethod
    def enqueue(root: Path, resolve: bool = False):
        """Persist the campaign enqueue, or resolve an unresolved one."""
        store, bridge, _records = run_store.open_live_store(root / "store", True)
        try:
            replay = Acl2WorkflowReplay(bridge)
            journal = workflow_journal.WorkflowJournal(root / "workflow", replay)
            journal.open()
            try:
                values = child_module.enqueue_values()
                if resolve and replay.fenced():
                    journal.recover_intent(values, "committed")
                    return "recovered"
                if any(kind == "enqueue" for kind, _values in
                       (workflow_journal.decode_record(path.read_bytes())
                        for path in sorted(journal.records.iterdir()))):
                    return "duplicate"
                journal.persist_enqueue(values, lambda _values: True)
                return "accepted"
            finally:
                journal.close()
        finally:
            bridge.close()
            store.close()

    @staticmethod
    def workflow_records(root: Path):
        return tuple(workflow_journal.decode_record(path.read_bytes())
                     for path in sorted((root / "workflow" / "records").iterdir()))

    # -- one case ------------------------------------------------------------
    def case_root(self, scenario: str, label: str) -> Path:
        case = self.workdir / "cases" / "{}__{}".format(scenario, label)
        if case.exists():
            shutil.rmtree(case)
        case.parent.mkdir(parents=True, exist_ok=True)
        # The writer lock is copied, not removed: flock ownership dies with the
        # process, but an absent lock pathname is an invalid store, not a free
        # one, and the host refuses it rather than treating it as unlocked.
        shutil.copytree(self.template(scenario), case)
        return case

    def kill_at(self, scenario: str, cut, case: Path) -> tuple[str, str]:
        """Run the child to the cut and kill its group; return (line, stderr)."""
        ready_read, ready_write = os.pipe()
        control_read, control_write = os.pipe()
        command = [sys.executable, "tests/campaign/child.py",
                   "--scenario", scenario, "--component", cut.component,
                   "--point", cut.point, "--cut-id", cut.cut_id,
                   "--root", str(case), "--ready-fd", str(ready_write),
                   "--control-fd", str(control_read)]
        bound = self.max_transactions(scenario)
        if bound is not None:
            command += ["--max-transactions", str(bound)]
        environment = dict(os.environ)
        environment.setdefault("FN_ACL2_TIMEOUT_SECONDS", "1800")
        child = subprocess.Popen(
            command, cwd=ROOT, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            pass_fds=(ready_write, control_read), start_new_session=True,
            env=environment)
        os.close(ready_write)
        os.close(control_read)
        line = b""
        try:
            deadline = time.monotonic() + CHILD_READY_SECONDS
            while time.monotonic() < deadline:
                ready, _, _ = select.select([ready_read], [], [], 0.2)
                if ready:
                    line = os.read(ready_read, 256)
                    break
                if child.poll() is not None:
                    break
        finally:
            self.kill_group(child)
            os.close(ready_read)
            os.close(control_write)
            stderr = child.stderr.read().decode("utf-8", "replace")[-2000:]
            child.stdout.close()
            child.stderr.close()
        return line.decode("ascii", "replace"), stderr

    @staticmethod
    def kill_group(child: subprocess.Popen) -> None:
        """Kill only the group this campaign created, and reap the child."""
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            child.kill()
        try:
            child.wait(timeout=15)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=15)

    def observed(self, case: Path) -> dict:
        path = case / "observed.json"
        if not path.exists():
            return {}
        return json.loads(path.read_text())

    def run_case(self, scenario: str, cut) -> Failure | None:
        started = time.monotonic()
        case = self.case_root(scenario, cut.point)
        before = digest(case)
        checks: list[str] = []
        line, stderr = self.kill_at(scenario, cut, case)
        after = digest(case)
        observed = self.observed(case)
        expected_line = "READY {}\n".format(cut.cut_id)
        if line != expected_line:
            checks.append("cut not reached: line={!r} stderr={}".format(line, stderr))
            return self.failure(scenario, cut, checks, before, after,
                                "not-run", observed, started)
        with self.configured(scenario):
            checks += self.verify(scenario, cut, case, observed)
            state = self.store_state(case)
        if not checks:
            return None
        return self.failure(scenario, cut, checks, before, after,
                            state.replay, observed, started)

    @staticmethod
    def failure(scenario, cut, checks, before, after, replay, observed, started):
        return Failure(scenario=scenario, cut=cut.cut_id, path=cut.path,
                       model=cut.model, checks=checks, before_digest=before,
                       after_digest=after, acl2_replay=replay,
                       observed=observed, seconds=time.monotonic() - started)

    # -- the checks ----------------------------------------------------------
    def verify(self, scenario: str, cut, case: Path, observed: dict) -> list[str]:
        checks: list[str] = []
        reference = self.reference(scenario)
        if scenario not in self.template_states:
            self.template_states[scenario] = self.store_state(self.template(scenario))
        template_state = self.template_states[scenario]
        recovered = self.store_state(case)
        if recovered.replay != "recovering":
            return ["reopen through the real recovery path failed: {}".format(
                recovered.replay)]
        # Acknowledged content and the pins that belong to it survive.
        if not recovered.baseline_present:
            checks.append("baseline article lost")
        if recovered.articles < template_state.articles:
            checks.append("article count fell from {} to {}".format(
                template_state.articles, recovered.articles))
        if recovered.pins < template_state.pins:
            checks.append("pin count fell from {} to {}".format(
                template_state.pins, recovered.pins))
        # Absent or complete, never partial: the record count and the replayed
        # article count move together, and by at most this one operation.
        interrupted = recovered.records - template_state.records
        if interrupted not in (0, 1):
            checks.append("record count moved by {}".format(interrupted))
        if recovered.articles - template_state.articles != interrupted:
            checks.append("records and articles disagree: {} vs {}".format(
                interrupted, recovered.articles - template_state.articles))
        # The expectation is about the record *this operation* publishes: a
        # scenario whose template already holds the article (a retry) starts
        # with it present, and the cut still may not add a second one.
        if cut.record == "absent" and interrupted:
            checks.append("a record was published at a cut that cannot publish")
        if cut.record == "present":
            if not recovered.campaign_present:
                checks.append("record absent at a cut that had already published")
            elif not template_state.campaign_present and interrupted != 1:
                checks.append("the published record is not the interrupted one")
        # What the host told the world before the kill, against the table and
        # against the recovered state.
        checks += self.check_acknowledgement(cut, observed, recovered)
        # The byte model's own answer: what it admits at this cut.
        checks += self.check_model_images(scenario, cut, recovered)
        # The retry, and the state it must reach.
        checks += getattr(self, "retry_" + scenario.replace("-", "_"))(
            case, cut, reference, observed)
        return checks

    def check_model_images(self, scenario: str, cut, recovered) -> list[str]:
        """The recovered record count is one the byte model admits here.

        crash model v2 section 5.1 step 2, at the level the kernel predicate
        constrains.  The model state at the cut comes from fn-bs-run over
        the program constant applied to the imported template store; the
        admissible set is enumerated over the whole-or-lost choices of its
        pending list.  A count outside the set is a counterexample to K1/K2
        and is reported with that pending list.
        """
        if not self.model_images:
            return []
        program = model_images_module.PROGRAM_OF.get((cut.component, cut.path))
        if program is None:
            return []
        key = "{}/{}".format(scenario, cut.cut_id)
        try:
            if self.model_bridge is None:
                self.model_bridge = model_images_module.ModelBridge()
            if key not in self.model_sets:
                self.model_sets[key] = model_images_module.images_at_cut(
                    self.model_bridge, self.template(scenario) / "store",
                    model_images_module.program_form(program, cut.point),
                    model_images_module.cut_index(program, cut.point))
        except Exception as error:
            return ["model image set unavailable: {}: {}".format(
                type(error).__name__, error)]
        admitted = self.model_sets[key]
        # Log what the model said, so a green run is not mistaken for a
        # vacuous one: an empty or singleton set that happens to contain the
        # recovered count is visible here, not hidden behind "ok".
        self.log("    model {}: admits {} records, recovered {}, pending {}".format(
            cut.cut_id, admitted.record_counts, recovered.records,
            " ".join(admitted.pending.split())))
        if recovered.records not in admitted.record_counts:
            return ["recovered {} records; the byte model admits {} at this "
                    "cut (pending {})".format(recovered.records,
                                              admitted.record_counts,
                                              admitted.pending)]
        return []

    @staticmethod
    def check_acknowledgement(cut, observed: dict, recovered: StoreState) -> list[str]:
        checks = []
        if not observed:
            return ["the cut left no pre-kill observation"]
        seen = set()
        if observed.get("receipt_sha256"):
            seen.add("receipt")
        if observed.get("bpa_deleted"):
            seen.add("bpa-delete")
        declared = set(cut.acknowledged)
        if seen != declared:
            checks.append("acknowledgement {} but the table declares {}".format(
                sorted(seen) or ["none"], sorted(declared) or ["none"]))
        if "receipt" in seen and not recovered.campaign_present:
            checks.append("a receipt was acknowledged without a durable record")
        return checks

    def retry_cross_post(self, case, cut, reference, observed) -> list[str]:
        checks = []
        code = self.post(case, child_module.CAMPAIGN_MSGID,
                         child_module.CAMPAIGN_PAYLOAD, child_module.GROUPS)
        if code != run_store.EXIT_OK:
            checks.append("retry exited {}".format(code))
        checks += self.compare(self.store_state(case), reference.state)
        # A second retry is a duplicate, not a second article or pin.
        if self.post(case, child_module.CAMPAIGN_MSGID,
                     child_module.CAMPAIGN_PAYLOAD, child_module.GROUPS) != run_store.EXIT_OK:
            checks.append("second retry did not report a duplicate")
        checks += self.compare(self.store_state(case), reference.state,
                               label="after a duplicate retry")
        return checks

    def retry_bp(self, case, cut, reference, observed, expect_refusal=False) -> list[str]:
        checks = []
        request = (case / "request.adu").read_bytes()
        bid = child_module.CAMPAIGN_BID
        inventory = {} if observed.get("bpa_deleted") else {bid: request}
        if not inventory:
            bid = child_module.RETRY_BID
            inventory = {bid: request}
        try:
            result, _deleted = self.receive(case, bid, inventory)
        except run_bp_receive.BpReceiveError as error:
            if "pending" not in str(error):
                return checks + ["retry raised {}".format(error)]
            # Uncertain stays uncertain until an operator resolves it: the
            # host refuses to guess the outcome of a durable receipt intent.
            try:
                result, _deleted = self.receive(case, bid, {bid: request},
                                                pending_outcome="committed")
            except run_bp_receive.BpReceiveError as second:
                return checks + ["resolved retry raised {}".format(second)]
        except run_bp_receive.BpReceiveDeletePending as pending:
            result = run_bp_receive.ReceiveResult(pending.outcome,
                                                  pending.receipt_adu,
                                                  pending.staged_path)
        if expect_refusal:
            if result.outcome != reference.outcome:
                checks.append("retry outcome {} not the reference {}".format(
                    result.outcome, reference.outcome))
            checks += self.compare(self.store_state(case), reference.state)
            return checks
        if result.outcome not in ("accepted", "duplicate"):
            checks.append("retry outcome {}".format(result.outcome))
        checks += self.compare(self.store_state(case), reference.state)
        receipt = hashlib.sha256(result.receipt_adu).hexdigest()
        if reference.receipt_sha256 and receipt != reference.receipt_sha256:
            checks.append("receipt bytes differ from the reference run")
        if observed.get("receipt_sha256") and receipt != observed["receipt_sha256"]:
            checks.append("receipt bytes differ from the acknowledged receipt")
        # A fresh BID carrying the same ADU is a duplicate, and regenerates
        # the same receipt rather than charging a second article.
        again, _deleted = self.receive(case, "bid-again", {"bid-again": request})
        if again.outcome != "duplicate":
            checks.append("repeat outcome {}".format(again.outcome))
        if hashlib.sha256(again.receipt_adu).hexdigest() != receipt:
            checks.append("regenerated receipt is not byte-identical")
        checks += self.compare(self.store_state(case), reference.state,
                               label="after a duplicate retry")
        return checks

    def retry_bp_receive(self, case, cut, reference, observed):
        return self.retry_bp(case, cut, reference, observed)

    def retry_bp_retry(self, case, cut, reference, observed):
        return self.retry_bp(case, cut, reference, observed)

    def retry_capacity_refusal(self, case, cut, reference, observed):
        return self.retry_bp(case, cut, reference, observed, expect_refusal=True)

    def retry_sender_enqueue(self, case, cut, reference, observed) -> list[str]:
        checks = []
        try:
            records = self.workflow_records(case)
        except Exception as error:
            return ["a durable workflow record did not decode: {}".format(error)]
        enqueues = [values for kind, values in records if kind == "enqueue"]
        if len(enqueues) > 1:
            checks.append("{} enqueue records".format(len(enqueues)))
        try:
            self.enqueue(case, resolve=True)
        except Exception as error:
            return checks + ["retry raised {}: {}".format(type(error).__name__, error)]
        final = self.workflow_records(case)
        if sum(1 for kind, _values in final if kind == "enqueue") != 1:
            checks.append("the retry did not leave exactly one enqueue record")
        checks += self.compare(self.store_state(case), reference.state)
        return checks

    @staticmethod
    def compare(state: StoreState, reference: StoreState, label="") -> list[str]:
        suffix = " {}".format(label) if label else ""
        if (state.records, state.articles, state.pins) != (
                reference.records, reference.articles, reference.pins):
            return ["recovered state{} is {} not the reference {}".format(
                suffix, (state.records, state.articles, state.pins),
                (reference.records, reference.articles, reference.pins))]
        return []

    # -- the campaign --------------------------------------------------------
    def run(self) -> Report:
        report = Report()
        report.uncovered = ["{}: {}".format(cut.cut_id, cut.uncovered)
                            for cut in cuts_module.uncovered_cuts()]
        report.model_gaps = ["{}: {}".format(cut.cut_id, cut.gap)
                             for cut in cuts_module.model_gaps()]
        started = time.monotonic()
        for scenario, cut in cuts_module.pairs(self.quick):
            if self.only and cut.cut_id not in self.only:
                continue
            if self.scenarios and scenario not in self.scenarios:
                continue
            case_started = time.monotonic()
            failure = self.run_case(scenario, cut)
            elapsed = time.monotonic() - case_started
            report.pairs += 1
            report.timings["{}/{}".format(scenario, cut.cut_id)] = elapsed
            if failure is not None:
                report.failures.append(failure)
            self.log("{:<16} {:<34} {:>6.1f}s {}".format(
                scenario, cut.cut_id, elapsed,
                "FAIL: " + "; ".join(failure.checks) if failure else "ok"))
        report.seconds = time.monotonic() - started
        return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="run the marked subset of cuts only")
    parser.add_argument("--scenario", action="append", dest="scenarios")
    parser.add_argument("--cut", action="append", dest="only",
                        help="run only these cut ids (component:point); "
                             "repeatable. For checking a newly added cut "
                             "without paying for the whole table.")
    parser.add_argument("--json", default=None,
                        help="write the report here; a relative path is "
                             "under the worktree this was invoked from")
    parser.add_argument("--model-images", action="store_true",
                        help="also check the recovered store against the byte "
                             "model's admissible image set at each cut")
    parser.add_argument("--keep", action="store_true",
                        help="keep the case directories for inspection")
    args = parser.parse_args(argv)
    cuts_module.verify_table()
    workdir = Path(tempfile.mkdtemp(prefix="fn-campaign-"))
    try:
        campaign = Campaign(workdir, quick=args.quick,
                            scenarios=tuple(args.scenarios) if args.scenarios else None,
                            log=lambda message: print(message, flush=True),
                            model_images=args.model_images,
                            only=tuple(args.only) if args.only else None)
        report = campaign.run()
    finally:
        if not args.keep:
            shutil.rmtree(workdir, ignore_errors=True)
        else:
            print("cases kept in {}".format(workdir))
    body = json.dumps(report.as_json(), indent=2, sort_keys=True)
    if args.json:
        # Anchored on the invoking worktree, never on the process's working
        # directory: a lane's report must not land in another checkout.
        target = evidence_path(args.json, deploy_gate.repo_root(), "")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(body + "\n")
        print("report: {}".format(target))
    print("pairs={} failures={} seconds={:.1f}".format(
        report.pairs, len(report.failures), report.seconds))
    for failure in report.failures:
        print(json.dumps(failure.as_json(), indent=2, sort_keys=True))
    return 1 if report.failures else 0


if __name__ == "__main__":
    sys.exit(main())
