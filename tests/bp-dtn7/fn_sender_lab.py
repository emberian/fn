"""Actual ACL2-backed sender operations for the pinned BP laboratory exchange."""
from __future__ import annotations

from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools import run_store, run_bp_ingress
from tools.workflow_bridge import Acl2WorkflowReplay
from tools.workflow_journal import WorkflowJournal, JournalError

CONFIG = {'local-eid': 'dtn://bp-a/receipts', 'peer-eid': 'dtn://fn.lab/inbox',
          'policy-id': 'bp-lab-policy-v0', 'receipt-authority': 'dtn://fn.lab/issuer',
          'bp-lifetime': 300, 'incarnation': 'origin-a-lab-1',
          'authorization-context': 'trusted-loopback-lab-1'}
WORK_ID = 'work:letter:1'
MESSAGE_ID = '<bp-exchange@fn.example>'
ARTICLE = (b'Message-ID: <bp-exchange@fn.example>\r\nNewsgroups: fn.letters\r\n'
           b'Subject: A delayed letter and a lost receipt\r\n'
           b'From: lab sender <sender@fn.example>\r\n\r\n'
           b'The letter survives the contact; its promise survives the bundle.\r\n')


def text_form(value: str) -> str:
    return "(fn-store-octets->string '" + run_store.Acl2Store.literal(value.encode('utf-8')) + ')'


def create_sender(store_root: Path, article_path: Path):
    run_store.Store(store_root, True).initialize()
    article_path.write_bytes(ARTICLE)
    if run_store.command_post(SimpleNamespace(
            store=store_root, message_id=MESSAGE_ID, payload=article_path,
            group=['fn.letters'], charge=None, inject_fault=None)) != 0:
        raise RuntimeError('sender article publication failed')


class Sender:
    def __init__(self, store_root: Path, journal_root: Path):
        self.store, self.acl2, self.records = run_store.open_live_store(store_root, True)
        try:
            self.bridge = Acl2WorkflowReplay(self.acl2)
            self.journal = WorkflowJournal(journal_root, self.bridge)
            self.journal.open()
            self.acl2.call('(ld "host/bp-outbound-host.lisp" :ld-error-action :return :ld-error-triples t)')
        except BaseException:
            self.close()
            raise

    def close(self):
        if hasattr(self, 'journal'):
            self.journal.close()
        if hasattr(self, 'acl2'):
            self.acl2.close()
        if hasattr(self, 'store'):
            self.store.close()

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def enqueue(self):
        self.journal.initialize(CONFIG)
        archive, subject, _evidence = run_store.metadata(MESSAGE_ID.encode(), ARTICLE)
        values = {'txid': 10, 'tx-generation': 0, 'work-id': WORK_ID,
                  'msgid': MESSAGE_ID, 'immutable-subject': subject.decode(),
                  'archive-obligation-id': archive.decode(),
                  'forward-obligation-id': 'forward:letter:1',
                  'peer-eid': CONFIG['peer-eid'], 'policy-id': CONFIG['policy-id'],
                  'terms-id': 'keep-until-authorized-release:lab-v0'}
        # The callback is only an additional host gate; the ACL2 preflight checks
        # the actual recovered article/subject/archive binding before publication.
        self.journal.persist_enqueue(values, lambda _v: True)

    def submit(self, bpa, *, txid: int, generation: int, label: str):
        values = {'txid': txid, 'tx-generation': 0, 'work-id': WORK_ID,
                  'attempt-id': f'attempt:{generation}', 'attempt-generation': generation,
                  'local-eid': CONFIG['local-eid'], 'peer-eid': CONFIG['peer-eid'],
                  'policy-id': CONFIG['policy-id'], 'bp-lifetime': CONFIG['bp-lifetime']}
        projected = []

        def external_action():
            adu = run_store.acl2_octets(self.acl2.call(
                '(fn-bpo-host-request-adu ' + text_form(WORK_ID) + ' state)'))
            if not adu:
                raise RuntimeError('ACL2 refused the durable work projection')
            projected.append(adu)
            return bpa.submit(adu, CONFIG['peer-eid'], label, CONFIG['bp-lifetime'])

        bid = self.journal.persist_attempt_then_call(values, external_action)
        self.journal.publish('transport', {
            'work-id': WORK_ID, 'attempt-id': values['attempt-id'],
            'attempt-generation': generation, 'status': 'bpa-submit-replied'})
        return bid, projected[0]

    def request_retry(self, previous_generation: int):
        self.journal.publish("retry-request", {
            "work-id": WORK_ID, "attempt-id": f"attempt:{previous_generation}",
            "attempt-generation": previous_generation, "policy-id": CONFIG["policy-id"]})

    def accept_receipt(self, adu: bytes, txid=20):
        if not isinstance(adu, bytes) or len(adu) > 65538:
            raise ValueError('receipt ADU outside lab profile')
        suffix = " '" + self.acl2.literal(adu) + f' {txid} 0 t state)'
        # `t` is this explicitly trusted loopback experiment's A-POLICY premise,
        # not a conclusion from any field inside the receipt.
        if not run_store.acl2_boolean(self.acl2.call('(fn-bpo-host-receipt-validp' + suffix)):
            raise JournalError('ACL2 refused returned receipt')
        fields = [run_store.acl2_octets(self.acl2.call(
            f'(fn-bpo-host-receipt-field-octets {index}' + suffix)).decode('utf-8')
                  for index in range(9)]
        names = ('receipt-id', 'work-id', 'immutable-subject', 'issuer-eid', 'peer-eid',
                 'policy-id', 'incarnation', 'authorization-context', 'terms-id')
        values = dict(zip(names, fields))
        values.update({'txid': txid, 'tx-generation': 0})
        self.journal.publish_intent('receipt-intent', values)
        self.journal.publish_outcome(txid, 0, 'ordinary', 'durable')
        if self.outstanding():
            raise RuntimeError('receipt decision did not satisfy the workflow')

    def outstanding(self):
        form = ('(fn-bp-work-outstandingp (fn-bp-find-work ' + text_form(WORK_ID) +
                " (fn-bp-state-works (f-get-global 'fn-workflow-state state))))")
        return run_store.acl2_boolean(self.acl2.call(form))


def article_snapshot(root: Path):
    store, acl2, records = run_bp_ingress.open_live_bp_store(root, writable=False)
    try:
        payload = acl2.lookup(MESSAGE_ID.encode())
        result = {'records': len(records), 'articles': acl2.article_count(),
                  'pins': acl2.pin_count(), 'exact_article': payload == ARTICLE}
        if result != {'records': 1, 'articles': 1, 'pins': 1, 'exact_article': True}:
            raise RuntimeError(f'article/pin snapshot differs: {result}')
        return result
    finally:
        acl2.close()
        store.close()


# -----------------------------------------------------------------------------
# Running the exchange under a contact plan (C2-06)
#
# Two windows and one expiry.  The scheduler decides which work each contact
# tick attempts; `tools/workflow_journal.py` still owns durability, and ACL2
# still grants the submit permission.  Nothing here selects a work.

import http.server                                          # noqa: E402
import json                                                 # noqa: E402
import socket                                               # noqa: E402
import socketserver                                         # noqa: E402
import threading                                            # noqa: E402

from tools import scheduler as fn_scheduler                  # noqa: E402

# One contact window that closes before the letter is through, a second window
# after it, and a bundle whose lifetime runs out in between.  The expiry marks
# the item; it releases nothing, and the work stays in the queue.
CONTACT_PLAN = {
    "peer": CONFIG["peer-eid"],
    "config": {"queue-bound": 8, "aging-limit": 2, "retry-bound": 2},
    "works": [{"work-id": WORK_ID, "class": "article", "size": len(ARTICLE)}],
    "windows": [{"start": 0, "end": 1000, "ticks": [10, 20]},
                {"start": 5000, "end": 6000, "ticks": [5100, 5200]}],
    "expiries": [{"at-tick": 2, "work-id": WORK_ID,
                  "creation-time": 1599999000000, "lifetime": 1000,
                  "monotonic": 5100, "wall": 1600000000000,
                  "wall-error": 5000, "has-wall": True}],
}


class _MockServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    address_family = socket.AF_INET6


class _MockHandler(http.server.BaseHTTPRequestHandler):
    """The handler `tests/test_bpa_dtn7.py` uses, serving one bundle store."""

    bundles: dict = {}

    def log_message(self, _format, *_args):
        pass

    def do_GET(self):
        if self.path == "/status/bundles":
            body = json.dumps(sorted(self.__class__.bundles)).encode("utf-8")
            status, headers = 200, {"Content-Type": "application/json"}
        elif self.path.startswith("/download?"):
            bid = self.path.split("=", 1)[1]
            body = self.__class__.bundles.get(bid)
            status = 200 if body is not None else 404
            headers = {"Content-Type": "application/octet-stream"}
            body = body or b"not found"
        elif self.path.startswith("/delete?"):
            self.__class__.bundles.pop(self.path.split("=", 1)[1], None)
            status, headers, body = 200, {}, b"deleted"
        else:
            status, headers, body = 404, {}, b"not found"
        self.send_response(status)
        for name, value in headers.items():
            self.send_header(name, value)
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass


class MockBpa:
    """The mock BPA, for when the pinned dtn7-rs build is unavailable.

    It serves the dtn7-rs HTTP surface `tools/bpa_dtn7.BpaDtn7Client` speaks
    and mints a transport identifier for a submitted ADU.  No BPv7 bundle is
    transmitted and no second node exists: this exercises the scheduler,
    journal and ACL2 composition only, and any report that uses it must say
    so.  `tests/bp-dtn7/lab_bpa.LabBpa` is the real adapter.
    """

    profile = "mock-bpa: no BPv7 transmission, no peer, no receipt"

    def __init__(self):
        _MockHandler.bundles = {}
        self.server = _MockServer(("::1", 0), _MockHandler)
        self.thread = threading.Thread(target=self.server.serve_forever,
                                       daemon=True)
        self.thread.start()
        self.port = self.server.server_port
        self.submissions = []

    def submit(self, adu: bytes, destination: str, label: str, lifetime=300) -> str:
        if not isinstance(adu, bytes) or not 0 < len(adu) <= 65538:
            raise ValueError("outbound ADU outside lab profile")
        bid = f"dtn://mock/{label}-{len(self.submissions)}"
        _MockHandler.bundles[bid] = adu
        self.submissions.append((bid, destination, lifetime, adu))
        return bid

    def close(self):
        self.server.shutdown()


def scheduled_submit(sender, bpa, work_id: str, attempt_id: str, txid: int,
                     generation: int) -> bool:
    """One durable attempt, named by the scheduler.  Returns ACL2's verdict."""
    values = {"txid": txid, "tx-generation": 0, "work-id": work_id,
              "attempt-id": attempt_id, "attempt-generation": generation,
              "local-eid": CONFIG["local-eid"], "peer-eid": CONFIG["peer-eid"],
              "policy-id": CONFIG["policy-id"],
              "bp-lifetime": CONFIG["bp-lifetime"]}

    def external_action():
        adu = run_store.acl2_octets(sender.acl2.call(
            "(fn-bpo-host-request-adu " + text_form(work_id) + " state)"))
        if not adu:
            raise RuntimeError("ACL2 refused the durable work projection")
        return bpa.submit(adu, CONFIG["peer-eid"], attempt_id,
                          CONFIG["bp-lifetime"])

    try:
        sender.journal.persist_attempt_then_call(values, external_action)
    except JournalError:
        return False
    sender.journal.publish("transport", {
        "work-id": work_id, "attempt-id": attempt_id,
        "attempt-generation": generation, "status": "bpa-submit-replied"})
    return True


def run_contact_plan(sender, bpa, plan_document=None, *, next_tx=2000):
    """Drive the sender's attempts from a contact plan through the scheduler."""
    plan = fn_scheduler.plan_from(plan_document or CONTACT_PLAN)
    host = fn_scheduler.Acl2SchedulerHost(sender.acl2)
    log = fn_scheduler.DecisionLog(sender.journal.root)
    counter = {"tx": next_tx, "generation": 0}

    def attempt(work_id, attempt_id, tick):
        granted = scheduled_submit(sender, bpa, work_id, attempt_id,
                                   counter["tx"], counter["generation"])
        counter["tx"] += 1
        if granted:
            counter["generation"] += 1
        else:
            # A refused attempt leaves the work retryable; the scheduler
            # charges no retry for it, and the next window will pass over it.
            sender.journal.publish("transport", {
                "work-id": work_id, "attempt-id": attempt_id,
                "attempt-generation": counter["generation"],
                "status": "no-contact"})
        return granted

    outcomes = fn_scheduler.run_plan(plan, host, log, attempt)
    return {"outcomes": outcomes, "decisions": len(log.entries()),
            "submissions": len(getattr(bpa, "submissions", ())),
            "bpa_profile": getattr(bpa, "profile", "pinned dtn7-rs"),
            "outstanding": sender.outstanding()}
