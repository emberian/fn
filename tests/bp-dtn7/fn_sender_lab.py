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
