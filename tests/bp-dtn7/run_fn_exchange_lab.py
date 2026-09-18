#!/usr/bin/env python3
"""Actual fn → BPv7 → fn exchange, lost receipt, retry and durable return decision.

A trusted loopback laboratory profile, not authenticated remote service or a
power-loss qualification. All article/work/receipt decisions execute in ACL2.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
from pathlib import Path
import subprocess
import sys
import tempfile

from lab_bpa import LabBpa, ROOT, verify_build
from fn_sender_lab import Sender, ARTICLE, CONFIG, create_sender, article_snapshot
from tools import run_bp_ingress, run_store, workflow_journal


def inbox_only(records):
    if records:
        raise RuntimeError('receipt inbox unexpectedly contains sender records')
    return ()


def receive_request(bpa, run, bid):
    from tools.run_bp_receive import receive_bpa_request
    return receive_bpa_request(
        store_root=run / 'b-store', inbox_root=run / 'b-inbox',
        receipt_root=run / 'b-receipts', bid=bid, source_eid='dtn://bp-a',
        inventory=bpa.client.inventory, download=bpa.download, delete=bpa.client.delete,
        local_policy_authorized=True)


def source_snapshot():
    paths = list((ROOT / "books").glob("*.lisp")) + list((ROOT / "host").glob("*.lisp"))
    paths += list((ROOT / "tools").glob("*.py"))
    paths += list((ROOT / "tests/bp-dtn7").glob("*.py"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dtn7-repo', required=True, type=Path)
    parser.add_argument('--run-base', type=Path, default=ROOT / 'build/bp-fn-exchange')
    args = parser.parse_args()
    checkout = args.dtn7_repo.resolve()
    pinned = verify_build(checkout)
    args.run_base.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='exchange-', dir=args.run_base)).resolve()
    a = LabBpa(checkout, run, 'a', 'bp-a', 'receipts', 'fn.lab', 32401, 32411, 32412)
    b = LabBpa(checkout, run, 'b', 'fn.lab', 'inbox', 'bp-a', 32402, 32412, 32411)
    report = {'schema': 1, 'status': 'running', 'pinned_bpa': pinned,
              'revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              'a_policy': 'explicitly trusted loopback lab, no cryptographic verification',
              'run': str(run), 'assertions': {}}
    report['invocation'] = [sys.executable, *sys.argv]
    report['versions'] = {'python': sys.version, 'platform': platform.platform(),
        'dtnd': subprocess.check_output([str(checkout / 'target/release/dtnd'), '--version'], text=True).strip(),
        'cargo': subprocess.check_output(['cargo', '--version'], text=True).strip()}
    checks = report['assertions']
    report['source_sha256'] = source_snapshot()
    try:
        create_sender(run / 'a-store', run / 'source.article')
        run_store.Store(run / 'b-store', True).initialize()
        a.start()  # B is absent: useful work is queued without an interactive peer.
        with Sender(run / 'a-store', run / 'a-workflow') as sender:
            sender.enqueue()
            first_bid, request = sender.submit(a, txid=11, generation=0, label='request-first')
            assert sender.outstanding()
        a.wait_for(first_bid)
        a.stop()
        a.start()
        a.wait_for(first_bid)
        with Sender(run / 'a-store', run / 'a-workflow') as sender:
            assert sender.outstanding()
            assert not sender.bridge.fenced()
            # BPA inventory presence does not prove forwarding eligibility.
            # The pinned BPA can restart between initial persistence and its
            # DispatchPending/ForwardPending update. fn owns recovery: record
            # an explicit retry and submit identical application work anew.
            sender.request_retry(previous_generation=0)
            resumed_bid, resumed_request = sender.submit(
                a, txid=12, generation=1, label='request-after-restart')
        assert resumed_bid != first_bid and resumed_request == request
        a.wait_for(resumed_bid)
        checks['durable_sender_work_and_bundle_survive_contact_outage_and_restart'] = True
        checks['explicit_durable_retry_recovers_uncertain_bpa_forwarding'] = True
        report['sender_before_receipt'] = article_snapshot(run / 'a-store')

        b.start()
        b.wait_for(resumed_bid)
        first = receive_request(b, run, resumed_bid)
        assert first.outcome == 'accepted' and first.receipt_adu
        assert resumed_bid not in b.client.inventory()
        report['receiver_first'] = article_snapshot(run / 'b-store')
        receipts_before = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in (run / 'b-receipts/records').iterdir()}
        lost_receipt = first.receipt_adu  # Intentionally never submitted to BP.
        checks['first_receipt_deliberately_lost_after_durable_receiver_decision'] = True
        b.stop()
        b.start()

        with Sender(run / 'a-store', run / 'a-workflow') as sender:
            assert sender.outstanding()
            sender.request_retry(previous_generation=1)
            retry_bid, retry_request = sender.submit(a, txid=13, generation=2, label='request-retry')
        assert retry_bid not in (first_bid, resumed_bid) and retry_request == request
        b.wait_for(retry_bid)
        second = receive_request(b, run, retry_bid)
        assert second.outcome == 'duplicate' and second.receipt_adu == lost_receipt
        assert retry_bid not in b.client.inventory()
        report['receiver_retry'] = article_snapshot(run / 'b-store')
        receipts_after = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (run / 'b-receipts/records').iterdir()}
        assert receipts_before == receipts_after
        checks['new_bid_retry_regenerates_exact_receipt_after_receiver_reopen'] = True
        checks['retry_adds_no_article_pin_or_receipt_decision'] = True

        receipt_bid = b.submit(second.receipt_adu, CONFIG['local-eid'], 'receipt-return')
        a.wait_for(receipt_bid)
        inbox = workflow_journal.WorkflowJournal(run / 'a-inbox', inbox_only)
        inbox.open()
        try:
            staged = run_bp_ingress._staged_item(
                inbox, workflow_journal, receipt_bid, a.client.inventory, a.download)
            staged_bid, receipt = workflow_journal.decode_inbound(staged.read_bytes())
            assert staged_bid == receipt_bid and receipt == lost_receipt
            with Sender(run / 'a-store', run / 'a-workflow') as sender:
                assert sender.outstanding()
                sender.accept_receipt(receipt)
                assert not sender.outstanding()
            a.client.delete(receipt_bid)
        finally:
            inbox.close()
        with Sender(run / 'a-store', run / 'a-workflow') as sender:
            assert not sender.outstanding()
            assert not sender.bridge.fenced()
        report['sender_after_receipt'] = article_snapshot(run / 'a-store')
        assert report['sender_before_receipt'] == report['sender_after_receipt']
        checks['return_receipt_traverses_actual_bp_and_commits_sender_decision'] = True
        checks['sender_decision_survives_reopen_and_preserves_independent_archive'] = True
        checks['all_bpa_listeners_ipv6_loopback'] = True
        report.update(status='passed', request_bid=first_bid, resumed_bid=resumed_bid, retry_bid=retry_bid,
                      receipt_bid=receipt_bid, request_sha256=hashlib.sha256(request).hexdigest(),
                      receipt_sha256=hashlib.sha256(receipt).hexdigest(),
                      article_sha256=hashlib.sha256(ARTICLE).hexdigest())
    except BaseException as error:
        report.update(status='failed', error=repr(error))
        raise
    finally:
        b.stop()
        a.stop()
        report['source_after_sha256'] = source_snapshot()
        report['sources_unchanged'] = report['source_sha256'] == report['source_after_sha256']
        if not report['sources_unchanged']:
            report.update(status='failed', error='sources changed during exchange')
        report['limitations'] = [
            'BPA inventory alone does not establish forwarding readiness; fn explicitly retries after sender restart. The original bundle may remain inert or arrive as another duplicate.',
            'Explicit trusted local A-POLICY; no authenticated remote peer or author signature.',
            'No LTP, multi-relay/contact-schedule liveness, private encryption, or mission qualification.',
            'Real local process/file recovery; no hardware power-loss or physical media qualification.',
            'Receipt loss is application-level omission after decision; BPA restart uses SIGTERM and waits for process exit; stop logs record any SIGKILL fallback.',
            'Pinned BPA/native decoder, Python I/O and stated filesystem behavior remain trusted boundaries.']
        (run / 'evidence.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'status': report['status'], 'evidence': str(run / 'evidence.json')}))
    if report['status'] != 'passed':
        raise RuntimeError(report.get('error', 'exchange failed'))


if __name__ == '__main__':
    main()
