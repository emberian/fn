#!/usr/bin/env python3
"""One finite author world; checked_queue bundles own every requested repair."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    pending = path.with_name(path.name + '.pending')
    pending.write_text(json.dumps(value, indent=2) + '\n')
    pending.replace(path)


def validate(plan, receipt_path=None):
    import certs
    import proof_repl as pr
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == plan['source_commit']
    assert digest(ROOT / 'tools/proof_repl.py') == plan['proof_repl_sha256']
    known = set(plan['qualified'])
    order = plan['source_order']
    assert len(order) == len(set(order)) and not known.intersection(order)
    assert set(plan['books']) == known | set(order)
    fingerprint = hashlib.sha256(json.dumps(plan, sort_keys=True).encode()).hexdigest()
    reusable = False
    if receipt_path and receipt_path.exists():
        reusable = json.loads(receipt_path.read_text()).get('plan_sha256') == fingerprint
    for book, row in plan['books'].items():
        path = ROOT / (book + '.lisp')
        assert digest(path) == row['sha256'], ('source changed', book)
        if not reusable:
            assert set(certs.closure(ROOT, book)) - {book} == set(row['ancestors']), book
            assert certs.closure_key(ROOT, book)[0] == row['key'], book
    for book in order:
        row = plan['books'][book]
        assert set(row['ancestors']) <= known, ('parent not present', book)
        if not reusable:
            path = ROOT / (book + '.lisp')
            text = path.read_text()
            assert not pr.attachment_events(text), ('source attachment', book)
            macros, _, _ = pr.source_event_inventory(path)
            pr.encapsulated(text, path.parent, set(), 20, 2000000, macros)
        known.add(book)
    assert set().union(*(set(certs.closure(ROOT, b)) for b in plan['entry_roots'])) == set(plan['qualified'])
    cache = Path(os.environ.get('FN_CERT_CACHE', '/home/fn/.cache/fn-certs'))
    for book in plan['qualified']:
        entries = certs.cached_entries(cache, plan['books'][book]['key'], lambda m:
            m.get('toolchain_identity') == plan['toolchain_identity'] and bool(m.get('fasl_sha256')))
        assert any(certs.usable_origin(m, str(ROOT)) for _, m in entries), ('qualified artifact unavailable', book)
    if receipt_path:
        save(receipt_path, {'plan_sha256': fingerprint, 'verdict': 'PASS',
                            'books': len(plan['books']), 'source': len(order)})


def start_ticks(pid):
    return int(Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[19])


def loaded_bindings(plan, state):
    assert set(plan['qualified']) == set(state['qualified_bindings']), 'loaded warm set changed'
    assert digest(ROOT / 'tools/proof_repl.py') == state['proof_repl_sha256']
    for book, initial in state['qualified_bindings'].items():
        row = plan['books'][book]
        assert {k: row[k] for k in ('sha256', 'key')} == initial, ('loaded warm parent changed', book)
        assert digest(ROOT / (book + '.lisp')) == initial['sha256'], book
    for book, sha in state['passed'].items():
        assert digest(ROOT / (book + '.lisp')) == sha, ('already-admitted source changed', book)


def same_server(state):
    import proof_repl as pr
    initial = state['server']
    current = pr.read_state(state['session'])
    assert current and current['pid'] == initial['pid'] and current['started_at'] == initial['started_at']
    assert start_ticks(current['pid']) == initial['start_ticks'], 'server process changed'
    current = pr.ask(state['session'], {'op': 'status'}, timeout=10)['state']
    assert current['pid'] == initial['pid'] and current['ready'], 'same server is not ready'


def invoke(args, log, limit):
    with log.open('w') as output:
        return subprocess.run([sys.executable, str(ROOT / 'tools/proof_repl.py'), *args], cwd=ROOT,
                              stdout=output, stderr=subprocess.STDOUT, timeout=limit).returncode


def replay(plan, state_path, session, logs, deadline):
    state = json.loads(state_path.read_text())
    assert state['session'] == session
    loaded_bindings(plan, state)  # Reject changed parents before even a status RPC.
    same_server(state)
    seen = set(plan['qualified']) | set(state['passed'])
    for book in plan['source_order']:
        if book in state['passed']:
            continue
        row = plan['books'][book]
        assert set(row['ancestors']) <= seen, (book, sorted(set(row['ancestors']) - seen))
        assert digest(ROOT / (book + '.lisp')) == row['sha256'], book
        state.update(phase='source', current=book)
        save(state_path, state)
        log = logs / (book.replace('/', '--') + '.log')
        print('SOURCE_BEGIN', book, str(log), flush=True)
        rc = invoke(['send-range', session, book, '--skip-includes', '--ld-local',
                     '--per-event-steps', '2000000', '--limit', '20'], log,
                    min(600, max(1, deadline - time.monotonic())))
        print('SOURCE_RESULT', book, rc, flush=True)
        if rc:
            state.update(phase='refused-retained', refusal=book)
            save(state_path, state)
            return rc
        state['passed'][book] = row['sha256']
        seen.add(book)
        save(state_path, state)
    state.update(phase='actual-roots-passed', current=None)
    save(state_path, state)
    return 0


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['validate', 'campaign', 'replay'])
    p.add_argument('--plan', type=Path, required=True)
    p.add_argument('--state', type=Path, required=True)
    p.add_argument('--logs', type=Path, required=True)
    p.add_argument('--session', required=True)
    p.add_argument('--queue', type=Path)
    p.add_argument('--seconds', type=int, default=3500)
    p.add_argument('--preflight-receipt', type=Path)
    a = p.parse_args()
    plan = json.loads(a.plan.read_text())
    validate(plan, a.preflight_receipt)
    if a.mode == 'validate':
        print('PREFLIGHT_PASS', len(plan['books']), len(plan['source_order']), flush=True)
        return 0
    assert 0 < a.seconds <= 3500
    a.logs.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + a.seconds
    if a.mode == 'replay':
        return replay(plan, a.state, a.session, a.logs, deadline)
    assert a.queue is not None and not a.state.exists() and not a.queue.exists()
    import proof_repl as pr
    # A fresh unique session makes cleanup on a start timeout unambiguous.
    assert not pr.session_dir(a.session).exists(), 'session directory already exists; choose a fresh name'
    scope = Path('/sys/fs/cgroup') / Path(Path('/proc/self/cgroup').read_text().strip().split(':', 2)[2]).relative_to('/')
    assert (scope / 'memory.max').read_text().strip() == '6442450944'
    assert (scope / 'memory.swap.max').read_text().strip() == '0'
    entry = ROOT / 'build' / (a.session + '-qualified-entry.lisp')
    entry.parent.mkdir(exist_ok=True)
    entry.write_text('(in-package "ACL2")\n' + ''.join('(include-book "../' + b + '")\n' for b in plan['entry_roots']))
    save(a.state, {'source_commit': plan['source_commit'], 'session': a.session, 'passed': {},
                   'phase': 'cached-start', 'owner_pid': os.getpid(), 'scope': str(scope),
                   'event_steps': 2000000, 'event_seconds': 20, 'seconds': a.seconds,
                   'proof_repl_sha256': plan['proof_repl_sha256'],
                   'qualified_bindings': {b: {k: plan['books'][b][k] for k in ('sha256', 'key')}
                                          for b in plan['qualified']}})
    attempted = False
    def terminate(_sig, _frame):
        raise SystemExit(143)
    signal.signal(signal.SIGTERM, terminate)
    signal.signal(signal.SIGINT, terminate)
    try:
        attempted = True  # A start timeout must also clean up its created session.
        rc = invoke(['start', a.session, str(entry.relative_to(ROOT))[:-5], '--cached-only',
                     '--load-limit', '20', '--limit', '20', '--load-timeout', '600',
                     '--idle-timeout', '61'], a.logs / 'start.log', min(600, a.seconds))
        if rc:
            return rc
        server = pr.read_state(a.session)
        assert server and server['ready']
        state = json.loads(a.state.read_text())
        state['server'] = {'pid': server['pid'], 'started_at': server['started_at'],
                           'start_ticks': start_ticks(server['pid'])}
        save(a.state, state)
        replay(plan, a.state, a.session, a.logs, deadline)
        # Ordinary source refusal retains the world. The sole coordinator
        # publishes a complete checked_queue bundle; no guessed nested path.
        while time.monotonic() < deadline:
            if a.queue.exists():
                running = a.queue.with_name(a.queue.name + '.running')
                a.queue.replace(running)
                code = subprocess.run(['bash', str(running)], cwd=ROOT,
                                      timeout=max(1, deadline - time.monotonic())).returncode
                print('BUNDLE_RESULT', code, flush=True)
            time.sleep(.2)
        return 0
    finally:
        if attempted:
            invoke(['stop', a.session], a.logs / 'stop.log', 12)


if __name__ == '__main__':
    raise SystemExit(main())
