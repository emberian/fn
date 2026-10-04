#!/usr/bin/env python3
"""Run an actual matcher graph probe in an explicitly loaned warm ACL2 world.

No cache miss fallback or proof replay. The source root identifies the admitted
matcher; the raw fixture additionally refuses missing, unverified or uncompiled
normal counterparts. Source admission is ONLY two numeric capacity definitions
read literally from the supplied wildmat-live book, not its theorems.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from proof_repl import forms
import native_trace

PREFIX = 'FN_MATCHER_GRAPH '
SUBJECTS = ('books/wildmat-cursor.lisp', 'books/wildmat-work.lisp', 'books/wildmat.lisp',
            'books/nntp-responses.lisp')
ASSETS = ('tools/native_heap_graph.lisp', 'tools/native_matcher_heap_probe.lisp', 'host/native/trace.lisp')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def report(text):
    rows = [json.loads(line[len(PREFIX):]) for line in text.splitlines() if line.startswith(PREFIX)]
    cases = []
    spans = [json.loads(line[len(native_trace.PREFIX):]) for line in text.splitlines()
             if line.startswith(native_trace.PREFIX)]
    summary = [s for s in spans if s.get('type') == 'summary']
    if len(summary) != 1 or summary[0].get('dropped') or summary[0].get('incomplete'):
        raise ValueError('incomplete allocation trace')
    for case in (row for row in rows if row['type'] == 'case'):
        states = [row for row in rows if row['type'] == 'state' and row['case_id'] == case['case_id']]
        done = [row for row in rows if row['type'] == 'done' and row['case_id'] == case['case_id']]
        if len(done) != 1 or [s['step'] for s in states] != list(range(done[0]['steps'] + 1)):
            raise ValueError('incomplete retained state trace')
        samples = [s for s in spans if s.get('type') == 'span' and s.get('phase') == 'matcher-round'
                   and s.get('operation_id') == case['case_id']]
        if len(samples) != 1 or samples[0].get('outcome') != 'returned':
            raise ValueError('missing matched allocation replay')
        cases.append(dict(case, steps=done[0]['steps'], matched=done[0]['matched'],
            max_owned_conses=max(s['owned']['conses'] for s in states),
            max_owned_direct_bytes=max(s['owned']['direct-bytes'] for s in states),
            max_union_conses=max(s.get('old_new_union', s['owned'])['conses'] for s in states),
            max_union_direct_bytes=max(s.get('old_new_union', s['owned'])['direct-bytes'] for s in states),
            allocation_sample=samples[0],
            over_bound_steps=[s['step'] for s in states if s['over_bound']],
            union_over_single_state_bound_steps=[s['step'] for s in states
                                                  if s.get('union_over_single_state_bound')]))
    if 'NATIVE_MATCHER_HEAP_PASS' not in text or len(cases) != 11:
        raise ValueError('actual matcher probe did not complete all cases')
    return {'scope': 'distinct EQ retained graph/direct primitive object bytes; not GC/allocator overhead, '
                     'production pricing, or whole process retained heap. The bound is owned cons cells '
                     'of one state; old/new union is measured separately. FN_TRACE measures cumulative '
                     'allocation during32 replays, not retained heap; graph walking is outside spans.',
            'cases': cases}


def literal(value):
    return '"' + str(value).replace('\\', '\\\\').replace('"', '\\"') + '"'


def remote_digests(host, root, names):
    code = 'import hashlib,json,pathlib,sys; print(json.dumps({p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in sys.argv[1:]}))'
    command = 'cd ' + shlex.quote(root) + ' && python3 -c ' + shlex.quote(code) + ' ' + \
              ' '.join(map(shlex.quote, names))
    return json.loads(subprocess.run(['ssh', host, command], capture_output=True, text=True,
                                    timeout=15, check=True).stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_root', nargs='?', type=Path)
    parser.add_argument('--report-only', type=Path, help='Analyze an existing complete raw log without a runtime')
    parser.add_argument('--live-book', type=Path)
    parser.add_argument('--warm', help='Explicitly loaned existing session name')
    parser.add_argument('--control-root', type=Path)
    parser.add_argument('--host', default='hbox')
    parser.add_argument('--remote-tree')
    args = parser.parse_args()
    if args.report_only:
        print(json.dumps(report(args.report_only.read_text()), indent=2))
        return
    if not all((args.source_root, args.live_book, args.warm, args.control_root, args.remote_tree)):
        parser.error('run needs source_root, --live-book, --warm, --control-root and --remote-tree')
    dest = ROOT / 'build/runtime-tests' / ('matcher-graph-' + uuid.uuid4().hex[:10])
    dest.mkdir(parents=True)
    snapshot = {str(path): digest(path) for path in
                [args.source_root / p for p in SUBJECTS] + [ROOT / p for p in ASSETS] +
                [args.live_book, Path(__file__)]}
    # Exact warm source coordinate, no remote source sync or replacement.
    remote_hashes = remote_digests(args.host, args.remote_tree, SUBJECTS)
    for name in SUBJECTS:
        expected = snapshot[str(args.source_root / name)]
        if expected != remote_hashes.get(name):
            raise SystemExit('REFUSED warm source differs or is missing: ' + name)
    # No definitions are rewritten or duplicated here: literal original forms.
    capacity_forms = [f for f in forms(args.live_book.read_text())
                      if any(f.startswith('(defun ' + name + ' ') for name in
                             ('fn-wml-capacity', 'fn-wml-owned-capacity'))]
    if len(capacity_forms) != 2:
        raise SystemExit('REFUSED exact numeric capacity definitions missing')
    remote = '/tank/fn/scratch/matcher-graph-' + uuid.uuid4().hex
    subprocess.run(['ssh', args.host, 'mkdir -p ' + shlex.quote(remote + '/tools') + ' ' +
                    shlex.quote(remote + '/tests') + ' ' + shlex.quote(remote + '/host/native')],
                   check=True, timeout=15)
    for name in ASSETS:
        subprocess.run(['scp', '-q', str(ROOT / name), args.host + ':' + remote + '/' + name],
                       check=True, timeout=15)
    asset_hashes = remote_digests(args.host, remote, ASSETS)
    if asset_hashes != {name: snapshot[str(ROOT / name)] for name in ASSETS}:
        raise SystemExit('REFUSED copied diagnostic assets differ')
    source = '(in-package "ACL2")\n' + '\n'.join(capacity_forms) + '\n' + \
             '(defttag :fn-matcher-heap-debug)\n' + \
             '(progn! (set-raw-mode t) (defparameter *fnmg-probe-root* ' + literal(remote) + ') ' + \
             '(load ' + literal(remote + '/tools/native_matcher_heap_probe.lisp') + '))\n'
    (dest / 'input.lisp').write_text(source)
    (dest / 'sources.json').write_text(json.dumps({'sha256': snapshot, 'warm_tree': args.remote_tree,
        'warm_session': args.warm, 'remote_asset_root': remote, 'numeric_book_only': str(args.live_book)}, indent=2)+'\n')
    with (dest / 'repl.log').open('w') as log:
        result = subprocess.run([sys.executable, str(args.control_root / 'tools/proof_repl.py'), 'send',
            args.warm, '-', '--host', args.host, '--remote-tree', args.remote_tree, '--no-sync', '--full'],
            input=source, text=True, stdout=log, stderr=subprocess.STDOUT,
            cwd=args.control_root, timeout=90)
    for name, expected in snapshot.items():
        if digest(Path(name)) != expected:
            raise SystemExit('REFUSED source changed during observation: ' + name)
    if remote_digests(args.host, args.remote_tree, SUBJECTS) != remote_hashes or \
            remote_digests(args.host, remote, ASSETS) != asset_hashes:
        raise SystemExit('REFUSED remote source changed during observation')
    if result.returncode:
        raise SystemExit('REFUSED actual probe; preserved log ' + str(dest / 'repl.log'))
    summary = report((dest / 'repl.log').read_text())
    (dest / 'report.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(dest / 'report.json')
    for case in summary['cases']:
        print('case', case['case_id'], 'steps', case['steps'], 'owned cons/bytes',
              case['max_owned_conses'], case['max_owned_direct_bytes'], 'bound',
              case['owned_cons_bound'], 'overlap cons', case['max_union_conses'])


if __name__ == '__main__':
    main()
