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

PREFIX = 'FN_MATCHER_GRAPH '
SUBJECTS = ('books/wildmat-cursor.lisp', 'books/wildmat-work.lisp', 'books/wildmat.lisp',
            'books/nntp-responses.lisp')
ASSETS = ('tools/native_heap_graph.lisp', 'tests/native_matcher_heap_raw.lisp', 'host/native/trace.lisp')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def report(text):
    rows = [json.loads(line[len(PREFIX):]) for line in text.splitlines() if line.startswith(PREFIX)]
    cases = []
    for case in (row for row in rows if row['type'] == 'case'):
        states = [row for row in rows if row['type'] == 'state' and row['case_id'] == case['case_id']]
        done = [row for row in rows if row['type'] == 'done' and row['case_id'] == case['case_id']]
        if len(done) != 1 or len(states) != done[0]['steps'] + 1:
            raise ValueError('incomplete retained state trace')
        cases.append(dict(case, steps=done[0]['steps'], matched=done[0]['matched'],
            max_owned_conses=max(s['owned']['conses'] for s in states),
            max_owned_direct_bytes=max(s['owned']['direct-bytes'] for s in states),
            max_union_conses=max(s.get('old_new_union', s['owned'])['conses'] for s in states),
            max_union_direct_bytes=max(s.get('old_new_union', s['owned'])['direct-bytes'] for s in states),
            over_bound_steps=[s['step'] for s in states if s['over_bound']],
            union_over_single_state_bound_steps=[s['step'] for s in states
                                                  if s.get('union_over_single_state_bound')]))
    if 'NATIVE_MATCHER_HEAP_PASS' not in text or len(cases) != 9:
        raise ValueError('actual matcher probe did not complete all cases')
    return {'scope': 'distinct EQ retained graph/direct primitive object bytes; not GC/allocator overhead, '
                     'production pricing, or whole process retained heap. The bound is owned cons cells '
                     'of one state; old/new union is measured separately. FN_TRACE measures cumulative '
                     'allocation during32 replays, not retained heap; graph walking is outside spans.',
            'cases': cases}


def literal(value):
    return '"' + str(value).replace('\\', '\\\\').replace('"', '\\"') + '"'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_root', type=Path)
    parser.add_argument('--live-book', required=True, type=Path)
    parser.add_argument('--warm', required=True, help='Explicitly loaned existing session name')
    parser.add_argument('--control-root', required=True, type=Path)
    parser.add_argument('--host', default='hbox')
    parser.add_argument('--remote-tree', required=True)
    args = parser.parse_args()
    dest = ROOT / 'build/runtime-tests' / ('matcher-graph-' + uuid.uuid4().hex[:10])
    dest.mkdir(parents=True)
    snapshot = {str(path): digest(path) for path in
                [args.source_root / p for p in SUBJECTS] + [ROOT / p for p in ASSETS] +
                [args.live_book, Path(__file__)]}
    # Exact warm source coordinate, no remote source sync or replacement.
    command = 'cd ' + shlex.quote(args.remote_tree) + ' && sha256 ' + ' '.join(map(shlex.quote, SUBJECTS))
    remote_hashes = subprocess.run(['ssh', args.host, command], capture_output=True, text=True,
                                   timeout=15, check=True).stdout
    for name in SUBJECTS:
        expected = snapshot[str(args.source_root / name)]
        if expected not in remote_hashes:
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
    source = '(in-package "ACL2")\n' + '\n'.join(capacity_forms) + '\n' + \
             '(defttag :fn-matcher-heap-debug)\n' + \
             '(progn! (set-raw-mode t) (defvar *fnmg-probe-root* ' + literal(remote) + ') ' + \
             '(load ' + literal(remote + '/tests/native_matcher_heap_raw.lisp') + '))\n'
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
