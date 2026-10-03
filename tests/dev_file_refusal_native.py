#!/usr/bin/env python3
"""Check file refusal/recovery through an existing private developer owner.

Run on the socket's host with its UID. --scratch must be a new private path.
This attaches only: it never creates an owner, ACL2 world, image, or Store.
Logs and trusted source fixtures remain at the scratch coordinate. Deliberate
evaluation-fault fencing belongs to dev_repl_native.py's owned fault phase.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import fn_dev


def run(socket, root, timeout=10):
    root = root.resolve()
    root.mkdir(parents=True, exist_ok=False, mode=0o700)
    name = 'fn-dev-file-' + uuid.uuid4().hex
    marker = '*' + name + '-prefix*'
    sources = {
        'bad-first': ')',
        'unclosed': '(list 1',
        'reader-eval': f'#.(setf {marker} :unsafe)',
        'partial': f'(setf {marker} :kept) )',
        'admit-partial': f'(defun {name}-one (x) (declare (xargs :guard t)) x) )',
        'admit-refusal': (f'(defun {name}-two (x) (declare (xargs :guard t)) x)\n'
                          f'(defthm {name}-false (equal 1 2) :rule-classes nil)\n'
                          f'(defun {name}-not-reached (x) x)'),
        'admit-continue': f'(defun {name}-after (x) (declare (xargs :guard t)) x)',
    }
    paths = {}
    for key, source in sources.items():
        path = root / (key + '.lisp')
        path.write_text(source)
        paths[key] = path
    observations = []

    def check(form, ok_expected, fragment):
        # A timeout/incomplete envelope is unknown execution, not refusal.
        # Do not retry or send a followup in that case; leave the files/log.
        try:
            ok, text = fn_dev.evaluate(socket, form, timeout)
        except Exception as error:
            observations.append({'form': form, 'unknown': str(error)})
            raise
        observations.append({'form': form, 'ok': ok, 'text': text})
        assert ok == ok_expected and fragment in ' '.join(text.split()), (ok, text)

    def load(key, admit=False):
        path = fn_dev.lisp_string(str(paths[key]))
        return (f'(fnn-dev-admit-file {path} :step-limit 10000)' if admit
                else f'(fnn-dev-load {path})')

    try:
        check(f'(defvar {marker} nil)', True, marker.upper())
        for key in ['bad-first', 'unclosed', 'reader-eval']:
            check('(multiple-value-list ' + load(key) + ')', False,
                  '(:REFUSED :READER-ERROR 0 0)')
            check(f'(list {marker} (+ 20 22))', True, '(NIL 42)')
        check('(multiple-value-list (fnn-dev-load ' +
              fn_dev.lisp_string(str(root / 'missing.lisp')) + '))', False,
              '(:REFUSED :OPEN-ERROR 0 0)')
        check('(multiple-value-list ' + load('partial') + ')', False,
              '(:PARTIAL :READER-ERROR 1 1)')
        check(f'(list {marker} (+ 20 22))', True, '(:KEPT 42)')
        check('(multiple-value-list ' + load('admit-partial', True) + ')', False,
              '(:PARTIAL :READER-ERROR 1 1)')
        check(f'({name}-one 17)', True, '17')
        check('(multiple-value-list ' + load('admit-refusal', True) + ')', False,
              '(:PARTIAL :ACL2-REFUSAL 2 1)')
        check(f'(list ({name}-two 23) (getpropc (quote {name}-not-reached) '
              '(quote formals) nil (w *the-live-state*)))', True, '(23 NIL)')
        check('(multiple-value-list ' + load('admit-continue', True) + ')', True,
              '(:ADMITTED 1 1)')
        check(f'(list ({name}-after 29) (+ 20 22))', True, '(29 42)')
        check('#.(error "reader evaluation must be disabled")', False,
              "can't read #.")
        check('(+ 20 22)', True, '42')
    finally:
        (root / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
        (root / 'source-hashes.json').write_text(json.dumps({
            str(path): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths.values()}, indent=2) + '\n')
    print('DEV-FILE-REFUSAL-NATIVE-PASS', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--socket', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=10)
    args = parser.parse_args()
    run(args.socket, args.scratch, args.timeout)
