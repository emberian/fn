#!/usr/bin/env python3
"""Audit the served raw-host load graph; optionally load its certified prefix.

This checks readable source, literal repository-contained LOADs, absence of
Lisp-reader/evaluator calls, and that the actual startup prefix loads without
starting the server. The load gate also checks actual ACL2 function bindings
across raw startup; only the declared native replacements may change. This is
an assumption census, not a proof of the native implementations' behavior.
The fn1 definterface/DTN registry is not an interface for this runtime.
"""
from __future__ import annotations

import argparse
import platform
from pathlib import Path
import subprocess
import sys
import tempfile

import ledger
import lisp_source

ROOT = Path(__file__).resolve().parents[1]
BANNED = {'read', 'read-preserving-whitespace', 'read-from-string', 'eval',
          'read-delimited-list', 'read-eval'}
# Deliberately independent of the mutable host's *fn2-b3-native-entries*.
# These implementations remain trusted (fn2-a-crypto-native/fn2-a-native-span);
# checking their function identities does not establish output/effect refinement.
NATIVE_REPLACEMENTS = (
    ('fn2-b3-fragment-into', 'fn2-b3-native-fragment'),
    ('fn2-fc-zero-prefix', 'fn2-b3-native-zero-prefix'),
    ('fn2-b3-subtree-cv-into', 'fn2-b3-native-subtree'),
    ('fn2-b3-chunk-output-into', 'fn2-b3-native-chunk'),
    ('fn2-b3-parent-cv', 'fn2-b3-native-parent-cv'),
    ('fn2-b3-parent-root', 'fn2-b3-native-parent-root'),
    ('fn2-b3-output', 'fn2-b3-native-output'),
    ('fn2-mk-node', 'fn2-b3-native-node'),
)


def walk(form):
    if not isinstance(form, list):
        return
    yield form
    if ledger.head(form) in ('quote', 'declare'):
        return
    for item in form:
        yield from walk(item)


def forms(path):
    return ledger.read_forms(path.read_text())


def inspect(root=ROOT):
    """Return startup prefix, load-order source names, and explicit findings."""
    root = Path(root).resolve()
    launcher = root / 'tools/image-node.lsp'
    source = launcher.read_text()
    marker = '(setf *fn2-nserve-base*'
    if source.count(marker) != 1:
        raise ValueError('launcher must have exactly one served entry boundary')
    prefix = source[:source.index(marker)]
    if ':q' not in prefix or '(include-book "books/node-profile"' not in prefix:
        raise ValueError('launcher lacks certified node prefix or raw-mode boundary')
    findings, visited, order = [], set(), []

    def visit(path):
        path = path.resolve()
        if not path.is_relative_to(root):
            findings.append(f'load escapes repository: {path}')
            return
        if path in visited:
            return
        visited.add(path)
        try:
            source = path.read_text()
            if any(token == "#." for kind, start, end in lisp_source.tokens(source)
                   for token in [source[start:end]]):
                findings.append(f"{path.relative_to(root)}: forbidden read-time evaluation")
            parsed = ledger.read_forms(source)
        except (OSError, ledger.ReadError) as error:
            findings.append(f'{path.relative_to(root)}: {error}')
            return
        order.append(path.relative_to(root).as_posix())
        scan(parsed, path.relative_to(root).as_posix())

    def scan(parsed, location):
        for form in parsed:
            for call in walk(form):
                h = ledger.head(call)
                if h and not h.startswith(':') and h.split(':')[-1] in BANNED:
                    findings.append(f'{location}: forbidden reader/evaluator {h}')
                if h in ('load', 'cl:load', 'common-lisp:load'):
                    if len(call) != 2 or not isinstance(call[1], str) or isinstance(call[1], ledger.Sym):
                        findings.append(f'{location}: nonliteral or unsupported LOAD')
                    else:
                        visit(root / call[1])

    scan(ledger.read_forms(prefix), 'tools/image-node.lsp')
    return prefix, order, findings


def selected(items):
    """Resolve the source's explicit SBCL platform features for this load host.

    The reader/eval audit still sees every branch; only runtime binding checks
    select the platform actually loaded. New feature expressions fail closed.
    """
    known = {'linux': sys.platform.startswith('linux'), 'darwin': sys.platform == 'darwin',
             'x86-64': platform.machine().lower() in ('x86_64', 'amd64')}
    out, i = [], 0
    while i < len(items):
        value = items[i]
        if isinstance(value, ledger.Sym) and str(value).startswith(('#+', '#-')):
            flag = str(value)[2:]
            if flag not in known or i + 1 == len(items):
                raise ValueError(f'unsupported source feature {value}')
            enabled = known[flag] == (str(value)[1] == '+')
            i += 1
            if not enabled:
                i += 1
                continue
            value = items[i]
        out.append(selected(value) if isinstance(value, list) else value)
        i += 1
    return out


def expression_calls(form):
    """Calls in expression positions, excluding binding and declaration syntax."""
    if not isinstance(form, list) or not form:
        return
    h = ledger.head(form)
    if h in ('quote', 'declare', 'defstruct', 'define-condition',
             'sb-alien:define-alien-routine', 'in-package'):
        return
    if h in ('defun', 'defmacro'):
        children = form[3:]
    elif h == 'lambda':
        children = form[2:]
    elif h in ('defvar', 'defparameter', 'defconstant'):
        children = form[2:3]
    elif h in ('let', 'let*'):
        children = [value for binding in form[1] if isinstance(binding, list)
                    for value in binding[1:]] + form[2:]
    elif h == 'multiple-value-bind':
        children = form[2:]
    elif h in ('dolist', 'dotimes'):
        children = form[1][1:] + form[2:]
    elif h in ('flet', 'labels', 'macrolet'):
        children = [body for definition in form[1] for body in definition[2:]] + form[2:]
    elif h == 'cond':
        children = [part for clause in form[1:] for part in clause]
    elif h in ('case', 'ecase', 'typecase', 'etypecase'):
        children = form[1:2] + [part for clause in form[2:] for part in clause[1:]]
    else:
        if h:
            name = h.removeprefix('acl2::').removeprefix('acl2:')
            if name.startswith(('fn2-', '%fn2-')):
                yield name
        if h == 'function' and len(form) == 2 and isinstance(form[1], ledger.Sym):
            name = str(form[1]).removeprefix('acl2::').removeprefix('acl2:')
            if name.startswith(('fn2-', '%fn2-')):
                yield name
        if h in ('funcall', 'apply') and len(form) > 1:
            target = form[1]
            if ledger.head(target) == 'quote' and len(target) == 2:
                name = str(target[1]).removeprefix('acl2::').removeprefix('acl2:')
                if name.startswith(('fn2-', '%fn2-')):
                    yield name
        children = form[1:] if h else form
    for child in children:
        yield from expression_calls(child)


def entry_names(root, order):
    """Direct fn2 calls and raw definitions; no broad name-prefix exemptions."""
    calls, helpers, structures = set(), set(), set()
    for name in order:
        for form in (node for top in selected(forms(root / name)) for node in walk(top)):
            h = ledger.head(form)
            if h in ('defun', 'defmacro'):
                helpers.add(str(form[1]))
            if h == 'define-condition':
                for slot in form[3]:
                    for index, option in enumerate(slot[:-1]):
                        if str(option) in (':reader', ':writer', ':accessor'):
                            helpers.add(str(slot[index + 1]))
            if h == 'sb-alien:define-alien-routine':
                spec = form[1]
                if isinstance(spec, list) and len(spec) == 2:
                    helpers.add(str(spec[1]))
            if h == 'defstruct':
                spec = form[1]
                struct = str(spec[0] if isinstance(spec, list) else spec)
                structures.add(struct)
                helpers.update((struct + '-p', 'make-' + struct, 'copy-' + struct))
                for slot in form[2:]:
                    if isinstance(slot, str) and not isinstance(slot, ledger.Sym):
                        continue
                    key = str(slot[0] if isinstance(slot, list) else slot)
                    helpers.add(struct + '-' + key)
                continue
        for form in selected(forms(root / name)):
            calls.update(expression_calls(form))
    return sorted(calls - structures), sorted(helpers)


def load_program(prefix, calls, helpers, replacements=()):
    logical, raw = prefix.split(':q', 1)
    names = ' '.join(calls)
    local = ' '.join(helpers)
    replacement_map = ' '.join(f'({name} . {native})' for name, native in replacements)
    # Capture and validate the ACL2 status BEFORE native BLAKE3 replacements
    # are installed. Raw helpers are exactly the definitions in the load graph.
    return logical + f"""
:q
(handler-case
 (let ((bindings nil) (seen (make-hash-table :test #'eq))
       (replacements '({replacement_map})))
  ;; Snapshot the live world's function objects, including transitive callees
  ;; absent from the raw source call inventory. Do not infer identity from guards.
  (do-all-symbols (name)
   (unless (gethash name seen)
    (setf (gethash name seen) t)
    (unless (or (special-operator-p name)
                (eq (getpropc name 'symbol-class :missing (w *the-live-state*)) :missing))
     (push (cons name (if (fboundp name) (fdefinition name) :unbound)) bindings))))
  (dolist (pair replacements)
   (unless (and (assoc (car pair) bindings)
                (not (eq (cdr (assoc (car pair) bindings)) :unbound))
                (eq (getpropc (car pair) 'symbol-class :missing (w *the-live-state*))
                    :common-lisp-compliant))
    (error "Declared native target ~s lacks a guarded ACL2 binding" (car pair))))
  (dolist (name '({names}))
   (let* ((world (w *the-live-state*))
          (class (getpropc name 'symbol-class :missing world)))
    (cond ((not (eq class :missing))
           (unless (eq class :common-lisp-compliant)
            (error "Served callee ~s has unverified guards (~s)" name class)))
          ((not (member name '({local})))
           (error "Undeclared served callee ~s" name)))))
  {raw}
  (dolist (pair bindings)
   (let* ((name (car pair)) (replacement (assoc name replacements)))
    (unless (if (and (not replacement) (eq (cdr pair) :unbound))
                (not (fboundp name))
                (and (fboundp name)
                     (if replacement
                         (and (fboundp (cdr replacement))
                              (eq (fdefinition name) (fdefinition (cdr replacement))))
                         (eq (fdefinition name) (cdr pair)))))
     (error "Undeclared or mismatched raw replacement of ACL2 function ~s" name))))
  (dolist (name '({names}))
   (unless (fboundp name)
    (error "Served callee ~s is not bound" name)))
  (format t "~%FN_SERVED_HOST_BINDINGS_OK ~d unchanged-or-declared, ~d native assumptions~%"
          (length bindings) (length replacements))
  (format t "~%FN_SERVED_HOST_LOAD_OK~%")
  (sb-ext:exit :code 0))
 (error (condition)
  (format t "~%FN_SERVED_HOST_LOAD_ERROR ~a~%" condition)
  (sb-ext:exit :code 1)))
"""


def load_prefix(prefix, root, order, timeout):
    calls, helpers = entry_names(root, order)
    program = load_program(prefix, calls, helpers, NATIVE_REPLACEMENTS)
    with tempfile.TemporaryFile(mode='w+') as log:
        try:
            result = subprocess.run([str(root / 'tools/acl2'), '--timeout', str(timeout)],
                                    input=program, text=True, cwd=root, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=timeout + 10)
        except subprocess.TimeoutExpired:
            return 2, 'served host load timed out'
        log.seek(0)
        output = log.read()
    if result.returncode or 'FN_SERVED_HOST_LOAD_OK' not in output.splitlines():
        return 1, '\n'.join(output.splitlines()[-60:])
    return 0, (f'certified node prefix and {len(calls)} guarded/host callees loaded; '
               f'ACL2 bindings preserved except {len(NATIVE_REPLACEMENTS)} declared '
               'native replacements (fn2-a-crypto-native/fn2-a-native-span); no listener started')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--load', action='store_true')
    parser.add_argument('--timeout-seconds', type=int, default=180)
    args = parser.parse_args(argv)
    try:
        prefix, order, findings = inspect()
    except (OSError, ValueError, ledger.ReadError) as error:
        print(f'served_host_check: {error}', file=sys.stderr)
        return 1
    for finding in findings:
        print('FAIL ' + finding)
    print(f'served_host_check: {len(order)} raw sources, {len(findings)} findings')
    if findings:
        return 1
    if args.load:
        code, message = load_prefix(prefix, ROOT, order, args.timeout_seconds)
        print(message)
        return code
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
