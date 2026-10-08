#!/usr/bin/env python3
"""Generate BLAKE3 execution bodies and audit unchanged logical formulas.

Only the known scalar quarter-round and list-entry shapes are accepted.
ACL2 guard verification, not this rewriter, proves the generated MBE equalities.
"""
from __future__ import annotations
import argparse
import json
import subprocess
from pathlib import Path
from lisp_rewrite import Atom, Lst, Pre, Str, parse, write

ROUND_NAMES = {'fn-b3-round', *(f'fn-b3-rounds-{i}' for i in range(1, 8))}


def inline_rounds(text, names=ROUND_NAMES, *, selected=None):
    edits, found = [], set()
    for form in parse(text).forms:
        if not isinstance(form, Lst) or len(form.items) < 3:
            continue
        head, name = form.items[:2]
        if not isinstance(name, Atom) or name.low not in names:
            continue
        if not isinstance(head, Atom) or head.low not in ('defun', 'defun-inline'):
            raise ValueError(f'not-a-defun: {name.text}')
        if name.low in found:
            raise ValueError(f'duplicate-definition: {name.text}')
        found.add(name.low)
        target = 'defun-inline' if selected is None or name.low in selected else 'defun'
        if head.low != target:
            edits.append((head.start, head.end, target))
    if names - found:
        raise ValueError(f'missing-definitions: {sorted(names - found)}')
    return write(text, edits), {'changed': len(edits), 'residual': sorted(names - found)}


def flatten_round(text):
    forms = {f.items[1].low: f for f in parse(text).forms
             if isinstance(f, Lst) and len(f.items) > 3
             and isinstance(f.items[0], Atom) and f.items[0].low in ('defun', 'defun-inline')}
    quarter, round_ = forms['fn-b3-g'], forms['fn-b3-round']
    body, qbody = round_.items[-1], quarter.items[-1]
    if body.items[0].low == 'mbe':
        raise ValueError('already-flattened')
    if qbody.items[0].low != 'let*' or len(qbody.items) != 3:
        raise ValueError('quarter-not-let-star')
    if logical(qbody.items[2]) != ('mv', 'a', 'b', 'c', 'd'):
        raise ValueError('quarter-result-not-four-words')
    if len(qbody.items[1].items) != 8:
        raise ValueError('quarter-not-eight-bindings')
    bindings, cursor = [], body
    while isinstance(cursor, Lst) and cursor.items[0].low == 'mv-let':
        outputs, call, rest = cursor.items[1:]
        if call.items[0].low != 'fn-b3-g' or len(call.items) != 7:
            raise ValueError('round-not-quarter-call')
        if [x.low for x in outputs.items] != [x.low for x in call.items[1:5]]:
            raise ValueError('quarter-output-renaming')
        rename = dict(zip((x.low for x in quarter.items[2].items), (x.text for x in call.items[1:])))
        for binding in qbody.items[1].items:
            edits = []
            def walk(node):
                if isinstance(node, Atom) and node.low in rename:
                    edits.append((node.start-binding.start, node.end-binding.start, rename[node.low]))
                elif isinstance(node, Lst):
                    for child in node.items:
                        walk(child)
                elif not isinstance(node, Atom):
                    raise ValueError('unsupported-quarter-expression')
            walk(binding)
            bindings.append(write(text[binding.start:binding.end], edits))
        cursor = rest
    if len(bindings) != 64 or cursor.items[0].low != 'mv':
        raise ValueError('round-not-eight-quarters')
    exec_body = '(let* (' + '\n              '.join(bindings) + ')\n         ' + text[cursor.start:cursor.end] + ')'
    replacement = '(mbe :logic\n       ' + text[body.start:body.end] + '\n       :exec\n       ' + exec_body + ')'
    guard = '\n  (declare (xargs :guard-hints (("Goal" :in-theory (enable fn-b3-g mv-nth)))))'
    return write(text, [(body.start, body.end, replacement), (round_.items[2].end, round_.items[2].end, guard)])


def linear_entry(text):
    matches = [f for f in parse(text).forms if isinstance(f, Lst) and len(f.items) > 3
               and isinstance(f.items[0], Atom) and f.items[0].low == 'defun'
               and f.items[1].low == 'fn-b3-compress']
    if len(matches) != 1:
        raise ValueError('missing-unique-compress')
    form = matches[0]
    if logical(form.items[2]) != ('cv', 'words', 'counter', 'blen', 'flags'):
        raise ValueError('unexpected-compress-formals')
    body = form.items[-1]
    if body.items[0].low != 'mv-let':
        raise ValueError('compress-not-mv-let')
    call = body.items[2]
    if call.items[0].low != 'fn-b3-compress-core':
        raise ValueError('compress-not-core-call')
    bindings, replacements = [], []
    for source, prefix, count in [('cv', 'c', 8), ('words', 'm', 16)]:
        for i in range(count):
            variable = f'{prefix}{i}'
            bindings.append(f'({variable} (if (consp {source}) (car {source}) 0))')
            if i != count - 1:
                bindings.append(f'({source} (if (consp {source}) (cdr {source}) nil))')
            arg = call.items[1 + i + (8 if source == 'words' else 0)]
            if logical(arg) != ('fn-b3-nthx', str(i), source):
                raise ValueError('unexpected-core-argument')
            replacements.append((arg.start-body.start, arg.end-body.start, variable))
    exec_body = write(text[body.start:body.end], replacements)
    replacement = '(mbe :logic\n       ' + text[body.start:body.end] + '\n       :exec\n       (let* (' + '\n              '.join(bindings) + ')\n         ' + exec_body + '))'
    return write(text, [(body.start, body.end, replacement)])


def logical(node):
    if isinstance(node, Str):
        return ('string', node.text)
    if isinstance(node, Atom):
        return node.low
    if isinstance(node, Pre):
        return (node.prefix, logical(node.node))
    items = node.items
    if items and isinstance(items[0], Atom):
        if items[0].low == 'mbe':
            for i in range(1, len(items), 2):
                if isinstance(items[i], Atom) and items[i].low == ':logic':
                    return logical(items[i + 1])
            raise ValueError('mbe-without-logic')
        if items[0].low == 'the':
            return logical(items[2])
    return tuple(logical(x) for x in items)


def statements(text):
    result = {}
    def visit(form):
        if not isinstance(form, Lst) or not form.items:
            return
        items = form.items
        head = items[0].low if isinstance(items[0], Atom) else ''
        if head == 'local':
            visit(items[1])
        elif head == 'encapsulate':
            for child in items[2:]:
                visit(child)
        elif head in ('defun', 'defun-inline'):
            name = items[1].low
            body = [x for x in items[3:] if not (isinstance(x, Lst) and x.items and isinstance(x.items[0], Atom) and x.items[0].low == 'declare')]
            result[name] = ('defun', logical(items[2]), tuple(logical(x) for x in body))
        elif head == 'defthm':
            options = []
            for i in range(3, len(items), 2):
                if items[i].low != ':hints':
                    options.extend((logical(items[i]), logical(items[i + 1])))
            result[items[1].low] = ('defthm', logical(items[2]), tuple(options))
    for form in parse(text).forms:
        visit(form)
    return result


def compare(before, after):
    old, new = statements(before), statements(after)
    return {'original_count': len(old),
            'changed': sorted(k for k in old if k in new and old[k] != new[k]),
            'removed': sorted(old.keys() - new.keys()),
            'added': sorted(new.keys() - old.keys())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--book', type=Path, default=Path('books/blake3.lisp'))
    parser.add_argument('--inline', action='store_true')
    parser.add_argument('--mode', choices=['all', 'round', 'none'], default='all')
    parser.add_argument('--check-against')
    parser.add_argument('--flatten-round', action='store_true')
    parser.add_argument('--linear-entry', action='store_true')
    args = parser.parse_args()
    if args.inline:
        selected = ROUND_NAMES if args.mode == 'all' else {'fn-b3-round'} if args.mode == 'round' else set()
        result, report = inline_rounds(args.book.read_text(), selected=selected)
        args.book.write_text(result)
        print(json.dumps(report))
    if args.flatten_round:
        args.book.write_text(flatten_round(args.book.read_text()))
        print(json.dumps({'flattened_round': True, 'residual': []}))
    if args.linear_entry:
        args.book.write_text(linear_entry(args.book.read_text()))
        print(json.dumps({'linear_entry': True, 'residual': []}))
    if args.check_against:
        before = subprocess.check_output(['git', 'show', f'{args.check_against}:{args.book.as_posix()}'], text=True)
        report = compare(before, args.book.read_text())
        print(json.dumps(report, indent=2))
        return bool(report['changed'] or report['removed'])
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
