#!/usr/bin/env python3
"""Guard-preserving totalization of the recorded actual checkpoint worker scans."""
from pathlib import Path
import argparse
import hashlib
import json
import lisp_rewrite as lisp

RECEIPT = Path('tools/fixtures/checkpoint-worker-totalization.json')

def canonical(node):
    if isinstance(node, lisp.Lst):
        return tuple(canonical(x) for x in node.items)
    if isinstance(node, lisp.Pre):
        return (node.prefix, canonical(node.node))
    return node.text.lower()

def definition(text, name):
    return next(n for n in lisp.parse(text).forms
                if text[n.start:n.end].startswith('(defun ' + name + ' '))

def parts(text, node):
    decl = node.items[3].items[1]
    opts = {getattr(x, 'text', '').lower(): decl.items[i+1]
            for i, x in enumerate(decl.items[:-1])}
    return opts[':guard'], opts[':measure'], node.items[-1]

def domain(row):
    return '(and ' + ' '.join(row['clauses']) + ')'

def validate_guard(row):
    original = row['original_form']
    assert hashlib.sha256(original.encode()).hexdigest() == row['original_sha256']
    node = definition(original, row['name'])
    guard, _, _ = parts(original, node)
    assert original[guard.start:guard.end] == row['original_guard']
    assert getattr(guard.items[0], 'text', '').lower() == 'and'
    conjuncts = [canonical(n) for n in guard.items[1:]]
    for clause in row['clauses']:
        assert canonical(lisp.parse(clause).forms[0]) in conjuncts, clause


def transformed(row):
    validate_guard(row)
    original = row['original_form']
    node = definition(original, row['name'])
    _, measure, body = parts(original, node)
    wrapped = '(if ' + domain(row) + '\n  ' + original[body.start:body.end] + '\n  ' + row['fallback'] + ')'
    return lisp.write(original, [(measure.start, measure.end, row['measure']),
                                 (body.start, body.end, wrapped)])

def restored(text, row):
    node = definition(text, row['name'])
    guard, measure, body = parts(text, node)
    assert text[guard.start:guard.end] == row['original_guard']
    assert text[measure.start:measure.end] == row['measure']
    assert canonical(body.items[0]) == 'if' and len(body.items) == 4
    assert canonical(body.items[1]) == canonical(lisp.parse(domain(row)).forms[0])
    assert canonical(body.items[3]) == canonical(lisp.parse(row['fallback']).forms[0])
    return lisp.write(text, [(measure.start, measure.end, row['original_measure']),
                            (body.start, body.end, text[body.items[2].start:body.items[2].end])])




def fixture(rows):
    out = ['; Prepared source equations, not an executed checkpoint/cut witness.\n'
           '; Each guarded equation is the unchanged actual one-step transition.\n'
           '; Off-guard logical controls establish total refusal, not served calls.\n'
           '(in-package "ACL2")\n'
           '(include-book "../books/checkpoint-future-working")\n']
    for row in rows:
        original = row['original_form']
        node = definition(original, row['name'])
        args = original[node.items[2].start:node.items[2].end][1:-1]
        _, _, body = parts(original, node)
        call = '(' + row['name'] + ' ' + args + ')'
        old_body = original[body.start:body.end]
        out.append('(defthm ' + row['name'] + '-guard-implies-domain\n'
                   ' (implies ' + row['original_guard'] + '\n          ' + domain(row) + '))\n')
        out.append('(defthm ' + row['name'] + '-guarded-measure-by-definition\n'
                   ' (implies ' + row['original_guard'] + '\n'
                   '  (equal ' + row['measure'] + ' ' + row['original_measure'] + '))\n'
                   ' :hints (("Goal" :in-theory (enable nfix))))\n')
        out.append('(defthm ' + row['name'] + '-guarded-transition-unfolds\n'
                   ' (implies ' + row['original_guard'] + '\n'
                   '  (equal ' + call + '\n   ' + old_body + '))\n'
                   ' :hints (("Goal" :expand (' + call + ')\n'
                   '  :in-theory (disable ' + row['name'] + '))))\n')
        formal = node.items[2].items[0].text
        bad = '(' + row['name'] + ' 1/2 ' + ' '.join(x.text for x in node.items[2].items[1:]) + ')'
        out.append('(defthm ' + row['name'] + '-logical-nonnatural-index-refuses-by-definition\n'
                   ' (equal ' + bad + ' ' + row['fallback'] + ')\n'
                   ' :hints (("Goal" :expand (' + bad + ')\n'
                   '  :in-theory (disable ' + row['name'] + '))))\n')
        if formal == 'i' and any(c == '(natp end)' for c in row['clauses']):
            actuals = [x.text for x in node.items[2].items]
            actuals[0] = '0'
            actuals[1] = '1/2'
            bad_end = '(' + row['name'] + ' ' + ' '.join(actuals) + ')'
            out.append('(defthm ' + row['name'] + '-logical-nonnatural-end-refuses-by-definition\n'
                       ' (equal ' + bad_end + ' ' + row['fallback'] + ')\n'
                       ' :hints (("Goal" :expand (' + bad_end + ')\n'
                       '  :in-theory (disable ' + row['name'] + '))))\n')
    return '\n'.join(out)


def substitute(text, values):
    edits = []
    def walk(node):
        if isinstance(node, lisp.Pre):
            if node.prefix == ',' and isinstance(node.node, lisp.Atom) and node.node.text in values:
                edits.append((node.start, node.end, values[node.node.text]))
            else:
                walk(node.node)
        elif isinstance(node, lisp.Lst):
            for item in node.items:
                walk(item)
        elif isinstance(node, lisp.Atom) and node.text in values:
            edits.append((node.start, node.end, values[node.text]))
    for node in lisp.parse(text).forms:
        walk(node)
    return lisp.write(text, edits)


def caller_fixture(rows):
    specs = {row['name']: row for row in rows}
    root = Path('books/checkpoint-working-reserve.lisp').read_text()
    future = Path('books/checkpoint-future-working.lisp').read_text()
    out = []
    def theorem(name, condition, result):
        out.append('(defthm ' + name + '\n (implies ' + condition + '\n          ' + result + '))\n')
    for source, caller, helper in [
        (root, 'fn2-checkpoint-root1-reserve', 'fn2-checkpoint-windows-reserve-loop'),
        (future, 'fn2-checkpoint-future-reserve-with-credit', 'fn2-checkpoint-future-reserve-loop')]:
        node = definition(source, caller)
        binding = node.items[-1].items[1].items[0]
        assert binding.items[0].items[0].text == 'unless'
        condition = binding.items[0].items[1]
        theorem(caller + '-actual-zero-entry-domain', source[condition.start:condition.end],
                substitute(domain(specs[helper]), {'i': '0'}))
    macro = next(n for n in lisp.parse(future).forms
                 if future[n.start:n.end].startswith('(defmacro fn2-checkpoint-future-transfer-interface '))
    template = macro.items[-1].node
    condition = template.items[-1].items[1]
    condition_text = future[condition.start:condition.end]
    for node in lisp.parse(future).forms:
        if isinstance(node, lisp.Lst) and getattr(node.items[0], 'text', '') == 'fn2-checkpoint-future-transfer-interface':
            name, first, end, returning = [future[x.start:x.end] for x in node.items[1:]]
            values = {'first': first, 'end': end, 'returning': returning}
            theorem(name + '-actual-transfer-entry-domain', substitute(condition_text, values),
                    substitute(domain(specs['fn2-checkpoint-future-transfer-loop']), {'i': first, 'end': end}))
    release = definition(future, 'fn2-checkpoint-future-release-one')
    binding = release.items[-1].items[1].items[2]
    assert binding.items[0].items[0].text == 'unless'
    condition = binding.items[0].items[1]
    theorem('fn2-checkpoint-future-release-one-actual-prefix-domain', future[condition.start:condition.end],
            substitute(domain(specs['fn2-checkpoint-future-no-loansp']), {'i': '0', 'end': 'left'}))
    return '\n'.join(out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--fixture', action='store_true')
    args = parser.parse_args()
    rows = json.loads(RECEIPT.read_text())['functions']
    if args.fixture:
        Path('tests/root-future-totalization-unit.lisp').write_text(fixture(rows))
        raise SystemExit(0)
    paths = list(dict.fromkeys(row['path'] for row in rows))
    for path in paths:
        source = Path(path).read_text()
        edits = []
        for row in rows:
            if row['path'] != path:
                continue
            node = definition(source, row['name'])
            current = source[node.start:node.end]
            if args.check:
                validate_guard(row)
                assert restored(current, row) == row['original_form']
            else:
                assert current == row['original_form'], row['name']
                edits.append((node.start, node.end, transformed(row)))
        if not args.check:
            Path(path).write_text(lisp.write(source, edits))
