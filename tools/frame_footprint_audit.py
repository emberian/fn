#!/usr/bin/env python3
"""Audit literal child-footprint arguments against admitted ACL2 theorem premises.

This source diagnostic is not a proof checker. Dynamic footprints and generated
instance names are reported as unresolved, never counted as validated. The world
log must come from the emitted query loaded after the intended certified books.
Only direct antecedent conjuncts supply mandatory subset requirements; constraints
inside disjunctions, negations, conditionals or other unsupported forms do not.
"""
import argparse
import json
import re
from pathlib import Path
import lisp_rewrite as lr

PARAMETERS = {'fn2-arm-ch', 'fn2-arm-free', 'children', 'free', 'ch'}


def literal(node):
    if not isinstance(node, lr.Pre) or node.prefix != "'":
        return None
    if not isinstance(node.node, lr.Lst):
        return None
    vals = [lr.flat(x) for x in node.node.items]
    return set(map(int, vals)) if all(x.isdecimal() for x in vals) else None


def instances(source):
    parsed = lr.parse(source)
    rows = []
    for match in lr.match('(:instance ?fn ?*args)', parsed.forms):
        fn = match.captures['fn']
        for arg in match.captures['args']:
            if not isinstance(arg, lr.Lst) or len(arg.items) != 2:
                continue
            parameter = lr.flat(arg.items[0]).lower()
            if parameter not in PARAMETERS:
                continue
            rows.append(dict(theorem=lr.flat(fn), concrete=isinstance(fn, lr.Atom),
                             parameter=parameter, value=lr.flat(arg.items[1]),
                             line=parsed.text.count('\n', 0, match.start) + 1))
    # These generators pass literal footprints through to theorem instances.
    # Column lists (cs) are deliberately not treated as child indices.
    patterns = [
        ('(fn2-env-x-call-events ?name ?call ?free ?theorem)', 'free', 'fn2-arm-free'),
        ('(fn2-env-x-same-events ?name ?call ?theorem ?dir ?cs ?ch)', 'ch', 'fn2-arm-ch'),
    ]
    for pattern, footprint, parameter in patterns:
        for match in lr.match(pattern, parsed.forms):
            fn = match.captures['theorem']
            if not isinstance(fn, lr.Pre) or fn.prefix != "'":
                continue
            rows.append(dict(theorem=lr.flat(fn.node), concrete=isinstance(fn.node, lr.Atom),
                             parameter=parameter, value=lr.flat(match.captures[footprint]),
                             line=parsed.text.count('\n', 0, match.start) + 1,
                             generator=pattern.split()[0][1:]))
    for match in lr.match('(fn2-env-x-kids-call-events ?name ?call ?free)', parsed.forms):
        call = match.captures['call']
        if not isinstance(call, lr.Pre) or call.prefix != "'":
            continue
        call = call.node
        if isinstance(call, lr.Lst) and lr.flat(call.items[0]).lower() == 'mv-nth':
            call = call.items[2]
        if not isinstance(call, lr.Lst) or not isinstance(call.items[0], lr.Atom):
            continue
        rows.append(dict(theorem='fn2-commit~' + lr.flat(call.items[0]) + '-arm-kids',
                         concrete=True, parameter='fn2-arm-free',
                         value=lr.flat(match.captures['free']),
                         line=parsed.text.count('\n', 0, match.start) + 1,
                         generator='fn2-env-x-kids-call-events'))
    return rows


def query(rows, book):
    if not all(c.isalnum() or c in '/-_' for c in book):
        raise ValueError('invalid book path')
    names = sorted({r['theorem'] for r in rows if r['concrete']})
    lines = ['(in-package "ACL2")', f'(include-book "{book}")',
             '(set-fmt-hard-right-margin 100000 state)',
             '(set-fmt-soft-right-margin 100000 state)']
    lines.extend(f'(cw "FRAMEAUDIT ~x0~%" (list \'{n} (getpropc \'{n} \'theorem nil (w state))))'
                 for n in names)
    return '\n'.join(lines + ['(cw "FRAMEAUDIT-DONE~%")', '(good-bye)', ''])


def world(log):
    if not any(re.fullmatch(r'(?:ACL2 [!>]*>)?FRAMEAUDIT-DONE', line.strip()) for line in log.splitlines()):
        raise ValueError('incomplete world query')
    result = {}
    for line in log.splitlines():
        marker = 'FRAMEAUDIT ('
        if marker not in line:
            continue
        form = lr.parse('(' + line.split(marker, 1)[1]).forms[0]
        result[lr.flat(form.items[0]).lower()] = form.items[1]
    return result


def conjuncts(term):
    """Flatten AND only; do not descend through other logical contexts."""
    if (isinstance(term, lr.Lst) and term.items
            and lr.flat(term.items[0]).lower() == 'and'):
        for argument in term.items[1:]:
            yield from conjuncts(argument)
    else:
        yield term


def check(rows, theorems):
    results = []
    for row in rows:
        row = dict(row)
        actual = literal(lr.parse(row['value']).forms[0])
        theorem = theorems.get(row['theorem'].lower())
        requirements = []
        if (row['concrete'] and actual is not None and isinstance(theorem, lr.Lst)
                and len(theorem.items) == 3 and lr.flat(theorem.items[0]).lower() == 'implies'):
            for m in lr.match('(subsetp-equal ?required ?parameter)',
                              conjuncts(theorem.items[1]), deep=False):
                required = literal(m.captures['required'])
                if lr.flat(m.captures['parameter']).lower() == row['parameter'] and required is not None:
                    requirements.append(required)
        if requirements:
            missing = set().union(*requirements) - actual
            row.update(status='mismatch' if missing else 'checked-subset', missing=sorted(missing))
        else:
            row.update(status='unresolved')
        results.append(row)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--query-book', default='books/commit-turn-frame')
    parser.add_argument('--emit-query', action='store_true')
    parser.add_argument('--world-log', type=Path)
    args = parser.parse_args()
    rows = instances(args.source)
    if args.emit_query:
        print(query(rows, args.query_book), end='')
        return 0
    if args.world_log:
        rows = check(rows, world(args.world_log.read_text()))
    print(json.dumps(rows, indent=2))
    return int(any(r.get('status') == 'mismatch' for r in rows))


if __name__ == '__main__':
    raise SystemExit(main())
