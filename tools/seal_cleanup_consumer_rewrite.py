#!/usr/bin/env python3
"""Drain actual sealer loader-status, cost-answer, and machine-arm consumers."""

import json
from pathlib import Path
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
BEFORE = json.loads((ROOT / 'tools/fixtures/seal-cleanup-consumers-before.json').read_text())


def form(file, source):
    spec = BEFORE[file]
    found = lr.match(spec['pattern'], lr.parse(source).forms, deep=False)
    if len(found) != 1:
        raise ValueError(f'{file}: expected one {spec["pattern"]}')
    if file.endswith('events.lisp'):
        arms = lr.match('(:sealing ?*body)', [found[0].node])
        if len(arms) != 1:
            raise ValueError('sealing arm changed')
        return arms[0].node
    return found[0].node


def target(file, old):
    node = lr.parse(old).forms[0]
    if file.endswith('physical-loader.lisp'):
        bindings = node.items[-1].items[1].items
        if len(bindings) < 3 or not lr.match(
                '(equal (fn2-csnapshot-phase 0 fn2-csnapshot) '
                '*fn2-csnapshot-phase-held*)', [bindings[2]]):
            raise ValueError('source-closed pause boundary changed')
        return lr.write(old, [(bindings[2].end, bindings[2].end,
           '\n      ((when (fn2-csnapshot-source-closed-p fn2-csnapshot)) :pause)'
           '\n      ((when (or (equal phase *fn2-seal-phase-overlay-return*)'
           '\n                 (equal phase *fn2-seal-phase-hash-return*))) :run)')])
    if file.endswith('kind.lisp'):
        items = node.items
        answers = [items[i + 1] for i in range(len(items) - 1)
                   if getattr(items[i], 'low', None) == ':answers']
        if len(answers) != 1:
            raise ValueError('sealer cost answers changed')
        more = lr.match(':more', [answers[0]])
        if len(more) != 1:
            raise ValueError('sealer cost :more changed')
        return lr.write(old, [(more[0].end, more[0].end, ' :held :credit')])
    if file.endswith('events.lisp'):
        more = lr.match('((:more) (:charge ?*body))', [node])
        if len(more) != 1:
            raise ValueError('sealer arm :more changed')
        branches = '''
       ((:held) (:charge :steps *fn2-work-transition* :runnable t))
       ((:credit) (:do () (fn2-sealer-refuse code)) (:set (stopped 1))
        (:next :stopped) (:charge :steps *fn2-work-transition*))'''
        return lr.write(old, [(more[0].end, more[0].end, branches)])
    raise ValueError(file)


def transform(file, source):
    node = form(file, source)
    current = source[node.start:node.end]
    old = BEFORE[file]['before']
    desired = target(file, old)
    if current != old and current != desired:
        raise ValueError(f'{file}: fixed original consumer changed')
    count = 0 if current == desired else 1
    result = source if not count else lr.write(source, [(node.start, node.end, desired)])
    if file.endswith('events.lisp'):
        old_comment = (';; wake for that, every other answer stops the core by name through fn2-sealer-refuse (:full is\n'
                       ';; :sealer-full, :cache :sealer-cache, any other :sealer) rather than park a\n'
                       ';; row nothing would wake, and moves the row to :stopped.')
        new_comment = (';; wake for that, :held retries the retained cleanup phase. :credit stops\n'
                       ';; with its handles and observer retained for recovery; other refusals stop\n'
                       ';; the core by name through fn2-sealer-refuse (:full is :sealer-full,\n'
                       ';; :cache :sealer-cache, any other :sealer).')
        if old_comment in result:
            result = result.replace(old_comment, new_comment, 1)
        elif new_comment not in result:
            raise ValueError('sealer arm comment changed')
    return result, count


if __name__ == '__main__':
    total = 0
    for file in BEFORE:
        path = ROOT / file
        result, count = transform(file, path.read_text())
        if count:
            path.write_text(result)
        total += count
    print(f'{total} fixed original phase consumers transformed')
