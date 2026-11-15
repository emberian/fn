#!/usr/bin/env python3
"""Syntax controls for process C-base lifetime. No execution/admission claim."""
from pathlib import Path
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]
def walk(x):
    if isinstance(x, list):
        yield x
        for y in x:
            yield from walk(y)
def definition(src, name):
    return next(f for text in forms(src) if (f := read_sexp(text))[:2] == ['defun', name])
def check(acquire, release):
    source = list(walk(definition(acquire, 'fn2-checkpoint-cbase-acquire-source-p')))
    for fn in ('fn2-checkpoint-projection-protected-p', 'fn2-checkpoint-summary-current-p', 'fn2-checkpoint-restore-events-complete-p'):
        assert any(n and n[0] == fn for n in source), fn
    assert ['equal', ['fn2-checkpoint-restore-semantic-phase', '0', 'fn2-checkpoint-restore-semantic'], '*fn2-checkpoint-restore-semantic-phase-complete*'] in source
    step = definition(acquire, 'fn2-checkpoint-cbase-acquire-step')[-1]
    bindings = step[1]
    assert bindings[0] == [['unless', ['and', ['natp', 'budget'], ['<', '0', 'budget']]], ['mv', ':yield', 'fn2-checkpoint-cbase-holds', 'fn2-extents', 'fn2-alloc-edges']]
    nodes = list(walk(step))
    assert ['equal', ['fn2-extents-release-pending', 'e', 'fn2-extents'], '0'] in nodes
    assert ['fn2-alloc-edge-matchesp', 'source', ['fn2-checkpoint-cbase-holds-checkpoint', 'c', 'fn2-checkpoint-cbase-holds'], 'e', 'epoch', 'allocation', ':recovery-base', 'fn2-alloc-edges'] in nodes
    assert ['fn2-alloc-edge-add', 'edge', 'tag', 'e', 'epoch', 'allocation', ':promised-read', 'fn2-extents', 'fn2-alloc-edges'] in nodes
    assert not any(n and n[0] in ('fn2-alloc-edge-add-transition', 'fn2-alloc-edge-drop', 'fn2-alloc-release') for n in nodes)
    closing = list(walk(definition(release, 'fn2-checkpoint-cbase-row-release-step')))
    assert ['equal', ['fn2-checkpoint-summary-lease-count', 's', 'fn2-checkpoint-summary'], '0'] in closing
    assert ['fn2-checkpoint-summary-row-retire-row', 's', 'r', 'fn2-checkpoint-summary', 'fn2-checkpoint-summary-sources', 'fn2-checkpoint-cbase-holds', 'fn2-run-installed'] in closing
    assert ['equal', ['fn2-checkpoint-summary-installed', 's', 'fn2-checkpoint-summary'], '0'] in closing
    drops = [n for n in closing if n and n[0] == 'fn2-alloc-edge-drop']
    assert len(drops) == 1 and drops[0][-3:] == [':promised-read', 'fn2-extents', 'fn2-alloc-edges']
    assert not any(n and n[0] in ('fn2-alloc-release', 'fn2-run-retired-next', 'fn2-cache-drop') for n in closing)
if __name__ == '__main__':
    a = (ROOT/'books/checkpoint-cbase-acquire.lisp').read_text()
    r = (ROOT/'books/checkpoint-cbase-release.lisp').read_text()
    check(a, r)
    mutations = []
    for fn in ('fn2-checkpoint-projection-protected-p', 'fn2-checkpoint-summary-current-p', 'fn2-checkpoint-restore-events-complete-p'):
        mutations.append((a.replace('('+fn+' ', '(missing-authority ', 1), r))
    mutations += [(a.replace('(equal (fn2-extents-release-pending e fn2-extents) 0)', 't', 1), r),
                  (a.replace(':recovery-base fn2-alloc-edges)', ':installed-root fn2-alloc-edges)', 1), r),
                  (a.replace('(fn2-alloc-edge-add edge tag e epoch allocation :promised-read', '(fn2-alloc-edge-add-transition edge tag e epoch allocation :promised-read', 1), r),
                  (a, r.replace('(equal (fn2-checkpoint-summary-lease-count s fn2-checkpoint-summary) 0)', 't')),
                  (a, r.replace('(fn2-checkpoint-summary-row-retire-row s r ', '(fn2-run-retired-next r ', 1)),
                  (a, r.replace('(equal (fn2-checkpoint-summary-installed s fn2-checkpoint-summary) 0)', 't'))]
    for x, y in mutations:
        try:
            check(x, y)
        except (AssertionError, StopIteration):
            continue
        raise AssertionError('weakened lifetime source survived')
    print(f'C-base source controls: {len(mutations)} rejected mutations; no execution/admission claim')
