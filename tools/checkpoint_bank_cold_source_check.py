#!/usr/bin/env python3
"""Syntax controls for authenticated cold evidence retention, not admission."""
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
def check(src):
    source = list(walk(definition(src, 'fn2-checkpoint-bank-cold-source-p')))
    for name in ('fn2-checkpoint-recovery-census-bound-p', 'fn2-checkpoint-restore-events-complete-p'):
        assert any(n and n[0] == name for n in source)
    assert ['posp', ['fn2-checkpoint-restore-map-control-reach-generation', '0', 'fn2-checkpoint-restore-map-control']] in source
    assert any(n and n[0]=='fn2-checkpoint-restore-semantic-current-p' for n in source)
    assert ['equal',['fn2-checkpoint-restore-semantic-phase','0','fn2-checkpoint-restore-semantic'],'*fn2-checkpoint-restore-semantic-phase-complete*'] in source
    meta = list(walk(definition(src, 'fn2-checkpoint-bank-cold-source-meta')))
    assert ['7', ['fn2-checkpoint-recovery-evidence-commit', ['+', 'c', '1'], 'fn2-checkpoint-recovery-evidence']] in meta
    assert ['8', ['fn2-checkpoint-recovery-evidence-event', ['+', 'c', '1'], 'fn2-checkpoint-recovery-evidence']] in meta
    word = list(walk(definition(src, 'fn2-checkpoint-bank-cold-source-word')))
    assert ['equal', 'which', '1'] in word
    assert any(n and n[0] == 'fn2-checkpoint-restore-events-cut-seal-word' for n in word)
    assert ['2', '128'] in word and ['3', '32'] in word and ['4', '96'] in word and ['otherwise', '64'] in word
    step = definition(src, 'fn2-checkpoint-bank-cold-seed-step')[-1]
    bindings = step[1]
    assert bindings[0] == [['unless', ['and', ['natp', 'budget'], ['<', '0', 'budget']]], ['mv', ':yield', 'fn2-checkpoint-publication', 'fn2-checkpoint-bank-closures']]
    assert any(n and n[0] == 'fn2-checkpoint-bank-cold-source-p' for n in walk(bindings[1]))
    nodes = list(walk(step))
    assert ['c', ['fn2-checkpoint-restore-map-control-candidate', '0', 'fn2-checkpoint-restore-map-control']] in nodes
    assert any(n[:4] == ['fn2-checkpoint-bank-cold-meta-equal-p', '1', '10', 'c'] for n in nodes)
    assert any(n[:3] == ['fn2-checkpoint-bank-cold-words-equal-p', '0', 'c'] for n in nodes)
    ready = next(b for b in bindings if b[0] == ['when', ['equal', 'i', '48']])
    assert ['update-fn2-checkpoint-publication-cold-metai', ['*', '12', 'c'], '2', 'fn2-checkpoint-publication'] in list(walk(ready))
    assert ['eq','code',':captured'] in list(walk(ready))
    assert any(n and n[0]=='fn2-checkpoint-bank-closure-capture-step' for n in walk(ready))
    assert not any(n and n[0] in ('fn2-checkpoint-publication-record-bank', 'fn2-commit-directory-lookup', 'fn2-commit-directory-seal-slot') for n in walk(src_forms(src)))
    for name in ('snapshot', 'event', 'word'):
        reader = list(walk(definition(src, 'fn2-checkpoint-bank-cold-'+name)))
        assert ['fn2-checkpoint-bank-cold-ready-p', 'c', 'fn2-checkpoint-publication'] in reader
        assert not any(n and n[0] in ('fn2-checkpoint-bank-cold-source-p', 'fn2-commit-directory-lookup') for n in reader)
def src_forms(src):
    return [read_sexp(t) for t in forms(src)]
if __name__ == '__main__':
    src = (ROOT/'books/checkpoint-bank-cold.lisp').read_text()
    check(src)
    mutations = [src.replace('(fn2-checkpoint-restore-semantic-current-p ', '(missing-semantic ', 1),
                 src.replace('(eq code :captured)', 't',1),
                 src.replace('(fn2-checkpoint-bank-closure-capture-step ', '(missing-reach-copy ',1),
                 src.replace('(fn2-checkpoint-recovery-census-bound-p ', '(missing-anchor ', 1),
                 src.replace('(fn2-checkpoint-restore-events-complete-p ', '(missing-frontier ', 1),
                 src.replace('(fn2-checkpoint-restore-events-cut-seal-word ', '(wrong-J-seal ', 1),
                 src.replace('(fn2-checkpoint-recovery-evidence-event (+ c 1) fn2-checkpoint-recovery-evidence)', '(fn2-checkpoints-cut-event c fn2-checkpoints)', 1),
                 src.replace('(equal i 48)', '(equal i 47)', 1),
                 src.replace('(fn2-checkpoint-bank-cold-meta-equal-p 1 10 c ', '(fn2-checkpoint-bank-cold-meta-equal-p 1 8 c ', 1),
                 src.replace('(fn2-checkpoint-bank-cold-words-equal-p 0 c ', '(missing-repeat-comparison 0 c ', 1)]
    for bad in mutations:
        try:
            check(bad)
        except (AssertionError, StopIteration):
            continue
        raise AssertionError('weakened cold bank source survived')
    print(f'cold bank source controls: {len(mutations)} rejected mutations; no execution/admission claim')
