#!/usr/bin/env python3
"""Syntax controls for owned bank evidence; no ACL2 or durability claim."""
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
def check(evidence, writer, coordinator):
    capture = list(walk(definition(evidence, 'fn2-checkpoint-bank-evidence-capture')))
    for batch in ('batch', 'cut', ['-', 'batch', '1']):
        assert ['fn2-commit-directory-seal-slot', batch, ['fn2-fc-rows', 'fn2-fc'], 'fn2-commit-root'] in capture
    assert ['fn2-checkpoint-bank-evidence-candidate-p', '0', 'c', 'fn2-checkpoint-bytes', 'fn2-checkpoint-publication'] in capture
    assert ['event', ['fn2-checkpoints-installation-event', 'c', 'fn2-checkpoints']] in capture
    meta = list(walk(definition(evidence, 'fn2-checkpoint-bank-evidence-capture-meta')))
    assert ['8', ['fn2-checkpoints-installation-event', 'c', 'fn2-checkpoints']] in meta
    words = list(walk(definition(evidence, 'fn2-checkpoint-bank-evidence-capture-words')))
    assert ['0', ['fn2-digest-word', 'jseal', 'word', 'fn2-digests']] in words
    assert ['1', ['if', ['equal', 'cut', '0'], '0', ['fn2-digest-word', 'cseal', 'word', 'fn2-digests']]] in words
    assert ['2', ['if', ['equal', 'batch', '1'], '0', ['fn2-digest-word', 'pseal', 'word', 'fn2-digests']]] in words
    record = list(walk(definition(evidence, 'fn2-checkpoint-bank-evidence-record-fence')))
    assert ['fn2-checkpoint-bank-evidence-current-p', '2', 'fn2-checkpoint-publication'] in record
    assert ['fn2-checkpoint-bank-evidence-copy', '0', 'bank', '3', 'fn2-checkpoint-publication'] in record
    assert ['fn2-checkpoint-bank-evidence-copy', '0', '2', 'bank', 'fn2-checkpoint-publication'] in record
    for name in ('snapshot', 'event', 'word'):
        nodes = list(walk(definition(evidence, 'fn2-checkpoint-bank-evidence-'+name)))
        assert ['member-equal', 'slot', ['quote', ['0', '1', '3']]] in nodes
        assert ['fn2-checkpoint-bank-evidence-current-p', 'slot', 'fn2-checkpoint-publication'] in nodes
        assert not any(n and n[0] in ('fn2-commit-directory-lookup', 'fn2-commit-directory-seal-slot') for n in nodes)
    assert '(fn2-checkpoint-bank-evidence-capture c fn2-checkpoints fn2-commit-root fn2-fc fn2-checkpoint-bytes fn2-digests fn2-checkpoint-publication)' in writer
    stamp = coordinator.index('(fn2-checkpoints-set-installation-event c event fn2-checkpoints)')
    install = coordinator.index('(fn2-checkpoint-install c batch ')
    reject = coordinator.index('((unless (eq code :ok)) (mv code fn2-retirement-control fn2-checkpoints fn2-fields))', install)
    assert install < reject < stamp
    assert '(= (fn2-checkpoints-installation-event c fn2-checkpoints) event)' in coordinator
if __name__ == '__main__':
    e = (ROOT/'books/checkpoint-bank-evidence.lisp').read_text()
    w = (ROOT/'books/checkpoint-writer-ops.lisp').read_text()
    c = (ROOT/'books/checkpoint-lifecycle-coordinator.lisp').read_text()
    check(e, w, c)
    from rewrite_checkpoint_bank_capture import rewrite_evidence_identity
    assert rewrite_evidence_identity(e) == e, 'identity recipe must be idempotent'
    damaged = e.replace('(fn2-checkpoint-publication-bank1-hash-7 0', '(fn2-checkpoint-publication-bank1-hash-6 0', 1)
    assert rewrite_evidence_identity(damaged) == e, 'scoped identity regeneration must repair the full hash'
    mutations = [e.replace('(fn2-digest-word cseal word fn2-digests)', '(fn2-digest-word jseal word fn2-digests)', 1),
                 e.replace('(fn2-digest-word pseal word fn2-digests)', '(fn2-digest-word cseal word fn2-digests)', 1),
                 e.replace('(fn2-checkpoint-bank-evidence-current-p 2 fn2-checkpoint-publication)', 't', 1),
                 e.replace('(fn2-checkpoint-bank-evidence-copy 0 bank 3 fn2-checkpoint-publication)', 'fn2-checkpoint-publication', 1),
                 e.replace("(member-equal slot '(0 1 3))", "(member-equal slot '(0 1 2 3))", 1),
                 e.replace('(fn2-checkpoints-installation-event c fn2-checkpoints)', '(fn2-checkpoints-cut-event c fn2-checkpoints)', 1)]
    for bad in mutations:
        try:
            check(bad, w, c)
        except (AssertionError, StopIteration):
            continue
        raise AssertionError('weakened bank evidence survived')
    print(f'bank evidence source controls: {len(mutations)} rejected mutations; no execution/admission claim')
