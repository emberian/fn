#!/usr/bin/env python3
"""Regenerate the literal two-bank capture from its one identity-field recipe.

The named defun alone changes; lisp_rewrite preserves unrelated source bytes.
"""
from pathlib import Path
from lisp_rewrite import parse, match, write
helper='''; Only HARVEST calls this after the exact successful covering Fence. Debt has
; no clear operation: later teardown must prove bank exclusion and durable
; descendant retirement before it can discharge this retained identity.
(defun fn2-checkpoint-publication-record-bank (fn2-checkpoint-publication)
 (declare (xargs :stobjs fn2-checkpoint-publication
  :guard (and (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)
              (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication)))))
 (if (equal (fn2-checkpoint-publication-bank 0 fn2-checkpoint-publication) 0)
'''
for n in range(2):
 prefix=f'bank{n}'
 helper+='  (let* ((fn2-checkpoint-publication\n           (if (equal (fn2-checkpoint-publication-'+prefix+'-valid 0 fn2-checkpoint-publication) 1)\n            (fn2-checkpoint-publication-put 0 (debt-valid 1)\n'
 for f in ('candidate','checkpoint','history','incarnation',*[f'hash-{i}' for i in range(8)]):
  helper+=f'             (debt-{f} (fn2-checkpoint-publication-{prefix}-{f} 0 fn2-checkpoint-publication))\n'
 helper+='             ) fn2-checkpoint-publication))\n         (fn2-checkpoint-publication (fn2-checkpoint-publication-put 0\n          ('+prefix+'-valid 1)\n'
 for f in ('candidate','checkpoint','history','incarnation',*[f'hash-{i}' for i in range(8)]):
  src='candidate' if f=='candidate' else 'attempt-'+f
  helper+=f'          ({prefix}-{f} (fn2-checkpoint-publication-{src} 0 fn2-checkpoint-publication))\n'
 helper+='          ))) fn2-checkpoint-publication)'+('' if n==0 else '))')+'\n'
helper+='\n'
helper=helper.replace(' (if (equal (fn2-checkpoint-publication-bank 0 fn2-checkpoint-publication) 0)\n  (let*', ' (if (not (equal (fn2-checkpoint-publication-debt-valid 0 fn2-checkpoint-publication) 0))\n     fn2-checkpoint-publication\n  (if (equal (fn2-checkpoint-publication-bank 0 fn2-checkpoint-publication) 0)\n  (let*', 1)
helper=helper.replace('))) fn2-checkpoint-publication)))\n', '))) fn2-checkpoint-publication))))\n', 1)

helper=helper.replace(' (if (not (equal (fn2-checkpoint-publication-debt-valid', ' (if (or (zp (fn2-checkpoint-publication-rows fn2-checkpoint-publication))\n         (not (equal (fn2-checkpoint-publication-debt-valid', 1)
helper=helper.replace('fn2-checkpoint-publication) 0))\n     fn2-checkpoint-publication', 'fn2-checkpoint-publication) 0)))\n     fn2-checkpoint-publication', 1)


def rewrite(source):
    parsed=parse(source)
    hits=match('(defun fn2-checkpoint-publication-record-bank ?*body)',parsed.forms,deep=False)
    if len(hits)!=1: raise ValueError('expected one bank-capture definition')
    node=hits[0].node
    # The comment belongs to the book; regenerate only the named definition.
    code=helper[helper.index('(defun '):].rstrip()
    return write(source,[(node.start,node.end,code)])
def evidence_identity_helpers():
    out = {}
    for suffix, formal, guard, fields in (
        ('word', 'i', '(natp i) (< i 8)', [f'hash-{i}' for i in range(8)]),
        ('scalar', 'i', '(natp i) (<= 1 i) (<= i 4)', ['candidate', 'checkpoint', 'history', 'incarnation'])):
        name = 'fn2-checkpoint-bank-evidence-id-'+suffix
        code = f'(defun {name} (slot {formal} fn2-checkpoint-publication)\n (declare (xargs :stobjs fn2-checkpoint-publication :guard (and (fn2-checkpoint-publication-wfp fn2-checkpoint-publication) (fn2-checkpoint-bank-evidence-capacityp fn2-checkpoint-publication) (natp slot) (< slot 4) {guard})))\n (case slot\n'
        for n, prefix in enumerate(('bank0', 'bank1', 'attempt', 'debt')):
            code += f'  ({n} (case i\n'
            for i, field in enumerate(fields, 0 if suffix == 'word' else 1):
                src = 'candidate' if prefix == 'attempt' and field == 'candidate' else prefix+'-'+field
                code += f'    ({i} (fn2-checkpoint-publication-{src} 0 fn2-checkpoint-publication))\n'
            code += '    (otherwise 0)))\n'
        code += '  (otherwise 0)))'
        out[name] = code
    return out

def rewrite_evidence_identity(source):
    parsed = parse(source)
    edits = []
    for name, code in evidence_identity_helpers().items():
        hits = match('(defun '+name+' ?*body)', parsed.forms, deep=False)
        if len(hits) != 1:
            raise ValueError('expected one '+name)
        node = hits[0].node
        edits.append((node.start, node.end, code))
    return write(source, edits)

if __name__=='__main__':
    path=Path(__file__).resolve().parents[1]/'books/checkpoint-publication-state.lisp'
    source=path.read_text(); updated=rewrite(source)
    if source!=updated:path.write_text(updated)
    print('bank identity capture:', 'unchanged' if source==updated else 'regenerated')
