#!/usr/bin/env python3
"""Scoped actual cold-seed carrier/output projection; no alternate worker."""
from pathlib import Path
import sys
sys.path.insert(0,'tools')
from lisp_rewrite import parse,match,write
p=Path('books/checkpoint-bank-cold.lisp');src=p.read_text()
if 'fn2-checkpoint-bank-closure-capture-step' in src:
 print('cold seed closure projection: unchanged')
 sys.exit(0)
oldS='fn2-boot-config fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-origin fn2-checkpoint-recovery-evidence fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work'.split()
S=oldS+['fn2-checkpoint-restore-semantic'];ALL=S+['fn2-checkpoint-restore-reach','fn2-checkpoint-bank-closures','fn2-checkpoint-publication']
E='fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work'
sem='fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic'
source='(defun fn2-checkpoint-bank-cold-source-p ('+' '.join(S)+')\n (declare (xargs :stobjs ('+' '.join(S)+') :guard (and '+' '.join('('+x+'-wfp '+x+')' for x in S)+')))\n'
source+=''' (and (< 0 (fn2-checkpoint-restore-map-control-rows fn2-checkpoint-restore-map-control))
      (posp (fn2-checkpoint-restore-map-control-reach-generation 0 fn2-checkpoint-restore-map-control))
      (fn2-checkpoint-restore-semantic-current-p '''+sem+''')
      (equal (fn2-checkpoint-restore-semantic-phase 0 fn2-checkpoint-restore-semantic) *fn2-checkpoint-restore-semantic-phase-complete*)
      (let ((c (fn2-checkpoint-restore-map-control-candidate 0 fn2-checkpoint-restore-map-control)))
       (and (fn2-checkpoint-recovery-census-bound-p c fn2-boot-config fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-origin fn2-checkpoint-recovery-evidence)
            (posp (fn2-checkpoint-recovery-evidence-tag (+ 1 c) fn2-checkpoint-recovery-evidence))
            (fn2-checkpoint-restore-events-complete-p '''+E+''')))))'''
def span(src,name):return match('(defun '+name+' ?*body)',parse(src).forms,deep=False)[0].node
n=span(src,'fn2-checkpoint-bank-cold-source-p');src=write(src,[(n.start,n.end,source)])
n=span(src,'fn2-checkpoint-bank-cold-seed-step');seed=src[n.start:n.end];oldseed=seed
# Project every return through the new actually changed closure child.
tree=parse(seed);edits=[]
for hit in match('(mv ?code fn2-checkpoint-publication)',tree.forms):
 c=hit.captures['code'];expr=seed[c.start:c.end]
 edits.append((hit.start,hit.end,'(mv '+expr+' fn2-checkpoint-publication fn2-checkpoint-bank-closures)'))
seed=write(seed,edits)
# Replace declaration only, retain the actual existing body/word copy path.
tree=parse(seed);decl=match('(declare ?*body)',tree.forms,deep=True)[0].node
seed=write(seed,[(decl.start,decl.end,'(declare (xargs :stobjs ('+' '.join(ALL)+') :guard (and '+' '.join('('+x+'-wfp '+x+')' for x in ALL)+')))')])
seed=seed.replace('(budget '+' '.join(oldS+['fn2-checkpoint-publication'])+')','(budget '+' '.join(ALL)+')',1)
seed=seed.replace('(fn2-checkpoint-bank-cold-source-p '+' '.join(oldS)+')','(fn2-checkpoint-bank-cold-source-p '+' '.join(S)+')',1)
seed=seed.replace('(and (fn2-checkpoint-bank-cold-capacityp fn2-checkpoint-publication)\n', '''(and (fn2-checkpoint-bank-cold-capacityp fn2-checkpoint-publication)
                    (fn2-checkpoint-bank-closures-capacityp fn2-checkpoint-bank-closures)
                    (equal (fn2-checkpoint-bank-closures-extents fn2-checkpoint-bank-closures) (fn2-boot-config-extents fn2-boot-config))
''',1)
needle='''(and (fn2-checkpoint-bank-cold-meta-equal-p 1 8 c'''
seed=seed.replace(needle,'''(and (fn2-checkpoint-bank-closure-ready-p c fn2-checkpoint-bank-closures fn2-checkpoint-publication)
                    (fn2-checkpoint-bank-cold-meta-equal-p 1 8 c''',1)
# Replace hash EOF with the actual bounded typed reach continuation.
tree=parse(seed);eof=match('((when (equal i 48)) ?*body)',tree.forms,deep=True)
assert len(eof)==1
capture='c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic fn2-checkpoint-publication fn2-checkpoint-bank-closures'
replacement='''((when (equal i 48))
       (b* (((mv code fn2-checkpoint-bank-closures) (fn2-checkpoint-bank-closure-capture-step '''+capture+''')))
        (if (eq code :captured)
         (let ((fn2-checkpoint-publication (update-fn2-checkpoint-publication-cold-metai (* 12 c) 2 fn2-checkpoint-publication)))
          (mv :seeded fn2-checkpoint-publication fn2-checkpoint-bank-closures))
         (mv code fn2-checkpoint-publication fn2-checkpoint-bank-closures))))'''
seed=write(seed,[(eof[0].start,eof[0].end,replacement)])
src=write(src,[(n.start,n.end,seed)])
# Replace source shape/footprint declarations using actual output positions.
parsed=parse(src);edits=[]
for h in match('(fn2-checkpoint-publication-preserves fn2-checkpoint-bank-cold-seed-step ?*body)',parsed.forms,deep=False):
 specs=[]
 for pos,x in [(1,'fn2-checkpoint-publication'),(2,'fn2-checkpoint-bank-closures')]:
  stem=x[4:].upper()
  specs += [f'("-{stem}-GUARD-DOMAIN-TYPE" {x}p {pos})',f'("-{stem}-GUARD-DOMAIN-WFP" {x}-wfp {pos})',f'("-{stem}-ROWS" {x}-rows {pos} :frame {x})']
 text='(fn2-checkpoint-publication-preserves fn2-checkpoint-bank-cold-seed-step\n (budget '+' '.join(ALL)+')\n :hyps ('+' '.join('('+x+'p '+x+') ('+x+'-wfp '+x+')' for x in ALL)+')\n :specs ('+' '.join(specs)+'))'
 edits.append((h.start,h.end,text))
for h in match('(defcost fn2-checkpoint-bank-cold-seed-op ?*body)',parsed.forms,deep=False):
 text='(defcost fn2-checkpoint-bank-cold-seed-op :child fn2-checkpoint-bank-cold-seed-step :answers t\n :tables ('+' '.join('fn2-core-'+x[4:] for x in ALL)+')\n :doc "Retain one actual evidence word or typed closure row before cold scratch reuse; READY requires both EOFs and no caller completion assertion.")'
 edits.append((h.start,h.end,text))
src=write(src,edits).replace('(include-book "checkpoint-restore-events-source")','(include-book "checkpoint-restore-events-source")\n(include-book "checkpoint-bank-closure-capture")',1)
p.write_text(src)
