"""Exact source-class repair: frozen loader donor -> named COPY/idle fixes.

This projects source only. It does not execute a loader, prove admission, or
accept arbitrary differences in its authority, parser, hash or read algorithm.
"""
from pathlib import Path
import lisp_rewrite as lr
FIXTURES=Path(__file__).resolve().parent/'fixtures'/'physical-loader-repair'
def one(pattern,forms):
 found=lr.match(pattern,forms,deep=True)
 if len(found)!=1:raise ValueError('expected one repair subject: '+pattern)
 return found[0].node

def copy_prefix():
 prefix=(FIXTURES/'copy-budget-prefix.lisp').read_text()
 forms=lr.parse(prefix).forms
 if len(forms)!=2:raise ValueError('COPY prefix must contain only its count and bound')
 count=one('(defun fn2-run-load-copy-count ?*body)',forms)
 # Refuse a changed fixture that would retain the old full-unit count.
 if lr.emit(count.items[-1],drop_comments=True)!='(min (floor budget 2) (- *fn2-commit-unit-bytes* copied))':
  raise ValueError('COPY count no longer charges source read and destination write')
 bound=one('(defthm fn2-run-load-copy-count-bound ?*body)',forms)
 one('(<= (* 2 (fn2-run-load-copy-count budget copied)) budget)',[bound])
 one('(<= (+ copied (fn2-run-load-copy-count budget copied)) *fn2-commit-unit-bytes*)',[bound])
 return prefix

def project(name,source):
 forms=lr.parse(source).forms
 if name=='run-physical-region.lisp':
  f=one('(defun fn2-run-load-region-freep ?*body)',forms)
  if lr.match('(fn2-run-loads-pending ?*args)',[f]) or lr.match('(fn2-run-loads-windows ?*args)',[f]):
   raise ValueError('idle region repair already present or not the frozen class')
  at=one('(equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-idle*)',[f])
  return lr.write(source,[(at.end,at.end,'\n        (equal (fn2-run-loads-pending c fn2-run-loads) 0) (equal (fn2-run-loads-windows c fn2-run-loads) 0)')])
 if name=='run-physical-bound-step.lisp':
  if lr.match('(defun fn2-run-load-copy-count ?*body)',forms):
   raise ValueError('COPY repair already present')
  f=one('(defun fn2-run-bound-step ?*body)',forms)
  branch=one('((equal phase *fn2-run-load-phase-copy*) ?*body)',[f])
  n=one('(n (min budget (- *fn2-commit-unit-bytes* copied)))',[branch])
  copied=one('(copied (fn2-run-loads-copied c fn2-run-loads))',[branch])
  return lr.write(source,[(f.start,f.start,copy_prefix()),
   (copied.start,copied.start,'((when (< budget 2)) (fn2-run-load-step-mv :yield))\n         '),
   (n.start,n.end,'(n (fn2-run-load-copy-count budget copied))')])
 raise ValueError('no approved physical loader repair for '+name)

def require_projection(name,donor,candidate):
 if project(name,donor)!=candidate:
  raise ValueError('candidate differs outside exact named physical loader repair: '+name)

def actual_step_branch():
 branch=(FIXTURES/'actual-step-copy-branch.lisp').read_text().rstrip('\n')
 forms=lr.parse(branch).forms
 if len(forms)!=1:raise ValueError('expected only the actual STEP control branch')
 one('((equal phase *fn2-run-load-phase-copy*) ?*body)',forms)
 one('((mv small fn2-core) (fn2-tal-bound-step-op c 1 fn2-core))',forms)
 if len(lr.match('(fn2-tal-bound-step-op c 4096 fn2-core)',forms))!=2:
  raise ValueError('expected two actual supported-budget STEP calls')
 one('(before-yield (fn2-test-core-snapshot fn2-core))',forms)
 one('(equal before-yield (fn2-test-core-snapshot fn2-core))',forms)
 one('(= (fn2-run-loads-copied c fn2-run-loads) 2048)',forms)
 one('(= (fn2-run-loads-copied c fn2-run-loads) 0)',forms)
 one('(= (fn2-run-loads-sector c fn2-run-loads) (+ 1 sector))',forms)
 one('(if (= (+ 1 sector) *fn2-storage-extent-units*) *fn2-run-load-phase-context* *fn2-run-load-phase-read*)',forms)
 one('(fn2-pool-compare ?*args)',forms)
 for head in ('fn2-run-loads-put','fn2-run-loads-set-phase','fn2-run-loads-set-copied','fn2-pool-copy-range'):
  if lr.match('('+head+' ?*args)',forms):raise ValueError('STEP control must not construct its own result: '+head)
 return branch

def project_actual_step_fixture(source):
 f=one('(defun fn2-tal-physical-drive ?*body)',lr.parse(source).forms)
 if lr.match('((equal phase *fn2-run-load-phase-copy*) ?*body)',[f]):
  raise ValueError('actual STEP branch already present')
 cond=one('(cond ?*clauses)',[f])
 fallback=cond.items[-1]
 if not isinstance(fallback,lr.Lst) or getattr(fallback.items[0],'low',None)!='t':
  raise ValueError('expected original actual physical driver fallback')
 return lr.write(source,[(fallback.start,fallback.start,actual_step_branch()+'\n         ')])

def require_actual_step_fixture(donor,candidate):
 if project_actual_step_fixture(donor)!=candidate:
  raise ValueError('actual I/O fixture differs outside the named STEP branch')
