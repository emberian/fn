#!/usr/bin/env python3
"""Replay the shared physical-engine extraction from pre-extraction fixtures.

The fixture is the original implementation, not a second served implementation.
Tests compare engine bodies modulo the source-authority predicate and require
source wrappers to retain exact catalog authority before each engine call.
"""
from pathlib import Path
import sys
sys.path.insert(0,'tools')
import lisp_rewrite as lr
B=Path('books')
F=Path('tools/fixtures/run-physical-bound')
def fn(s,n):return lr.match('(defun '+n+' ?*body)',lr.parse(s).forms,deep=False)[0].node
def raw(s,n):return s[n.start:n.end]
source=(F/'source.lisp').read_text(); p=fn(source,'fn2-run-load-sourcep'); form=p.items[-1]; clauses=form.items[1:]
# Common physical identity fields move as one class; catalog authority stays
# in sourcep. Both wrappers use the same immutable cursor/load binding.
common=[];catalog=[]
for c in clauses:
 t=raw(source,c)
 if any(x in t for x in ['fn2-checkpoint-summary','(fn2-run-loads-history','(fn2-run-loads-incarnation']): catalog.append(t)
 else:common.append(t)
commonargs='c fn2-run-loads fn2-run-cursors'
commondef='''; The physical binding is shared by source-specific authorities. It is
; necessary but never sufficient to admit a catalog or archive source.
(defun fn2-run-load-boundp ('''+commonargs+''')
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors))))
 (and '''+'\n      '.join(common)+'))\n'
# hash helper must be defined before shared predicate.
h=fn(source,'fn2-run-load-hash-current-p')
(B/'run-physical-bound.lisp').write_text('; Shared immutable physical cursor binding; no catalog or descriptor authority.\n(in-package "ACL2")\n(include-book "run-physical-resources")\n(fn2-book-layer :c)\n'+raw(source,h)+'\n'+commondef)
newform='(and (fn2-run-load-boundp '+commonargs+')\n      '+'\n      '.join(catalog)+')'
source=lr.write(source,[(form.start,form.end,newform),(h.start,h.end,'' )]).replace('(include-book "run-physical-resources")','(include-book "run-physical-bound")\n(include-book "checkpoint-summary-leases")')
(B/'run-physical-source.lisp').write_text(source)
catalogargs='fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed '
catalogwf=['(fn2-checkpoint-summary-wfp fn2-checkpoint-summary)','(fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources)','(fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases)','(fn2-run-installed-wfp fn2-run-installed)']
for suffix,extra,pre in [('issue','', '(include-book "run-physical-bound")'),('step',' fn2-boot-config','(include-book "run-physical-bound-io")\n(include-book "boot-geometry-state")\n(include-book "checkpoint-semantic-page")')]:
 path=B/('run-physical-'+('io' if suffix=='issue' else suffix)+'.lisp'); s=(F/('io.lisp' if suffix=='issue' else 'step.lisp')).read_text();name='fn2-run-load-'+suffix;n=fn(s,name); original=raw(s,n);engine=original.replace(name,'fn2-run-bound-'+suffix,1)
 # Remove only source authority carriers, retaining all physical work state.
 engine=engine.replace(catalogargs,'').replace(catalogargs.rstrip()+'\n','')
 for x in catalogwf:engine=engine.replace(x,'')
 old='(fn2-run-load-sourcep c fn2-run-loads fn2-run-cursors '+catalogargs.rstrip()+')'
 if engine.count(old)!=1:raise ValueError('source predicate drift '+suffix)
 engine=engine.replace(old,'(fn2-run-load-boundp c fn2-run-loads fn2-run-cursors)')
 # Macros are shared return tuples, defined once in the lower engine book.
 macro=lr.match('(defmacro fn2-run-load-'+suffix+'-mv ?*body)',lr.parse(s).forms,deep=False)[0].node
 macros=raw(s,macro)
 prefix='; Shared bounded physical engine; callers establish their source authority each turn.\n(in-package "ACL2")\n'+pre+'\n(fn2-book-layer :c)\n'
 if suffix=='step':
  d=fn(s,'fn2-run-load-digest'); prefix+=raw(s,d)+'\n';s=lr.write(s,[(d.start,d.end,'')]);n=fn(s,name);macro=lr.match('(defmacro fn2-run-load-step-mv ?*body)',lr.parse(s).forms,deep=False)[0].node
 # Harvest is source-independent and shared with bound-engine clients.
 observer=''
 if suffix=='issue':
  moved=[]
  for pattern in ['(defun fn2-run-load-harvest ?*body)','(fn2-run-load-frames fn2-run-load-harvest ?*body)']:
   node=lr.match(pattern,lr.parse(s).forms,deep=False)[0].node
   moved.append(node)
  observer='\n'.join(raw(s,node) for node in moved)+'\n'
  s=lr.write(s,[(node.start,node.end,'') for node in moved])
  n=fn(s,name);macro=lr.match('(defmacro fn2-run-load-issue-mv ?*body)',lr.parse(s).forms,deep=False)[0].node
 # Full wrapper retains original signature and declaration; invokes one engine.
 header=original[:original.index('\n (b*')]
 params=[x.low for x in n.items[2].items]
 lower=[x for x in params if x not in catalogargs.split()]
 fail='(fn2-run-load-'+suffix+'-mv :source'+(' 0 0' if suffix=='issue' else '')+')'
 budget='(posp budget)' if suffix=='issue' else '(and (posp budget) (<= budget *fn2-commit-unit-bytes*))'
 wrapper=header+'\n (cond ((not '+budget+') (fn2-run-load-'+suffix+'-mv :yield'+(' 0 0' if suffix=='issue' else '')+'))\n       ((not '+old+') '+fail+')\n       (t (fn2-run-bound-'+suffix+' '+' '.join(lower)+'))))'
 # Export frame theorems for engine using the same output positions.
 frames=lr.match('(fn2-run-load-frames '+name+' ?*body)',lr.parse(s).forms,deep=False)[0].node
 ef=raw(s,frames).replace(name,'fn2-run-bound-'+suffix,1).replace(catalogargs,'')
 engine='\n'.join(line for line in engine.splitlines() if line.strip())
 (B/('run-physical-bound-'+('io' if suffix=='issue' else suffix)+'.lisp')).write_text(prefix+macros+'\n'+engine+'\n\n'+ef+'\n'+observer)
 s=lr.write(s,[(n.start,n.end,wrapper),(macro.start,macro.end,'')])
 if suffix=='issue':s=s.replace('(include-book "run-physical-source")','(include-book "run-physical-source")\n(include-book "run-physical-bound-io")')
 else:s=s.replace('(include-book "checkpoint-boot")\n(include-book "checkpoint-semantic-page")','(include-book "run-physical-bound-step")')
 path.write_text(s.rstrip()+'\n')
