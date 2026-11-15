#!/usr/bin/env python3
"""Extract the actual cold installed-row write into the shared counted constructor."""
from pathlib import Path
import lisp_rewrite as lr
FIELDS=['schema','run','wire-run','top','entries','unit','epoch','counter','catalog-tag']+['hash-'+str(i) for i in range(8)]
def extract(source):
    fn=lr.match('(defun fn2-checkpoint-summary-apply-step ?*body)',lr.parse(source).forms,deep=False)[0].node
    calls=lr.match('(fn2-run-installed-put r ?*fields)',[fn])
    if len(calls)!=1:raise ValueError('expected one actual installed row write')
    call=calls[0].node
    fields={x.items[0].low:x for x in call.items[2:]}
    if (set(FIELDS)-{'wire-run'})-set(fields):raise ValueError('missing physical Ref fields')
    if 'wire-run' not in fields:fields['wire-run']=fields['run']
    if getattr(fields['physical'].items[1],'low',None)!='1':raise ValueError('not actual physical install')
    return call,fields

def transform_apply(source):
    call,fields=extract(source)
    values=[source[fields[x].items[1].start:fields[x].items[1].end] for x in FIELDS]
    runpos=FIELDS.index('run');values[runpos]='(+ (fn2-checkpoint-summary-priority-base 0 fn2-checkpoint-summary) '+values[runpos]+')'
    # The original binding receives one updated table. The shared constructor
    # also returns a code, consumed before coverage changes.
    binding=next(m.node for m in lr.match('(fn2-run-installed ?value)',lr.parse(source).forms) if m.captures['value'].start==call.start)
    replacement='''((mv install-code fn2-run-installed) (fn2-run-install-physical r '''+'\n       '.join(values)+''' fn2-run-installed))
      ((unless (eq install-code :ok)) (mv install-code fn2-checkpoint-summary fn2-run-installed fn2-id-engine fn2-seals))'''
    return lr.write(source,[(binding.start,binding.end,replacement)])

def constructor(source):
    call,fields=extract(source)
    assignments=[]
    for x in call.items[2:]:
        field=x.items[0].low
        assignments.append('('+field+' '+(field if field in FIELDS else source[x.items[1].start:x.items[1].end])+')')
        if field=='run' and not any(y.items[0].low=='wire-run' for y in call.items[2:]):assignments.append('(wire-run wire-run)')
    params='r '+' '.join(FIELDS)+' fn2-run-installed'
    domain=['(natp r)','(< r (fn2-run-installed-rows fn2-run-installed))']
    for field in FIELDS:
        domain.append(f'(unsigned-byte-p {32 if field.startswith("hash-") else 8 if field=="top" else 60} {field})')
    domain += ['(< top *fn2-run-max-levels*)','(posp run)','(posp wire-run)','(<= wire-run run)','(posp catalog-tag)','(= (mod unit *fn2-storage-extent-units*) 0)']
    return f'''; The sole physical installation transition updates the global count. Its
; caller supplies Ref fields from an authenticated source catalog/producer.
(defun fn2-run-install-physical ({params})
 (declare (xargs :stobjs fn2-run-installed :guard (fn2-run-installed-wfp fn2-run-installed)))
 (b* (((unless (and {' '.join(domain)})) (mv :bounds fn2-run-installed))
      ((unless (and (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*)
                    (= (fn2-run-installed-physical r fn2-run-installed) 0)))
       (mv :state fn2-run-installed))
      (count (+ 1 (fn2-run-installed-physical-count fn2-run-installed)))
      ((unless (unsigned-byte-p 32 count)) (mv :exhausted fn2-run-installed))
      (fn2-run-installed (fn2-run-installed-put r {' '.join(assignments)}))
      (fn2-run-installed (update-fn2-run-installed-physical-count count fn2-run-installed)))
  (mv :ok fn2-run-installed)))
(fn2-run-installed-preserves fn2-run-install-physical ({params}) :position 1 :raw-rows t)
'''

def transform_runs(runs,apply):
    forms=lr.parse(runs).forms
    decl=lr.match('(defcolumns fn2-run-installed ?*body)',forms,deep=False)[0].node
    runcol=lr.match('(run :u60)',[decl])[0].node
    runs=lr.write(runs,[(runcol.end,runcol.end,' (wire-run :u60)')])
    decl=lr.match('(defcolumns fn2-run-installed ?*body)',lr.parse(runs).forms,deep=False)[0].node
    extra='''
 :extra-fields ((fn2-run-installed-physical-count :type (unsigned-byte 32) :initially 0
 :why "All nonFREE physical installed rows, maintained by shared install/free transitions; not catalog-local or a caller readiness flag."))'''
    out=lr.write(runs,[(decl.end-1,decl.end-1,extra)])
    fn=lr.match('(defun fn2-run-install ?*body)',lr.parse(out).forms,deep=False)[0].node
    out=lr.write(out,[(fn.start,fn.start,constructor(apply)+'\n')])
    # Resident install must not erase an unaccounted physical free-row marker.
    old='((unless (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*))'
    new='((unless (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*)\n                    (= (fn2-run-installed-physical r fn2-run-installed) 0)))'
    if out.count(old)!=1:raise ValueError('resident install shape changed')
    out=out.replace(old,new)
    resident=lr.match('(defun fn2-run-install ?*body)',lr.parse(out).forms,deep=False)[0].node
    runput=lr.match('(run run)',[resident])[0].node
    out=lr.write(out,[(runput.end,runput.end,' (wire-run run)')])
    fn=lr.match('(defun fn2-run-retired-next ?*body)',lr.parse(out).forms,deep=False)[0].node
    tail='''      ((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) (mv :physical fn2-run-installed))
'''
    nextbind=lr.match('(next ?value)',[fn])[0].node
    out=lr.write(out,[(nextbind.start,nextbind.start,tail)])
    return out
if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]/'books'
    apply=root/'checkpoint-summary-apply.lisp';runs=root/'runs.lisp';source=apply.read_text()
    runs.write_text(transform_runs(runs.read_text(),source))
    apply.write_text(transform_apply(source))
