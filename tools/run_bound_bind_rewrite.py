"""Extract the actual physical bind tail; keep catalog/lease admission intact."""
from pathlib import Path
import lisp_rewrite as lr
def one(s,p):
 m=lr.match(p,lr.parse(s).forms,deep=False)
 if len(m)!=1:raise ValueError(p)
 return m[0].node
def transform(source):
 if '(include-book "run-physical-bound-bind")' in source:return source,None
 f=one(source,'(defun fn2-run-load-bind ?*body)');body=f.items[-1]
 if body.items[0].low!='b*':raise ValueError('bind is not b*')
 bindings=body.items[1].items
 hits=[i for i,b in enumerate(bindings) if lr.match('(fn2-pool-reset ?*args)',[b])]
 if len(hits)!=1:raise ValueError('expected sole actual page reset')
 start=hits[0];tail=bindings[start:]
 if len(tail)!=3:raise ValueError('physical binding tail drift')
 tailtext='\n      '.join(source[n.start:n.end] for n in tail)
 replacements=[('(fn2-checkpoint-summary-history 0 fn2-checkpoint-summary)','history'),
  ('(fn2-checkpoint-summary-incarnation 0 fn2-checkpoint-summary)','incarnation'),
  ('(mv code fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)',
   '(mv code fn2-run-loads fn2-pool)')]
 for old,new in replacements:
  if tailtext.count(old)!=1:raise ValueError('tail field drift '+old)
  tailtext=tailtext.replace(old,new)
 # Keep the exact noncatalog part of the original admission conjunction.
 gate=bindings[0].items[0].items[1]
 gates=gate.items[1:]
 if len(gates)!=14:raise ValueError('admission guard drift')
 retained=[]
 for n in gates:
  text=source[n.start:n.end]
  if 'fn2-checkpoint-summary' not in text:retained.append(text)
 if len(retained)!=12:raise ValueError('catalog guard partition drift')
 guard='\n                    '.join(retained)
 lower='''; Shared physical MISS-to-READ transition. Callers retain source authority.
(in-package "ACL2")
(include-book "run-physical-bound")
(fn2-book-layer :c)
(defun fn2-run-bound-bind (c kind owner generation history incarnation fn2-run-loads fn2-run-cursors fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-pool)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and '''+guard+'''
                    (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation)))
       (mv :source fn2-run-loads fn2-pool))
      '''+tailtext+''')
  (mv :need-read fn2-run-loads fn2-pool)))
(fn2-run-load-frames fn2-run-bound-bind
 (c kind owner generation history incarnation fn2-run-loads fn2-run-cursors fn2-pool)
 (fn2-run-loads fn2-run-cursors fn2-pool) ((fn2-run-loads 1) (fn2-pool 2)))
'''
 call='''((mv code fn2-run-loads fn2-pool)
       (fn2-run-bound-bind c kind owner generation
        (fn2-checkpoint-summary-history 0 fn2-checkpoint-summary)
        (fn2-checkpoint-summary-incarnation 0 fn2-checkpoint-summary) fn2-run-loads fn2-run-cursors fn2-pool))'''
 edits=[(tail[0].start,tail[-1].end,call),
        (body.items[-1].start,body.items[-1].end,'(mv code fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)')]
 after=lr.write(source,edits).replace('(include-book "run-physical-bound")','(include-book "run-physical-bound-bind")')
 return after,lower
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1];p=root/'books/run-physical-source.lisp'
 after,lower=transform(p.read_text());p.write_text(after)
 if lower is not None:(root/'books/run-physical-bound-bind.lisp').write_text(lower)
