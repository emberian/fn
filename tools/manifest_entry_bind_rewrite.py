#!/usr/bin/env python3
"""Extract the actual no-filter manifest field binding into one shared helper."""
from pathlib import Path
import lisp_rewrite as lr
SCALARS={'schema':'schema','run':'run','height':'height','entries':'entries','root-unit':'unit','root-epoch':'epoch','root-allocation':'allocation'}
EXPECTED=set(SCALARS)|{'filter-unit','filter-epoch','filter-allocation','root-hash','filter-hash'}
def raw(s,n):return s[n.start:n.end]
def extract(s,head,name):
 fn=lr.match('('+head+' '+name+' ?*body)',lr.parse(s).forms,deep=False)[0].node
 bindings=[];fields={}
 for m in lr.match('(fn2-fields ?value)',[fn]):
  b=m.node;v=m.captures['value']
  if not hasattr(v,'items') or v.items[0].low not in ['fn2-fields-set-value','fn2-fields-put']:continue
  offset=v.items[1]
  if not hasattr(offset,'items') or len(offset.items)!=3:continue
  constant=offset.items[2].low
  if not constant.startswith('*fn2-manifest-entry-field-'):continue
  field=constant[len('*fn2-manifest-entry-field-'):-1]
  bindings.append(b);fields[field]=(b,v)
 if set(fields)!=EXPECTED or len(bindings)!=12:raise ValueError('manifest binding class drift')
 for f in ['filter-unit','filter-epoch','filter-allocation']:
  if fields[f][1].items[2].low!='0':raise ValueError('not no-filter producer')
 return fn,bindings,fields

def helper(source):
 _,bindings,fields=extract(source,'defun','fn2-checkpoint-metadata-manifest-emit')
 rewritten=[]
 for b in bindings:
  field=next(k for k,(x,_) in fields.items() if x.start==b.start)
  text=raw(source,b)
  if field in SCALARS:
   v=fields[field][1].items[2];text=lr.write(source,[(v.start,v.end,SCALARS[field])])[b.start:b.end-(v.end-v.start)+len(SCALARS[field])]
  rewritten.append(text)
 return '''; Shared field binding only: callers derive subject/Ref/hash from their
; actual completed source. Both producers own a 64-byte root/zero-filter window.
(defun fn2-manifest-bind-unfiltered (base schema run height entries unit epoch allocation slot gen fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (fn2-fields-wfp fn2-fields)))
 (b* (((unless (and (natp base) (<= (+ base *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run) (unsigned-byte-p 8 height)
                    (unsigned-byte-p 60 entries) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
                    (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))) (mv :bounds fn2-fields))
      '''+'\n      '.join(rewritten)+''')
  (mv :ok fn2-fields)))
(fn2-fields-preserves fn2-manifest-bind-unfiltered
 (base schema run height entries unit epoch allocation slot gen fn2-fields) :position 1 :raw-rows t)
'''

def replace(source,head,name,refusal):
 _,bindings,fields=extract(source,head,name)
 values=[raw(source,fields[f][1].items[2]) for f in SCALARS]
 root=fields['root-hash'][1]
 def value(field):
  return next(x.items[1] for x in root.items[2:] if hasattr(x,'items') and x.items[0].low==field)
 values += [raw(source,value('ref-slot')),raw(source,value('ref-gen'))]
 call='''((mv field-code fn2-fields) (fn2-manifest-bind-unfiltered base '''+' '.join(values)+''' fn2-fields))
      ((unless (eq field-code :ok)) '''+refusal+''')'''
 return lr.write(source,[(bindings[0].start,bindings[-1].end,call)])
if __name__=='__main__':
 b=Path(__file__).resolve().parents[1]/'books'
 old=(b/'checkpoint-metadata-manifest.lisp').read_text()
 manifest=b/'runs-manifest.lisp';manifest.write_text(manifest.read_text()+'\n'+helper(old))
 (b/'checkpoint-metadata-manifest.lisp').write_text(replace(old,'defun','fn2-checkpoint-metadata-manifest-emit','(fn2-checkpoint-metadata-manifest-emit-mv field-code)'))
 p=b/'event-archive-manifest.lisp';p.write_text(replace(p.read_text(),'fn2-event-archive-operation','fn2-event-archive-manifest-emit',
 '(mv field-code fn2-event-archive fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)'))
