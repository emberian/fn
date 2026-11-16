"""Append actual checkpoint declarations without replacing modern ROOT/core."""
from pathlib import Path
import json
import lisp_rewrite as lr
DATA=json.loads((Path(__file__).parent/'fixtures/checkpoint-preindex-current-source.json').read_text())
def event(text,head,name):
 ms=lr.match('('+head+' '+name+' ?*body)',lr.parse(text).forms,deep=False)
 if len(ms)!=1:raise ValueError('one actual declaration '+head+' '+name)
 return ms[0].node
def src(text,n):return text[n.start:n.end]
def project_index(text):
 if all('(include-book "'+b+'")' in text for b in ('checkpoint-cbase-kind','boot-reader-kind','boot-semantic-kind','checkpoint-master-kind')):return text
 anchor=lr.match('(fn2-machine-index-events)',lr.parse(text).forms,deep=False)
 if len(anchor)!=1:raise ValueError('one actual index boundary')
 # Append after ALL existing kind includes: no existing kind tag shifts.
 added=''.join('(include-book "'+b+'")\n' for b in ('checkpoint-cbase-kind','boot-reader-kind','boot-semantic-kind','checkpoint-master-kind') if '(include-book "'+b+'")' not in text)
 return lr.write(text,[(anchor[0].node.start,anchor[0].node.start,added)])
def project_sealer(text):
 donor=DATA['donor']['machines-c-sealer'];edits=[]
 a=event(text,'defmacro','fn2-sealer-child');b=event(donor,'defmacro','fn2-sealer-child')
 if src(text,a)!=src(donor,b):edits.append((a.start,a.end,src(donor,b)))
 a=event(text,'defun','fn2-sealer-profilep')
 body=src(text,a.items[-1]);add='(unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))'
 if add not in body:edits.append((a.items[-1].end-1,a.items[-1].end-1,' '+add))
 for name in ('fn2-core-run-builds','fn2-core-run-writers','fn2-core-run-restarts'):
  a=event(text,'fn2-sealer-child',name);b=event(donor,'fn2-sealer-child',name)
  old=a.items[3];new=b.items[3]
  if src(text,old)!=src(donor,new):edits.append((old.start,old.end,src(donor,new)))
 return lr.write(text,edits)
def project_read_work(text):
 if '(include-book "run-active-geometry")' not in text:
  anchor=lr.match('(include-book "overlay")',lr.parse(text).forms,deep=False)[0].node
  text=lr.write(text,[(anchor.end,anchor.end,'\n(include-book "run-active-geometry")')])
 donor=DATA['donor']['runs-assemble'];names=('fn2-ra-layout-max-sizes','fn2-ra-layout-max-expression','fn2-ra-key-octet-bound','fn2-ra-key-octet-bounds');added=[]
 for name in names:
  if not lr.match('(defun '+name+' ?*body)',lr.parse(text).forms,deep=False):added.append(src(donor,event(donor,'defun',name)))
 if '(defconst *fn2-run-overlay-search-steps* ' not in text:added.append('(defconst *fn2-run-overlay-search-steps* *fn2-ov-search-steps*)')
 if added:
  anchor=event(text,'defun','fn2-ra-dispatch-events');text=lr.write(text,[(anchor.start,anchor.start,'\n'.join(added)+'\n')])
 a=event(text,'defun','fn2-ra-dispatch-events');b=event(donor,'defun','fn2-ra-dispatch-events')
 # Only generated work declarations are spliced. All existing codec/reader
 # implementations, guard hints and dispatch clauses are byte-preserved.
 wanted=('*fn2-run-layout-max-entry-bytes*','*fn2-run-layout-max-key-octets*','*fn2-c-read-step-bytes*','*fn2-c-read-callback-bytes*')
 events=[]
 for name in wanted:
  if not lr.match('(defconst '+name+' ?*value)',[a],deep=True):
   n=lr.match('(defconst '+name+' ?*value)',[b],deep=True)
   if len(n)!=1:raise ValueError('one generated work bound '+name)
   events.append(src(donor,n[0].node))
 if events:
  first=lr.match('(defun fn2-run-layout-physical-ref-p ?*body)',[a],deep=True)
  if len(first)!=1:raise ValueError('existing codec dispatcher anchor')
  text=lr.write(text,[(first[0].node.start,first[0].node.start,'\n   '.join(events)+'\n   ')])
 return text
if __name__=='__main__':
 for book,fn in (('assembly-index',project_index),('machines-c-sealer',project_sealer),('runs-assemble',project_read_work)):
  p=Path(__file__).resolve().parents[1]/'books'/(book+'.lisp');text=p.read_text();p.write_text(fn(text))

def project_writer_table_references(text):
 """Only :tables fields in actual cost declarations; no runtime replacement."""
 edits=[]
 for m in lr.match('(defcost ?name ?*body)',lr.parse(text).forms,deep=True):
  xs=m.captures['body']
  for i,x in enumerate(xs[:-1]):
   if getattr(x,'low','')==':tables' and isinstance(xs[i+1],lr.Lst):
    for field in xs[i+1].items:
     if getattr(field,'low','')=='fn2-core-checkpoint-writer':edits.append((field.start,field.end,'fn2-checkpoint-writer-table'))
 return lr.write(text,edits)
