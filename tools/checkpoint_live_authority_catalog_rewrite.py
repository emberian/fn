"""Thread the actual pending catalog into the existing live authority class."""
from pathlib import Path
import lisp_rewrite as lr
N='fn2-checkpoint-summary-authority-live-'
def rewrite(s):
 forms=lr.parse(s).forms;ed=[]
 live=[lr.match(f'(defun {N}{name} ?*body)',forms)[0].node for name in ['source-p','begin','step']]
 if '(include-book "checkpoint-summary-live-catalog")' in s:raise ValueError('already bound')
 for m in lr.match('(?head ?*args)',forms):
  n=m.node;h=getattr(n.items[0],'low','')
  if h in [N+'source-p',N+'begin',N+'step','fn2-checkpoint-summary-authority'] and any(getattr(x,'low','')=='fn2-checkpoint-source' for x in n.items):
   ed.append((n.items[-1].end,n.items[-1].end,' fn2-checkpoint-summary'))
  elif h=='fn2-core-checkpoint-summary-authority':ed.append((n.items[-1].end,n.items[-1].end,' fn2-core-checkpoint-summary'))
  elif h=='fn2-checkpoint-summary-authority-wfp' and any(f.start <= n.start < f.end for f in live):
   ed.append((n.end,n.end,' (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)'))
 s=lr.write(s,ed);forms=lr.parse(s).forms;ed=[]
 source=lr.match(f'(defun {N}source-p ?*body)',forms)[0].node
 owner=lr.match('(fn2-checkpoint-source-ownerp fn2-checkpoint-source fn2-csnapshot)',[source])[0].node
 ed.append((owner.end,owner.end,'''
  (fn2-checkpoint-summary-live-current-p fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot)
  (= (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-checkpoint-source-rank 0 fn2-checkpoint-source))'''))
 catalog=lr.match('(catalog-tag 0)',forms)[0].node
 ed.append((catalog.start,catalog.end,'(catalog-tag (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary))'))
 step=lr.match(f'(defun {N}step ?*body)',forms)[0].node
 tag=lr.match('(= (fn2-checkpoint-summary-authority-tag 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-source-token 0 fn2-checkpoint-source))',[step])[0].node
 ed.append((tag.end,tag.end,'''
       (= (fn2-checkpoint-summary-authority-catalog-tag 1 fn2-checkpoint-summary-authority)
          (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary))'''))
 return lr.write(s,ed).replace('fn2-core-checkpoint-writer','fn2-checkpoint-writer-table').replace('(include-book "checkpoint-summary-authority-state")','(include-book "checkpoint-summary-authority-state")\n(include-book "checkpoint-summary-live-catalog")\n(include-book "checkpoint-summary-live-close")')
if __name__=='__main__':
 p=Path(__file__).resolve().parents[1]/'books/checkpoint-summary-authority-live.lisp';p.write_text(rewrite(p.read_text()))
