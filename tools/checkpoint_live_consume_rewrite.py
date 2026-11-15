"""Require the real ADOPTED terminal at the existing atomic base join."""
from pathlib import Path
import lisp_rewrite as lr
import checkpoint_summary_recursion_rewrite as total

def children(source):
 n=lr.match('(defconst *fn2-live-adoption-children* ?value)',lr.parse(source).forms,deep=False)[0].node
 return [x.low for x in n.items[2].node.items]
def rewrite(source,adopter):
 source,_=total.rewrite(source,{'fn2-directory-rebase-transfer-bytes':520,'fn2-directory-rebase-seal-p':8,'fn2-directory-rebase-base-seal':8})
 forms=lr.parse(source).forms
 n=lr.match('(defun fn2-directory-rebase-consume ?*body)',forms,deep=False)[0].node
 present={x.low for x in n.items[2].items};extra=[x for x in children(adopter) if x not in present]
 ed=[]
 ed.append((n.items[2].items[-1].end,n.items[2].items[-1].end,' '+' '.join(extra)))
 xargs=lr.match('(xargs ?*body)',[n])[0].node
 st=next(xargs.items[i+1] for i,x in enumerate(xargs.items) if getattr(x,'low','')==':stobjs')
 ed.append((st.items[-1].end,st.items[-1].end,' '+' '.join(extra)))
 guard=next(xargs.items[i+1] for i,x in enumerate(xargs.items) if getattr(x,'low','')==':guard')
 ed.append((guard.items[-1].end,guard.items[-1].end,' '+' '.join(f'({x}-wfp {x})' for x in extra)))
 held=lr.match('(= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)',[n])[0].node
 ed.append((held.start,held.end,'(= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-adopted*)\n                    (fn2-checkpoint-live-adoption-adopted-p '+' '.join(children(adopter))+')'))
 proof=lr.match('(fn2-directory-rebase-preserves fn2-directory-rebase-consume ?*body)',forms,deep=False)[0].node
 params=proof.items[2];ed.append((params.items[-1].end,params.items[-1].end,' '+' '.join(extra)))
 hyps=next(proof.items[i+1] for i,x in enumerate(proof.items) if getattr(x,'low','')==':hyps')
 ed.append((hyps.items[-1].end,hyps.items[-1].end,' '+' '.join(f'({x}p {x}) ({x}-wfp {x})' for x in extra)))
 cost=lr.match('(defcost fn2-checkpoint-directory-rebase-consume-op ?*body)',forms,deep=False)[0].node
 tables=next(cost.items[i+1] for i,x in enumerate(cost.items) if getattr(x,'low','')==':tables')
 ed.append((tables.items[-1].end,tables.items[-1].end,' '+' '.join(x.replace('fn2-','fn2-core-',1) for x in extra)))
 return lr.write(source,ed).replace('(in-package "ACL2")','(in-package "ACL2")\n(include-book "checkpoint-live-adoption")',1)
if __name__=='__main__':
 b=Path(__file__).resolve().parents[1]/'books';p=b/'checkpoint-directory-consume.lisp';p.write_text(rewrite(p.read_text(),(b/'checkpoint-live-adoption.lisp').read_text()))
