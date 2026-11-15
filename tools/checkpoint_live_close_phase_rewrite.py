"""Insert the real catalog-close child before the existing rebase route."""
import lisp_rewrite as lr

def value(n,key):return next(n.items[i+1] for i,x in enumerate(n.items) if getattr(x,'low','')==key)
def rewrite(decl,impl):
 phase=':live-catalog-close';ed=[]
 node=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(decl).forms,deep=False)[0].node
 for key,text in [(':states',phase),(':holds','('+phase+' :storage-window :storage-window)'),(':arms','('+phase+')')]:
  n=value(node,key);ed.append((n.items[-1].end,n.items[-1].end,' '+text))
 decl=lr.write(decl,ed)
 node=lr.match('(defmachine-arms fn2-checkpoint-master ?*body)',lr.parse(impl).forms,deep=False)[0].node
 arms=value(node,':arms');arm=next(x for x in arms.items if x.items[0].low==':summary-authority-copy')
 route=lr.match('(:next :rebase-begin)',[arm])[0].node
 new='''
  (:live-catalog-close :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-summary-live-close-op) :accept (:captured))
   (:next :rebase-begin) (:charge :bytes 32 :steps *fn2-work-stage* :runnable t))'''
 impl=lr.write(impl,[(route.start,route.end,'(:next :live-catalog-close)'),(arms.items[-1].end,arms.items[-1].end,new)])
 return decl,impl
if __name__=='__main__':
 from pathlib import Path
 b=Path(__file__).resolve().parents[1]/'books';a=b/'checkpoint-master-state.lisp';c=b/'checkpoint-master-arms.lisp'
 x,y=rewrite(a.read_text(),c.read_text());a.write_text(x);c.write_text(y)
