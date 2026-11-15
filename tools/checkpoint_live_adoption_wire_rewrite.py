"""Connect actual bounded live handoff to the existing maintenance actor."""
from pathlib import Path
import lisp_rewrite as lr
PHASES=['live-hold','live-preflight-begin','live-preflight','live-writer-begin','live-writer-poll','live-open','live-install','live-versions','live-retire-runs','live-retire-overlays','live-swap','live-release-old']
def value(n,key):return next(n.items[i+1] for i,x in enumerate(n.items) if getattr(x,'low','')==key)
def source():
 return '''
  (:live-hold :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-cbase-live-acquire-op budget) :accept () :case
    (((:more :yield) (:charge :steps *fn2-work-stage* :runnable t))
     ((:held) (:next :rebase-begin) (:charge :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-preflight-begin :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-begin-op row-token *fn2-checkpoint-master-kind* id row-generation) :accept (:more))
   (:next :live-preflight) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
  (:live-preflight :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-preflight-op budget) :accept () :case
    (((:more :yield) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     ((:prepared) (:next :live-writer-begin) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-writer-begin :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code writer) (fn2-c-source-writer-begin id row-generation) :accept () :case
    (((:waiting) (:set (source-writer writer)) (:next :live-writer-poll) (:charge :steps *fn2-work-small* :runnable t))
     ((:exclusive) (:set (source-writer writer)) (:next :live-open) (:charge :steps *fn2-work-small* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-writer-poll :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-c-source-writer-poll row-source-writer id row-generation) :accept () :case
    (((:waiting) (:idle))
     ((:exclusive) (:next :live-open) (:charge :steps *fn2-work-small* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-open :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-open-op row-source-writer) :accept (:more))
   (:next :live-install) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
  (:live-install :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-install-op budget) :accept () :case
    (((:more :yield) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     ((:versions) (:next :live-versions) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-versions :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-versions-op) :accept (:retire))
   (:next :live-retire-runs) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
  (:live-retire-runs :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-retire-runs-op budget) :accept () :case
    (((:more :yield :held) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     ((:overlays) (:next :live-retire-overlays) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-retire-overlays :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-retire-overlays-op budget) :accept () :case
    (((:more :yield :held) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     ((:swap) (:next :live-swap) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:live-swap :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-swap-op) :accept (:adopted))
   (:next :rebase-consume) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
  (:live-release-old :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-live-adoption-release-old-op budget) :accept () :case
    (((:more :yield :retained) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     ((:released) (:next :release) (:charge :bytes 512 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))'''
def rewrite(decl,impl):
 d=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(decl).forms,deep=False)[0].node;ed=[]
 for key,text in [(':states',' '.join(':'+x for x in PHASES)),(':holds',' '.join('(:'+x+' :storage-window :storage-window)' for x in PHASES)),(':arms',' '.join('(:'+x+')' for x in PHASES)),(':fields','(source-writer :u60)')]:
  n=value(d,key);ed.append((n.items[-1].end,n.items[-1].end,' '+text))
 decl=lr.write(decl,ed)
 m=lr.match('(defmachine-arms fn2-checkpoint-master ?*body)',lr.parse(impl).forms,deep=False)[0].node;arms=value(m,':arms');ed=[]
 for phase,old,new in [('live-catalog-close','rebase-begin','live-hold'),('rebase-archive','rebase-consume','live-preflight-begin'),('rebase-consume','release','live-release-old')]:
  arm=next(x for x in arms.items if x.items[0].low==':'+phase);n=lr.match(f'(:next :{old})',[arm])[0].node;ed.append((n.start,n.end,f'(:next :{new})'))
 replacements={'fn2-checkpoint-master-release-complete-op':'fn2-checkpoint-live-adoption-release-complete-op','fn2-checkpoint-events-rearm':'fn2-checkpoint-live-adoption-events-rearm-op','fn2-checkpoint-master-rearm-op':'fn2-checkpoint-live-adoption-rearm-op','fn2-csnapshot-release':'fn2-checkpoint-live-adoption-finish-op'}
 for old,new in replacements.items():
  n=lr.match(f'({old} ?*args)',[m])[0].node;ed.append((n.items[0].start,n.items[0].end,new))
  if old=='fn2-csnapshot-release':ed.append((n.end,n.end,' :accept (:complete)'))
 ed.append((arms.items[-1].end,arms.items[-1].end,source()))
 impl=lr.write(impl,ed)
 include='(include-book "checkpoint-live-adoption-rearm")'
 if include not in impl:impl=impl.replace('(include-book "checkpoint-summary-authority-live")','(include-book "checkpoint-summary-authority-live")\n'+include)
 return decl,impl
if __name__=='__main__':
 b=Path(__file__).resolve().parents[1]/'books';a=b/'checkpoint-master-state.lisp';c=b/'checkpoint-master-arms.lisp'
 x,y=rewrite(a.read_text(),c.read_text());a.write_text(x);c.write_text(y)
