"""Join the actual typed live replacement to the existing archive/base cleanup."""
from pathlib import Path
import argparse
import lisp_rewrite as lr
PHASES=(':live-catalog-begin',':live-catalog-copy',':live-cbase',':live-exclusive',':live-install',':live-retire',':live-readiness-begin',':live-readiness-scan',':live-promote',':live-reopen')
ARMS='''
  (:live-catalog-begin :on-refusal ((:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-one-turn-steps* :runnable t))
   (:do (code) (fn2-checkpoint-live-catalog-begin-op) :accept () :case
    (((:more) (:next :live-catalog-copy) (:charge :bytes 64 :steps *fn2-master-live-one-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-one-turn-steps* :runnable t)))))
  (:live-catalog-copy :on-refusal ((:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t))
   (:do (code) (fn2-checkpoint-live-catalog-step-op) :accept () :case
    (((:more) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t))
     ((:captured) (:next :live-cbase) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t)))))
  (:live-cbase :on-refusal ((:next :uncertain) (:charge :bytes 32 :steps *fn2-master-live-two-turn-steps* :runnable t))
   (:do (code) (fn2-checkpoint-live-cbase-step-op) :accept () :case
    (((:more) (:charge :bytes 32 :steps *fn2-master-live-two-turn-steps* :runnable t))
     ((:held) (:next :live-exclusive) (:charge :bytes 32 :steps *fn2-master-live-two-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes 32 :steps *fn2-master-live-two-turn-steps* :runnable t)))))
  (:live-exclusive :on-refusal ((:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t))
   (:do (code) (fn2-checkpoint-live-replace-begin-op) :accept () :case
    (((:more) (:next :live-install) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t))
     ((:waiting) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-two-turn-steps* :runnable t)))))
  (:live-install :on-refusal ((:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
   (:if (< budget 1) ((:charge :steps *fn2-master-three-case-controller-steps* :runnable t))
    ((:do (code) (fn2-checkpoint-live-replace-install-step-op budget) :accept () :case
      (((:more) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
       ((:installed) (:next :live-retire) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
       ((:yield) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
       (:otherwise (:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t)))))))
  (:live-retire :on-refusal ((:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
   (:if (< budget 1) ((:charge :steps *fn2-master-three-case-controller-steps* :runnable t))
    ((:do (code) (fn2-checkpoint-live-replace-retire-step-op budget) :accept () :case
      (((:more) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
       ((:resources) (:next :live-readiness-begin) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
       ((:yield) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t))
       (:otherwise (:next :uncertain) (:charge :bytes 64 :steps *fn2-master-live-three-turn-steps* :runnable t)))))))
  (:live-readiness-begin :on-refusal ((:next :uncertain) (:charge :bytes 0 :steps *fn2-master-live-one-turn-steps* :runnable t))
   (:do (code) (fn2-run-load-readiness-live-begin-op) :accept () :case
    (((:more) (:next :live-readiness-scan) (:charge :bytes 0 :steps *fn2-master-live-one-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes 0 :steps *fn2-master-live-one-turn-steps* :runnable t)))))
  (:live-readiness-scan :on-refusal ((:next :uncertain) (:charge :bytes 0 :steps *fn2-master-live-three-turn-steps* :runnable t))
   (:if (< budget 1) ((:charge :steps *fn2-master-three-case-controller-steps* :runnable t))
    ((:do (code) (fn2-run-load-readiness-owned-step budget) :accept () :case
      (((:more) (:charge :bytes 0 :steps *fn2-master-live-three-turn-steps* :runnable t))
       ((:complete) (:next :live-promote) (:charge :bytes 0 :steps *fn2-master-live-three-turn-steps* :runnable t))
       ((:yield) (:charge :bytes 0 :steps *fn2-master-live-three-turn-steps* :runnable t))
       (:otherwise (:next :uncertain) (:charge :bytes 0 :steps *fn2-master-live-three-turn-steps* :runnable t)))))))
  (:live-promote :on-refusal ((:next :uncertain) (:charge :bytes *fn2-checkpoint-live-promotion-bytes* :steps *fn2-master-promote-turn-steps* :runnable t))
   (:do (code) (fn2-checkpoint-live-replace-finish-op) :accept () :case
    (((:more) (:charge :bytes *fn2-checkpoint-live-promotion-bytes* :steps *fn2-master-promote-turn-steps* :runnable t))
     ((:promoted) (:next :rebase-begin) (:charge :bytes *fn2-checkpoint-live-promotion-bytes* :steps *fn2-master-promote-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes *fn2-checkpoint-live-promotion-bytes* :steps *fn2-master-promote-turn-steps* :runnable t)))))
  (:live-reopen :on-refusal ((:next :uncertain) (:charge :bytes *fn2-checkpoint-live-reopen-bytes* :steps *fn2-master-reopen-turn-steps* :runnable t))
   (:do (code) (fn2-checkpoint-live-replace-reopen-op) :accept () :case
    (((:applied) (:next :release) (:charge :bytes *fn2-checkpoint-live-reopen-bytes* :steps *fn2-master-reopen-turn-steps* :runnable t))
     (:otherwise (:next :uncertain) (:charge :bytes *fn2-checkpoint-live-reopen-bytes* :steps *fn2-master-reopen-turn-steps* :runnable t)))))
'''
def _state(text):
 m=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(text).forms,deep=False)
 if len(m)!=1:raise ValueError('one actual master declaration required')
 xs=m[0].captures['body'];edits=[]
 for key in (':states',':holds',':arms'):
  seq=next(xs[i+1] for i,x in enumerate(xs[:-1]) if getattr(x,'low','')==key)
  names={getattr(x,'low','') if isinstance(x,lr.Atom) else getattr(x.items[0],'low','') for x in seq.items}
  if all(x in names for x in PHASES):continue
  if any(x in names for x in PHASES):raise ValueError('partial live master declaration '+key)
  added=' '.join(PHASES) if key==':states' else ' '.join('('+x+(' :storage-window :storage-window' if key==':holds' else '')+')' for x in PHASES)
  edits.append((seq.end-1,seq.end-1,'\n          '+added))
 return lr.write(text,edits),len(edits)
def _arms(text):
 parsed=lr.parse(text);m=lr.match('(defmachine-arms fn2-checkpoint-master :declare ?*body)',parsed.forms,deep=False)
 if len(m)!=1:raise ValueError('one actual declared master body required')
 xs=m[0].captures['body'];seq=next(xs[i+1] for i,x in enumerate(xs[:-1]) if getattr(x,'low','')==':arms')
 live=[x for x in seq.items if x.items and getattr(x.items[0],'low','') in PHASES]
 if len(live)==len(PHASES):return text,0
 if live:raise ValueError('partial live master arms')
 edits=[]
 for phase,old,new in ((':summary-authority-copy',':rebase-begin',':live-catalog-begin'),(':rebase-consume',':release',':live-reopen')):
  matches=lr.match('('+phase+' ?*body)',[seq],deep=True)
  if len(matches)!=1:raise ValueError('exact existing '+phase+' required')
  n=matches[0].node;src=text[n.start:n.end];needle='(:next '+old+')'
  if src.count(needle)!=1:raise ValueError('ambiguous source continuation '+phase)
  edits.append((n.start,n.end,src.replace(needle,'(:next '+new+')')))
 edits.append((seq.end-1,seq.end-1,'\n'+ARMS))
 return lr.write(text,edits),len(edits)
def state(text):
 text,n=_state(text);edits=[]
 for book in ('checkpoint-master-work',):
  if not lr.match('(include-book "'+book+'")',lr.parse(text).forms,deep=False):
   anchor=lr.match('(include-book "machine-arms")',lr.parse(text).forms,deep=False)
   if len(anchor)!=1:raise ValueError('one kind declaration anchor required')
   text=lr.write(text,[(anchor[0].node.end,anchor[0].node.end,'\n(include-book "'+book+'")')]);n+=1
 m=lr.match('(defconst *fn2-checkpoint-master-byte-budget* ?expr)',lr.parse(text).forms,deep=False)
 if len(m)!=1:raise ValueError('one existing master byte budget required')
 node=m[0].captures['expr'];src=text[node.start:node.end]
 assertion='(assert-event (and (<= *fn2-directory-rebase-consume-bytes* *fn2-checkpoint-master-byte-budget*) (<= *fn2-checkpoint-live-reopen-bytes* *fn2-checkpoint-master-byte-budget*)))'
 if assertion not in text:
  text=lr.write(text,[(m[0].node.end,m[0].node.end,'\n'+assertion)]);n+=1
 if not lr.match('(defconst *fn2-checkpoint-master-step-budget* ?expr)',lr.parse(text).forms,deep=False):
  machine=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(text).forms,deep=False)[0].node
  text=lr.write(text,[(machine.start,machine.start,'(defconst *fn2-checkpoint-master-step-budget* (max 32 *fn2-master-consume-turn-steps* *fn2-master-promote-turn-steps* *fn2-master-reopen-turn-steps* *fn2-master-live-three-turn-steps*))\n\n')]);n+=1
 machine=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(text).forms,deep=False)[0]
 xs=machine.captures['body'];seq=next(xs[i+1] for i,x in enumerate(xs[:-1]) if getattr(x,'low','')==':budget-cost')
 items=seq.items;node=next(items[i+1] for i,x in enumerate(items[:-1]) if getattr(x,'low','')==':steps')
 if getattr(node,'low','')!='*fn2-checkpoint-master-step-budget*':
  if getattr(node,'low','')!='32':raise ValueError('unexpected master step budget')
  text=lr.write(text,[(node.start,node.end,'*fn2-checkpoint-master-step-budget*')]);n+=1
 return text,n
def arms(text):
 text,n=_arms(text)
 m=lr.match('(:rebase-consume ?*body)',lr.parse(text).forms,deep=True)
 if len(m)!=1:raise ValueError('one canonical consume arm required')
 node=m[0].node;src=text[node.start:node.end]
 old='(:charge :bytes 4096 :steps *fn2-work-stage* :runnable t)'
 new='(:charge :bytes *fn2-directory-rebase-consume-bytes* :steps *fn2-master-consume-turn-steps* :runnable t)'
 if old in src:text=lr.write(text,[(node.start,node.end,src.replace(old,new).replace('(:charge :steps *fn2-work-small* :runnable t)',new))]);n+=1
 elif new not in src:raise ValueError('unexpected canonical consume charge')
 # Only these audited callees forward BUDGET into byte/span codecs. Abort,
 # release, bind and consume use structural/positive budgets and are untouched.
 edits=[]
 for op in ('fn2-checkpoint-root1-step-op','fn2-checkpoint-events-step','fn2-checkpoint-map-source-step-op','fn2-checkpoint-build-source-op'):
  matches=lr.match('('+op+' ?budget ?*rest)',lr.parse(text).forms,deep=True)
  if len(matches)!=1:raise ValueError('one actual pure byte callback required: '+op)
  arg=matches[0].captures['budget']
  if getattr(arg,'low','')=='*fn2-checkpoint-master-pure-byte-quantum*':continue
  if getattr(arg,'low','')!='budget':raise ValueError('unexpected byte callback quantum '+op)
  edits.append((arg.start,arg.end,'*fn2-checkpoint-master-pure-byte-quantum*'))
 text=lr.write(text,edits);n+=len(edits)
 text,count=pure_result_charges(text)
 return text,n+count

def pure_result_charges(text):
 # Every result follows the same real pure call. Charge its declared byte
 # envelope even on refusal/wait; WAIT still parks, YIELD stays runnable.
 edits=[]
 for phase,byte in ((':root1-source','*fn2-checkpoint-root1-turn-bytes*'),(':events-source','4096'),(':map-source','4096'),(':descriptor-source','4096')):
  matches=lr.match('('+phase+' ?*body)',lr.parse(text).forms,deep=True)
  if len(matches)!=1:raise ValueError('one audited pure source arm required '+phase)
  node=matches[0].node
  for m in lr.match('(:charge ?*body)',[node],deep=True):
   runnable='nil' if ':runnable nil' in text[m.node.start:m.node.end] else 't'
   charge='(:charge :bytes '+byte+' :steps *fn2-work-stage* :runnable '+runnable+')'
   if text[m.node.start:m.node.end]!=charge:edits.append((m.node.start,m.node.end,charge))
  for head,runnable in ((':yield','t'),(':idle','nil')):
   for m in lr.match('('+head+')',[node],deep=True):
    edits.append((m.node.start,m.node.end,'(:charge :bytes '+byte+' :steps *fn2-work-stage* :runnable '+runnable+')'))
 return lr.write(text,edits),len(edits)

def face_reopen(e):
 matches=lr.match('(fn2-run-loader-core-face-events ?ops ?world)',lr.parse(e).forms,deep=True)
 selected=[]
 for m in matches:
  seq=m.captures['ops']
  if isinstance(seq,lr.Pre) and isinstance(seq.node,lr.Lst) and any(getattr(x,'low','')=='fn2-checkpoint-live-replace-finish-op' for x in seq.node.items):selected.append(seq.node)
 if len(selected)!=1:raise ValueError('one actual typed face projection required')
 seq=selected[0]
 if any(getattr(x,'low','')=='fn2-checkpoint-live-replace-reopen-op' for x in seq.items):return e,0
 return lr.write(e,[(seq.end-1,seq.end-1,' fn2-checkpoint-live-replace-reopen-op')]),1
def assembly(c,e):
 e,facecount=face_reopen(e)
 early=lr.match('(fn2-checkpoint-master-events)',lr.parse(c).forms,deep=False)
 late=lr.match('(fn2-checkpoint-master-events)',lr.parse(e).forms,deep=False)
 if not early and len(late)==1:return c,e,facecount
 if len(early)!=1 or late:raise ValueError('one early actual master emitter required')
 anchors=[f for f in lr.parse(e).forms if isinstance(f,lr.Lst) and f.items and getattr(f.items[0],'low','')=='make-event' and 'fn2-checkpoint-live-replace-finish-op' in e[f.start:f.end]]
 if len(anchors)!=1:raise ValueError('exact actual typed finish face emitter required')
 n=early[0].node;a=anchors[0]
 return lr.write(c,[(n.start,n.end+(1 if c[n.end:n.end+1]=='\n' else 0),'')]),lr.write(e,[(a.end,a.end,'\n(fn2-checkpoint-master-events)')]),2+facecount
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);a=ap.parse_args()
 for name,fn in [('checkpoint-master-state',state),('checkpoint-master-arms',arms)]:
  p=a.root/'books'/(name+'.lisp');out,n=fn(p.read_text());p.write_text(out);print(name,n)
 c=a.root/'books/assembly-callbacks-c.lisp';e=a.root/'books/assembly-callbacks-e-cns.lisp'
 co,eo,n=assembly(c.read_text(),e.read_text());c.write_text(co);e.write_text(eo);print('actual master emission move',n)
if __name__=='__main__':main()
