"""Wire the existing singleton maintenance actor to its bounded orphan pass."""
from pathlib import Path
import lisp_rewrite as lr
STATES = tuple(':teardown-owned-'+s for s in ('begin','scan','submit','wait','uncertain','holding-uncertain'))
def keyword_value(node, key):
    for i,x in enumerate(node.items):
        if isinstance(x,lr.Atom) and x.low==key:return node.items[i+1]
    raise ValueError(key)
def rewrite_state(text):
    if STATES[0] in text:return text,0
    f=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(text).forms)[0].node
    edits=[]
    for key,addition in [(':states','\n          '+' '.join(STATES)),(':arms','\n          '+' '.join('('+s+')' for s in STATES)),(':holds','\n         (:teardown-owned-wait :storage-window) (:teardown-owned-holding-uncertain :storage-window)')]:
        n=keyword_value(f,key);edits.append((n.end-1,n.end-1,addition))
    return lr.write(text,edits),len(edits)
ARMS='''
  (:teardown-owned-begin :on-refusal ((:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-owned-retirement-begin-op id row-generation) :accept () :case
    (((:more) (:set (scan 0)) (:next :teardown-owned-scan) (:charge :steps *fn2-work-stage* :runnable t))
     ((:none) (:next :done) (:charge :steps *fn2-work-small* :runnable t))
     (:otherwise (:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:teardown-owned-scan :on-refusal ((:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:if (and (natp budget) (< 0 budget))
    ((:do (code next epoch allocation) (fn2-checkpoint-owned-retirement-scan-op *fn2-checkpoint-master-kind* row-scan)
      :accept () :case
      (((:more) (:set (scan next)) (:charge :steps *fn2-work-stage* :runnable t))
       ((:eligible) (:set (teardown-extent next) (teardown-epoch epoch) (teardown-allocation allocation))
        (:next :teardown-owned-submit) (:charge :steps *fn2-work-stage* :runnable t))
       ((:done) (:next :done) (:charge :steps *fn2-work-small* :runnable t))
       (:otherwise (:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
    ((:yield))))
  (:teardown-owned-submit :on-refusal ((:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:if (and (natp budget) (< 0 budget))
    ((:do (code outcome batch event) (fn2-checkpoint-owned-retirement-submit-op id row-generation)
      :effects ((:acquire (:storage-window))) :accept () :case
      (((:ok) (:set (batch batch) (event event))
        (:if (eq outcome :ok)
         ((:next :teardown-owned-wait) (:charge :bytes *fn2-checkpoint-teardown-member-bytes* :steps *fn2-work-stage* :runnable t))
         ((:next :teardown-owned-holding-uncertain) (:charge :bytes *fn2-checkpoint-teardown-member-bytes* :steps *fn2-work-small* :runnable t))))
       ((:busy :exhausted) (:park :checkpoint-needed))
       ((:retained) (:if (< row-scan *fn2-alloc-none*)
         ((:set (scan (+ 1 row-scan))) (:next :teardown-owned-scan) (:charge :steps *fn2-work-stage* :runnable t))
         ((:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t))))
       (:otherwise (:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
    ((:yield))))
  (:teardown-owned-wait :on-refusal ((:next :teardown-owned-holding-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:if (and (natp budget) (< 0 budget))
    ((:do (code outcome batch event) (fn2-checkpoint-owned-retirement-poll-op id row-generation)
      :effects ((:release (:storage-window))) :accept () :case
      (((:pending) (:idle))
       ((:ok) (:if (and (equal batch row-batch) (equal event row-event) (< row-scan *fn2-alloc-none*))
         ((:set (scan (+ 1 row-scan))) (:next :teardown-owned-scan) (:charge :steps *fn2-work-stage* :runnable t))
         ((:next :teardown-owned-uncertain) (:charge :steps *fn2-work-small* :runnable t))))
       (:otherwise (:next :teardown-owned-holding-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
    ((:yield))))
  (:teardown-owned-uncertain (:set (stopped 1)) (:stop :checkpoint))
  (:teardown-owned-holding-uncertain (:set (stopped 1)) (:stop :checkpoint))
'''
def rewrite_arms(text):
    if STATES[0] in text:return text,0
    text=text.replace('(include-book "checkpoint-teardown-sweep")','(include-book "checkpoint-teardown-sweep")\n(include-book "checkpoint-owned-retirement")')
    parsed=lr.parse(text);f=lr.match('(defmachine-arms fn2-checkpoint-master ?*body)',parsed.forms)[0].node
    arms=keyword_value(f,':arms');sel=lr.match('(:teardown-select ?*body)',[arms])[0]
    done=lr.match('((:done) (:next :done) ?*tail)',[sel.node])[0]
    old=text[done.start:done.end];new=old.replace('(:next :done)','(:next :teardown-owned-begin)',1)
    return lr.write(text,[(done.start,done.end,new),(arms.end-1,arms.end-1,ARMS)]),2
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');args=p.parse_args()
    for filename,fn in [('checkpoint-master-state.lisp',rewrite_state),('checkpoint-master-arms.lisp',rewrite_arms)]:
        path=Path(__file__).resolve().parents[1]/'books'/filename;out,n=fn(path.read_text());lr.parse(out);print(filename,n)
        if args.write:path.write_text(out)
