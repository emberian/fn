"""Change ONLY two old source-fit arms to canonical bank admission calls."""
from pathlib import Path
import lisp_rewrite as lr
BEGIN='''(:source-fit-overlays :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-live-bank-begin-op row-token *fn2-checkpoint-master-kind* id row-generation)
    :accept () :case
    (((:more) (:next :source-fit-runs) (:charge :steps *fn2-work-stage* :runnable t))
     (:otherwise (:stop :checkpoint)))))'''
STEP='''(:source-fit-runs :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-live-bank-step-op row-token *fn2-checkpoint-master-kind* id row-generation)
    :accept () :case
    (((:more) (:charge :steps *fn2-work-stage* :runnable t))
     ((:ready)
      (:do (fit) (fn2-checkpoint-live-fit-step-op row-token *fn2-checkpoint-master-kind* id row-generation)
       :accept () :case
       (((:fit) (:next :reserve) (:charge :steps *fn2-work-stage* :runnable t))
        ((:resources) (:next :abort-empty) (:charge :steps *fn2-work-small* :runnable t))
        (:otherwise (:stop :checkpoint)))))
     ((:resources) (:next :abort-empty) (:charge :steps *fn2-work-small* :runnable t))
     (:otherwise (:stop :checkpoint)))))'''
OLD_COMMENT='''  ; The actual held cut is measured before construction or working admission.
  ; A shortage goes through the same exact empty-attempt cut release, then
  ; the existing :sealable grant observes the measured compaction demand.
'''
NEW_COMMENT='''  ; Real row admission scans only the retained inactive physical bank. It
  ; precedes working/B allocations and never compares original count to FREE R.
'''
def atom(n):return n.low if isinstance(n,lr.Atom) else None
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,lr.Pre):yield from walk(n.node)
def transform(text):
 tops=[n for n in lr.parse(text).forms if isinstance(n,lr.Lst) and len(n.items)>1 and atom(n.items[0])=='defmachine-arms' and atom(n.items[1])=='fn2-checkpoint-master']
 if len(tops)!=1:raise ValueError('expected exactly one actual master arm declaration')
 edits=[]
 for name,replacement in [(':source-fit-overlays',BEGIN),(':source-fit-runs',STEP)]:
  matches=[n for n in walk(tops[0]) if isinstance(n,lr.Lst) and n.items and atom(n.items[0])==name]
  if len(matches)!=1:raise ValueError('missing/duplicate actual source-fit arm '+name)
  n=matches[0]
  if text[n.start:n.end]!=replacement:edits.append((n.start,n.end,replacement))
 out=lr.write(text,edits)
 if OLD_COMMENT in out:out=out.replace(OLD_COMMENT,NEW_COMMENT,1)
 return out
if __name__=='__main__':
 import sys
 p=Path(sys.argv[1]);p.write_text(transform(p.read_text()))
