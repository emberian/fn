"""Join actual named private MK initialization to the real borrow constructor."""
from pathlib import Path
import lisp_rewrite as lr
EXTRA=['fn2-mk','fn2-b3','fn2-digests']
def one(s,p):
 m=lr.match(p,lr.parse(s).forms)
 if len(m)!=1:raise ValueError(p)
 return m[0].node
def cursor(source):
 f=one(source,'(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)')
 children=f.items[2];outputs=f.items[3]
 if any(getattr(x,'low',None)=='fn2-mk' for x in outputs.items):return source
 edits=[(children.end-1,children.end-1,' '+' '.join(EXTRA)),(outputs.end-1,outputs.end-1,' fn2-mk')]
 body=f.items[-1]
 row=one(source[body.start:body.end],'(row (fn2-run-loads-checker c fn2-run-loads))')
 # The offset within the isolated body is lifted back into the actual book.
 edits.append((body.start+row.end,body.start+row.end,'\n      (event-row (fn2-b-event-row (fn2-fc-rows fn2-fc)))'))
 guards=lr.match('(unless (and (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-idle*) ?*rest))',[body])
 if len(guards)!=1:raise ValueError('borrow preflight drift')
 gate=guards[0].node.items[1]
 extra='''
                    (< 0 event-row) (< event-row (fn2-fc-rows fn2-fc))
                    (equal (fn2-fc-phase event-row fn2-fc) *fn2-fc-phase-idle*)
                    (fn2-mk-ready event-row fn2-mk fn2-digests) (fn2-b3-ready event-row fn2-b3 fn2-digests)'''
 edits.append((gate.end-1,gate.end-1,extra))
 starts=lr.match('(fn2-event-archive-cold-start-root c :manifest base fn2-event-archive fn2-run-cursors)',[body])
 if len(starts)!=1:raise ValueError('manifest root constructor drift')
 binding=[n for n in body.items[1].items if n.start<starts[0].node.start<n.end]
 if len(binding)!=1:raise ValueError('constructor binding drift')
 edits.append((binding[0].start,binding[0].start,'(fn2-mk (fn2-mk-init event-row fn2-mk))\n      '))
 returns=lr.match('(mv ?code fn2-event-archive fn2-run-loads fn2-run-cursors fn2-fields)',[body])
 if len(returns)!=5:raise ValueError('borrow return class drift')
 edits += [(m.node.end-1,m.node.end-1,' fn2-mk') for m in returns]
 return lr.write(source,edits)
def boot(source):
 f=one(source,'(defun fn2-boot-checkpoint-archive-begin ?*body)')
 view=lr.match('(stobj-let ?*body)',[f])[0].node
 if any(getattr(n.items[0],'low',None)=='fn2-mk' for n in view.items[1].items):return source
 binding=' '.join('('+x+' (fn2-core-'+x[4:]+' fn2-core))' for x in EXTRA)
 call=lr.match('(fn2-event-archive-cold-cursor-begin ?*args)',[f])[0].node
 cost=one(source,'(defcost fn2-boot-checkpoint-archive-begin ?*body)')
 tables=[cost.items[i+1] for i,x in enumerate(cost.items[:-1]) if getattr(x,'low',None)==':tables'][0]
 return lr.write(source,[(view.items[1].end-1,view.items[1].end-1,' '+binding),
  (view.items[2].end-1,view.items[2].end-1,' fn2-mk'),(call.end-1,call.end-1,' '+' '.join(EXTRA)),
  (tables.end-1,tables.end-1,' '+' '.join('fn2-core-'+x[4:] for x in EXTRA))])
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for name,fn in [('event-archive-cold-cursor',cursor),('event-archive-cold-boot',boot)]:
  p=root/'books'/(name+'.lisp');p.write_text(fn(p.read_text()))
