"""Thread the actual common cold generation through all archive boot faces."""
from pathlib import Path
import lisp_rewrite as lr
EXTRA=['fn2-core-checkpoint-restore-map','fn2-core-checkpoint-restore-map-control','fn2-core-checkpoint-restore-reach','fn2-core-checkpoint-restore-reach-control']
def transform(source):
 if '(include-book "event-archive-cold-reach")' in source:return source,0
 forms=lr.parse(source).forms;edits=[];costs=[]
 for m in lr.match('(defcost ?name ?*body)',forms,deep=False):
  if not m.captures['name'].low.startswith('fn2-boot-checkpoint-archive-'):continue
  n=m.node;costs.append(n)
  tables=[n.items[i+1] for i,x in enumerate(n.items[:-1]) if getattr(x,'low',None)==':tables']
  if len(tables)!=1:raise ValueError('expected actual tables')
  row=tables[0]
  if any(getattr(x,'low',None) in EXTRA for x in row.items):raise ValueError('partially threaded tables')
  edits.append((row.end-1,row.end-1,' '+' '.join(EXTRA)))
 if len(costs)!=5:raise ValueError('archive boot face class drift')
 owner=lr.match('(defun fn2-boot-checkpoint-archive-owner-p ?*body)',forms)[0].node
 view=lr.match('(stobj-let ?*body)',[owner])[0].node
 bindings=' '.join('('+x+' (fn2-core-'+x[4:]+' fn2-core))' for x in ['fn2-checkpoints','fn2-checkpoint-refs','fn2-checkpoint-bytes','fn2-checkpoint-restore-map','fn2-checkpoint-restore-map-control','fn2-checkpoint-restore-reach-control'])
 edits.append((view.items[1].end-1,view.items[1].end-1,' '+bindings))
 body=view.items[3]
 if body.items[0].low!='and':raise ValueError('owner view shape drift')
 predicate='''
              (fn2-event-archive-cold-reach-current-p fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
               fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)'''
 edits.append((body.end-1,body.end-1,predicate))
 out=lr.write(source,edits)
 if out.count('fn2-event-archive-cold-cursor-step')!=2:raise ValueError('shared step call class drift')
 out=out.replace('fn2-event-archive-cold-cursor-step','fn2-event-archive-cold-step-reach')
 out=out.replace('(include-book "event-archive-cold-read")','(include-book "event-archive-cold-reach")')
 return out,len(edits)
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1];p=root/'books/event-archive-cold-boot.lisp'
 out,count=transform(p.read_text());p.write_text(out);print(count)
