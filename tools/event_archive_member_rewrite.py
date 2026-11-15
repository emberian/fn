"""Exact selected member root/query and cursor consumer class transformation."""
import lisp_rewrite as lr
def replace_once(source,old,new):
 if source.count(old)!=1:raise ValueError('archive member class drift')
 return source.replace(old,new,1)
def cursor(source):
 if ':member-entry' in source:return source
 source=replace_once(source,'(scan 0) (next-event 1) (entry-pending 0)','(scan 0) (next-event 1) (entry-pending 0) (leaf-pending 0)')
 source=replace_once(source,'(equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-manifest*)\n      (< 1','(member-equal (fn2-event-archive-phase 1 fn2-event-archive)\n       (list *fn2-event-archive-phase-cold-manifest* *fn2-event-archive-phase-cold-members*))\n      (< 1')
 source=replace_once(source,'(equal (fn2-run-cursors-schema c fn2-run-cursors) 10)\n            (equal (fn2-run-cursors-run c fn2-run-cursors) (fn2-event-archive-checkpoint 1 fn2-event-archive))','''(equal (fn2-run-cursors-schema c fn2-run-cursors)
             (if (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-manifest*) 10 *fn2-event-archive-schema*))
            (equal (fn2-run-cursors-run c fn2-run-cursors)
             (if (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-manifest*)
                 (fn2-event-archive-checkpoint 1 fn2-event-archive) (fn2-event-archive-member-last-event 1 fn2-event-archive)))''')
 source=replace_once(source,'(mv :manifest-entry fn2-event-archive fn2-run-loads','(mv (if (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-manifest*) :manifest-entry :member-entry) fn2-event-archive fn2-run-loads')
 return replace_once(source,'(mv (if (eq code :entry) :manifest-entry code)','(mv (if (eq code :entry)\n           (if (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-manifest*) :manifest-entry :member-entry) code)')
def bind(source):
 nodes=lr.match('(fn2-event-archive-operation fn2-event-archive-cold-bind-member ?*body)',lr.parse(source).forms)
 if len(nodes)!=1:raise ValueError('member bind operation drift')
 n=nodes[0].node;s=source[n.start:n.end]
 if '(q (+ base *fn2-run-reader-fields*))' in s:return source
 returns=lr.match('(mv ?code fn2-event-archive fn2-run-cursors fn2-digests)',[n])
 if len(returns)!=6:raise ValueError('member bind return class drift')
 edits=[]
 for m in returns:
  code=source[m.captures['code'].start:m.captures['code'].end]
  edits.append((m.node.start,m.node.end,'(mv '+code+' fn2-event-archive fn2-run-cursors fn2-fields fn2-digests)'))
 out=n.items[3]
 if lr.flat(out)!='(fn2-event-archive fn2-run-cursors fn2-digests)':raise ValueError('mutable output drift')
 edits.append((out.start,out.end,'(fn2-event-archive fn2-run-cursors fn2-fields fn2-digests)'))
 result=lr.write(source,edits)
 result=replace_once(result,'(<= (+ eb *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))', '(<= (+ eb *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))\n                    (<= (+ base *fn2-run-reader-fields* 3) (fn2-fields-rows fn2-fields))')
 anchor='      (fn2-event-archive (if (eq code :ok)'
 q='''      (q (+ base *fn2-run-reader-fields*))
      (fn2-fields (fn2-fields-set-value q (fn2-event-archive-history 1 fn2-event-archive) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ q 1) (fn2-event-archive-incarnation 1 fn2-event-archive) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ q 2) (fn2-event-archive-next-event 1 fn2-event-archive) fn2-fields))
'''
 result=replace_once(result,anchor,q+anchor)
 return replace_once(result,'(entry-pending 0)) fn2-event-archive)','(entry-pending 0) (leaf-pending 0)) fn2-event-archive)')

def boot(source):
 if '(include-book "event-archive-cold-step")' in source:return source
 source=replace_once(source,'(include-book "event-archive-cold-reach")','(include-book "event-archive-cold-step")')
 edits=[]
 for name in ['fn2-boot-checkpoint-archive-check-raw','fn2-boot-checkpoint-archive-check']:
  nodes=lr.match('(defcost '+name+' ?*body)',lr.parse(source).forms)
  if len(nodes)!=1:raise ValueError('boot CHECK declaration drift')
  n=nodes[0].node;s=source[n.start:n.end]
  anchor='fn2-core-checkpoint-restore-reach-control))'
  if s.count(anchor)!=1:raise ValueError('CHECK tables tail drift')
  s=s.replace(anchor,'fn2-core-checkpoint-restore-reach-control fn2-core-journal-members fn2-core-mk fn2-core-extents))')
  if name.endswith('-raw'):
   if s.count(':child fn2-event-archive-cold-step-reach')!=1:raise ValueError('CHECK child drift')
   s=s.replace(':child fn2-event-archive-cold-step-reach',':child fn2-event-archive-cold-step')
  edits.append((n.start,n.end,s))
 source=lr.write(source,edits)
 return replace_once(source,"'fn2-boot-checkpoint-archive-check-raw 'fn2-event-archive-cold-step-reach", "'fn2-boot-checkpoint-archive-check-raw 'fn2-event-archive-cold-step")
