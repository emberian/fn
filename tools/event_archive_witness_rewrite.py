"""Thread the existing reader through actual archive constructor/stage outputs."""
import lisp_rewrite as lr
def operation(source,name,add_input):
 nodes=lr.match('(fn2-event-archive-operation '+name+' ?*body)',lr.parse(source).forms)
 if len(nodes)!=1:raise ValueError('archive operation drift '+name)
 n=nodes[0].node;children=n.items[2];outs=n.items[3]
 if any(getattr(x,'low',None)=='fn2-event-read' for x in outs.items):return source
 old=[x.low for x in outs.items];pattern='(mv ?code '+' '.join(old)+')'
 returns=lr.match(pattern,[n])
 expected={'fn2-event-archive-begin':5,'fn2-event-archive-stage':7,'fn2-event-archive-fresh-start':3}
 if len(returns)!=expected[name]:raise ValueError(('actual MV class drift',name,len(returns)))
 edits=[(outs.start,outs.end,'('+ ' '.join(old+['fn2-event-read'])+')')]
 if add_input:edits.append((children.start,children.end,source[children.start:children.end-1]+' fn2-event-read)'))
 for m in returns:
  code=m.captures['code'];edits.append((m.node.start,m.node.end,'(mv '+source[code.start:code.end]+' '+' '.join(old+['fn2-event-read'])+')'))
 return lr.write(source,edits)

def state(source):
 if '(witness-enabled :bool)' in source:return source
 source=source.replace('(include-book "arm-children")','(include-book "arm-children")\n(include-book "event-read-witness-geometry")',1)
 source=source.replace(':seal-tail :semantic-seal', ':seal-tail :semantic-seal :witness-seal :witness-header',1)
 anchor='  ; Physical identity captured'
 if source.count(anchor)!=1:raise ValueError('reader state owner declaration drift')
 source=source.replace(anchor,'''  ; Enabled only by the actual archive constructor's owned working source.
  (witness-enabled :bool) (witness-token :u60) (witness-slot :u32) (witness-gen :u60)
  (witness-phase (:enum fn2-event-witness-phase (:idle :bound :seal :records :ready :emitted :uncertain)))
  (witness-commit :u60) (witness-first :u60) (witness-members :u32)
  (witness-seal-length :u32) (witness-header-length :u32) (witness-cursor :u32) (witness-staged-event :u60)
'''+anchor,1)
 return source.replace('*fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-frame-records*', '*fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-witness-seal*\n                               *fn2-event-read-phase-witness-header* *fn2-event-read-phase-frame-records*',1)

def producer_gate(source):
 if ':archive-stage' in source:return source
 anchor='   ((equal read-phase *fn2-event-read-phase-members*)'
 if source.count(anchor)!=1:raise ValueError('actual member driver branch drift')
 gate='''   ((and (equal read-phase *fn2-event-read-phase-members*)
         (equal (fn2-event-read-witness-enabled 0 fn2-event-read) 1)
         (equal (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-leaf*)
         (equal (fn2-journal-members-hash-phase 0 fn2-journal-members) 3)
         (not (equal (fn2-event-read-witness-staged-event 0 fn2-event-read)
                     (fn2-journal-members-event 0 fn2-journal-members))))
    (mv :archive-stage fn2-event-build fn2-event-read fn2-journal-members fn2-mk fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
'''
 return source.replace(anchor,gate+anchor,1)
