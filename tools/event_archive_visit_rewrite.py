"""Add an explicit byte-cost directive without changing existing operation forms."""
import lisp_rewrite as lr
OLD='''        (formals (append (if (consp name) (cdr name) nil) children)))'''
NEW='''        (formals (append (if (consp name) (cdr name) nil) children))
        (costp (and (consp (car body)) (eq (caar body) :bytes)))
        (bytes (if costp (cadar body) '(* 2 *fn2-run-layout-max-entry-bytes*)))
        (body (if costp (cdr body) body)))'''
def operation(source):
 nodes=lr.match('(defmacro fn2-event-archive-operation ?*body)',lr.parse(source).forms,deep=False)
 if len(nodes)!=1:raise ValueError('operation macro drift')
 node=nodes[0].node;s=source[node.start:node.end]
 if '(costp ' in s:return source
 if s.count(OLD)!=1 or s.count(':bytes (* 2 *fn2-run-layout-max-entry-bytes*)')!=1:raise ValueError('operation template drift')
 s=s.replace(OLD,NEW).replace(':bytes (* 2 *fn2-run-layout-max-entry-bytes*)',':bytes ,bytes')
 return lr.write(source,[(node.start,node.end,s)])
def explicit(source,names):
 edits=[]
 for name in names:
  nodes=lr.match('(defcost '+name+' ?*body)',lr.parse(source).forms)
  if len(nodes)!=1:raise ValueError('cost declaration drift '+name)
  n=nodes[0].node;items=n.items
  positions=[i+1 for i,t in enumerate(items[:-1]) if getattr(t,'low',None)==':bytes']
  if len(positions)!=1:raise ValueError('byte cost count drift')
  v=items[positions[0]]
  if source[v.start:v.end]=='*fn2-run-entry-visit-bytes*':continue
  if source[v.start:v.end]!='(* 2 *fn2-run-layout-max-entry-bytes*)':raise ValueError('unexpected old bound')
  edits.append((v.start,v.end,'*fn2-run-entry-visit-bytes*'))
 return lr.write(source,edits)
