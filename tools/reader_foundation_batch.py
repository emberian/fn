"""Project the reviewed current proof foundation, preserving cold runtime."""
from pathlib import Path
import subprocess
import lisp_rewrite as lr
BASE='65cb67fe7ca8ea4fc934ddc5d17e48928e595f59'
ROOT_SOURCE='9c2eabc4c9b94de947c4705f8c7d684eeb61d136'
SAFE=('runs-page','checkpoint-allocation','block-integrity','ribbon','checkpoint-allocation-coordinator','runs-schema')
HELPERS=('columns-call-guards','layout-size-bounds','blake3-row-frames','columns-carrier-contracts')

def source(root,revision,path):return subprocess.check_output(['git','show',revision+':'+path],cwd=root,text=True)
def atom(node):return getattr(node,'low',None)
def walk(node):
 if isinstance(node,lr.Lst):
  yield node
  for child in node.items:yield from walk(child)
 elif isinstance(node,lr.Pre):yield from walk(node.node)
def plain(node):
 if isinstance(node,lr.Lst):return tuple(plain(x) for x in node.items)
 if isinstance(node,lr.Pre):return (node.prefix,plain(node.node))
 return ('string' if isinstance(node,lr.Str) else 'atom',node.text)
def props(items,start,kind):
 out=[norm(x) for x in items[:start]];i=start
 while i<len(items):
  key=atom(items[i]);value=items[i+1] if i+1<len(items) else None
  if key in (':hints',':guard-hints',':type-hints'):i+=2;continue
  out.append(norm(items[i]))
  if value is not None:
   if kind=='preserves' and key in (':specs',':carriers') and isinstance(value,lr.Lst):
    index=3 if key==':specs' else 2
    out.append(tuple(tuple(props(v.items,index,'options')) if isinstance(v,lr.Lst) else norm(v) for v in value.items))
   else:out.append(norm(value))
  i+=2
 return out
def norm(node):
 if isinstance(node,lr.Lst):
  head=atom(node.items[0]) if node.items else None
  if head=='xargs':return tuple(props(node.items,1,'xargs'))
  if head and head.endswith('-preserves') and head!='fn2-columns-preserves':return tuple(props(node.items,3,'preserves'))
  return tuple(norm(x) for x in node.items)
 if isinstance(node,lr.Pre):return (node.prefix,norm(node.node))
 return plain(node)
def definitions(text):
 return {plain(n.items[1]):n for f in lr.parse(text).forms for n in walk(f)
         if len(n.items)>2 and atom(n.items[0]) in ('defun','defmacro')}
def claims(text):
 return {plain(n.items[1]):tuple(plain(v) for v in n.items[:3]) for f in lr.parse(text).forms for n in walk(f)
         if len(n.items)>2 and atom(n.items[0])=='defthm'}
def validate_safe(before,after):
 a=definitions(before);b=definitions(after)
 assert set(a)==set(b),(set(a)-set(b),set(b)-set(a))
 for name in a:assert norm(a[name])==norm(b[name]),name
 a=claims(before);b=claims(after)
 for name in a:assert a[name]==b[name],name
 for head in ('defcolumns','deflayout','defrunschema','defconst'):
  a=[plain(n) for n in lr.parse(before).forms if isinstance(n,lr.Lst) and n.items and atom(n.items[0])==head]
  b=[plain(n) for n in lr.parse(after).forms if isinstance(n,lr.Lst) and n.items and atom(n.items[0])==head]
  assert a==b,head

def unique(text,pattern):
 matches=lr.match(pattern,lr.parse(text).forms);assert len(matches)==1,(pattern,len(matches));return matches[0].node
def tickets(before,reference):
 if '(defthm fn2-checkpoint-ticket-account-raw-rows' in before:return before
 additions=[]
 for name in ('fn2-checkpoint-ticket-account-raw-rows','fn2-checkpoint-ticket-commit-allocation-raw-rows'):
  node=unique(reference,'(local (defthm '+name+' ?*body))');additions.append(reference[node.start:node.end])
 anchor=unique(before,'(defun fn2-checkpoint-ticket-install ?*body)')
 return lr.write(before,[(anchor.start,anchor.start,'\n'.join(additions)+'\n\n')])
def coordinator(before,reference):
 if 'fn2-checkpoint-installation-pack-member-fields-type-under-guard' in before:return before
 old=unique(before,'(fn2-core-preserves fn2-checkpoint-installation-step ?*body)')
 new=unique(reference,'(fn2-core-preserves fn2-checkpoint-installation-step ?*body)')
 out=lr.write(before,[(old.start,old.end,reference[new.start:new.end])])
 return out.replace('(include-book "checkpoint-production")','(include-book "checkpoint-production")\n(include-book "arms")',1)
def member(reference):
 return reference.replace('(include-book "columns-guard-hints")','(include-book "columns-guard-hints")\n(include-book "columns-carrier-contracts")',1)
def project(root):
 for name in SAFE:
  path='books/'+name+'.lisp';old=source(root,BASE,path);new=source(root,ROOT_SOURCE,path);validate_safe(old,new)
  actual=(root/path).read_text();assert actual in (old,new),path
  (root/path).write_text(new)
 for name in HELPERS:
  path='books/'+name+'.lisp';new=source(root,ROOT_SOURCE,path);p=root/path
  assert not p.exists() or p.read_text()==new,path;p.write_text(new)
 for name,transform in [('checkpoint-tickets',tickets),('checkpoint-installation-coordinator',coordinator)]:
  path='books/'+name+'.lisp';old=source(root,BASE,path);new=transform(old,source(root,ROOT_SOURCE,path))
  # Hints/local theorem additions only; actual cold function/guard definitions survive.
  a=definitions(old);b=definitions(new)
  for key in a:assert norm(a[key])==norm(b[key]),(name,key)
  assert (root/path).read_text() in (old,new),path;(root/path).write_text(new)
 path='books/checkpoint-member.lisp';old=source(root,BASE,path);new=member(source(root,ROOT_SOURCE,path))
 a=definitions(old);b=definitions(new)
 for key in a:assert norm(a[key])==norm(b[key]),key
 assert (root/path).read_text() in (old,new),path;(root/path).write_text(new)
 for name in ('checkpoint-member-readonly-removal','checkpoint-member-interface-unit'):
  path='tests/'+name+'.lisp';new=source(root,ROOT_SOURCE,path);p=root/path
  assert not p.exists() or p.read_text()==new,path;p.write_text(new)
if __name__=='__main__':project(Path(__file__).resolve().parents[1])
