"""Replace the explicit ROWS chain with requested, ABI-derived dimensions."""
from lisp_rewrite import parse,match,write,Atom,Lst,flat
OPAQUE={
 'fn2-core-lease':'fn2-pool-lease-in fn2-pool-lease-out',
 'fn2-issue-children':'fn2-core-lease',
 'fn2-pinned-block-io-children':'fn2-issue-read-children fn2-issue-write-children fn2-alloc-handle-code fn2-alloc-edge-add fn2-b-read-pin-drop fn2-control-record-stop fn2-control-stop fn2-op-slotp fn2-ops-free-head fn2-ops-gen fn2-extents-state',
 'fn2-block-read-children':'fn2-pinned-block-io-children',
 'fn2-block-write-children':'fn2-pinned-block-io-children'}
def request(name):return f'(fn2-pool-dimensions {name} :opaque ({OPAQUE[name]}))'
def transform(text,owner):
 p=parse(text);ed=[];count=0
 if any(flat(m.node.items[1])=='"pool-dimensions"' for m in match(None,p,deep=False,head='include-book')):
  names=('fn2-core-lease','fn2-issue-children') if owner=='arm-children' else ('fn2-pinned-block-io-children','fn2-block-read-children','fn2-block-write-children')
  actual=[flat(m.node) for m in match(None,p,deep=True,head='fn2-pool-dimensions') if isinstance(m.node.items[1],Atom)]
  assert sorted(actual)==sorted(flat(parse(request(name)).forms[0]) for name in names),'missing, unknown or duplicate dimension request'
  if owner=='arm-children':
   wrappers=[m.node for m in match(None,p,deep=False,head='fn2-issue-children-wrapper') if flat(m.node.items[1]) in ('fn2-issue-read-children','fn2-issue-write-children')]
   assert len(wrappers)==2 and all(flat(n.items[-2])==':dimensions' and flat(n.items[-1])=='(:rows :data)' for n in wrappers)
  return text,0
 if owner=='arm-children':
  inc=next(m.node for m in match(None,p,deep=False,head='include-book'))
  ed.append((inc.end,inc.end,'\n(include-book "pool-dimensions")'))
  core=next(m.node for m in match(None,p,deep=False,head='fn2-pool-preserves') if flat(m.node.items[1])=='fn2-core-lease')
  ed.append((core.end,core.end,'\n'+request('fn2-core-lease')));count+=1
  macro=next(m.node for m in match(None,p,deep=False,head='defmacro') if flat(m.node.items[1])=='fn2-issue-children-wrapper')
  option=macro.items[2].items[-1];assert flat(option)=="(rows 'nil)";ed.append((option.start,option.end,"(dimensions 'nil)"))
  choice=next(m.node for m in match(None,[macro],deep=True,head='and') if len(m.node.items)>1 and flat(m.node.items[1])=='rows')
  ed.append((choice.start,choice.end,"(and dimensions `((fn2-pool-dimensions ,name :observations ,dimensions :opaque (fn2-issue-children))))"));count+=1
  for m in match(None,p,deep=False,head='fn2-issue-children-wrapper'):
   n=m.node
   if flat(n.items[1]) in ('fn2-issue-read-children','fn2-issue-write-children'):
    assert flat(n.items[-2])==':rows' and flat(n.items[-1])=='t'
    ed.append((n.items[-2].start,n.items[-1].end,':dimensions (:rows :data)'));count+=1
 else:
  inc=next(m.node for m in match(None,p,deep=False,head='include-book'));ed.append((inc.end,inc.end,'\n(include-book "pool-dimensions")'))
 for m in match(None,p,deep=True,head='fn2-pool-preserves'):
  n=m.node
  if '"-DIMENSION-ROWS"' in flat(n) and isinstance(n.items[1],Atom):
   name=n.items[1].low;assert name in OPAQUE
   ed.append((n.start,n.end,request(name)));count+=1
 for m in match(None,p,deep=True,head='assert-event'):
  n=m.node
  if flat(n).startswith('(assert-event (eq (nth 3 (getpropc') and not (owner=='arm-children' and macro.start <= n.start < macro.end):
   ed.append((n.start,n.end,''))
 assert count==(5 if owner=='arm-children' else 3),(owner,count)
 return write(text,ed),count
if __name__=='__main__':
 from pathlib import Path
 import sys
 for name in ('arm-children','storage-block-io'):
  p=Path(sys.argv[1])/'books'/(name+'.lisp');s,n=transform(p.read_text(),name);p.write_text(s);print(name,n)
