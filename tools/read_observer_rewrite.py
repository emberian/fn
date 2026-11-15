"""Project READ endpoint lifecycle onto existing actual child/core operations."""
from pathlib import Path
import lisp_rewrite as lr
MUT={'key','key-octets','lookup','range','seek','release','scan','identity'}
ALL=MUT|{'next','seek-step','scan-next','value','octets'}
def nodes(n):
 yield n
 if isinstance(n,lr.Lst):
  for a in n.items:yield from nodes(a)
 elif isinstance(n,lr.Pre):yield from nodes(n.node)
def sym(n):return getattr(n,'low','')
def project(s,helpers,frames):
 p=lr.parse(s); edits=[]
 def text(n):return s[n.start:n.end]
 def insert(n,x):edits.append((n.end-1,n.end-1,' '+x))
 if 'observer-serial :u60' in s:raise ValueError('already projected')
 inc=next(n for n in p.forms if isinstance(n,lr.Lst) and sym(n.items[0])=='include-book')
 edits.append((inc.end,inc.end,'\n(include-book "c-source-observer")'))
 cols=next(n for n in p.forms if isinstance(n,lr.Lst) and len(n.items)>1 and sym(n.items[1])=='fn2-reads' and sym(n.items[0])=='defcolumns')
 insert(cols.items[2],'(observer-serial :u60) (observer-parent :u32) (observer-parent-serial :u60)')
 edits.append((cols.end,cols.end,'\n\n'+helpers))
 macro=next(n for n in p.forms if isinstance(n,lr.Lst) and sym(n.items[0])=='defmacro' and sym(n.items[1])=='fn2-rd-shape')
 edits.append((macro.end,macro.end,'\n\n'+frames))
 core={}
 for n in nodes(p.forms[-1]):
  if not isinstance(n,lr.Lst) or len(n.items)<4 or sym(n.items[0])!='defun':continue
  name=sym(n.items[1]); op=name.removeprefix('fn2-read-')
  if op not in ALL:continue
  st=n.items[-1]; assert sym(st.items[0])=='stobj-let'
  outputs=[text(x) for x in st.items[2].items];core[op]=outputs
  extra=['fn2-c-source-control','fn2-c-source-readers'] if op in MUT else ['fn2-c-source-readers']
  insert(st.items[1],' '.join('('+v+' ('+v.replace('fn2-','fn2-core-',1)+' fn2-core))' for v in extra))
  if op in MUT:insert(st.items[2],' '.join(extra))
  insert(st.items[3],' '.join(extra))
 assert set(core)==ALL
 for n in p.forms:
  if not isinstance(n,lr.Lst) or len(n.items)<3:continue
  head=sym(n.items[0]);name=sym(n.items[1]);op=name.removeprefix('fn2-read-').removesuffix('-children')
  if op not in ALL:continue
  if head=='defcost':
   if op in MUT:
    i=next(i for i,a in enumerate(n.items) if sym(a)==':tables');insert(n.items[i+1],'fn2-core-c-source-control fn2-core-c-source-readers')
   if op in {'range','seek','scan'}:
    i=next(i for i,a in enumerate(n.items) if sym(a)==':answers');insert(n.items[i+1],':more')
   continue
  if head!='defun' or not name.endswith('-children'):continue
  extra=['fn2-c-source-control','fn2-c-source-readers'] if op in MUT else ['fn2-c-source-readers']
  insert(n.items[2],' '.join(extra))
  decl=n.items[3]; xargs=decl.items[1]
  i=next(i for i,a in enumerate(xargs.items) if sym(a)==':stobjs');insert(xargs.items[i+1],' '.join(extra))
  i=next(i for i,a in enumerate(xargs.items) if sym(a)==':guard');insert(xargs.items[i+1],' '.join('('+v+'-wfp '+v+')' for v in extra))
  old=text(n.items[-1]); outs=core[op]; tail=' '.join(outs[1:]); failure=' '.join(x if x.startswith('fn2-') else '0' for x in outs[1:])
  if op in {'key','key-octets','release'}:
   body=f'(mv-let ({" ".join(outs)})\n {old}\n (if (eq code :ok)\n  (mv-let (closed fn2-reads fn2-c-source-control fn2-c-source-readers)\n   (fn2-read-observer-release x fn2-reads fn2-c-source-control fn2-c-source-readers)\n   (mv closed {tail} fn2-c-source-control fn2-c-source-readers))\n  (mv code {tail} fn2-c-source-control fn2-c-source-readers)))'
  elif op in MUT:
   fresh='t'
   if op=='lookup':fresh='(not (and (natp x) (< x (fn2-reads-rows fn2-reads)) (equal (fn2-reads-op x fn2-reads) *fn2-read-op-lookup*) (equal (fn2-reads-sid x fn2-reads) sid)))'
   if op=='identity':fresh='(not (and (natp x) (< x (fn2-reads-rows fn2-reads)) (equal (fn2-reads-op x fn2-reads) *fn2-read-op-identity*)))'
   body=f'(mv-let (admitted fn2-reads fn2-c-source-control fn2-c-source-readers)\n (fn2-read-observer-enter x {fresh} fn2-reads fn2-c-source-control fn2-c-source-readers)\n (if (eq admitted :ok)\n  (mv-let ({" ".join(outs)})\n   {old}\n   (mv code {tail} fn2-c-source-control fn2-c-source-readers))\n  (mv admitted {failure} fn2-c-source-control fn2-c-source-readers)))'
  else:
   fail=':stale' if op in {'value','octets'} else ':more'
   body=f'(if (fn2-read-observer-current-p x fn2-reads fn2-c-source-readers)\n {old}\n (mv {fail} {failure}))'
  edits.append((n.items[-1].start,n.items[-1].end,body))
 return lr.write(s,edits)
if __name__=='__main__':
 import sys
 p=Path(sys.argv[1]);p.write_text(project(p.read_text(),Path('tools/fixtures/read-observer/helpers.lisp').read_text(),Path('tools/fixtures/read-observer/frames.lisp').read_text()))
