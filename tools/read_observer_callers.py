"""Inventory actual READ callback calls for barrier-refusal consumer migration."""
import json
from pathlib import Path
import lisp_rewrite as lr
from read_observer_rewrite import nodes, sym
START={'fn2-read-'+x for x in ('lookup','range','seek','scan','identity')}
CHILD={'fn2-read-'+x+'-children' for x in ('key','key-octets','lookup','range','seek','release','scan','identity','next','seek-step','scan-next','value','octets')}
def inventory(root):
 out=[]
 for path in sorted((root/'books').glob('*.lisp')):
  if path.name=='machines-c-read.lisp':continue
  s=path.read_text();p=lr.parse(s)
  for form in p.forms:
   for n in nodes(form):
    if isinstance(n,lr.Lst) and n.items and sym(n.items[0]) in START|CHILD:
     out.append({'file':str(path.relative_to(root)),'line':s.count('\n',0,n.start)+1,'name':sym(n.items[0]),'kind':'child-abi' if sym(n.items[0]) in CHILD else 'start-refusal','arity':len(n.items)-1,'call':s[n.start:n.end]})
 return out
if __name__=='__main__':
 import sys
 print(json.dumps(inventory(Path(sys.argv[1] if len(sys.argv)>1 else '.')),indent=2))
