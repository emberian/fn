"""Append actual boot inventory continuations without renumbering old states."""
from pathlib import Path
import lisp_rewrite as lr
PHASES=(':checkpoint-release-inventory-begin',':checkpoint-release-inventory-verify',':checkpoint-release-inventory-apply')
def rewrite(text):
 p=lr.parse(text);edits=[]
 for m in lr.match('(defmachine fn2-boot ?*body)',p.forms,deep=False):
  items=m.node.items
  for key in (':states',':holds',':arms'):
   at=next(i for i,x in enumerate(items) if isinstance(x,lr.Atom) and x.low==key);node=items[at+1]
   present={x.low for x in node.items if isinstance(x,lr.Atom)} if key==':states' else {x.items[0].low for x in node.items if isinstance(x,lr.Lst) and x.items}
   add=[phase if key==':states' else '('+phase+(' :storage-window' if key==':holds' else '')+')' for phase in PHASES if phase not in present]
   if add:edits.append((node.end-1,node.end-1,' '+' '.join(add)))
 return lr.write(text,edits),len(edits)
if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 path=Path(__file__).resolve().parents[1]/'books/boot-kind.lisp';out,n=rewrite(path.read_text());print(n)
 if args.write:path.write_text(out)
