"""Thread actual B-row geometry through the existing arena consumer class."""
from pathlib import Path
import argparse,json,hashlib
import lisp_rewrite as lr
TARGETS={'fn2-idc-add-spare','fn2-idc-hold-spares','fn2-succ-stage','fn2-succ-drop-overlays','fn2-succ-drop','fn2-seal-retire','fn2-seal-start','fn2-seal-install','fn2-seal-step','fn2-seal-overlay-return','fn2-grp-genesis','fn2-succ-replay'}
FRAMES={'fn2-idc-fn-shape','fn2-seal-shape','fn2-overlays-preserves','fn2-pool-preserves'}
def atom(n):return n.text.lower() if isinstance(n,lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  # Frame emitters take raw callee-name lists, not applications.
  if n.items and atom(n.items[0]) in FRAMES:return
  for x in n.items:yield from walk(x)
 elif isinstance(n,lr.Pre):
  # Literal function-name lists are data; quoted macro event bodies are code.
  if n.prefix=="'" and isinstance(n.node,lr.Lst) and n.node.items and atom(n.node.items[0]) not in {'progn','defun','make-event','encapsulate'}:return
  yield from walk(n.node)
def transform(text,test=False,targets=TARGETS):
 edits=[]
 for top in lr.parse(text).forms:
  for n in walk(top):
   if not isinstance(n,lr.Lst) or not n.items:continue
   h=atom(n.items[0])
   if h=='defun' and len(n.items)>2 and atom(n.items[1]) in targets:
    edits.append((n.items[2].start+1,n.items[2].start+1,'commitrows '))
   elif h in targets:edits.append((n.items[0].end,n.items[0].end,' '+('0' if test else 'commitrows')))
   elif h in FRAMES and len(n.items)>2 and atom(n.items[1]) in targets:
    edits.append((n.items[2].start+1,n.items[2].start+1,'commitrows '))
 return lr.write(text,edits),len(edits)
def run(root):
 receipt=[]
 for folder in ['books','tests']:
  for p in (root/folder).glob('*.lisp'):
   if p.name=='identity-arena-credit.lisp':continue
   old=p.read_text();new,n=transform(old,folder=='tests')
   if n:
    receipt.append({'file':str(p.relative_to(root)),'edits':n,'original':old,'sha256':hashlib.sha256(old.encode()).hexdigest()});p.write_text(new)
 (root/'tools/fixtures/identity-arena-thread.json').write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path);run(p.parse_args().root)
