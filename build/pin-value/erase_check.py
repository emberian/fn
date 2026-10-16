#!/usr/bin/env python3
"""Audit all 60 A formulas byte-for-byte against the frozen base."""
from mechanical import ROOT, A, SPECS, gittext, lr, walk, head, formulas
import difflib

def erase(text, node):
 edits=[]
 for n in walk(node):
  h=head(n)
  if h in SPECS:
   old,pos=SPECS[h]
   if len(n.items)!=old+2:
    raise ValueError(f'{h}: expected {old+1} arguments')
   arg=n.items[pos+1]
   # Erase exactly the inserted separator and argument, preserving old whitespace.
   if pos==old:
    assert text[arg.start-1]==' '
    edits.append((arg.start-1-node.start,arg.end-node.start,''))
   else:
    assert text[arg.end]==' '
    edits.append((arg.start-node.start,arg.end+1-node.start,''))
 return lr.write(text[node.start:node.end],edits)

def main():
 differences=0
 for path,name in A:
  base=gittext(path); current=(ROOT/path).read_text()
  b=formulas(lr.parse(base))[name]; c=formulas(lr.parse(current))[name]
  want=base[b.start:b.end]
  try: got=erase(current,c)
  except (ValueError,AssertionError) as e:
   print(path,name,e); differences+=1; continue
  if got!=want:
   differences+=1
   print(path,name)
   print(''.join(difflib.unified_diff(want.splitlines(True),got.splitlines(True))))
 print(f'{len(A)} formulas checked; {differences} differences')
 return bool(differences)
if __name__=='__main__': raise SystemExit(main())
