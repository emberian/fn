"""Update thread-reservation witnesses for the explicitly funded append actor."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def transform(text):
 edits=[]
 def walk(n):
  if isinstance(n,rw.Lst):
   for x in n.items:walk(x)
  elif isinstance(n,rw.Atom) and n.text=='34': edits.append((n.start,n.end,'35'))
  elif hasattr(n,'node'):walk(n.node)
 for n in rw.parse(text).forms:walk(n)
 text=rw.write(text,edits)
 return text.replace('threads=34','threads=35')
assert transform("'(34 134)")=="'(35 134)"
assert transform('; 34\n(foo 34)')=='; 34\n(foo 35)'
if __name__=='__main__':
 p=ROOT/'tests/acl2/heap-reservation-tests.lisp';s=transform(p.read_text())
 s=s.replace('and 34 threads -- the','and 35 threads -- the').replace('12 fixed, the 2 I/O loops','12 fixed plus the append worker, the 2 I/O loops')
 s=s.replace('*hrt-2200*','*hrt-2205*').replace('(* 2200 *fn-heap-mib*)','(* 2205 *fn-heap-mib*)').replace('"small" 2200 1024','"small" 2205 1024').replace(':machine-cannot-hold-threads 2200 2048',':machine-cannot-hold-threads 2205 2048')
 p.write_text(s)

# ACL2 ground probes confirmed each affected reservation rises by 5 MiB:
# one 1 MiB stack plus the existing 4 MiB per-thread runtime allowance.
# Only the expected side of these assertions changes; inputs and bounds stay.
if __name__=='__main__':
 import re
 p=ROOT/'tests/acl2/heap-reservation-tests.lisp';s=p.read_text();forms=rw.parse(s).forms
 ids=[59,60,63,64,71,73,74,78,80,81,82,86,87,88,89,91,260]
 old={3638:3643,20830:20835,1476:1481,2197:2202,1647:1652,1274:1279,3942:3947,1078:1083}
 edits=[]
 for n in ids:
  term=forms[n-1].items[1];assert term.items[0].low=='equal'
  rhs=term.items[2];raw=s[rhs.start:rhs.end]
  after=re.sub(r'(?<![0-9])(?:'+ '|'.join(map(str,old))+r')(?![0-9])',lambda m:str(old[int(m.group())]),raw)
  edits.append((rhs.start,rhs.end,after))
 p.write_text(rw.write(s,edits))
