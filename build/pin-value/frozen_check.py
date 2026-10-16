#!/usr/bin/env python3
"""All existing book theorem formulas match frozen c824a73ee, modulo A args."""
from pathlib import Path
import subprocess
from mechanical import ROOT,A,lr,formulas
from erase_check import erase
allowed=set(A)
books=subprocess.check_output(['git','-C',str(ROOT),'diff','--name-only','8c4c8c8d8','--','books']).decode().splitlines()
checked=0;errors=[]
for book in books:
 if not book.endswith('.lisp'):continue
 base=subprocess.check_output(['git','-C',str(ROOT),'show','c824a73ee:'+book],timeout=30).decode()
 current=(ROOT/book).read_text()
 old=formulas(lr.parse(base));new=formulas(lr.parse(current))
 for name,b in old.items():
  checked+=1
  if name not in new:errors.append((book,name,'missing'));continue
  c=new[name]
  got=erase(current,c) if (book,name) in allowed else current[c.start:c.end]
  if got!=base[b.start:b.end]:errors.append((book,name,'formula changed'))
print(f'{checked} existing book theorem formulas checked against frozen c824a73ee; {len(errors)} differences (A arguments erased)')
for row in errors:print(*row)
raise SystemExit(bool(errors))
