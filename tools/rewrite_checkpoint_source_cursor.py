#!/usr/bin/env python3
"""Migrate root1's actual cursor selectors to the named private-row geometry.
Shared structural source rewrite, never a runtime profile or identity model.
"""
from pathlib import Path
import argparse
from lisp_rewrite import parse, match, write
PATTERNS=(
 ('(< 0 (fn2-run-loads-rows fn2-run-loads))','(<= 2 (fn2-run-loads-rows fn2-run-loads))'),
 ('(< 0 (fn2-run-cursors-rows fn2-run-cursors))','(<= 2 (fn2-run-cursors-rows fn2-run-cursors))'),
 ('(- (fn2-run-loads-rows fn2-run-loads) 1)','(fn2-b-checkpoint-source-cursor-from-rows (fn2-run-loads-rows fn2-run-loads))'),
 ('(- (fn2-run-cursors-rows fn2-run-cursors) 1)','(fn2-b-checkpoint-source-cursor-from-rows (fn2-run-cursors-rows fn2-run-cursors))'))
def transform(text,fixture=False):
 p=parse(text);edits=[]
 for pattern,replacement in PATTERNS:
  edits.extend((m.start,m.end,replacement) for m in match(pattern,p.forms))
 if fixture:
  # Only the named source borrow fixture binds ROWS from actual profile K.
  edits.extend((m.start,m.end,'(fn2-b-checkpoint-source-cursor-from-rows rows)') for m in match('(- rows 1)',p.forms))
 return write(text,edits),len(edits)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('path',type=Path);a.add_argument('--fixture',action='store_true');a.add_argument('--write',action='store_true');o=a.parse_args()
 out,n=transform(o.path.read_text(),o.fixture)
 if o.write:o.path.write_text(out)
 print(f'{o.path}: {n} source cursor selectors')
