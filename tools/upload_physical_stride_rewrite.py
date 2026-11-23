#!/usr/bin/env python3
"""Rewrite only physical extent identities; leave three-block grouping intact."""
from pathlib import Path
import argparse
import lisp_rewrite as lr
RULES = {
 'books/assembly-callbacks-d-upload.lisp': [('(* *fn2-commit-write-resources* row-cext)', 1)],
 'books/upload.lisp': [('(mod unit *fn2-commit-write-resources*)', 1), ('(floor unit *fn2-commit-write-resources*)', 2)],
 'books/recovery-payload.lisp': [('(mod unit *fn2-commit-write-resources*)', 2), ('(floor unit *fn2-commit-write-resources*)', 2)],
}
def transform(source, rules):
 parsed = lr.parse(source)
 edits = []
 for pattern, expected in rules:
  matches = lr.match(pattern, parsed.forms)
  if len(matches) != expected:
   raise ValueError(f'{pattern}: expected {expected}, got {len(matches)}')
  for m in matches:
   old = source[m.start:m.end]
   edits.append((m.start, m.end, old.replace('*fn2-commit-write-resources*', '*fn2-storage-extent-units*')))
 return lr.write(source, edits)
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('root',type=Path)
 args=ap.parse_args()
 for name,rules in RULES.items():
  path=args.root/name
  path.write_text(transform(path.read_text(),rules))
if __name__ == '__main__': main()
