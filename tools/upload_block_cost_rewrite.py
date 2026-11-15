#!/usr/bin/env python3
"""Change the same block-work charge at every actual declared call site."""
import lisp_rewrite as lr
NAMES={'fn2-upload-block-hash','fn2-upload-block-cv','fn2-upload-location-hash'}
def sym(n):
 return n.text.lower() if isinstance(n,lr.Atom) else ''
def arm_charges(text):
 p=lr.parse(text)
 calls=[m for m in lr.match('(?fn ?*args)',p.forms) if sym(m.captures['fn']) in NAMES]
 charges=lr.match('(:charge :bytes ?bytes ?*rest)',p.forms)
 edits=[]
 for call in calls:
  following=[m for m in charges if m.start>call.end]
  assert following, 'missing charge after block operation'
  node=min(following,key=lambda m:m.start).captures['bytes']
  assert sym(node)=='*fn2-commit-unit-bytes*', 'changed/missing original charge'
  edits.append((node.start,node.end,'*fn2-upload-block-work-bytes*'))
 assert len(edits)==7, len(edits)
 return lr.write(text,edits)
def declarations(text):
 p=lr.parse(text); edits=[]
 for name in sorted(NAMES):
  found=lr.match('(defcost '+name+' ?*rest)',p.forms)
  assert len(found)==1
  m=found[0]; part=text[m.start:m.end]
  assert part.count(':bytes *fn2-commit-unit-bytes*')==1
  edits.append((m.start,m.end,part.replace(':bytes *fn2-commit-unit-bytes*', ':bytes *fn2-upload-block-work-bytes*')))
 return lr.write(text,edits)
