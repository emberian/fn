"""Factor the unchanged actual checkpoint producer helpers out of UNIT.

Parse source positions only; no Lisp evaluation or checkpoint construction.
"""
from pathlib import Path
import lisp_rewrite as lr
HELPER='checkpoint-cold-path-producer-support'
def extract(source):
 forms=lr.parse(source).forms
 if lr.match(f'(include-book "{HELPER}")',forms,deep=False):raise ValueError('producer already extracted')
 start=lr.match('(defconst *fn2-ccp-image-size* ?*body)',forms,deep=False)[0].node.start
 body=lr.match('(defun fn2-ccp-body ?*body)',forms,deep=False)[0].node.start
 block=source[start:body]
 helper='''; Exact shared producer/observer support for persisted cold-path fixtures.
; Test-only maintenance entry; activation remains NIL, scheduler unqualified.
; No selected candidate, authenticated phase or persistence outcome is seeded.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/node-profile")
(include-book "checkpoint-cold-path-drive")

'''+block
 prefix=source[:start];edits=[]
 for old,new in [('../books/node-profile',f'(include-book "{HELPER}")'),('checkpoint-cold-path-drive','')]:
  nodes=lr.match(f'(include-book "{old}")',forms,deep=False)
  if len(nodes)!=1:raise ValueError('changed producer dependency '+old)
  node=nodes[0].node;edits.append((node.start,node.end,new))
 for a,b,new in sorted(edits,reverse=True):prefix=prefix[:a]+new+prefix[b:]
 unit=prefix+source[body:]
 lr.parse(helper);lr.parse(unit)
 return helper,unit
if __name__=='__main__':
 unit=Path('tests/checkpoint-cold-path-unit.lisp');helper=unit.with_name(HELPER+'.lisp')
 if helper.exists():raise SystemExit('refuse overwriting existing producer support')
 h,u=extract(unit.read_text());helper.write_text(h);unit.write_text(u)
