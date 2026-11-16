"""Emit SOURCE model arithmetic/inventory from the shared category walker.
No runtime authorizer, parser, codec or ACL2-world evaluator is implemented here.
"""
from pathlib import Path
from machine_reader_costs import machine_reader_inventory
import sys,json
sys.path.insert(0,'tools');import boot_callback_cost_audit as b
roots=list(b.WRAPPERS)
seen=set();ordered=[]
def visit(n):
 if n in seen:return
 seen.add(n)
 for key in b.a.body(n):
  if key not in ('metadata','spine') and not key.startswith('@'):visit(key)
 ordered.append(n)
for n in roots:visit(n)
def symbol(n):return '*fn2-boot-work-'+n.removeprefix('fn2-')+'*'
book='''; Audited SOURCE model components at CORE273 +canonical lower17f.
; No runtime cost face is bound here. PAGE component REQUIRES the actual
; HASH/pad-end source gate; pending BEGIN/controller additions are not hidden.
; Typed octet helpers remain payload primitives; per-byte ownership is not
; charged again. Field completion/storage, scalar shape and CORE GET/store
; are structural units. Physical/extraction/critical refinement remains owed.
(in-package "ACL2")
(include-book "checkpoint-geometry")
(include-book "format-check")
(fn2-book-layer :b)
(defconst *fn2-boot-work-format-anchor*
 (+ (* (+ 18 3) (+ (length (fn2-fc-domain :anchor)) *fn2-format-anchor-max-size* 32 2)) 7))
; Actual readable PAGE plus HASH/pad-end=len gate bounds PAGE-span to one
; yield. No unconditional WFP-only theorem or generic FORMAT cost is claimed.
(defconst *fn2-boot-work-format-page-conditional*
 (+ (* 15 (+ (length (fn2-fc-domain :page)) 32 2)) 32 (+ (length (fn2-fc-domain :page)) 32 2 1) (* 3 (+ (length (fn2-fc-domain :page)) 32 2 1)) 7))
'''
report={'scope':'SOURCE category components; no ACL2/emission/runtime execution. CORE273+lower17f. Conditional PAGE fence and fresh descriptor BEGIN/controller composition remain pending.','primitive_boundary':'Pool octet read/write/copy/hash and per-octet codec validation remain payload primitives; metadata outside is expanded.','providers':[],'roots':{}}
for n in ordered:
 c=b.a.body(n);terms=[]
 for key,v in c.items():
  if key in ('metadata','spine'):terms.append(str(v))
  elif key=='@format-run':terms.append('(* '+str(v)+' '+('*fn2-boot-work-format-anchor*' if 'anchor' in n else '*fn2-boot-work-format-page-conditional*')+')')
  else:terms.append('(* '+str(v)+' '+symbol(key)+')')
 book+='(defconst '+symbol(n)+' (+ 0 '+' '.join(terms)+'))\n'
 report['providers'].append({'provider':n,'source':str(b.a.D[n][0]),'component':dict(c),'expanded':dict(b.full(n))})
for n in roots:report['roots'][n]=dict(b.full(n))
classification=machine_reader_inventory()
report['machine_reader_uses']={n:{call:dict(classification[call],calls=count) for call,count in b.machine_call_inventory(n).items()} for n in roots}
book+='''; Payload work uses actual encoded-layout maximum, not arbitrary data caps.
(defconst *fn2-boot-work-geometry-max* *fn2-checkpoint-geometry-record-max-size*)
(defconst *fn2-boot-work-pack-bytes*
 (+ (* 2 *fn2-format-sector-size*) 32 (* 3 32)
    (length *fn2-checkpoint-geometry-domain*) *fn2-boot-work-geometry-max*))
(defconst *fn2-boot-work-verify-bytes*
 (+ *fn2-boot-work-pack-bytes* (* 2 *fn2-format-sector-size*) (* 2 32)))
(defconst *fn2-boot-work-anchor-step-bytes*
 (max (+ (* 2 *fn2-format-sector-size*) (* 2 32))
      (+ (* 2 32) (length (fn2-fc-domain :anchor)) *fn2-format-anchor-max-size* (* 32 4) (* 32 4) 32 (* 2 32) (* 3 2 32))))
; FORMAT page may scan then hash each admitted octet. Its OK digest visit
; adds descriptor decode and five copied root hashes; hashing returns MORE.
(defconst *fn2-boot-work-descriptor-check-conditional-bytes*
 (+ (max (* 2 2 32) (* 2 32)) (+ 32 (* 32 4))
    (max (* 2 *fn2-format-sector-size*)
         (+ (* 2 32 4) *fn2-codec-decode-fuel* (* 5 2 32)))))
(assert-event (equal *fn2-boot-work-pack-bytes* 8468))
(assert-event (equal *fn2-boot-work-verify-bytes* 16724))
(assert-event (equal *fn2-boot-work-anchor-step-bytes* 8256))
(assert-event (equal *fn2-boot-work-descriptor-check-conditional-bytes* 8480))
'''
Path('books/boot-callback-work.lisp').write_text(book)
Path('tests/fixtures/boot-callback-cost-components.json').write_text(json.dumps(report,indent=2)+'\n')
