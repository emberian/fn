#!/usr/bin/env python3
"""Share the actual typed manifest-entry recording path between cold/live intake."""
from pathlib import Path
import lisp_rewrite as lr
P='fn2-checkpoint-summary'
def txt(s,n):return s[n.start:n.end]
def rewrite(source):
 forms=lr.parse(source).forms
 load=lr.match(f'(defun {P}-load-hash ?*body)',forms,deep=False)[0].node
 cap=lr.match(f'(defun {P}-capture ?*body)',forms,deep=False)[0].node
 block=cap.items[-1];bind=block.items[1];items=list(bind.items)
 start=next(i for i,n in enumerate(items) if getattr(n.items[0],'low',None)=='schema')
 guard=next(i for i,n in enumerate(items) if i>=start and 'fn2-checkpoint-restore-map-present' in txt(source,n))
 tail='\n      '.join(txt(source,n) for n in items[start:])
 body='(b* ('+tail+') (mv :captured fn2-checkpoint-summary fn2-checkpoint-summary-sources))'
 parsed=lr.parse(body);ed=[]
 # Only actual control-row accesses become parameterized. Digest i=0 and
 # source-directory extent indices retain their original meanings.
 for m in lr.match('(?head ?*args)',parsed.forms):
  n=m.node
  if not n.items or not hasattr(n.items[0],'low'):continue
  h=n.items[0].low
  if h.startswith(P+'-') and len(n.items)>2 and getattr(n.items[1],'low',None)=='0' and getattr(n.items[-1],'low',None)==P:
   ed.append((n.items[1].start,n.items[1].end,'r'))
  if h=='mv' and getattr(n.items[-1],'low',None)=='fn2-fields':ed.append((n.items[-1].start,n.items[-1].end,''))
  owners={'fn2-checkpoint-restore-semantic-owner-kind':'kind','fn2-checkpoint-restore-semantic-owner-slot':'owner','fn2-checkpoint-restore-semantic-owner-gen':'generation'}
  if h in owners:ed.append((n.start,n.end,owners[h]))
 body=lr.write(body,ed)
 # Cold allocation-map checks stay at the authenticated cold caller. Live
 # intake has the actual completed writer/extent checks instead.
 parsed=lr.parse(body);typed=next(m.node for m in lr.match('(unless (and ?*checks))',parsed.forms) if 'fn2-checkpoint-restore-map-present' in txt(body,m.node))
 andnode=typed.items[1];ed=[]
 for n in andnode.items[1:]:
  if 'fn2-checkpoint-restore-map' in txt(body,n):ed.append((n.start,n.end,''))
 body=lr.write(body,ed)
 parsed=lr.parse(body);bindings=parsed.forms[0].items[1]
 g=next(n for n in bindings.items if hasattr(n.items[0],'items') and n.items[0].items and getattr(n.items[0].items[0],'low',None)=='unless')
 protection='''
      (other (if (= r 0) 1 0))
      ((when (and (< other (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                  (posp (fn2-checkpoint-summary-tag other fn2-checkpoint-summary))
                  (= (fn2-checkpoint-summary-sources-tag e fn2-checkpoint-summary-sources)
                     (fn2-checkpoint-summary-tag other fn2-checkpoint-summary))
                  (not (member-equal (fn2-checkpoint-summary-phase other fn2-checkpoint-summary)
                    (list *fn2-checkpoint-summary-phase-idle* *fn2-checkpoint-summary-phase-retired*)))))
       (mv :held-source fn2-checkpoint-summary fn2-checkpoint-summary-sources))'''
 body=lr.write(body,[(g.end,g.end,protection)])
 # Guard the selected row and field region before any access.
 parsed=lr.parse(body);bindings=parsed.forms[0].items[1]
 initial='''((unless (and (natp r) (< r 2) (< r (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                  (posp (fn2-checkpoint-summary-tag r fn2-checkpoint-summary))
                  (= (fn2-checkpoint-summary-phase r fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-capture*)
                  (natp eb) (<= (+ eb *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :source fn2-checkpoint-summary fn2-checkpoint-summary-sources))\n      '''
 body=lr.write(body,[(bindings.start+1,bindings.start+1,initial)])
 helper='''; Shared recording consumes existing generated schema10 fields, never a new
; parser or caller-computed hash. The caller supplies actual authenticated
; cold-entry or physically completed producer provenance before this step.
(defun fn2-checkpoint-summary-record-fields (r eb kind owner generation
 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields fn2-pool)
 :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
             (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources)
             (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 '''+body+')\n'
 entry='''; Canonical root Ref recording shared by cold and live source intake.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-summary-state")
(include-book "runs-served")
(fn2-book-layer :c)

'''+txt(source,load)+'\n\n'+helper
 # The cold caller retains all original typed map checks, then delegates the
 # exact field write; field decoding still happens once before this call.
 call='''((mv code fn2-checkpoint-summary fn2-checkpoint-summary-sources)
       (fn2-checkpoint-summary-record-fields 0 eb
        (fn2-checkpoint-restore-semantic-owner-kind 0 fn2-checkpoint-restore-semantic)
        (fn2-checkpoint-restore-semantic-owner-slot 0 fn2-checkpoint-restore-semantic)
        (fn2-checkpoint-restore-semantic-owner-gen 0 fn2-checkpoint-restore-semantic)
        fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields fn2-pool))'''
 newbind=source[bind.start:items[guard].end]+'\n      '+call+')'
 tagbind=lr.match('(tag ?value)',lr.parse(newbind).forms)[0].node
 line=newbind.rfind('\n',0,tagbind.start)+1
 end=tagbind.end+1 if newbind[tagbind.end:tagbind.end+1]=='\n' else tagbind.end
 newbind=lr.write(newbind,[(line,end,'')])
 final=block.items[-1];newfinal='(mv code fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields)'
 cold=lr.write(source,[(load.start,load.end,''),(bind.start,bind.end,newbind),(final.start,final.end,newfinal)])
 cold=cold.replace('(include-book "checkpoint-summary-state")','(include-book "checkpoint-summary-state")\n(include-book "checkpoint-summary-entry")')
 entry='\n'.join(line.rstrip() for line in entry.splitlines())+'\n'
 while '\n\n\n' in entry:entry=entry.replace('\n\n\n','\n\n')
 return cold,entry
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]/'books';p=root/'checkpoint-summary-catalog.lisp';cold,entry=rewrite(p.read_text())
 lr.parse(cold);lr.parse(entry);p.write_text(cold);(root/'checkpoint-summary-entry.lisp').write_text(entry)
