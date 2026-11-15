"""Emit profile-indexed original-source inventory and actual compaction hooks."""
from pathlib import Path
from checkpoint_live_old_identity import FIELDS
pfx='fn2-checkpoint-predecessors'
control='fn2-checkpoint-predecessor-control'
comp='fn2-checkpoint-compaction'
common=[comp,'fn2-checkpoint-build','fn2-csnapshot','fn2-checkpoints','fn2-overlays','fn2-run-installed',pfx,control]
state='''; One slot per actual overlay or installed row, independent of output count.
; Original ownership survives all schema rescans and post-Fence replacement.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :c)
(defcolumns fn2-checkpoint-predecessors
 ((live :bool) (token :u60) (kind :u8) (row :u32) (schema :u60) (order :u60)
  (source-state :u8) (seen :u60) (last-round :u60) (ended :bool)
  (output-rank :u60) (retire-stage :u8)
'''
state+='\n'.join('  (old-'+f+' '+t+')' for f,t in FIELDS)+'''))
(defcolumns fn2-checkpoint-predecessor-control
 ((phase (:enum fn2-checkpoint-predecessor-phase (:idle :capture :ready :checking :complete :retiring :done)))
  (token :u60) (candidate :u32) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (cut-commit :u60) (cut-event :u60) (overlay-rows :u32) (run-rows :u32)
  (cursor :u32) (count :u32) (checked :u32)))
'''
Path('books/checkpoint-predecessors-state.lisp').write_text(state)
def decl(args):return ' (declare (xargs :stobjs ('+' '.join(args)+') :guard (and '+' '.join('('+a+'-wfp '+a+')' for a in args)+')))\n'
def defin(name,args,body,scalars=[]):return '(defun '+name+' ('+' '.join(scalars+args)+')\n'+decl(args)+body+')\n'
def mv(code,outputs):return '(mv '+code+' '+' '.join(outputs)+')'
owner='(fn2-checkpoint-compaction-ownerp '+' '.join(common[:6])+')'
s='''; Actual held-source inventory. No caller chooses a verified flag, output
; rank or source count. Every hook derives current source from the real merge
; continuation. One row/cell per positive step; no stored-entry ceiling.
(in-package "ACL2")
(include-book "checkpoint-predecessors-state")
(include-book "checkpoint-compaction-source")
(fn2-book-layer :c)
'''
body=''' (and (< 0 (fn2-checkpoint-predecessor-control-rows fn2-checkpoint-predecessor-control))
  (< 0 (fn2-checkpoint-compaction-rows fn2-checkpoint-compaction))
  (= (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors)
     (+ (fn2-overlays-rows fn2-overlays) (fn2-run-installed-rows fn2-run-installed)))
  (= (fn2-checkpoint-predecessor-control-overlay-rows 0 fn2-checkpoint-predecessor-control) (fn2-overlays-rows fn2-overlays))
  (= (fn2-checkpoint-predecessor-control-run-rows 0 fn2-checkpoint-predecessor-control) (fn2-run-installed-rows fn2-run-installed))
'''
for a,b in [('token','token'),('candidate','candidate'),('owner-kind','owner-kind'),('owner-slot','owner-slot'),('owner-gen','owner-gen')]:body+='  (= ('+control+'-'+a+' 0 '+control+') ('+comp+'-'+b+' 0 '+comp+'))\n'
for f in ['cut-commit','cut-event']:body+='  (= ('+control+'-'+f+' 0 '+control+') (fn2-csnapshot-'+f+' 0 fn2-csnapshot))\n'
body+=')'
s+=defin('fn2-checkpoint-predecessor-bound-p',common,body)
for name,phase in [('ready','ready'),('complete','complete')]:
 body=' (and '+owner+' (fn2-checkpoint-predecessor-bound-p '+' '.join(common)+')\n (= (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control) *fn2-checkpoint-predecessor-phase-'+phase+'*)'+('\n (= (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-done*)' if phase=='complete' else '')+')'
 s+=defin('fn2-checkpoint-predecessor-'+name+'-p',common,body)

# Pure exact capture identity independent of compaction active phase.
a=[pfx,'fn2-overlays','fn2-run-installed']
body=''' (and (natp i) (< i (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors))
 (= (fn2-checkpoint-predecessors-live i fn2-checkpoint-predecessors) 1)
 (let ((r (fn2-checkpoint-predecessors-row i fn2-checkpoint-predecessors)))
  (case (fn2-checkpoint-predecessors-kind i fn2-checkpoint-predecessors)
   (0 (and (< r (fn2-overlays-rows fn2-overlays))
'''
for f,actual in [('source-state','phase'),('schema','schema'),('order','seq')]:body+='    (= (fn2-overlays-'+actual+' r fn2-overlays) ('+pfx+'-'+f+' i '+pfx+'))\n'
over={'slot':'slot','gen':'gen','entries':'count','okind':'okind','oslot':'oslot','ogen':'ogen'}
for f,actual in over.items():body+='    (= (fn2-overlays-'+actual+' r fn2-overlays) ('+pfx+'-old-'+f+' i '+pfx+'))\n'
body+='   ))\n   (1 (and (< r (fn2-run-installed-rows fn2-run-installed))\n'
for f,actual in [('source-state','state'),('schema','schema'),('order','run')]:body+='    (= (fn2-run-installed-'+actual+' r fn2-run-installed) ('+pfx+'-'+f+' i '+pfx+'))\n'
for f,_ in FIELDS:
 actual={'allocation':'counter','tag':'catalog-tag'}.get(f,f)
 body+='    (= (fn2-run-installed-'+actual+' r fn2-run-installed) ('+pfx+'-old-'+f+' i '+pfx+'))\n'
body+='   ))\n   (otherwise nil))))'
s+=defin('fn2-checkpoint-predecessor-identity-p',a,body,['i'])
out=[control]
body=' (b* (((unless (and '+owner+'''
 (= (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-schema*)
 (< 0 (fn2-checkpoint-predecessor-control-rows fn2-checkpoint-predecessor-control))
 (or (= (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control) *fn2-checkpoint-predecessor-phase-idle*)
     (and (= (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control) *fn2-checkpoint-predecessor-phase-done*)
          (not (= (fn2-checkpoint-predecessor-control-token 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction)))))
 (unsigned-byte-p 32 (+ (fn2-overlays-rows fn2-overlays) (fn2-run-installed-rows fn2-run-installed)))
 (= (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors) (+ (fn2-overlays-rows fn2-overlays) (fn2-run-installed-rows fn2-run-installed))))) '''+mv(':snapshot',out)+''')
 (fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0
  (phase *fn2-checkpoint-predecessor-phase-capture*) (cursor 0) (count 0) (checked 0)
'''
for f in ['token','candidate','owner-kind','owner-slot','owner-gen']:body+='  ('+f+' ('+comp+'-'+f+' 0 '+comp+'))\n'
for f in ['cut-commit','cut-event']:body+='  ('+f+' (fn2-csnapshot-'+f+' 0 fn2-csnapshot))\n'
body+='  (overlay-rows (fn2-overlays-rows fn2-overlays)) (run-rows (fn2-run-installed-rows fn2-run-installed)))))\n '+mv(':more',out)+')'
s+=defin('fn2-checkpoint-predecessor-begin',common,body)
# Capture actual raw O+R rows one at a time.
out=[pfx,control]
body=' (b* (((unless (posp budget)) '+mv(':yield',out)+''')
 ((unless (and '''+owner+' (fn2-checkpoint-predecessor-bound-p '+' '.join(common)+''')
  (= (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control) *fn2-checkpoint-predecessor-phase-capture*)
  (= (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-schema*))) '''+mv(':snapshot',out)+''')
 (i (fn2-checkpoint-predecessor-control-cursor 0 fn2-checkpoint-predecessor-control))
 (o (fn2-overlays-rows fn2-overlays)) (n (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors))
 ((when (= i n)) (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-set-phase 0 *fn2-checkpoint-predecessor-phase-ready* fn2-checkpoint-predecessor-control))) '''+mv(':ready',out)+'''))
 ((unless (and (< i n) (unsigned-byte-p 32 (+ 1 i)))) '''+mv(':bounds',out)+''')
 (kind (if (< i o) 0 1)) (r (if (< i o) i (- i o)))
 ((mv code schema order) (fn2-checkpoint-compaction-source-tuple kind r fn2-overlays fn2-run-installed))
 ((unless (eq code :ok))
  (b* ((fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-put i (live 0) (token 0)))
       (fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-set-cursor 0 (+ 1 i) fn2-checkpoint-predecessor-control))) '''+mv(':more',out)+'''))
 (count (+ 1 (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control)))
 ((unless (unsigned-byte-p 32 count)) '''+mv(':bounds',out)+''')
 (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-put i
  (live 1) (token (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction))
  (kind kind) (row r) (schema schema) (order order)
  (source-state (if (= kind 0) (fn2-overlays-phase r fn2-overlays) (fn2-run-installed-state r fn2-run-installed)))
  (seen 0) (last-round 0) (ended 0) (output-rank 0) (retire-stage 0)
'''
for f,_ in FIELDS:
 rv='(fn2-run-installed-'+{'allocation':'counter','tag':'catalog-tag'}.get(f,f)+' r fn2-run-installed)'
 ov='(fn2-overlays-'+over[f]+' r fn2-overlays)' if f in over else '0'
 body+='  (old-'+f+' (if (= kind 0) '+ov+' '+rv+'))\n'
body+='  ))\n (fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (cursor (+ 1 i)) (count count))))\n '+mv(':more',out)+')'
s+=defin('fn2-checkpoint-predecessor-capture-step',common,body,['budget'])
# Internal hook shared bindings derive exact source, never supplied by caller.
hook=''' (b* (((unless (and '''+owner+' (fn2-checkpoint-predecessor-bound-p '+' '.join(common)+''')
  (= (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control) *fn2-checkpoint-predecessor-phase-ready*)
  (= (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) PHASE))) REFUSE)
 (kind (fn2-checkpoint-compaction-source-kind 0 fn2-checkpoint-compaction))
 (r (fn2-checkpoint-compaction-source-row 0 fn2-checkpoint-compaction))
 (i (if (= kind 0) r (+ (fn2-overlays-rows fn2-overlays) r)))
 (rank (fn2-checkpoint-compaction-output-rank 0 fn2-checkpoint-compaction))
 ((unless (and (<= kind 1) (< i (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors))
  (fn2-checkpoint-predecessor-identity-p i fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)
  (= (fn2-checkpoint-predecessors-token i fn2-checkpoint-predecessors) (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction))
  (= (fn2-checkpoint-predecessors-schema i fn2-checkpoint-predecessors) (fn2-checkpoint-compaction-schema 0 fn2-checkpoint-compaction))
  (= (fn2-checkpoint-predecessors-order i fn2-checkpoint-predecessors) (fn2-checkpoint-compaction-source-order 0 fn2-checkpoint-compaction))
  (posp rank) (or (= (fn2-checkpoint-predecessors-output-rank i fn2-checkpoint-predecessors) 0)
                 (= (fn2-checkpoint-predecessors-output-rank i fn2-checkpoint-predecessors) rank)))) REFUSE)
'''
out=[comp,pfx]
body=hook.replace('PHASE','*fn2-checkpoint-compaction-phase-equal-lower*').replace('REFUSE',mv(':source',out))
body+=''' (round (fn2-checkpoint-compaction-lower-round 0 fn2-checkpoint-compaction))
 ((unless (and (= (fn2-checkpoint-compaction-has-lower 0 fn2-checkpoint-compaction) 1)
               (= (fn2-checkpoint-predecessors-ended i fn2-checkpoint-predecessors) 0)
               (< (fn2-checkpoint-predecessors-last-round i fn2-checkpoint-predecessors) round)
               (< (fn2-checkpoint-predecessors-seen i fn2-checkpoint-predecessors) (fn2-checkpoint-predecessors-old-entries i fn2-checkpoint-predecessors)))) '''+mv(':count',out)+''')
 (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-put i
  (seen (+ 1 (fn2-checkpoint-predecessors-seen i fn2-checkpoint-predecessors))) (last-round round) (output-rank rank)))
 (fn2-checkpoint-compaction (fn2-checkpoint-compaction-set-phase 0 *fn2-checkpoint-compaction-phase-seek* fn2-checkpoint-compaction)))
 '''+mv(':more',out)+')'
s+=defin('fn2-checkpoint-predecessor-source-key',common,body)
body=hook.replace('PHASE','*fn2-checkpoint-compaction-phase-source-end*').replace('REFUSE',mv(':source',out))
body+=''' ((unless (= (fn2-checkpoint-predecessors-seen i fn2-checkpoint-predecessors) (fn2-checkpoint-predecessors-old-entries i fn2-checkpoint-predecessors))) '''+mv(':count',out)+''')
 (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-put i (ended 1) (output-rank rank)))
 (fn2-checkpoint-compaction (fn2-checkpoint-compaction-set-phase 0 *fn2-checkpoint-compaction-phase-park* fn2-checkpoint-compaction)))
 '''+mv(':more',out)+')'
s+=defin('fn2-checkpoint-predecessor-source-end',common,body)
out=[control]
body=' (b* (((unless (posp budget)) '+mv(':yield',out)+''')
 ((unless (and '''+owner+' (fn2-checkpoint-predecessor-bound-p '+' '.join(common)+''')
  (= (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-done*))) '''+mv(':snapshot',out)+''')
 (phase (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control))
 ((when (= phase *fn2-checkpoint-predecessor-phase-ready*))
  (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (phase *fn2-checkpoint-predecessor-phase-checking*) (cursor 0) (checked 0)))) '''+mv(':more',out)+'''))
 ((unless (= phase *fn2-checkpoint-predecessor-phase-checking*)) '''+mv(':phase',out)+''')
 (i (fn2-checkpoint-predecessor-control-cursor 0 fn2-checkpoint-predecessor-control))
 (n (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors))
 ((when (= i n))
  (if (not (= (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control))) '''+mv(':count',out)+'''
   (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-set-phase 0 *fn2-checkpoint-predecessor-phase-complete* fn2-checkpoint-predecessor-control))) '''+mv(':complete',out)+''')))
 ((unless (and (< i n) (unsigned-byte-p 32 (+ 1 i)))) '''+mv(':bounds',out)+''')
 (kind (if (< i (fn2-overlays-rows fn2-overlays)) 0 1))
 (r (if (= kind 0) i (- i (fn2-overlays-rows fn2-overlays))))
 ((mv code & &) (fn2-checkpoint-compaction-source-tuple kind r fn2-overlays fn2-run-installed))
 (live (= (fn2-checkpoint-predecessors-live i fn2-checkpoint-predecessors) 1))
 ((unless (and (eq live (eq code :ok))
  (or (not live) (and
   (= (fn2-checkpoint-predecessors-token i fn2-checkpoint-predecessors) (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction))
   (fn2-checkpoint-predecessor-identity-p i fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)
   (= (fn2-checkpoint-predecessors-ended i fn2-checkpoint-predecessors) 1)
   (= (fn2-checkpoint-predecessors-seen i fn2-checkpoint-predecessors) (fn2-checkpoint-predecessors-old-entries i fn2-checkpoint-predecessors))
   (posp (fn2-checkpoint-predecessors-output-rank i fn2-checkpoint-predecessors)))))) '''+mv(':source',out)+''')
 (checked (+ (if live 1 0) (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control)))
 ((unless (unsigned-byte-p 32 checked)) '''+mv(':bounds',out)+''')
 (fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (cursor (+ 1 i)) (checked checked))))
 '''+mv(':more',out)+')'
s+=defin('fn2-checkpoint-predecessor-complete-step',common,body,['budget'])
for name in ['begin','capture-step','source-key','source-end','complete-step']:
 s+='(defcost fn2-checkpoint-predecessor-'+name+'-op :child fn2-checkpoint-predecessor-'+name+' :answers t :steps *fn2-work-stage* :bytes 128 :descriptors 0\n :tables ('+' '.join(x.replace('fn2-','fn2-core-',1) for x in common)+')\n :doc "One actual held original-source inventory transition; no output/source count ceiling.")\n'
Path('books/checkpoint-predecessors.lisp').write_text(s)
