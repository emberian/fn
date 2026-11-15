from pathlib import Path
import sys
sys.path.insert(0,'tools');import lisp_rewrite as lr
owned=lr.match('(defun fn2-checkpoint-projection-owned-step ?*body)',lr.parse(Path('books/checkpoint-owned-projection.lisp').read_text()).forms,deep=False)[0].node
args=[x.text for x in owned.items[2].items];carriers=[x for x in args if x.startswith('fn2-')]
current=lr.match('(defun fn2-checkpoint-projection-current-p ?*body)',lr.parse(Path('books/checkpoint-projection-state.lisp').read_text()).forms,deep=False)[0].node
currentcall='(fn2-checkpoint-projection-current-p '+' '.join(x.text for x in current.items[2].items)+')'
outs='fn2-checkpoint-projection fn2-checkpoint-selected-source fn2-extents fn2-alloc-edges fn2-checkpoint-construction'
call='(fn2-checkpoint-projection-owned-step '+' '.join(args)+')'
loop='(fn2-checkpoint-projection-index-loop-p fn2-checkpoint-projection fn2-checkpoint-restore-map fn2-extents)'
domain='(fn2-checkpoint-projection-index-carriers '+' '.join(carriers)+')'
text='''; Actual owned projection consumer, with per-yield identity observations.
; Checked census/selected validated premises remain synthetic exactly as in
; checkpoint-projection-unit. This is not disk authentication/full cold boot.
; SOURCE corruption controls change the retained owner only AFTER real
; prepare/probe produced PROBE or READY; no pending phase is manually minted.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-projection-unit")
(include-book "../books/checkpoint-projection-identity-preservation")
(fn2-alloc-test-reference-events fn2-checkpoint-construction)
(defun fn2-cpi-snapshot (fn2-checkpoint-projection fn2-checkpoint-selected-source fn2-extents fn2-alloc-edges fn2-checkpoint-construction)
 (declare (xargs :stobjs (fn2-checkpoint-projection fn2-checkpoint-selected-source fn2-extents fn2-alloc-edges fn2-checkpoint-construction) :verify-guards nil))
 (list (fn2-cpu-snapshot fn2-checkpoint-projection fn2-checkpoint-selected-source fn2-extents fn2-alloc-edges)
       (fn2-checkpoint-construction-logical-snapshot fn2-checkpoint-construction)))
'''
snap='(fn2-cpi-snapshot '+outs+')'
text+='''(defun fn2-cpi-owned-drive (fuel mode trace saw-probe saw-ready '''+' '.join(args)+''')
 (declare (xargs :stobjs ('''+ ' '.join(carriers)+''') :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :budget nil saw-probe saw-ready '''+outs+''')
  (b* ((phase (fn2-alloc-identity-phase fn2-extents))
       (saw-probe (or saw-probe (= phase *fn2-alloc-identity-phase-probe*)))
       (saw-ready (or saw-ready (= phase *fn2-alloc-identity-phase-ready*)))
       (before-domain '''+domain+''')
       (before-loop '''+loop+''')
       (before-current '''+currentcall+''')
       (refuse (or (and (eq mode :probe-owner) (= phase *fn2-alloc-identity-phase-probe*))
                   (and (eq mode :ready-owner) (= phase *fn2-alloc-identity-phase-ready*))))
       (fn2-checkpoint-selected-source (if refuse
        (fn2-checkpoint-selected-source-set-owner-gen 0
         (+ 1 (fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source)) fn2-checkpoint-selected-source)
        fn2-checkpoint-selected-source))
       (call-domain '''+domain+''')
       (current-after-corruption '''+currentcall+''')
       (before (if refuse '''+snap+''' nil))
       ((mv code '''+outs+''') '''+call+''')
       (after-loop '''+loop+''')
       (trace (and trace before-domain before-loop before-current call-domain after-loop)))
   (cond
    (refuse (mv code (and trace (not current-after-corruption) (eq code :ownership) (equal before '''+snap+''')
                           (= phase (fn2-alloc-identity-phase fn2-extents))) saw-probe saw-ready '''+outs+'''))
    ((eq code :more) (fn2-cpi-owned-drive (- fuel 1) mode trace saw-probe saw-ready '''+' '.join(args)+'''))
    (t (mv code trace saw-probe saw-ready '''+outs+'''))))))
'''
# Use the actual concrete CORE child accessors, just as the production/test consumers.
bindings=' '.join('('+x+' (fn2-core-'+x.removeprefix('fn2-')+' fn2-core))' for x in carriers if x!='fn2-checkpoint-projection')
text+='''(defun fn2-cpi-body (mode fn2-checkpoint-projection fn2-core)
 (declare (xargs :stobjs (fn2-checkpoint-projection fn2-core) :verify-guards nil))
 (b* ((fn2-core (fn2-core-init (put-assoc-equal :extent-slots 6 *fn2-profile-tiny*) fn2-core))
      (fn2-checkpoint-projection (fn2-checkpoint-projection-init 1 fn2-checkpoint-projection))
      ((mv selected fn2-core) (fn2-cpu-select fn2-core))
      ((mv decoded fn2-core) (fn2-cpu-map fn2-core)))
  (stobj-let ('''+bindings+''')
   (answer '''+outs+''')
   (b* ((fn2-checkpoint-selected-source (fn2-checkpoint-selected-source-put 0
         (phase *fn2-checkpoint-selected-source-phase-validated*)
         (generation (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control))))
        (fn2-extents (fn2-alloc-init 6 fn2-extents))
        (fn2-alloc-edges (fn2-alloc-edges-init 128 fn2-alloc-edges))
        ((mv begun fn2-checkpoint-projection fn2-checkpoint-selected-source fn2-extents)
         (fn2-checkpoint-projection-begin '''+' '.join(args[1:-2])+'''))
        (initial '''+loop+''')
        ((mv code trace saw-probe saw-ready '''+outs+''')
         (fn2-cpi-owned-drive (+ 16 (* 6 (+ 6 4))) mode t nil nil *fn2-checkpoint-master-kind* '''+' '.join(args[1:])+''')))
    (mv (and selected decoded (eq begun :more) initial trace saw-probe
         (if mode
          (and (eq code :ownership) (if (eq mode :ready-owner) saw-ready (not saw-ready))
               (= (fn2-extents-state (fn2-checkpoint-projection-cursor 0 fn2-checkpoint-projection) fn2-extents)
                  *fn2-extent-state-free*))
          (and (eq code :projected) saw-ready
               (fn2-alloc-identity-maintained-p fn2-extents)
               (fn2-cpu-rows-p 0 fn2-extents fn2-checkpoint-restore-map)))) '''+outs+'''))
   (mv answer fn2-checkpoint-projection fn2-core))))
(defun fn2-cpi-run (mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (with-local-stobj fn2-checkpoint-projection
    (mv-let (answer fn2-checkpoint-projection fn2-core)
     (fn2-cpi-body mode fn2-checkpoint-projection fn2-core) (mv answer fn2-core))) answer)))
(assert-event (fn2-cpi-run nil))
(assert-event (fn2-cpi-run :probe-owner))
(assert-event (fn2-cpi-run :ready-owner))
'''
Path('tests/checkpoint-projection-identity-unit.lisp').write_text(text)
