; Physical anchor roles are independent of canonical catalog candidates.
; Duplicate anchors may share a descriptor while a formerly aliased candidate
; is FREE for the next builder, so neither source nor C-base regions are loans.
(in-package "ACL2")
(include-book "checkpoint-cbase-state")
(include-book "checkpoint-geometry")
(fn2-book-layer :b)
(defun fn2-checkpoint-bank-closure-edge (slot e fn2-extents fn2-ops fn2-checkpoints)
 (declare (xargs :stobjs (fn2-extents fn2-ops fn2-checkpoints)
 :guard (and (fn2-extents-wfp fn2-extents) (fn2-ops-wfp fn2-ops) (fn2-checkpoints-wfp fn2-checkpoints)
             (natp slot) (< slot *fn2-checkpoint-anchor-slots*) (natp e) (< e (fn2-extents-rows fn2-extents)))))
 (+ (fn2-checkpoint-source-edge slot e fn2-extents fn2-ops fn2-checkpoints)
    (* 2 (fn2-checkpoints-rows fn2-checkpoints) (fn2-extents-rows fn2-extents))))
(defthm fn2-checkpoint-bank-closure-edge-after-cbase
 (implies (and (posp (fn2-checkpoints-rows checkpoints)) (posp (fn2-extents-rows extents)))
  (equal (fn2-checkpoint-bank-closure-edge 0 0 extents ops checkpoints)
   (+ 1 (fn2-checkpoint-cbase-edge (- (fn2-checkpoints-rows checkpoints) 1)
         (- (fn2-extents-rows extents) 1) extents ops checkpoints))))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-bank-closure-edge fn2-checkpoint-cbase-edge fn2-checkpoint-source-edge))))
(defthm fn2-checkpoint-bank-closure-edge-stride
 (equal (fn2-checkpoint-bank-closure-edge (+ 1 slot) e extents ops checkpoints)
  (+ (fn2-extents-rows extents) (fn2-checkpoint-bank-closure-edge slot e extents ops checkpoints)))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-bank-closure-edge fn2-checkpoint-source-edge))))
