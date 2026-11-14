; The four physical anchor slots are format geometry, not a namespace ceiling.
; This cold census records what their actual retained installation evidence
; establishes. A head of the observed ancestry graph is NOT a selected base.
(in-package "ACL2")
(include-book "columns")
(include-book "checkpoint-geometry")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-recovery-census
 ((phase (:enum fn2-checkpoint-recovery-census-phase
    (:idle :candidates :pairs :closure :heads :complete :uncertain)))
  (topology (:enum fn2-checkpoint-recovery-census-topology
    (:none :single-head :fork :conflict :incomplete)))
  (candidate :u8) (left :u8) (right :u8) (via :u8)
  (checked-mask :u8) (empty-mask :u8) (invalid-mask :u8)
  (bound-mask :u8) (missing-mask :u8) (head-mask :u8) (head :u8)
  (duplicates :u16) (parents :u16) (ancestry :u16) (conflicts :u16)
  (open-parent-mask :u8) (semantic-roots-owed :bool)))

(defun fn2-checkpoint-recovery-census-slotp (slot)
 (declare (xargs :guard t))
 (and (natp slot) (< slot *fn2-checkpoint-anchor-slots*)))
(defun fn2-checkpoint-recovery-census-bit (slot)
 (declare (xargs :guard t))
 (if (fn2-checkpoint-recovery-census-slotp slot) (ash 1 slot) 0))
(defun fn2-checkpoint-recovery-census-pair-bit (left right)
 (declare (xargs :guard t))
 (if (and (fn2-checkpoint-recovery-census-slotp left) (fn2-checkpoint-recovery-census-slotp right))
     (ash 1 (+ (* *fn2-checkpoint-anchor-slots* left) right)) 0))
(defun fn2-checkpoint-recovery-census-memberp (slot mask)
 (declare (xargs :guard t))
 (and (integerp mask) (not (equal (logand (fn2-checkpoint-recovery-census-bit slot) mask) 0))))
(defun fn2-checkpoint-recovery-census-relatedp (left right matrix)
 (declare (xargs :guard t))
 (and (integerp matrix) (not (equal (logand (fn2-checkpoint-recovery-census-pair-bit left right) matrix) 0))))

; A row of the 4x4 closure: this is constant format work, not an extent scan.
(defun fn2-checkpoint-recovery-census-covers (slot matrix)
 (declare (xargs :guard t))
 (if (and (fn2-checkpoint-recovery-census-slotp slot) (integerp matrix))
     (logand 15 (ash matrix (- (* *fn2-checkpoint-anchor-slots* slot)))) 0))
