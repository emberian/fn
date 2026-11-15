; Cold adoption consumes the completed loader scan for the actual selected
; source. The six identity scalars come from the retained selected-source row.
(in-package "ACL2")
(include-book "checkpoint-selected-source-state")
(include-book "run-physical-readiness")
(fn2-book-layer :c)
(defun fn2-checkpoint-summary-loader-ready-p
 (fn2-checkpoint-selected-source fn2-run-load-readiness fn2-run-load-geometry
  fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases
  fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)
 (declare (xargs :stobjs
  (fn2-checkpoint-selected-source fn2-run-load-readiness fn2-run-load-geometry
   fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases
   fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)
  :guard (and (fn2-checkpoint-selected-source-wfp fn2-checkpoint-selected-source)
              (fn2-run-load-readiness-guard))))
 (and (< 0 (fn2-checkpoint-selected-source-rows fn2-checkpoint-selected-source))
      (fn2-run-load-readiness-complete-current-p
       (fn2-checkpoint-selected-source-tag 0 fn2-checkpoint-selected-source)
       (fn2-checkpoint-selected-source-generation 0 fn2-checkpoint-selected-source)
       (fn2-checkpoint-selected-source-candidate 0 fn2-checkpoint-selected-source)
       (fn2-checkpoint-selected-source-owner-kind 0 fn2-checkpoint-selected-source)
       (fn2-checkpoint-selected-source-owner-slot 0 fn2-checkpoint-selected-source)
       (fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source)
       fn2-run-load-readiness fn2-run-load-geometry fn2-id-decides fn2-reads
       fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-run-load-ops
       fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)))

; Boot starts the actual bounded readiness scan for its retained selected
; source. Selection authority remains with the cold adoption source check.
(defun fn2-checkpoint-summary-loader-begin
 (fn2-checkpoint-selected-source fn2-run-load-readiness fn2-run-load-geometry
  fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases
  fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)
 (declare (xargs :stobjs
  (fn2-checkpoint-selected-source fn2-run-load-readiness fn2-run-load-geometry
   fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases
   fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)
  :guard (and (fn2-checkpoint-selected-source-wfp fn2-checkpoint-selected-source)
              (fn2-run-load-readiness-guard))))
 (if (not (and (< 0 (fn2-checkpoint-selected-source-rows fn2-checkpoint-selected-source))
               (= (fn2-checkpoint-selected-source-phase 0 fn2-checkpoint-selected-source)
                  *fn2-checkpoint-selected-source-phase-projected*)
               (posp (fn2-checkpoint-selected-source-tag 0 fn2-checkpoint-selected-source))
               (posp (fn2-checkpoint-selected-source-generation 0 fn2-checkpoint-selected-source))
               (posp (fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source))))
     (mv :source fn2-run-load-readiness)
  (fn2-run-load-readiness-begin
   (fn2-checkpoint-selected-source-tag 0 fn2-checkpoint-selected-source)
   (fn2-checkpoint-selected-source-generation 0 fn2-checkpoint-selected-source)
   (fn2-checkpoint-selected-source-candidate 0 fn2-checkpoint-selected-source)
   (fn2-checkpoint-selected-source-owner-kind 0 fn2-checkpoint-selected-source)
   (fn2-checkpoint-selected-source-owner-slot 0 fn2-checkpoint-selected-source)
   (fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source)
   fn2-run-load-readiness fn2-run-load-geometry fn2-id-decides fn2-reads
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-run-load-ops
   fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)))

; Each step delegates one bounded cursor/operation check to the real loader.
(defun fn2-checkpoint-summary-loader-step
 (budget fn2-run-load-readiness fn2-run-load-geometry fn2-id-decides fn2-reads
  fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-run-load-ops
  fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)
 (declare (xargs :stobjs
  (fn2-run-load-readiness fn2-run-load-geometry fn2-id-decides fn2-reads
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-run-load-ops
   fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool)
  :guard (fn2-run-load-readiness-guard)))
 (fn2-run-load-readiness-step budget fn2-run-load-readiness fn2-run-load-geometry
  fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases
  fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool))

(defcost fn2-checkpoint-summary-loader-begin-op :child fn2-checkpoint-summary-loader-begin
 :answers (:source :geometry :capacity :more)
 :steps *fn2-work-stage* :bytes 0 :descriptors 0
 :tables (fn2-core-checkpoint-selected-source fn2-core-run-load-readiness fn2-core-run-load-geometry
  fn2-core-id-decides fn2-core-reads fn2-core-run-loads fn2-core-run-cursors
  fn2-core-checkpoint-summary-leases fn2-core-run-load-ops fn2-core-ops fn2-core-fc
  fn2-core-fc-context fn2-core-b3 fn2-core-fields fn2-core-digests fn2-core-pool)
 :doc "Start the actual bounded physical-loader readiness scan for the retained selected source.")
(defcost fn2-checkpoint-summary-loader-step-op :child fn2-checkpoint-summary-loader-step
 :answers (:yield :changed :row :more :bounds :operation :capacity :complete)
 :steps *fn2-work-stage* :bytes 0 :descriptors 0
 :tables (fn2-core-run-load-readiness fn2-core-run-load-geometry fn2-core-id-decides
  fn2-core-reads fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary-leases
  fn2-core-run-load-ops fn2-core-ops fn2-core-fc fn2-core-fc-context fn2-core-b3
  fn2-core-fields fn2-core-digests fn2-core-pool)
 :doc "Advance one real physical-loader readiness cursor or operation row.")
