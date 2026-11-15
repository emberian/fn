; Before the first reply, admit every cursor of the request's declared read
; rows. This is resident active-request capacity, not a limit on stored data.
(in-package "ACL2")
(include-book "machines-c-read")
(include-book "run-physical-region")
(fn2-book-layer :c)
(defconst *fn2-run-query-bundle-count*
 *fn2-b-query-loader-jobs*)
(defun fn2-run-query-bundle-cursor (read0 ordinal transactions reads)
 (declare (xargs :guard t))
 (if (< (nfix ordinal) *fn2-b-query-read-rows*)
  (+ (nfix transactions) (nfix read0) (nfix ordinal))
  (+ (nfix transactions) (nfix reads) (* *fn2-b-range-source-cursors* (nfix read0))
     (- (nfix ordinal) *fn2-b-query-read-rows*))))
(defun fn2-run-page-bundle-reserve-children (read0 kind owner generation fn2-reads fn2-id-decides
 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (if (not (and (natp read0) (<= (+ read0 *fn2-b-query-read-rows*) (fn2-reads-rows fn2-reads))))
  (mv :state 0 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
  (fn2-run-load-region-reserve
   (+ (fn2-id-decides-rows fn2-id-decides) read0) *fn2-b-query-read-rows*
   (+ (fn2-id-decides-rows fn2-id-decides) (fn2-reads-rows fn2-reads) (* *fn2-b-range-source-cursors* read0))
   (* *fn2-b-query-read-rows* *fn2-b-range-source-cursors*) 0 0 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
(fn2-run-load-frames fn2-run-page-bundle-reserve-children
 (read0 kind owner generation fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 2) (fn2-run-cursors 3) (fn2-checkpoint-summary 4) (fn2-checkpoint-summary-leases 5) (fn2-pool 6)))
(defcost fn2-run-page-bundle-reserve :child fn2-run-page-bundle-reserve-children :answers t
 :tables (fn2-core-reads fn2-core-id-decides fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-leases fn2-core-pool)
 :effects ((:acquire (:storage-window)))
 :doc "Admit the declared cursor bundle before any reply; :OK/0 retains actual partial ownership solely for bounded cleanup.")
