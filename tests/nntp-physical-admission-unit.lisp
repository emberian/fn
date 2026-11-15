; Prepared/unexecuted actual resource recipe controls. No actor scheduling,
; disk result, parser or serving qualification is asserted here.
(in-package "ACL2")
(include-book "../books/cursor-physical-admission")
(include-book "std/util/bstar" :dir :system)
(defconst *fn2-npa-stobjs*
 '(fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
(defmacro fn2-npa-mv (answer) `(mv ,answer ,@*fn2-npa-stobjs*))
(defun fn2-npa-nest (n body)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (zp n) body
  (fn2-npa-nest (- n 1)
   `(with-local-stobj ,(nth (- n 1) *fn2-npa-stobjs*)
     (mv-let (answer ,@(take n *fn2-npa-stobjs*)) ,body
      ,(if (equal n 1) 'answer `(mv answer ,@(take (- n 1) *fn2-npa-stobjs*))))))))
(defmacro fn2-npa-with (body) (fn2-npa-nest (len *fn2-npa-stobjs*) body))
(defun fn2-npa-case (enough fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool) :verify-guards nil))
 (b* ((jobs *fn2-b-query-loader-jobs*)
      (capacity (+ (* 2 jobs) (if enough 1 0)))
      (fn2-reads (fn2-reads-init *fn2-b-query-read-rows* fn2-reads))
      (fn2-id-decides (fn2-id-decides-init 0 fn2-id-decides))
      (fn2-run-loads (fn2-run-loads-init jobs fn2-run-loads))
      (fn2-run-cursors (fn2-run-cursors-init jobs fn2-run-cursors))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 1 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init jobs fn2-checkpoint-summary-leases))
      ; All three byte requests resolve to THIS one actual pool class.
      (fn2-pool (fn2-pool-init (list (cons capacity *fn2-format-page-size*)) 1 100 fn2-pool))
      ((mv code complete slot gen fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
       (fn2-cursor-article-query-reserve-children 0 9 0 1 fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
  (fn2-npa-mv
   (if enough
    (and (eq code :ok) (equal complete 1) (eq (fn2-pool-workspace-code slot gen 9 0 1 fn2-pool) :ok)
         (equal (fn2-pool-class-countsi 0 fn2-pool) 0)
         (equal (fn2-run-loads-phase 0 fn2-run-loads) *fn2-run-load-phase-reserved*)
         (equal (fn2-run-loads-phase (- jobs 1) fn2-run-loads) *fn2-run-load-phase-reserved*))
    (and (eq code :exhausted) (equal complete 0) (equal slot *fn2-none*) (equal gen 0)
         (equal (fn2-pool-class-countsi 0 fn2-pool) capacity)
         (fn2-run-load-region-freep 0 0 *fn2-b-query-read-rows*
          *fn2-b-query-read-rows* (* *fn2-b-query-read-rows* *fn2-b-range-source-cursors*) 0 0
          fn2-run-loads fn2-checkpoint-summary-leases))))))
(assert-event (fn2-npa-with (fn2-npa-case t fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
(assert-event (fn2-npa-with (fn2-npa-case nil fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
