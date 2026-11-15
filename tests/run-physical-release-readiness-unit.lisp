; UNEXECUTED source fixture: actual resource reservation and canonical release.
; Checker geometry is a one-row fixture premise. No format/read operation or
; published catalog is seeded or claimed. The real one-row readiness consumer
; observes the release result; this is not a full profile readiness witness.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/run-physical-release")
(include-book "../books/run-physical-readiness")
(include-book "column-snapshot-support")
(make-event (cons 'progn (fn2-test-column-snapshot-events 'fn2-pool (w state))))
(make-event (cons 'progn (fn2-test-column-snapshot-events 'fn2-run-loads (w state))))
(make-event (cons 'progn (fn2-test-column-snapshot-events 'fn2-run-cursors (w state))))
(make-event (cons 'progn (fn2-test-column-snapshot-events 'fn2-checkpoint-summary (w state))))
(make-event (cons 'progn (fn2-test-column-snapshot-events 'fn2-checkpoint-summary-leases (w state))))
(defun fn2-rpr-body (wrong-gen fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool
 fn2-run-load-geometry fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool
 fn2-run-load-geometry fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests) :verify-guards nil))
 (b* ((fn2-run-loads (fn2-run-loads-init 1 fn2-run-loads))
      (fn2-run-cursors (fn2-run-cursors-init 1 fn2-run-cursors))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 2 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init 1 fn2-checkpoint-summary-leases))
      (fn2-pool (fn2-pool-init '((1 . 4096) (1 . 65536)) 1 100 fn2-pool))
      (fn2-run-load-geometry (fn2-run-load-geometry-init 1 fn2-run-load-geometry))
      (fn2-fc (fn2-fc-init 1 fn2-fc)) (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3)) (fn2-fields (fn2-fields-init 256 fn2-fields))
      (fn2-digests (fn2-digests-init (+ *fn2-digest-stride* 16) fn2-digests))
      (initial (fn2-run-load-readiness-one-row-p 0 fn2-run-load-geometry fn2-run-loads fn2-run-cursors
       fn2-checkpoint-summary-leases fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests))
      ((mv reserve fn2-run-loads fn2-pool) (fn2-run-load-reserve 0 7 8 1 fn2-run-loads fn2-pool))
      ((unless (eq reserve :ok)) (mv nil fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool
       fn2-run-load-geometry fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests))
      (before (list (fn2-test-table-snapshot-fn2-run-loads fn2-run-loads)
                    (fn2-test-table-snapshot-fn2-run-cursors fn2-run-cursors)
                    (fn2-test-table-snapshot-fn2-checkpoint-summary fn2-checkpoint-summary)
                    (fn2-test-table-snapshot-fn2-checkpoint-summary-leases fn2-checkpoint-summary-leases)
                    (fn2-test-table-snapshot-fn2-pool fn2-pool)))
      ((mv code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
       (fn2-run-load-release 0 7 8 (if wrong-gen 2 1) fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      (after (list (fn2-test-table-snapshot-fn2-run-loads fn2-run-loads)
                    (fn2-test-table-snapshot-fn2-run-cursors fn2-run-cursors)
                    (fn2-test-table-snapshot-fn2-checkpoint-summary fn2-checkpoint-summary)
                    (fn2-test-table-snapshot-fn2-checkpoint-summary-leases fn2-checkpoint-summary-leases)
                    (fn2-test-table-snapshot-fn2-pool fn2-pool)))
      (ready (fn2-run-load-readiness-one-row-p 0 fn2-run-load-geometry fn2-run-loads fn2-run-cursors
       fn2-checkpoint-summary-leases fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests)))
  (mv (and initial (if wrong-gen (and (eq code :pending) (equal before after)) (and (eq code :ok) ready)))
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool
   fn2-run-load-geometry fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests)))
(defun fn2-rpr-test (wrong-gen)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-run-loads (with-local-stobj fn2-run-cursors
 (with-local-stobj fn2-checkpoint-summary (with-local-stobj fn2-checkpoint-summary-leases
 (with-local-stobj fn2-pool (with-local-stobj fn2-run-load-geometry
 (with-local-stobj fn2-fc (with-local-stobj fn2-fc-context
 (with-local-stobj fn2-b3 (with-local-stobj fn2-fields (with-local-stobj fn2-digests
 (mv-let (ok fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool
 fn2-run-load-geometry fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests)
 (fn2-rpr-body wrong-gen fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool
 fn2-run-load-geometry fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests) ok)))))))))))))
(assert-event (fn2-rpr-test nil))
(assert-event (fn2-rpr-test t))
