; LAST is an observable result, independently of the pool state delta.
; This raw primitive control retains the complete core frame and aliases
; two real query windows. It is separate from callback/turn reachability.
(in-package "ACL2")
(include-book "reference-identity-support")

(defun fn2-ref-query-raw-release (drop-last slot gen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code last fn2-pool)
    (fn2-pool-query-release slot gen fn2-pool)
    (mv code (if drop-last nil last) fn2-core)))

(defun fn2-ref-query-raw-expected (slot before)
  (let* ((pool (fn2-cns-drain-child 'fn2-pool before))
         (count (fn2-cns-drain-cell 'fn2-pool-query-ref-count slot pool)))
    (if (zp count) (list :state nil before)
      (list :ok (equal count 1)
        (fn2-cns-drain-put-child 'fn2-pool
          (fn2-cns-drain-put-cell 'fn2-pool-query-ref-count slot (- count 1) pool) before)))))

(defun fn2-ref-query-last-run (drop-last fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv setup id & fn2-core) (fn2-ref-identity-admit-profile *fn2-cns-drain-profile* fn2-core))
       (owner-gen (fn2-cns-row-generation id fn2-core))
       (slot (fn2-cns-row-ns-slot id fn2-core)) (gen (fn2-cns-row-ns-gen id fn2-core))
       ((mv w0 fn2-core) (fn2-cns-query-write '(60 113 62) slot gen 0 id owner-gen fn2-core))
       ((mv w1 fn2-core) (fn2-cns-query-write (make-list 32 :initial-element 7)
                          slot gen 3 id owner-gen fn2-core))
       ((mv q fn2-core) (fn2-identity-decide-start 0 slot gen 0 3 slot gen 3
                         *fn2-cns-kind* id owner-gen fn2-core))
       (before0 (fn2-test-core-snapshot fn2-core))
       (whole-h (and setup (eq w0 :ok) (eq w1 :ok) (eq q :ok)
                     (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                     (equal (fn2-cns-drain-cell 'fn2-pool-query-ref-count slot
                              (fn2-cns-drain-child 'fn2-pool before0)) 2)))
       ((mv code0 last0 fn2-core) (fn2-ref-query-raw-release drop-last slot gen fn2-core))
       (before1 (fn2-test-core-snapshot fn2-core))
       (first (equal (list code0 last0 before1) (fn2-ref-query-raw-expected slot before0)))
       ((mv code1 last1 fn2-core) (fn2-ref-query-raw-release drop-last slot gen fn2-core))
       (before2 (fn2-test-core-snapshot fn2-core))
       (second (equal (list code1 last1 before2) (fn2-ref-query-raw-expected slot before1)))
       ((mv code2 last2 fn2-core) (fn2-ref-query-raw-release nil slot gen fn2-core))
       (after (fn2-test-core-snapshot fn2-core)))
    (mv (and whole-h first (if drop-last (not second) second)
             ; In the mutant, every state cell and CODE remain correct.
             ; Only the last-reference scalar differs from the oracle.
             (equal before2 (caddr (fn2-ref-query-raw-expected slot before1)))
             (eq code1 :ok) (equal last1 (not drop-last))
             (equal (list code2 last2 after) (fn2-ref-query-raw-expected slot before2))) fn2-core)))
(defun fn2-ref-query-last-control (drop-last)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (yes fn2-core) (fn2-ref-query-last-run drop-last fn2-core) yes)))
(assert-event (and (fn2-ref-query-last-control nil) (fn2-ref-query-last-control t)))
