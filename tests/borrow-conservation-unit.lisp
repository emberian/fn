(in-package "ACL2")
(include-book "../books/borrow-faces")
(include-book "../books/assembly-init")
(include-book "../books/host-boundary")
(include-book "std/util/bstar" :dir :system)

; Teeth for FN2-CORE-BORROW-CONSERVATION. Both runs lease one write borrow
; through the real issue, acknowledge it, and harvest one terminal cell
; through fn2-core-borrow-all-step; the positive run acknowledges and posts
; through the host's steps, then writes and releases the row through the
; pool's. The positive run harvests the write's own
; result: the antecedent holds, the count moves 1 -> 0, and the conclusion
; holds. The removal run plants a second, unregistered write row (phase
; reserved, a posted write-result naming the same pool row, queued in the
; posted FIFO), which only fn2-ops-semanticp excludes: every other
; antecedent holds, the harvest releases the first write's borrow on the
; planted row's behalf, and the conclusion fails.

(defun fn2-borrow-test-ack-post (n op og fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (b* (((mv ?ignored fn2-ops) (fn2-outbox-ack n fn2-ops))
         (fn2-ops (if (natp op)
                      (fn2-post-result 0 op og *fn2-event-write-result* *fn2-outcome-done*
                                       *fn2-reason-none* 1 0 0 fn2-ops)
                    fn2-ops)))
      fn2-ops)
    fn2-core))
(defun fn2-borrow-test-plant (b slot gen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (let* ((fn2-ops (fn2-ops-put b (phase *fn2-op-phase-reserved*) (kind *fn2-action-write*)
                                 (range-slot slot) (range-gen gen) (range-len 1)
                                 (c0-posted 1) (c0-harvested 0) (c0-event *fn2-event-write-result*)
                                 (c0-outcome *fn2-outcome-done*) (c0-reason *fn2-reason-none*)
                                 (c0-count 1)))
           (tail (fn2-ops-post-tail fn2-ops))
           (fn2-ops (update-fn2-ops-posted-fifoi tail (* 2 b) fn2-ops))
           (fn2-ops (update-fn2-ops-post-tail
                     (fn2-ring-next tail (fn2-ops-posted-fifo-length fn2-ops)) fn2-ops)))
      (update-fn2-ops-post-count (+ 1 (fn2-ops-post-count fn2-ops)) fn2-ops))
    fn2-core))
(defun fn2-borrow-test-free-head (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (h) (fn2-ops-free-head fn2-ops) h))
(defun fn2-borrow-test-semanticp (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (ok) (fn2-ops-semanticp fn2-ops) ok))
(defun fn2-borrow-test-out-count (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n) (fn2-pool-out-count slot fn2-pool) n))

;; One step of the statement whose antecedent holds: the conclusion holds after it.
(defun fn2-borrow-test-step (op a fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((unless (fn2-core-borrow-all-hyps op fn2-core)) (mv (list :hyps op) fn2-core))
       (fn2-core (fn2-core-borrow-all-step op a fn2-core))
       ((unless (fn2-core-borrows-accounted-check fn2-core)) (mv (list :conclusion op) fn2-core)))
    (mv t fn2-core)))
(defun fn2-borrow-test-run (positive fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       ((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv :reserve fn2-core))
       ((mv code fn2-core) (fn2-core-write slot gen 0 9 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv :write fn2-core))
       (op (fn2-borrow-test-free-head fn2-core))
       (a (list 0 slot gen 0 1 0 1 0 1 0))
       ((unless (fn2-core-borrow-all-hyps :write fn2-core)) (mv :issue-hyps fn2-core))
       (fn2-core (fn2-core-borrow-all-step :write a fn2-core))
       ((unless (and (fn2-core-borrows-accounted-check fn2-core)
                     (equal (fn2-borrow-test-out-count slot fn2-core) 1)))
        (mv :issue-conclusion fn2-core))
       (og (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (g) (fn2-ops-gen op fn2-ops) g))
       ((mv r fn2-core)
        (if positive
            (b* (((mv r fn2-core) (fn2-borrow-test-step :outbox-ack (list 1) fn2-core))
                 ((unless (eq r t)) (mv r fn2-core)))
              (fn2-borrow-test-step :post-result
                (list 0 op og *fn2-event-write-result* *fn2-outcome-done* *fn2-reason-none* 1 0 0) fn2-core))
          (let ((fn2-core (fn2-borrow-test-ack-post 1 nil og fn2-core))) (mv t fn2-core))))
       ((unless (eq r t)) (mv r fn2-core))
       (fn2-core (if positive fn2-core
                   (fn2-borrow-test-plant (fn2-borrow-test-free-head fn2-core) slot gen fn2-core)))
       (semantic (fn2-borrow-test-semanticp fn2-core))
       ((unless (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                     (fn2-core-borrows-accounted-check fn2-core)
                     (equal (fn2-borrow-test-out-count slot fn2-core) 1)
                     (equal semantic positive)
                     (equal (fn2-core-borrow-all-hyps :harvest fn2-core) positive)))
        (mv :harvest-hyps fn2-core))
       (fn2-core (fn2-core-borrow-all-step :harvest nil fn2-core))
       ((unless (and (equal (fn2-borrow-test-out-count slot fn2-core) 0)
                     (equal (fn2-core-borrows-accounted-check fn2-core) positive)))
        (mv :harvest-conclusion fn2-core))
       ((unless positive) (mv t fn2-core))
       ;; the released row is a workspace again: a pool write and its release
       ((mv r fn2-core) (fn2-borrow-test-step :pool-write (list slot gen 1 7 1 0 1) fn2-core))
       ((unless (eq r t)) (mv r fn2-core)))
    (fn2-borrow-test-step :release (list slot gen 1 0 1) fn2-core)))
(defun fn2-borrow-test-teeth-1 (positive)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-borrow-test-run positive fn2-core) result)))
(defun fn2-core-borrow-teeth ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-borrow-test-teeth-1 t) t) (equal (fn2-borrow-test-teeth-1 nil) t)))
(assert-event (equal (fn2-borrow-test-teeth-1 t) t))
(assert-event (equal (fn2-borrow-test-teeth-1 nil) t))
(fn2-assert-owed-teeth fn2-core-borrow-conservation)

; borrow-faces walks the faces in its own world (the books defining them);
; host-boundary's world has no other: every fn2-core-returning caller of a
; pool writer here is one A2 states.
(assert-event (subsetp-eq (fn2-bf-faces (w state)) *fn2-bf-faces*))
