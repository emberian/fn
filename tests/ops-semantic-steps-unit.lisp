(in-package "ACL2")
(include-book "../books/ops-semantic-steps")
(include-book "../books/assembly-init")
(include-book "std/util/bstar" :dir :system)

; Teeth for FN2-CORE-OPS-SEMANTIC. The positive run initializes the tiny
; profile (the init conjunct), then drives one write through the real steps
; by fn2-core-ops-step: its issue, the host's outbox-ack, the host's
; post-result, one harvest, then the host's clock post, the mailbox and the
; host's stray count, asserting the antecedent before and the conclusion after
; each step. The removal run plants a reserved write row with a posted result
; queued in the posted FIFO, which only fn2-ops-semanticp excludes: the step
; set and every other input are the positive run's, the antecedent fails, and
; the conclusion fails with it.

(defun fn2-oss-test-plant (b fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (let* ((fn2-ops (fn2-ops-put b (phase *fn2-op-phase-reserved*) (kind *fn2-action-write*)
                                 (range-len 1) (c0-posted 1) (c0-harvested 0)
                                 (c0-event *fn2-event-write-result*) (c0-outcome *fn2-outcome-done*)
                                 (c0-reason *fn2-reason-none*) (c0-count 1)))
           (tail (fn2-ops-post-tail fn2-ops))
           (fn2-ops (update-fn2-ops-posted-fifoi tail (* 2 b) fn2-ops))
           (fn2-ops (update-fn2-ops-post-tail
                     (fn2-ring-next tail (fn2-ops-posted-fifo-length fn2-ops)) fn2-ops)))
      (update-fn2-ops-post-count (+ 1 (fn2-ops-post-count fn2-ops)) fn2-ops))
    fn2-core))
(defun fn2-oss-test-free-head (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (h) (fn2-ops-free-head fn2-ops) h))
(defun fn2-oss-test-gen (op fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (g) (fn2-ops-gen op fn2-ops) g))

;; One step of the statement: the antecedent and conclusion both equal EXPECT.
(defun fn2-oss-test-step (op a expect fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((unless (equal (fn2-core-ops-semantic-hyps op fn2-core) expect)) (mv (list :hyps op) fn2-core))
       (fn2-core (fn2-core-ops-step op a fn2-core))
       ((unless (equal (fn2-core-ops-semantic-check fn2-core) expect)) (mv (list :conclusion op) fn2-core)))
    (mv t fn2-core)))
(defun fn2-oss-test-run (positive fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       ((unless (fn2-core-ops-semantic-check fn2-core)) (mv :init fn2-core))
       ((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv :reserve fn2-core))
       ((mv code fn2-core) (fn2-core-write slot gen 0 9 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv :write fn2-core))
       (op (fn2-oss-test-free-head fn2-core))
       ((mv r fn2-core) (fn2-oss-test-step :write (list 0 slot gen 0 1 0 1 0 1 0) t fn2-core))
       ((unless (eq r t)) (mv r fn2-core))
       (og (fn2-oss-test-gen op fn2-core))
       (fn2-core (if positive fn2-core (fn2-oss-test-plant (fn2-oss-test-free-head fn2-core) fn2-core)))
       ((mv r fn2-core) (fn2-oss-test-step :outbox-ack (list 1) positive fn2-core))
       ((unless (eq r t)) (mv r fn2-core))
       ((mv r fn2-core) (fn2-oss-test-step :post-result
                          (list 0 op og *fn2-event-write-result* *fn2-outcome-done* *fn2-reason-none* 1 0 0)
                          positive fn2-core))
       ((unless (eq r t)) (mv r fn2-core))
       ((mv r fn2-core) (if positive (fn2-oss-test-step :harvest nil t fn2-core) (mv t fn2-core)))
       ((unless (eq r t)) (mv r fn2-core))
       ((mv r fn2-core) (fn2-oss-test-step :post-clock (list 5 0 0) positive fn2-core))
       ((unless (eq r t)) (mv r fn2-core))
       ((mv r fn2-core) (fn2-oss-test-step :mailbox nil positive fn2-core))
       ((unless (eq r t)) (mv r fn2-core))
       ((mv r fn2-core) (fn2-oss-test-step :count-stray nil positive fn2-core)))
    (mv r fn2-core)))
(defun fn2-oss-test-teeth-1 (positive)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-oss-test-run positive fn2-core) result)))
(defun fn2-core-ops-semantic-teeth ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-oss-test-teeth-1 t) t) (equal (fn2-oss-test-teeth-1 nil) t)))
(assert-event (equal (fn2-oss-test-teeth-1 t) t))
(assert-event (equal (fn2-oss-test-teeth-1 nil) t))
(fn2-assert-owed-teeth fn2-core-ops-semantic)
