; Teeth for books/bp-request-recovery.lisp and the ION attempt plan of
; books/bp-request-plan.lisp, over the committed-article workflow of
; bp-outbound-tests: a journal whose attempt record is durable and whose
; outcome is not (the process died between them, the 5b cut of the
; native-request lane) opens fenced.
(in-package "ACL2")
(include-book "bp-request-plan-tests")
(include-book "../../books/bp-request-recovery")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bprv-history*
  (list *bpo-config-record* *bpo-enqueue-record*
        '(:outcome 10 0 :ordinary :durable) *bpo-attempt-record*))
(defconst *bprv-open* (fn-bpiw-replay-journal *bpo-node* *bprv-history*))

; Reachable witness: the journal opens, fenced on the pending attempt, and
; every request is refused (the finding this closes).
(assert-event (car *bprv-open*))
(assert-event (equal (fn-bp-state-fenced (nth 1 *bprv-open*)) t))
(assert-event (null (fn-bprq-plan (nth 1 *bprv-open*) "work:out" "attempt:two")))

(defun bprv-recover (outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((plan (fn-bprq-recovery-plan (nth 1 *bprv-open*) "work:out"
                                      "attempt:out" outcome))
         (r (nth 1 plan))
         (live (fn-bpiw-apply (nth 1 *bprv-open*) (nth 3 *bprv-open*) r))
         (reopen (fn-bpiw-replay-journal *bpo-node*
                                         (append *bprv-history* (list r)))))
    (list plan live reopen)))

; :committed.  The plan is the recovery outcome of the attempt's own
; transaction; live and reopen agree; the image is unfenced; the work's
; attempt is :unknown (retryable), and the next request is accepted, with
; no retry record needed, both live and after the next open.
(defconst *bprv-c* (bprv-recover :committed))
(assert-event (equal (nth 0 *bprv-c*)
                     '(:recover (:outcome 11 0 :recovery :committed))))
(assert-event (car (nth 1 *bprv-c*)))
(assert-event (not (fn-bp-state-fenced (nth 1 (nth 1 *bprv-c*)))))
(assert-event (car (nth 2 *bprv-c*)))
(assert-event (equal (nth 1 (nth 2 *bprv-c*)) (fn-bp-restart (nth 1 (nth 1 *bprv-c*)))))
(assert-event (equal (fn-bp-work-status "work:out"
                                        (fn-bp-state-works (nth 1 (nth 1 *bprv-c*))))
                     :unknown))
(assert-event (equal (car (fn-bprq-plan (nth 1 (nth 1 *bprv-c*)) "work:out" "attempt:two"))
                     :request))
(assert-event (equal (car (fn-bprq-plan (nth 1 (nth 2 *bprv-c*)) "work:out" "attempt:two"))
                     :request))
; The next request's records replay after the recovery outcome.
(defconst *bprv-next* (fn-bprq-plan (nth 1 (nth 2 *bprv-c*)) "work:out" "attempt:two"))
(assert-event
 (car (fn-bpiw-replay-journal
       *bpo-node*
       (append *bprv-history*
               (list '(:outcome 11 0 :recovery :committed))
               (if (fn-bprq-plan-retry *bprv-next*)
                   (list (fn-bprq-plan-retry *bprv-next*)) nil)
               (list (fn-bprq-plan-attempt *bprv-next*)
                     (fn-bprq-plan-outcome *bprv-next*))))))

; :absent.  The pending is dropped; the work keeps its earlier state and the
; next request is accepted.
(defconst *bprv-a* (bprv-recover :absent))
(assert-event (equal (nth 0 *bprv-a*)
                     '(:recover (:outcome 11 0 :recovery :absent))))
(assert-event (and (car (nth 1 *bprv-a*)) (car (nth 2 *bprv-a*))))
(assert-event (not (fn-bp-state-fenced (nth 1 (nth 1 *bprv-a*)))))
(assert-event (equal (car (fn-bprq-plan (nth 1 (nth 2 *bprv-a*)) "work:out" "attempt:two"))
                     :request))

; Refusals, each with its reason and nothing to publish.
(assert-event (equal (fn-bprq-recovery-plan (nth 1 *bprv-open*) "work:out" "attempt:out" :maybe)
                     '(:refused :outcome)))
(assert-event (equal (fn-bprq-recovery-plan (nth 1 *bprv-open*) "work:missing" "attempt:out" :committed)
                     '(:refused :attempt-unknown)))
(assert-event (equal (fn-bprq-recovery-plan (nth 1 *bprv-open*) "work:out" "attempt:other" :committed)
                     '(:refused :attempt-unknown)))
(assert-event (equal (fn-bprq-recovery-plan *bprq-s* "work:out" "attempt:out" :committed)
                     '(:refused :not-fenced)))
(assert-event (equal (fn-bprq-recovery-plan (nth 1 (nth 1 *bprv-c*)) "work:out" "attempt:out" :committed)
                     '(:refused :not-fenced)))
; A live pending that is not fenced (no restart yet) is not recoverable.
(assert-event (equal (fn-bprq-recovery-plan (nth 1 *bpo-attempt-prepared*) "work:out" "attempt:out" :committed)
                     '(:refused :not-fenced)))

; Keystone hypotheses.  (car open): a history that does not open has no
; image to recover.  (equal (car plan) :recover): a recovery outcome the
; plan did not produce (wrong transaction) is not accepted live.
(must-fail
 (assert-event (car (fn-bpiw-replay-journal *bpo-node* (cdr *bprv-history*)))))
(must-fail
 (assert-event (car (fn-bpiw-apply (nth 1 *bprv-open*) (nth 3 *bprv-open*)
                                   '(:outcome 99 0 :recovery :committed)))))
(must-fail
 (assert-event (equal (car (fn-bprq-recovery-plan (nth 1 *bprv-open*) "work:out"
                                                  "attempt:other" :committed))
                      :recover)))

; The ION attempt plan (host/native/workflow.lisp fnn-workflow-ion-submit).
; After a restart the in-flight attempt is :restart-observed; the plan puts
; the journaled retry request first, and the history replays.  Without it
; the same attempt is admitted live and refused by replay (the defect).
(defconst *bprv-ion* (fn-bprq-ion-attempt-plan *bprq-restarted* 12 0 "work:out" "attempt:two"))
(assert-event (equal (car *bprv-ion*)
                     '(:retry-request "work:out" "attempt:out" 0 "policy:out")))
(assert-event (equal (fn-bp-journal-nth 0 (cadr *bprv-ion*)) :attempt))
(assert-event
 (car (fn-bpiw-replay-journal
       *bpo-node*
       (append *bprq-history*
               (list (car *bprv-ion*) (cadr *bprv-ion*)
                     '(:outcome 12 0 :ordinary :durable))))))
(must-fail
 (assert-event
  (car (fn-bpiw-replay-journal
        *bpo-node*
        (append *bprq-history*
                (list (cadr *bprv-ion*)
                      '(:outcome 12 0 :ordinary :durable)))))))
; With no restart there is no retry record; the plan is the attempt alone.
(assert-event (null (car (fn-bprq-ion-attempt-plan *bprq-s* 11 0 "work:out" "attempt:out"))))
(assert-event (equal (cadr (fn-bprq-ion-attempt-plan *bprq-s* 11 0 "work:out" "attempt:out"))
                     *bpo-attempt-record*))
