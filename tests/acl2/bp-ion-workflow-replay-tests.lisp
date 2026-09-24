; Teeth for books/bp-ion-workflow-replay.lisp.
(in-package "ACL2")
(include-book "bp-ion-workflow-tests")
(include-book "../../books/bp-ion-workflow-replay")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Reachable witnesses: the process dies with an intent durable and its outcome
; unpublished; the reopen fences it; the host inspects storage and publishes
; the recovery outcome.  This is relay-a's cut in the four-node mock lab
; (planning/evidence/m4-app-receipt-2026-09-24.md, finding 4).

(defconst *bpiwr-enqueue-cut*
  (list *bpo-config-record* *bpo-enqueue-record*))
(defconst *bpiwr-open-1*
  (fn-bpiw-replay-journal *bpo-node* *bpiwr-enqueue-cut*))
(assert-event (car *bpiwr-open-1*))
(assert-event (fn-bp-state-fenced (nth 1 *bpiwr-open-1*)))

(defmacro bpiwr-agrees (open journal r)
  ; The keystone's three conclusions, evaluated.
  `(let* ((live (fn-bpiw-apply (nth 1 ,open) (nth 3 ,open) ,r))
          (reopen (fn-bpiw-replay-journal *bpo-node*
                                          (append ,journal (list ,r)))))
     (and (car ,open) (fn-bpiw-recovery-outcomep ,r) (car live)
          (car reopen)
          (equal (nth 1 reopen) (fn-bp-restart (nth 1 live)))
          (equal (nth 3 reopen) (nth 3 live)))))

; Enqueue intent, storage says the record committed: the work is kept.
(defconst *bpiwr-committed* '(:outcome 10 0 :recovery :committed))
(assert-event (bpiwr-agrees *bpiwr-open-1* *bpiwr-enqueue-cut* *bpiwr-committed*))
(assert-event
 (equal (fn-bp-work-status
         "work:out"
         (fn-bp-state-works
          (nth 1 (fn-bpiw-replay-journal
                  *bpo-node* (append *bpiwr-enqueue-cut*
                                     (list *bpiwr-committed*))))))
        :outstanding))
; Storage says absent: no work, and the fence is gone.
(defconst *bpiwr-absent* '(:outcome 10 0 :recovery :absent))
(assert-event (bpiwr-agrees *bpiwr-open-1* *bpiwr-enqueue-cut* *bpiwr-absent*))
(assert-event
 (not (fn-bp-state-fenced
       (nth 1 (fn-bpiw-replay-journal
               *bpo-node* (append *bpiwr-enqueue-cut*
                                  (list *bpiwr-absent*)))))))

; Attempt intent cut: the recovered attempt is :unknown live and
; :restart-observed after the reopen's restart, on both paths.
(defconst *bpiwr-attempt-cut*
  (list *bpo-config-record* *bpo-enqueue-record*
        '(:outcome 10 0 :ordinary :durable) *bpo-attempt-record*))
(defconst *bpiwr-open-2*
  (fn-bpiw-replay-journal *bpo-node* *bpiwr-attempt-cut*))
(assert-event (car *bpiwr-open-2*))
(assert-event (bpiwr-agrees *bpiwr-open-2* *bpiwr-attempt-cut*
                            '(:outcome 11 0 :recovery :committed)))
(assert-event (bpiwr-agrees *bpiwr-open-2* *bpiwr-attempt-cut*
                            '(:outcome 11 0 :recovery :absent)))

; The ION state rides through: a route and its observation recorded before
; the cut are what the reopen after recovery holds.
;; The ION state rides through: the route and observation recorded before the
; cut are what the reopen after recovery holds, on both paths.
(defconst *bpiwr-retry* '(:retry-request "work:out" "attempt:out" 0 "policy:out"))
(defconst *bpiwr-ion-cut*
  (append *bpiw-prefix*
          (list *bpiwr-retry*
                (fn-bpiw-attempt-record
                 (nth 1 (fn-bpiw-replay-journal
                         *bpo-node*
                         (append *bpiw-prefix* (list *bpiwr-retry*))))
                 12 0 "work:out" "attempt:out2"))))
(defconst *bpiwr-open-3*
  (fn-bpiw-replay-journal *bpo-node* *bpiwr-ion-cut*))
(assert-event (car *bpiwr-open-3*))
(assert-event (fn-bp-state-fenced (nth 1 *bpiwr-open-3*)))
(assert-event (consp (fn-bpiw-observations (nth 3 *bpiwr-open-3*))))
(assert-event (bpiwr-agrees *bpiwr-open-3* *bpiwr-ion-cut*
                            '(:outcome 12 0 :recovery :committed)))

; The defect this book closes: without the reconstructed fence the durable
; fold holds the pending unfenced, and the recovery outcome is a no-op there,
; which the live interpreter counts as refusal.
(defconst *bpiwr-fold-1*
  (fn-bpiw-durable-fold
   (fn-bp-initial-state *bpo-node*
                        (fn-bp-config-from-record *bpo-config-record*))
   (fn-bpiw-initial) (cdr *bpiwr-enqueue-cut*)))
(assert-event (car *bpiwr-fold-1*))
(assert-event (not (fn-bp-state-fenced (nth 1 *bpiwr-fold-1*))))
(assert-event
 (not (car (fn-bpiw-apply (nth 1 *bpiwr-fold-1*) (nth 2 *bpiwr-fold-1*)
                          *bpiwr-committed*))))
(assert-event
 (car (fn-bpiw-apply (fn-bpiw-replay-fence (nth 1 *bpiwr-fold-1*)
                                           *bpiwr-committed*)
                     (nth 2 *bpiwr-fold-1*) *bpiwr-committed*)))

; -----------------------------------------------------------------------------
; must-fail, one per hypothesis of
; fn-bpiw-reopen-after-live-recovery-is-the-live-image-restarted

; Without (fn-bpiw-recovery-outcomep r): after a reopen the in-flight attempt
; is :restart-observed, so the live image accepts a new attempt with no
; journaled retry request; the durable history has the attempt in flight and
; refuses it.  This is the "unrecorded restart" the Python host refuses at
; its history gate (tests/test_workflow_live.py).
(defconst *bpiwr-delivered-cut*
  (list *bpo-config-record* *bpo-enqueue-record*
        '(:outcome 10 0 :ordinary :durable) *bpo-attempt-record*
        '(:outcome 11 0 :ordinary :durable)))
(defconst *bpiwr-open-4*
  (fn-bpiw-replay-journal *bpo-node* *bpiwr-delivered-cut*))
(defconst *bpiwr-reattempt*
  (fn-bpiw-attempt-record (nth 1 *bpiwr-open-4*) 12 0 "work:out" "attempt:out2"))
(assert-event (car *bpiwr-open-4*))
(assert-event (not (fn-bpiw-recovery-outcomep *bpiwr-reattempt*)))
(assert-event (car (fn-bpiw-apply (nth 1 *bpiwr-open-4*) (nth 3 *bpiwr-open-4*)
                                  *bpiwr-reattempt*)))
(must-fail
 (defthm bpiwr-teeth-any-live-record-reopens
   (car (fn-bpiw-replay-journal
         *bpo-node* (append *bpiwr-delivered-cut* (list *bpiwr-reattempt*))))))

; Without (car live): a recovery outcome for a transaction the image does not
; hold is refused live and by the history.
(defconst *bpiwr-stranger* '(:outcome 99 0 :recovery :committed))
(assert-event (car *bpiwr-open-1*))
(assert-event (fn-bpiw-recovery-outcomep *bpiwr-stranger*))
(must-fail
 (defthm bpiwr-teeth-unaccepted-recovery-reopens
   (car (fn-bpiw-replay-journal
         *bpo-node* (append *bpiwr-enqueue-cut* (list *bpiwr-stranger*))))))

; (car open) has no separating witness: a failed open stops before any
; recovery outcome's fence, so its image holds no fenced pending and refuses
; every recovery outcome live.  The hypothesis is the host's own precondition
; (fn-workflow-install-replay installs nothing unless the replay succeeds);
; the witness below shows the refusal that makes it unseparable.
(defconst *bpiwr-broken* (append *bpiwr-enqueue-cut* '((:not-a-record))))
(defconst *bpiwr-open-broken*
  (fn-bpiw-replay-journal *bpo-node* *bpiwr-broken*))
(assert-event (not (car *bpiwr-open-broken*)))
(assert-event
 (not (car (fn-bpiw-apply (nth 1 *bpiwr-open-broken*)
                          (nth 3 *bpiwr-open-broken*) *bpiwr-committed*))))
