; Teeth for books/bp-node-forward-resume.lisp: the operator's resume of a
; stranded row and the connection-local :uncertain transfer, over
; fn-bpnp-step, from the durable FNBS rows of bp-node-forward-retry-tests.
(in-package "ACL2")
(include-book "bp-node-forward-retry-tests")
(include-book "../../books/bp-node-forward-resume")
(include-book "std/testing/must-fail" :dir :system)

(defun bprs-row (effect)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rec (fn-bpn-nth 3 effect)))
    (if (equal (car rec) :bpnf-forwarded)
        (list (fn-bpnf-stored-record-name (fn-bpn-nth 1 rec) (fn-bpn-nth 2 rec))
              (fn-bpnp-result-frame rec))
      (bpfr-row effect))))
(defun bprs-resume (st arrival)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-step st (list :operator-resume arrival)))
(defun bprs-identity (effect)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-nth 4 (fn-bpn-nth 3 effect)))

;; ---------------------------------------------------------------------
;; Resume, from durable rows.  *bpfr-d4* is the fourth restart: four durable
;; kind 8 rows, retries 3, and its session reports the row stranded.
(make-event `(defconst *bprs-res* ',(bprs-resume *bpfr-d4* 0)))
(defconst *bprs-res-effect* (car (fn-bpnf-answer-effects *bprs-res*)))
(make-event `(defconst *bprs-res-durable* ',(bpfr-durable *bprs-res*)))
(make-event `(defconst *bprs-rows4*
  ',(append *bpfr-rows3* (list (bprs-row *bprs-res-effect*)))))
(make-event `(defconst *bprs-d5* ',(bpfr-restart *bprs-rows4*)))
(make-event `(defconst *bprs-d5-open* ',(bpfr-reopen *bprs-d5*)))
(make-event `(defconst *bprs-d5-sent* ',(bpfr-durable *bprs-d5-open*)))

;; fn-bpnp-step-resume-writes-only-for-a-stranded-row: reachable witness.
(assert-event
 (and (fn-bpnp-stranded-slotp (bpfr-slot *bpfr-d4*) (fn-bpnf-epoch *bpfr-d4*) *bpfr-dest* 3)
      (fn-bpnp-host-eventp (list :operator-resume 0))
      (equal (car *bprs-res-effect*) :persist-forward-result)
      (equal (fn-bpn-nth 8 (fn-bpn-nth 3 *bprs-res-effect*)) :resumed)
      (equal (fn-bpn-nth 3 (fn-bpn-nth 3 *bprs-res-effect*)) 0)
      (equal (bprs-identity *bprs-res-effect*) (bprs-identity *bpfr-attempt-effect*))
      (not (equal (fn-bpnp-result-frame (fn-bpn-nth 3 *bprs-res-effect*)) :bad))))
;; Durable: the row is re-armed live: attempt slot cleared, still pending.
(assert-event
 (and (equal (fn-bpnf-answer-effects *bprs-res-durable*)
             (list (list :forward-ready 0 :resumed)))
      (null (bpfr-slot (fn-bpnf-answer-state *bprs-res-durable*)))
      (equal (fn-bpn-nth 12 (car (fn-bpnf-held-list
                                  (fn-bpnf-answer-state *bprs-res-durable*))))
             '(:forward-pending))))
;; fn-bpnp-resumed-row-is-a-forward-candidate, and the replay half: the
;; next restart replays the :resumed kind 9 from its frame to the same held
;; list; the history keeps all four kind 8 rows; its session offers the row
;; with its original arrival and primary identity, the durable offer sends
;; the original forwarding image, and the count starts again at 0.
(assert-event
 (and (equal (fn-bpnf-held-list *bprs-d5*) (bpfr-replayed *bprs-rows4*))
      (equal (fn-bpnf-held-list *bprs-d5*)
             (fn-bpnf-held-list (fn-bpnf-answer-state *bprs-res-durable*)))
      (equal (len *bprs-rows4*) 7)
      (fn-bpnp-forward-candidatep (car (fn-bpnf-held-list *bprs-d5*)) *bpfr-dest*
                                  *bpfr-obs* (fn-bpnf-epoch *bprs-d5*) 3)
      (equal (car (car (fn-bpnf-answer-effects *bprs-d5-open*))) :persist-attempt)
      (equal (fn-bpn-nth 3 (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bprs-d5-open*)))) 0)
      (equal (bprs-identity (car (fn-bpnf-answer-effects *bprs-d5-open*)))
             (bprs-identity *bpfr-attempt-effect*))
      (equal (car (car (fn-bpnf-answer-effects *bprs-d5-sent*))) :cl-send)
      (equal (fn-bpn-nth 6 (car (fn-bpnf-answer-effects *bprs-d5-sent*)))
             (fn-bpn-nth 6 (car (fn-bpnf-answer-effects *bpfr-s3-answer*))))
      (equal (fn-bpnp-attempt-retries
              (bpfr-slot (fn-bpnf-answer-state *bprs-d5-sent*)))
             0)))

;; Refusals: each reason, and the state is unchanged.
(defun bprs-refusal (answer)
  (declare (xargs :guard t :verify-guards nil))
  (car (fn-bpnf-answer-effects answer)))
(assert-event (equal (bprs-refusal (bprs-resume *bpfr-d4* 7))
                     '(:resume-refused 7 :no-row)))
(assert-event (not (fn-bpnp-host-eventp (list :operator-resume "zero"))))
;; Under the bound (retries 1, a restart ago): not stranded.
(assert-event (equal (bprs-refusal (bprs-resume *bpfr-d2* 0))
                     '(:resume-refused 0 :not-stranded)))
;; A live attempt of this process: not stranded.
(assert-event (equal (bprs-refusal (bprs-resume *bpfr-s3* 0))
                     '(:resume-refused 0 :not-stranded)))
;; Never attempted.
(assert-event (equal (bprs-refusal (bprs-resume *bpfr-s2* 0))
                     '(:resume-refused 0 :not-attempted)))
;; Settled (forwarded).
(assert-event (equal (bprs-refusal (bprs-resume (fn-bpnf-answer-state *bpfr-settled*) 0))
                     '(:resume-refused 0 :not-forward-pending)))
;; Already resumed: the slot is empty.
(assert-event (equal (bprs-refusal (bprs-resume *bprs-d5* 0))
                     '(:resume-refused 0 :not-attempted)))
;; A proposal pending: busy.
(assert-event (equal (bprs-refusal (bprs-resume (fn-bpnf-answer-state *bprs-res*) 0))
                     '(:resume-refused 0 :busy)))
(assert-event (equal (fn-bpnf-answer-state (bprs-resume *bpfr-d2* 0)) *bpfr-d2*))

;; Hypothesis teeth.
;; writes-only-for-a-stranded-row: without the stranded slot there is no
;; :persist-forward-result.
(must-fail
 (assert-event (equal (car (bprs-refusal (bprs-resume *bpfr-d2* 0)))
                      :persist-forward-result)))
;; clears-only-the-slot needs :resumed: a :sent kind 9 on a live attempt
;; also changes the row's dispatch state.
(defconst *bprs-sent-rec*
  (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpfr-settle*))))
(assert-event (equal (car (fn-bpnp-forward-result-apply
                           *bprs-sent-rec* (fn-bpnf-held-list *bpfr-s4*)))
                     :ready))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 2 (fn-bpnp-forward-result-apply
                        *bprs-sent-rec* (fn-bpnf-held-list *bpfr-s4*)))
         (update-nth 13 nil (car (fn-bpnf-held-list *bpfr-s4*))))))
;; A :resumed record on a row that is not stranded does not apply (live or
;; at replay).
(defconst *bprs-rec* (fn-bpn-nth 3 *bprs-res-effect*))
(assert-event (equal (car (fn-bpnp-forward-result-apply
                           *bprs-rec* (fn-bpnf-held-list *bpfr-d4*)))
                     :ready))
(must-fail
 (assert-event (equal (car (fn-bpnp-forward-result-apply
                            *bprs-rec* (fn-bpnf-held-list *bpfr-d2*)))
                      :ready)))
;; resumed-row-is-a-forward-candidate needs a live bundle: at an observation
;; after its lifetime the resumed row is no candidate.
(defconst *bprs-late* (fn-clock-observation 100000000000 0 0 nil))
(must-fail
 (assert-event
  (fn-bpnp-forward-candidatep (car (fn-bpnf-held-list *bprs-d5*)) *bpfr-dest*
                              *bprs-late* (fn-bpnf-epoch *bprs-d5*) 3)))

;; ---------------------------------------------------------------------
;; Connection-local :uncertain (fn-bpnp-tcpcl-outcome of a connection that
;; ended without XFER_ACK or XFER_REFUSE).  In one process: the kind 9
;; keeps the attempt under :uncertain, the next session of the same process
;; re-offers the row (no restart), and the count grows to the bound, where
;; the row is stranded and resume re-arms it.
(defun bprs-uncertain-cycle (st n)
  ;; open session n, make the offer durable, read the transfer as the
  ;; failed connection, make that kind 9 durable
  (declare (xargs :guard t :verify-guards nil))
  (let* ((open (fn-bpnp-step st (list :session *bpfr-dest*
                                      (cons (fn-bpnf-epoch st) n) t 32768
                                      *bpfr-obs*)))
         (sent (bpfr-durable open))
         (effect (car (fn-bpnf-answer-effects sent)))
         (result (fn-bpnp-step (fn-bpnf-answer-state sent)
                               (list :forward-result (fn-bpn-nth 3 effect)
                                     (fn-bpn-nth 4 effect) (fn-bpn-nth 2 effect)
                                     (fn-bpnp-tcpcl-outcome :connection-failed nil)
                                     *bpfr-obs*))))
    (list open sent result (bpfr-durable result))))
(defun bprs-after (cycle)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state (nth 3 cycle)))

(make-event `(defconst *bprs-u1* ',(bprs-uncertain-cycle *bpfr-s2* 1)))
(make-event `(defconst *bprs-u2* ',(bprs-uncertain-cycle (bprs-after *bprs-u1*) 2)))
(make-event `(defconst *bprs-u3* ',(bprs-uncertain-cycle (bprs-after *bprs-u2*) 3)))
(make-event `(defconst *bprs-u4* ',(bprs-uncertain-cycle (bprs-after *bprs-u3*) 4)))
(make-event `(defconst *bprs-u5-open*
  ',(fn-bpnp-step (bprs-after *bprs-u4*)
                  (list :session *bpfr-dest* (cons (fn-bpnf-epoch *bpfr-s2*) 5) t
                        32768 *bpfr-obs*))))
;; fn-bpnp-uncertain-result-keeps-the-count: witness.  The first attempt's
;; kind 9 is :uncertain, durable, and the slot keeps retries 0 under the
;; :uncertain head; the machine is not fenced (issued is empty) and the next
;; session of the same epoch offers the same arrival and identity.
(assert-event
 (and (equal (fn-bpn-nth 8 (fn-bpn-nth 3 (car (fn-bpnf-answer-effects
                                               (nth 2 *bprs-u1*)))))
             :uncertain)
      (equal (fn-bpnf-answer-effects (nth 3 *bprs-u1*))
             (list (list :forward-ready 0 :uncertain)))
      (equal (car (bpfr-slot (bprs-after *bprs-u1*))) :uncertain)
      (equal (fn-bpnp-attempt-retries (bpfr-slot (bprs-after *bprs-u1*))) 0)
      (null (fn-bpnf-issued (bprs-after *bprs-u1*)))
      (equal (fn-bpnf-epoch (bprs-after *bprs-u4*)) (fn-bpnf-epoch *bpfr-s2*))
      (equal (car (car (fn-bpnf-answer-effects (nth 0 *bprs-u2*)))) :persist-attempt)
      (equal (bprs-identity (car (fn-bpnf-answer-effects (nth 0 *bprs-u2*))))
             (bprs-identity *bpfr-attempt-effect*))
      (equal (fn-bpnp-attempt-retries (bpfr-slot (bprs-after *bprs-u2*))) 1)
      (equal (fn-bpnp-attempt-retries (bpfr-slot (bprs-after *bprs-u4*))) 3)
      (equal (fn-bpnf-answer-effects *bprs-u5-open*)
             (list (list :forward-stranded 0 *bpfr-dest* 3)))))
;; Resume in the same process re-arms it; the debt is the settled row's.
(make-event `(defconst *bprs-u-res* ',(bpfr-durable (bprs-resume (bprs-after *bprs-u4*) 0))))
(assert-event
 (and (equal (fn-bpnf-answer-effects *bprs-u-res*)
             (list (list :forward-ready 0 :resumed)))
      (null (bpfr-slot (fn-bpnf-answer-state *bprs-u-res*)))))
;; Replay of the in-process history (kind 8, kind 9 :uncertain, ... ) from
;; its frames gives the live held list.
(make-event `(defconst *bprs-u-rows*
  ',(append *bpfr-rows0*
            (list (bprs-row (car (fn-bpnf-answer-effects (nth 2 *bprs-u1*))))
                  (bprs-row (car (fn-bpnf-answer-effects (nth 0 *bprs-u2*))))
                  (bprs-row (car (fn-bpnf-answer-effects (nth 2 *bprs-u2*))))))))
(assert-event
 (equal (bpfr-replayed *bprs-u-rows*)
        (fn-bpnf-held-list (bprs-after *bprs-u2*))))
;; Hypothesis tooth: a :failed kind 9 settles the slot, so the count is not
;; kept (the row is offered again without one).
(make-event
 `(defconst *bprs-failed*
    ',(let* ((open (fn-bpnp-step *bpfr-s2* (list :session *bpfr-dest*
                                                  (cons (fn-bpnf-epoch *bpfr-s2*) 1)
                                                  t 32768 *bpfr-obs*)))
             (sent (bpfr-durable open))
             (effect (car (fn-bpnf-answer-effects sent))))
        (fn-bpnf-answer-state
         (bpfr-durable
          (fn-bpnp-step (fn-bpnf-answer-state sent)
                        (list :forward-result (fn-bpn-nth 3 effect)
                              (fn-bpn-nth 4 effect) (fn-bpn-nth 2 effect)
                              :failed *bpfr-obs*)))))))
(must-fail
 (assert-event (fn-bpnp-uncertain-attemptp (bpfr-slot *bprs-failed*)
                                           (fn-bpnf-epoch *bprs-failed*)
                                           *bpfr-dest*)))
;; fn-bpnp-no-transfer-reads-as-resumed: the operator's word is not a
;; transfer event.
(assert-event (not (fn-bpnp-host-eventp (list :forward-result 1 1 (cons 1 1) :resumed *bpfr-obs*))))
(assert-event (fn-bpnp-host-eventp (list :forward-result 1 1 (cons 1 1) :uncertain *bpfr-obs*)))
