; Teeth of books/bp-node-forward-retry.lisp: N08 under the retry policy of
; spec 4.3.1 (default adopted by the coordinator 2026-09-24, pending ember),
; the stranded-after-bound case, and one must-fail per keystone hypothesis.
; Every trace is through fn-bpnp-step, the function the native host calls
; (host/native/bp-service.lisp fnn-bps-foundation-step).  Recovery events
; carry a model replay result, the fixture shape of
; bp-node-counterexamples-tests.
(in-package "ACL2")
(include-book "../../books/bp-node-forward-retry")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)


(defconst *bpfr-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpfr-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpfr-dest* (cons :dtn '(47 47 98 112 45 100 101 115 116 47)))
(defconst *bpfr-config* (fn-bpn-config *bpfr-local* 3600000 2 32 1048576))
(defconst *bpfr-sender-config* (fn-bpn-config *bpfr-sender* 3600000 2 32 1048576))
(defconst *bpfr-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpfr-ingress*
  (list :cl (cons 0 1) 1 *bpfr-sender* '(115 101 110 100 101 114) 0))
(defun bpfr-receive-event (wire)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event *bpfr-config* wire *bpfr-obs* *bpfr-ingress*)))
(defun bpfr-durable (answer)
  (declare (xargs :guard t :verify-guards nil))
  (let ((effect (car (fn-bpnf-answer-effects answer))))
    (fn-bpnp-step (fn-bpnf-answer-state answer)
                  (list :persist-result (fn-bpn-nth 1 effect)
                        (fn-bpn-nth 2 effect) :durable))))
(defconst *bpfr-raw-s0* (fn-bpnf-initial-state *bpfr-config* 8 1048576))
(defconst *bpfr-s0*
  (fn-bpnf-answer-state
   (fn-bpnp-step *bpfr-raw-s0*
                 (fn-bpnf-family-recover-auto-event *bpfr-raw-s0* nil :ready nil))))
(defconst *bpfr-a*
  (fn-bpn-send-bundle *bpfr-sender-config* *bpfr-dest* '(1 2 3 4) 7 *bpfr-obs*))
(defconst *bpfr-a-wire* (fn-bpb-encode *bpfr-a*))
(defconst *bpfr-a-proposal* (fn-bpnp-step *bpfr-s0* (bpfr-receive-event *bpfr-a-wire*)))
(defconst *bpfr-s1* (fn-bpnf-answer-state (bpfr-durable *bpfr-a-proposal*)))


(defconst *bpfr-routes* (list (list *bpfr-dest* *bpfr-dest*)))
(defconst *bpfr-progress* (list :progress *bpfr-local* *bpfr-obs* *bpfr-routes* 1))
(make-event `(defconst *bpfr-dispatch* ',(fn-bpnp-step *bpfr-s1* *bpfr-progress*)))
(defconst *bpfr-s2* (fn-bpnf-answer-state (bpfr-durable *bpfr-dispatch*)))
(defconst *bpfr-session* (cons 1 1))
(defconst *bpfr-session-event*
  (list :session *bpfr-dest* *bpfr-session* t 32768 *bpfr-obs*))
(make-event `(defconst *bpfr-open* ',(fn-bpnp-step *bpfr-s2* *bpfr-session-event*)))
(defconst *bpfr-attempt-effect* (car (fn-bpnf-answer-effects *bpfr-open*)))
(defconst *bpfr-s3-answer* (bpfr-durable *bpfr-open*))
(defconst *bpfr-s3* (fn-bpnf-answer-state *bpfr-s3-answer*))

;; One death-and-retry cycle: recover the held rows at the next epoch, open a
;; fresh session to the next hop, and make the answered proposal durable.
(defun bpfr-recover (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state
   (fn-bpnp-step st (list :recover-fnbs (1+ (fn-bpnf-epoch st)) nil :ready
                          (list :ready (fn-bpnf-held-list st) nil) 3))))
(defun bpfr-session-event (st)
  (declare (xargs :guard t :verify-guards nil))
  (list :session *bpfr-dest* (cons (fn-bpnf-epoch st) 1) t 32768 *bpfr-obs*))
(defun bpfr-reopen (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-step st (bpfr-session-event st)))
(defun bpfr-slot (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-nth 13 (car (fn-bpnf-held-list st))))

(defconst *bpfr-r1* (bpfr-recover *bpfr-s3*))
(make-event `(defconst *bpfr-o1* ',(bpfr-reopen *bpfr-r1*)))
(defconst *bpfr-p1* (bpfr-durable *bpfr-o1*))
(defconst *bpfr-s4* (fn-bpnf-answer-state *bpfr-p1*))

;; N08, positive: the recovered row keeps its uncertain attempt, the next
;; session re-offers the same arrival and identity, and the durable retry
;; sends the same forwarding image with retry count 1.
(assert-event
 (and (equal (car (bpfr-slot *bpfr-r1*)) :forwarding)
      (fn-bpnp-uncertain-attemptp (bpfr-slot *bpfr-r1*) (fn-bpnf-epoch *bpfr-r1*)
                                  *bpfr-dest*)
      (fn-bpnp-host-eventp (bpfr-session-event *bpfr-r1*))
      (equal (car (car (fn-bpnf-answer-effects *bpfr-o1*))) :persist-attempt)
      (equal (fn-bpn-nth 3 (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpfr-o1*))))
             (fn-bpn-nth 3 (fn-bpn-nth 3 *bpfr-attempt-effect*)))
      (equal (fn-bpn-nth 4 (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpfr-o1*))))
             (fn-bpn-nth 4 (fn-bpn-nth 3 *bpfr-attempt-effect*)))
      (equal (car (car (fn-bpnf-answer-effects *bpfr-p1*))) :cl-send)
      (equal (fn-bpn-nth 6 (car (fn-bpnf-answer-effects *bpfr-p1*)))
             (fn-bpn-nth 6 (car (fn-bpnf-answer-effects *bpfr-s3-answer*))))
      (equal (fn-bpnp-attempt-retries (bpfr-slot *bpfr-s4*)) 1)
      (equal (fn-bpnp-debt *bpfr-s4*) (fn-bpnp-debt *bpfr-s3*))))

;; The peer already holds the bundle and absorbs the re-offer (XFER_ACK):
;; the loop answers :sent and the kind-9 result settles the row as
;; forwarded, attempt cleared, exactly as a first :sent would.
(make-event
 `(defconst *bpfr-settle*
    ',(let ((effect (car (fn-bpnf-answer-effects *bpfr-p1*))))
        (fn-bpnp-step *bpfr-s4*
                      (list :forward-result (fn-bpn-nth 3 effect) (fn-bpn-nth 4 effect)
                            (fn-bpn-nth 2 effect) :sent *bpfr-obs*)))))
(defconst *bpfr-settled* (bpfr-durable *bpfr-settle*))
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects *bpfr-settle*)))
             :persist-forward-result)
      (equal (car (car (fn-bpnf-answer-effects *bpfr-settled*))) :forward-ready)
      (equal (fn-bpn-nth 12 (car (fn-bpnf-held-list
                                  (fn-bpnf-answer-state *bpfr-settled*))))
             '(:dispatch-done))
      (null (bpfr-slot (fn-bpnf-answer-state *bpfr-settled*)))))

;; Stranded after the bound: three deaths after three durable retries leave
;; retries = 3; the fourth recovery's session offers nothing, reports the
;; stranded row, and the row, its attempt and its debt stay held.
(make-event `(defconst *bpfr-s5* ',(fn-bpnf-answer-state (bpfr-durable (bpfr-reopen (bpfr-recover *bpfr-s4*))))))
(make-event `(defconst *bpfr-s6* ',(fn-bpnf-answer-state (bpfr-durable (bpfr-reopen (bpfr-recover *bpfr-s5*))))))
(defconst *bpfr-r7* (bpfr-recover *bpfr-s6*))
(make-event `(defconst *bpfr-o7* ',(bpfr-reopen *bpfr-r7*)))
(assert-event
 (and (equal (fn-bpnp-attempt-retries (bpfr-slot *bpfr-s6*)) 3)
      (fn-bpnp-stranded-slotp (bpfr-slot *bpfr-r7*) (fn-bpnf-epoch *bpfr-r7*) *bpfr-dest* 3)
      (equal (fn-bpnf-answer-effects *bpfr-o7*)
             (list (list :forward-stranded
                         (fn-bpn-nth 3 (car (fn-bpnf-held-list *bpfr-r7*)))
                         *bpfr-dest* 3)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpfr-o7*))
             (fn-bpnf-held-list *bpfr-r7*))
      (null (fn-bpnf-issued (fn-bpnf-answer-state *bpfr-o7*)))
      (equal (fn-bpnp-debt (fn-bpnf-answer-state *bpfr-o7*)) (fn-bpnp-debt *bpfr-r7*))))
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects *bpfr-o7*))) :persist-attempt)))
;; A live attempt (current epoch) is never re-offered: the same session
;; event on the attempted state, before any death, offers nothing.
(assert-event
 (null (fn-bpnf-answer-effects
        (fn-bpnp-step *bpfr-s3* (list :session *bpfr-dest* (cons 1 2) t 32768 *bpfr-obs*)))))

;; ---------------------------------------------------------------------
;; Teeth of fn-bpnp-forward-scan-offers-the-only-candidate.  Witness: the
;; recovered row with its uncertain attempt, alone, fits and is offered.
(defconst *bpfr-h* (car (fn-bpnf-held-list *bpfr-r1*)))
(defconst *bpfr-fresh* (car (fn-bpnf-held-list *bpfr-s2*)))
(defconst *bpfr-live* (car (fn-bpnf-held-list *bpfr-s3*)))
(defconst *bpfr-e* (fn-bpnf-epoch *bpfr-r1*))
(defun bpfr-scan (ordered mru node waits free)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-forward-scan ordered *bpfr-dest* mru node *bpfr-obs* waits free *bpfr-e* 3))
(defun bpfr-offers-h (scan)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (car scan) :ready) (equal (fn-bpn-nth 1 scan) *bpfr-h*)))
(defconst *bpfr-key* (fn-bpnp-wait-key *bpfr-h*))
(assert-event
 (and (fn-bpnp-forward-candidatep *bpfr-h* *bpfr-dest* *bpfr-obs* *bpfr-e* 3)
      (equal (car (fn-bpnp-forward-image *bpfr-h* *bpfr-local* *bpfr-obs*)) :ready)
      (bpfr-offers-h (bpfr-scan (list *bpfr-h*) 32768 *bpfr-local* nil 100))))
;; member dropped: the row is not in the scanned list.
(must-fail (assert-event (bpfr-offers-h (bpfr-scan nil 32768 *bpfr-local* nil 100))))
;; only-candidate dropped: an older fresh candidate to the same peer wins.
(assert-event
 (fn-bpnp-forward-candidatep *bpfr-fresh* *bpfr-dest* *bpfr-obs* *bpfr-e* 3))
(must-fail
 (assert-event
  (bpfr-offers-h (bpfr-scan (list *bpfr-fresh* *bpfr-h*) 32768 *bpfr-local* nil 100))))
;; candidatep dropped: a live attempt (current epoch) is not re-offered.
(assert-event
 (not (fn-bpnp-forward-candidatep *bpfr-live* *bpfr-dest* *bpfr-obs*
                                  (fn-bpnf-epoch *bpfr-s3*) 3)))
(must-fail
 (assert-event
  (equal (car (fn-bpnp-forward-scan (list *bpfr-live*) *bpfr-dest* 32768 *bpfr-local*
                                    *bpfr-obs* nil 100 (fn-bpnf-epoch *bpfr-s3*) 3))
         :ready)))
;; mru-wait dropped.
(must-fail
 (assert-event
  (bpfr-offers-h (bpfr-scan (list *bpfr-h*) 32768 *bpfr-local*
                            (list (list :bpnp-wait *bpfr-key* :mru *bpfr-dest* 32768))
                            100))))
;; credit-blocked dropped.
(must-fail
 (assert-event
  (bpfr-offers-h (bpfr-scan (list *bpfr-h*) 32768 *bpfr-local*
                            (list (list :bpnp-wait *bpfr-key* :credit 5)) 3))))
;; image-ready dropped: no forwarding image at an invalid local node.
(assert-event
 (not (equal (car (fn-bpnp-forward-image *bpfr-h* :bad *bpfr-obs*)) :ready)))
(must-fail (assert-event (bpfr-offers-h (bpfr-scan (list *bpfr-h*) 32768 :bad nil 100))))
;; fits dropped: a 10-octet transfer MRU.
(must-fail (assert-event (bpfr-offers-h (bpfr-scan (list *bpfr-h*) 10 *bpfr-local* nil 100))))

;; Teeth of fn-bpnp-step-session-offer-is-the-scan-choice: witness *bpfr-o1*
;; above; without an offer (the live-attempt session) the scan is not ready.
(must-fail
 (assert-event
  (equal (car (fn-bpnp-forward-scan
               (reverse (fn-bpnf-held-list *bpfr-s3*)) *bpfr-dest* 32768 *bpfr-local*
               *bpfr-obs* (fn-bpnp-waits *bpfr-s3*)
               (fn-bpnd-free (fn-bpnp-used *bpfr-s3*) (fn-bpnp-debt *bpfr-s3*)
                             *fn-bpnp-control-margin*)
               (fn-bpnf-epoch *bpfr-s3*) 3))
         :ready)))

;; Teeth of fn-bpnp-forward-image-keeps-the-held-primary: witness, the
;; retry's image; without :ready the image carries no encoded bundle.
(assert-event
 (let ((image (fn-bpnp-forward-image *bpfr-h* *bpfr-local* *bpfr-obs*)))
   (and (equal (fn-bpn-nth 1 image) (fn-bpb-encode (fn-bpn-nth 2 image)))
        (equal (fn-bpb-bundle-primary (fn-bpn-nth 2 image))
               (fn-bpb-bundle-primary *bpfr-a*)))))
(must-fail
 (assert-event
  (let ((image (fn-bpnp-forward-image *bpfr-h* :bad *bpfr-obs*)))
    (equal (fn-bpn-nth 1 image) (fn-bpb-encode (fn-bpn-nth 2 image))))))

;; Teeth of the retry bound.  Witness: *bpfr-s6* reached exactly 3.  The
;; match hypothesis: a record applied to a row already at the bound would
;; write 4.
(defconst *bpfr-at-bound* (car (fn-bpnf-held-list *bpfr-r7*)))
(defconst *bpfr-rec*
  (fn-bpnp-forward-attempt-record (fn-bpnf-epoch *bpfr-r7*) 0
                                  (fn-bpn-nth 3 *bpfr-at-bound*)
                                  (fn-bpah-held-primary-identity *bpfr-at-bound*)
                                  *bpfr-dest* (cons (fn-bpnf-epoch *bpfr-r7*) 1) 0))
;; Since the budget is configured (lane bp-budgets-receipts), applying a
;; kind 8 does not re-judge it: the history replays whatever budget wrote
;; it.  The live proposal is what refuses a row at the budget.
(assert-event (fn-bpnp-attempt-matches-heldp *bpfr-rec* *bpfr-at-bound*))
(assert-event (not (fn-bpnp-under-budgetp *bpfr-at-bound* 3)))
(assert-event (fn-bpnp-under-budgetp *bpfr-at-bound* 4))
(must-fail
 (assert-event
  (<= (fn-bpnp-attempt-retries
       (fn-bpn-nth 13 (fn-bpnp-attempted-held *bpfr-at-bound* *bpfr-rec*)))
      *fn-bpnp-max-forward-retries*)))
;; The bounded-input hypothesis of the apply and step theorems: an unrelated
;; row already past the bound stays past it.  (The :ready hypothesis of the
;; apply theorem and the :attempt hypothesis of the step theorem have no
;; separating case: a fault answer carries no rows, and the other
;; :persist-result arms only clear attempt slots.)
(defconst *bpfr-over* (update-nth 3 99 (update-nth 13 '(:forwarding 0 0 x y 9) *bpfr-at-bound*)))
(make-event `(defconst *bpfr-pending* ',(fn-bpnf-answer-state (bpfr-reopen *bpfr-r1*))))
(defconst *bpfr-pending-over*
  (update-nth 2 (cons *bpfr-over* (fn-bpnf-held-list *bpfr-pending*)) *bpfr-pending*))
(assert-event
 (and (equal (fn-bpn-nth 3 (fn-bpnf-issued *bpfr-pending-over*)) :attempt)
      (fn-bpnp-retries-boundedp (fn-bpnf-held-list *bpfr-pending*) 3)
      (fn-bpnp-retries-boundedp
       (fn-bpnf-held-list
        (fn-bpnf-answer-state (bpfr-durable (bpfr-reopen *bpfr-r1*))))
       3)))
(must-fail
 (assert-event
  (fn-bpnp-retries-boundedp
   (fn-bpnf-held-list
    (fn-bpnf-answer-state
     (let ((effect (car (fn-bpnf-answer-effects (bpfr-reopen *bpfr-r1*)))))
       (fn-bpnp-step *bpfr-pending-over*
                     (list :persist-result (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect)
                           :durable))))
   3))))

;; ---------------------------------------------------------------------
;; The retry count survives recovery from the durable rows themselves.
;; Unlike bpfr-recover above (which hands recovery the in-memory held list),
;; each restart here starts from the fresh initial state and recovers from
;; the framed FNBS rows the effects asked the host to publish: kind 5, kind
;; 6 and every kind 8, each at its own process epoch.  Witness of
;; fn-bpnp-recovery-success-installs-the-replayed-held and
;; fn-bpnp-host-recovery-installs-the-durable-replay
;; (books/bp-node-progress-premises.lisp).
(defun bpfr-row (effect)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rec (if (equal (car effect) :persist)
                 (fn-bpnf-stored-record (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect)
                                        (fn-bpn-nth 3 effect))
               (fn-bpn-nth 3 effect))))
    (list (fn-bpnf-stored-record-name (fn-bpn-nth 1 rec) (fn-bpn-nth 2 rec))
          (cond ((equal (car rec) :bpnf-stored) (fn-bpnf-stored-record-frame rec))
                ((equal (car rec) :bpnf-dispatched) (fn-bpnp-dispatch-frame rec))
                (t (fn-bpnp-attempt-frame rec))))))
(defun bpfr-restart (rows)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state
   (fn-bpnp-step *bpfr-raw-s0*
                 (fn-bpnf-family-recover-auto-event *bpfr-raw-s0* nil :ready rows))))
(make-event `(defconst *bpfr-rows0*
  ',(list (bpfr-row (car (fn-bpnf-answer-effects *bpfr-a-proposal*)))
        (bpfr-row (car (fn-bpnf-answer-effects *bpfr-dispatch*)))
        (bpfr-row (car (fn-bpnf-answer-effects *bpfr-open*))))))
(make-event `(defconst *bpfr-d1* ',(bpfr-restart *bpfr-rows0*)))
(make-event `(defconst *bpfr-d1-open* ',(bpfr-reopen *bpfr-d1*)))
(make-event `(defconst *bpfr-rows1* ',(append *bpfr-rows0* (list (bpfr-row (car (fn-bpnf-answer-effects *bpfr-d1-open*)))))))
(make-event `(defconst *bpfr-d2* ',(bpfr-restart *bpfr-rows1*)))
(make-event `(defconst *bpfr-d2-open* ',(bpfr-reopen *bpfr-d2*)))
(make-event `(defconst *bpfr-rows2* ',(append *bpfr-rows1* (list (bpfr-row (car (fn-bpnf-answer-effects *bpfr-d2-open*)))))))
(make-event `(defconst *bpfr-d3* ',(bpfr-restart *bpfr-rows2*)))
(make-event `(defconst *bpfr-d3-open* ',(bpfr-reopen *bpfr-d3*)))
(make-event `(defconst *bpfr-rows3* ',(append *bpfr-rows2* (list (bpfr-row (car (fn-bpnf-answer-effects *bpfr-d3-open*)))))))
(make-event `(defconst *bpfr-d4* ',(bpfr-restart *bpfr-rows3*)))
(make-event `(defconst *bpfr-d4-open* ',(bpfr-reopen *bpfr-d4*)))

(defun bpfr-replayed (rows)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-nth 1 (fn-bpnf-family-replay-rows rows (fn-bpnf-base *bpfr-raw-s0*))))
(assert-event
 (and (equal (fn-bpnf-held-list *bpfr-d1*) (bpfr-replayed *bpfr-rows0*))
      (equal (fn-bpnf-held-list *bpfr-d2*) (bpfr-replayed *bpfr-rows1*))
      (equal (fn-bpnf-held-list *bpfr-d3*) (bpfr-replayed *bpfr-rows2*))
      (equal (fn-bpnf-held-list *bpfr-d4*) (bpfr-replayed *bpfr-rows3*))
      (equal (fn-bpnp-attempt-retries (bpfr-slot *bpfr-d1*)) 0)
      (equal (fn-bpnp-attempt-retries (bpfr-slot *bpfr-d2*)) 1)
      (equal (fn-bpnp-attempt-retries (bpfr-slot *bpfr-d3*)) 2)
      (equal (fn-bpnp-attempt-retries (bpfr-slot *bpfr-d4*)) 3)
      (equal (car (car (fn-bpnf-answer-effects *bpfr-d1-open*))) :persist-attempt)
      (equal (car (car (fn-bpnf-answer-effects *bpfr-d3-open*))) :persist-attempt)
      ;; Four restarts, four durable kind 8: stranded, not offered again.
      (equal (fn-bpnf-answer-effects *bpfr-d4-open*)
             (list (list :forward-stranded 0 *bpfr-dest* 3)))))
;; The :restart-ready hypothesis: the same durable rows under a fenced
;; clock-domain decision answer :restart-fault and install nothing.
(make-event
 `(defconst *bpfr-fenced*
    ',(fn-bpnp-step *bpfr-raw-s0*
                    (append (fn-bpnf-family-recover-auto-event
                             *bpfr-raw-s0* nil :ready *bpfr-rows3*)
                            (list '(:fence :test))))))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects *bpfr-fenced*))) :restart-fault))
(must-fail
 (assert-event
  (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpfr-fenced*))
         (bpfr-replayed *bpfr-rows3*))))

;; ---------------------------------------------------------------------
;; Teeth of the sender's refusal reading (books/bp-node-forward-retry.lisp).
;; fn-bpnp-tcpcl-outcome-keeps-the-refusal-reason: witness, reason 3
;; (Retransmission not acceptable); hypothesis dropped, no peer reason is
;; :failed, not a refusal result.
(assert-event (equal (fn-bpnp-tcpcl-outcome :refused 3) '(:refused 3)))
(assert-event (equal (fn-bpnp-tcpcl-outcome :refused nil) :failed))
(must-fail
 (assert-event (equal (fn-bpnp-tcpcl-outcome :refused nil) (list :refused nil))))
(assert-event (equal (fn-bpnp-tcpcl-outcome :accepted nil) :sent))
(assert-event (equal (fn-bpnp-tcpcl-outcome :uncertain nil) :uncertain))
(assert-event (equal (fn-bpnp-tcpcl-outcome :connection-failed nil) :uncertain))

(defun bpfr-result (st outcome session)
  (declare (xargs :guard t :verify-guards nil))
  (let ((effect (car (fn-bpnf-answer-effects *bpfr-p1*))))
    (fn-bpnp-step st (list :forward-result (fn-bpn-nth 3 effect) (fn-bpn-nth 4 effect)
                           session outcome *bpfr-obs*))))
(defconst *bpfr-p1-session* (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpfr-p1*))))
(make-event `(defconst *bpfr-refuse1*
               ',(bpfr-result *bpfr-s4* (fn-bpnp-tcpcl-outcome :refused 1) *bpfr-p1-session*)))
(make-event `(defconst *bpfr-refuse3*
               ',(bpfr-result *bpfr-s4* (fn-bpnp-tcpcl-outcome :refused 3) *bpfr-p1-session*)))
(make-event `(defconst *bpfr-refuse1-settled* ',(bpfr-durable *bpfr-refuse1*)))
(make-event `(defconst *bpfr-refuse3-settled* ',(bpfr-durable *bpfr-refuse3*)))
;; fn-bpnp-step-forward-result-records-the-transport-outcome: witness, the
;; kind-9 record of reason 3 carries (:refused 3); effect hypothesis dropped,
;; a stale session's answer is :forward-stale and records nothing.
(assert-event
 (let ((effect (car (fn-bpnf-answer-effects *bpfr-refuse3*))))
   (and (equal (car effect) :persist-forward-result)
        (equal (fn-bpn-nth 8 (fn-bpn-nth 3 effect)) '(:refused 3)))))
(make-event `(defconst *bpfr-stale*
               ',(bpfr-result *bpfr-s4* '(:refused 3) (cons 99 99))))
(assert-event (equal (car (car (fn-bpnf-answer-effects *bpfr-stale*))) :forward-stale))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 8 (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpfr-stale*))))
         '(:refused 3))))
;; fn-bpnp-completed-refusal-settles-as-sent: witness, reason 1 settles the
;; row exactly as the :sent settle above did (no hypothesis to drop).
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects *bpfr-refuse1-settled*))) :forward-ready)
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpfr-refuse1-settled*))
             (fn-bpnf-held-list (fn-bpnf-answer-state *bpfr-settled*)))
      (equal (fn-bpn-nth 12 (car (fn-bpnf-held-list
                                  (fn-bpnf-answer-state *bpfr-refuse1-settled*))))
             '(:dispatch-done))))
;; fn-bpnp-other-refusal-is-not-settled: witness, reason 3 leaves the row
;; forward pending with its attempt cleared; hypothesis dropped, reason 1 is
;; terminal.
(assert-event
 (let ((h (car (fn-bpnf-held-list (fn-bpnf-answer-state *bpfr-refuse3-settled*)))))
   (and (equal (fn-bpn-nth 12 h) '(:forward-pending))
        (null (fn-bpn-nth 13 h)))))
(must-fail
 (assert-event (not (fn-bpnp-forward-terminalp (fn-bpnp-tcpcl-outcome :refused 1)))))
