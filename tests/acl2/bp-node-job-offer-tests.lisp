; Teeth of books/bp-node-job-offer.lisp and books/bp-node-job-offer-progress.lisp
; (PRF-120).  Reachable states from the lower machine's own events: two base
; jobs queued for one peer, the older one routed on a hop the table no longer
; names (held :route-changed) or already offered on this contact.  The
; previous driver (fn-bpnp-contact-next) ends the contact there; the fair
; selection offers the younger job.  Then the named attempt: a stale result
; settles nothing, the current one records the transport outcome, only the
; durable :finished record reports :forwarded, and an encoder refusal
; settles the pending record.  One reachable witness per keystone and one
; hypothesis-removal witness per hypothesis.
(in-package "ACL2")
(include-book "../../books/bp-node-job-offer-progress")
(include-book "../../books/bp-node-receive-boundary")

(defconst *jo-local* (cons :dtn '(47 47 102 110 45 97 47)))   ; dtn://fn-a/
(defconst *jo-peer* (cons :dtn '(47 47 102 110 45 98 47)))    ; dtn://fn-b/
(defconst *jo-config* (fn-bpn-config *jo-local* 3600000 2 32 1048576))
(defconst *jo-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *jo-node* '(100 116 110 58 47 47 102 110 45 97 47))
(defconst *jo-table*
  (list (fn-bprt-route 100 "dtn://fn-b/" "relay" "dtn://relay/" 4556)))
(defconst *jo-old-table*
  (list (fn-bprt-route 100 "dtn://fn-b/" "relay" "dtn://relay/" 4557)))
(defconst *jo-route*
  (fn-bprt-job-route "dtn://fn-b/" *jo-table* *jo-node* 10 1024 1048576))
(defconst *jo-old-route*
  (fn-bprt-job-route "dtn://fn-b/" *jo-old-table* *jo-node* 10 1024 1048576))
(assert-event (not (equal *jo-route* *jo-old-route*)))

(defun jo-enqueue (work route sequence)
  (list :enqueue work '(97 49) 0 sequence route *jo-peer* '(104 105) *jo-obs*))

(defconst *jo-b0* (fn-bpn-initial-machine-state *jo-config* 4 1048576))
(defconst *jo-b1*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state
                 (fn-bpn-step *jo-b0* (jo-enqueue '(119 49) *jo-old-route* 7)))
                '(:persist-result 0 :durable))))
(defconst *jo-b2*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state
                 (fn-bpn-step *jo-b1* (jo-enqueue '(119 50) *jo-route* 8)))
                '(:persist-result 1 :durable))))
(defconst *jo-st* (fn-bpnf-with-base (fn-bpnf-initial-state *jo-config* 4 1048576)
                                     *jo-b2*))
(defconst *jo-jobs* (fn-bpn-machine-state-jobs *jo-b2*))
(defconst *jo-key1* (list '(119 49) '(97 49) 0))
(defconst *jo-key2* (list '(119 50) '(97 49) 0))
(defconst *jo-routing* (list :table *jo-table*))
(assert-event (and (true-listp *jo-st*)
                   (fn-bpn-machine-statep *jo-b2*)
                   (equal (len *jo-jobs*) 2)
                   (equal (fn-bpn-job-status (fn-bpn-find-job *jo-key1* *jo-jobs*)) :queued)
                   (equal (fn-bpn-job-status (fn-bpn-find-job *jo-key2* *jo-jobs*)) :queued)
                   (fn-bpnp-receipt-contact-event *jo-st* *jo-peer*)))

;; The starvation the fair selection removes.  The older job's durable route
;; is not the hop the table names now: the previous driver holds it and ends
;; the contact; the younger job is never offered.
(assert-event
 (equal (fn-bpnp-contact-next *jo-st* *jo-peer* *jo-routing* nil)
        (list :held *jo-key1* :route-changed)))
(assert-event
 (equal (car (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* nil)) :offer))
(assert-event
 (equal (cadr (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* nil))
        (list :contact-job *jo-peer* *jo-key2*)))
;; Without routing, an older job this contact already offered (a transfer
;; that was not accepted) ends the previous driver's contact; the fair one
;; offers the younger job.
(assert-event
 (equal (fn-bpnp-contact-next *jo-st* *jo-peer* nil (list *jo-key1*)) (list :close)))
(assert-event
 (equal (cadr (fn-bpnj-contact-next *jo-st* *jo-peer* nil (list *jo-key1*)))
        (list :contact-job *jo-peer* *jo-key2*)))

;; fn-bpnj-contact-offers-while-a-ready-job-remains.  Witness: gate open,
;; KEY2 ready; the answer is an offer.
(assert-event
 (and (fn-bpnp-receipt-contact-event *jo-st* *jo-peer*)
      (fn-bpnj-readyp (fn-bpn-find-job *jo-key2* *jo-jobs*) *jo-peer* *jo-routing* nil)
      (equal (car (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* nil)) :offer)))
;; Without readiness: KEY1 (held) is the only candidate once KEY2 is offered;
;; the gate holds, KEY1 is not ready, and the answer is :held.
(assert-event
 (and (fn-bpnp-receipt-contact-event *jo-st* *jo-peer*)
      (not (fn-bpnj-readyp (fn-bpn-find-job *jo-key1* *jo-jobs*) *jo-peer* *jo-routing*
                           (list *jo-key2*)))
      (equal (car (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* (list *jo-key2*)))
             :held)))
;; Without the gate: the base has a pending proposal (KEY2's :attempting
;; record, not yet answered).  KEY2's job is still queued and ready; the
;; answer is :close.
(defconst *jo-offer* (cadr (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* nil)))
(defconst *jo-a* (fn-bpnj-step *jo-st* *jo-offer*))
(defconst *jo-st-p* (fn-bpnf-answer-state *jo-a*))
(assert-event
 (and (not (fn-bpnp-receipt-contact-event *jo-st-p* *jo-peer*))
      (fn-bpnj-readyp (fn-bpn-find-job *jo-key2* (fn-bpn-machine-state-jobs
                                                  (fn-bpnf-base *jo-st-p*)))
                      *jo-peer* *jo-routing* nil)
      (equal (fn-bpnj-contact-next *jo-st-p* *jo-peer* *jo-routing* nil) (list :close))))

;; fn-bpnj-contact-offer-starts-the-ready-job: the step persists KEY2's
;; :attempting record, token 2, and owes the :cl-send on KEY2's route.
(assert-event
 (and (equal (fn-bpnf-answer-effects *jo-a*)
             (list (list :persist 2 (list :attempting 2 '(119 50) '(97 49) 0))))
      (equal (fn-bpn-pending-success-effects
              (fn-bpn-machine-state-pending (fn-bpnf-base *jo-st-p*)))
             (list (list :cl-send *jo-route* *jo-peer* *jo-key2*
                         (fn-bpn-job-wire (fn-bpn-find-job *jo-key2* *jo-jobs*)))))))
;; The same event without the gate (the pending state) answers nothing.
(assert-event (equal (fn-bpnf-answer-effects (fn-bpnj-step *jo-st-p* *jo-offer*)) nil))

;; The attempt becomes durable: its token is the record's, 2.
(defconst *jo-st-a*
  (fn-bpnf-answer-state (fn-bpnj-step *jo-st-p* '(:base (:persist-result 2 :durable)))))
(assert-event (equal (fn-bpnj-attempt-token *jo-st-a* *jo-key2*) 2))
(assert-event (equal (fn-bpn-machine-state-next-token (fn-bpnf-base *jo-st-a*)) 3))

;; fn-bpnj-stale-job-result-settles-nothing: a result naming another attempt
;; (token 1, an earlier record) settles nothing; the state is unchanged.
(assert-event
 (equal (fn-bpnj-step *jo-st-a* (list :job-result *jo-key2* 1 :accepted))
        (fn-bpnf-answer *jo-st-a* (list (list :job-result-stale *jo-key2* 1)))))
;; fn-bpnj-host-refuses-an-unnamed-transport-result: the host's event check
;; refuses a base transport result that names no attempt.
(assert-event
 (and (fn-bpnj-unnamed-result-p (list :base (list :forward-result *jo-key2* :accepted)))
      (not (fn-bpnj-host-eventp (list :base (list :forward-result *jo-key2* :accepted))))
      (fn-bpnj-host-eventp (list :job-result *jo-key2* 2 :accepted))))

;; fn-bpnj-named-result-is-the-transport-outcome, both arms.
(defconst *jo-acc* (fn-bpnj-step *jo-st-a* (list :job-result *jo-key2* 2 :accepted)))
(defconst *jo-ref* (fn-bpnj-step *jo-st-a* (list :job-result *jo-key2* 2 :refused)))
(assert-event
 (and (equal (fn-bpnf-answer-effects *jo-acc*)
             (list (list :persist 3 (list :finished 3 '(119 50) '(97 49) 0 :none :finished))))
      (equal (fn-bpn-pending-success-effects
              (fn-bpn-machine-state-pending (fn-bpnf-base (fn-bpnf-answer-state *jo-acc*))))
             (list (list :transport '(119 50) '(97 49) 0 :forwarded)))))
(assert-event
 (and (equal (fn-bpnf-answer-effects *jo-ref*)
             (list (list :persist 3 (list :requeued 3 '(119 50) '(97 49) 0 :refused :requeued))))
      (not (fn-bpnj-forwarded-transport-p
            (fn-bpn-pending-success-effects
             (fn-bpn-machine-state-pending (fn-bpnf-base (fn-bpnf-answer-state *jo-ref*))))))))
;; Without the matching attempt (token 2 named, but the job not attempting:
;; the queued state before the offer), the result settles nothing.
(assert-event
 (equal (fn-bpnf-answer-effects (fn-bpnj-step *jo-st* (list :job-result *jo-key2* 2 :accepted)))
        (list (list :job-result-stale *jo-key2* 2))))

;; fn-bpnj-step-forwarded-needs-a-durable-finished-record.  Witness: the
;; durable :finished record reports :forwarded.
(defconst *jo-st-f* (fn-bpnf-answer-state *jo-acc*))
(assert-event
 (fn-bpnj-forwarded-transport-p
  (fn-bpnf-answer-effects (fn-bpnj-step *jo-st-f* '(:base (:persist-result 3 :durable))))))
;; The same record answered :refused (an encoder refusal) reports nothing
;; forwarded, and fn-bpnj-encoder-refusal-settles-the-pending-record: the
;; pending record is gone, nothing fenced, the refusal effect answered.
(defconst *jo-enc* (fn-bpnj-step *jo-st-f* '(:base (:persist-result 3 :refused))))
(assert-event
 (and (not (fn-bpnj-forwarded-transport-p (fn-bpnf-answer-effects *jo-enc*)))
      (not (fn-bpn-machine-state-pending (fn-bpnf-base (fn-bpnf-answer-state *jo-enc*))))
      (not (fn-bpn-machine-state-fenced (fn-bpnf-base (fn-bpnf-answer-state *jo-enc*))))
      (equal (fn-bpnf-answer-effects *jo-enc*)
             (list (list :bundle-queue-refused '(119 50) '(97 49) 0
                         :result-persistence-refused)))))
;; An :uncertain answer to the same record is not a settlement: it fences.
(assert-event
 (fn-bpn-machine-state-fenced
  (fn-bpnf-base (fn-bpnf-answer-state
                 (fn-bpnj-step *jo-st-f* '(:base (:persist-result 3 :uncertain)))))))

;; fn-bpnj-contact-offers-a-ready-job-within-its-prefix.  Two asks at the
;; ready state, no routing: KEY1 then KEY2 are offered; with one ask KEY2 is
;; not (the prefix (KEY1 KEY2) has two unoffered keys).
(defconst *jo-prefix* (fn-bpnj-keys-through *jo-key2* *jo-jobs*))
(assert-event (equal *jo-prefix* (list *jo-key1* *jo-key2*)))
(assert-event
 (and (fn-bpnj-stays-ready-p (list *jo-st* *jo-st*) *jo-peer* nil *jo-key2* *jo-prefix*)
      (member-equal *jo-key2* (fn-bpnj-contact-offers (list *jo-st* *jo-st*) *jo-peer* nil nil))))
(assert-event
 (and (fn-bpnj-stays-ready-p (list *jo-st*) *jo-peer* nil *jo-key2* *jo-prefix*)
      (< (len (list *jo-st*)) (len (fn-bpnj-unoffered *jo-prefix* nil)))
      (not (member-equal *jo-key2*
                         (fn-bpnj-contact-offers (list *jo-st*) *jo-peer* nil nil)))))
;; Without readiness throughout: the second ask is at the pending state.
(assert-event
 (and (not (fn-bpnj-stays-ready-p (list *jo-st* *jo-st-p*) *jo-peer* nil *jo-key2* *jo-prefix*))
      (not (member-equal *jo-key2*
                         (fn-bpnj-contact-offers (list *jo-st* *jo-st-p*) *jo-peer* nil nil)))))
