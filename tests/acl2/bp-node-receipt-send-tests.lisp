; Teeth of books/bp-node-receipt-send.lisp: a reachable queued base job, the
; contact event `bp-node serve' asks for (fnn-bpnode-send-receipts), and one
; separating state per conjunct of fn-bpnp-receipt-contact-event-needs-a-
; queued-job and per hypothesis of fn-bpnp-receipt-contact-offers-the-queued-job.
(in-package "ACL2")
(include-book "../../books/bp-node-receipt-send")
(include-book "../../books/bp-node-receive-boundary")
(include-book "std/testing/must-fail" :dir :system)

(defconst *rs-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *rs-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *rs-config* (fn-bpn-config *rs-local* 3600000 2 32 1048576))
(defconst *rs-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *rs-route*
  (list :route '(49 50 55 46 48 46 48 46 49) 4556
        '(100 116 110 58 47 47 102 110 45 97 47) 10 1024 1048576))
(defconst *rs-enqueue*
  (list :enqueue '(119 111 114 107 45 49) '(97 116 116 101 109 112 116 45 49)
        0 7 *rs-route* *rs-peer* '(104 101 108 108 111) *rs-obs*))

; The owed job, queued and durable, in the node's base machine.
(defconst *rs-b0* (fn-bpn-initial-machine-state *rs-config* 4 1048576))
(defconst *rs-b1*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state (fn-bpn-step *rs-b0* *rs-enqueue*))
                '(:persist-result 0 :durable))))
(defconst *rs-init* (fn-bpnf-initial-state *rs-config* 4 1048576))
(defconst *rs-st* (fn-bpnf-with-base *rs-init* *rs-b1*))
(defconst *rs-job* (fn-bpn-find-queued-for-peer
                    *rs-peer* (fn-bpn-machine-state-jobs *rs-b1*)))
(assert-event (fn-bpn-machine-statep *rs-b1*))
(assert-event (equal (fn-bpn-job-status *rs-job*) :queued))

; Witness (both keystones): the event is the contact, the step's one
; effect persists the :attempting record for this job, and the pending
; success effect is the job's :cl-send on its route.
(defconst *rs-event* (fn-bpnp-receipt-contact-event *rs-st* *rs-peer*))
(assert-event (equal *rs-event* (list :contact *rs-peer* t)))
(defconst *rs-ans* (fn-bpnp-step *rs-st* (list :base *rs-event*)))
(defconst *rs-key* (fn-bpn-job-key *rs-job*))
(defconst *rs-token* (fn-bpn-machine-state-next-token *rs-b1*))
(assert-event (equal (fn-bpnf-answer-effects *rs-ans*)
                     (list (list :persist *rs-token*
                                 (list :attempting *rs-token* (nth 0 *rs-key*)
                                       (nth 1 *rs-key*) (nth 2 *rs-key*))))))
(defconst *rs-pending*
  (fn-bpn-machine-state-pending (fn-bpnf-base (fn-bpnf-answer-state *rs-ans*))))
(assert-event (equal (fn-bpn-pending-success-effects *rs-pending*)
                     (list (list :cl-send *rs-route* *rs-peer* *rs-key*
                                 (fn-bpn-job-wire *rs-job*)))))

; One separating state per conjunct of the event's iff.
;   peer is an EID
(assert-event (null (fn-bpnp-receipt-contact-event *rs-st* "dtn://fn-b/")))
;   nothing issued
(assert-event (null (fn-bpnp-receipt-contact-event
                     (fn-bpnf-with-issued *rs-st* '(0 0 0 :deferral nil :pending))
                     *rs-peer*)))
;   no delivery uncertain (the delivery marker, fn-bpnf-waits, slot 7)
(assert-event (null (fn-bpnp-receipt-contact-event
                     (update-nth 7 '(:delivery-uncertain 0) *rs-st*)
                     *rs-peer*)))
;   base not fenced (the same queued job, fenced)
(defconst *rs-fenced*
  (fn-bpnf-with-base *rs-init*
                     (fn-bpn-state-with *rs-b1* (fn-bpn-machine-state-jobs *rs-b1*)
                                        (fn-bpn-machine-state-contacts *rs-b1*)
                                        nil t *rs-token*)))
(assert-event (fn-bpn-find-queued-for-peer
               *rs-peer* (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-fenced*))))
(assert-event (null (fn-bpnp-receipt-contact-event *rs-fenced* *rs-peer*)))
;   base not pending: the state the offer leaves while its record is in flight
(defconst *rs-in-flight* (fn-bpnf-answer-state *rs-ans*))
(assert-event (null (fn-bpnp-receipt-contact-event *rs-in-flight* *rs-peer*)))
;   a queued job for the peer: another peer has none
(assert-event (null (fn-bpnp-receipt-contact-event *rs-st* *rs-local*)))

; Once the :attempting record is durable the job is no longer :queued, so
; the node's next pass does not offer it again (the step half of "once per
; contact"; the loop half is the host's, see the record).
(defconst *rs-after*
  (fn-bpnf-answer-state
   (fn-bpnp-step *rs-in-flight*
                 (list :base (list :persist-result *rs-token* :durable)))))
(assert-event (not (equal (fn-bpn-job-status
                           (fn-bpn-find-job *rs-key*
                                            (fn-bpn-machine-state-jobs
                                             (fn-bpnf-base *rs-after*))))
                          :queued)))
(assert-event (null (fn-bpnp-receipt-contact-event *rs-after* *rs-peer*)))

; Hypothesis "the event is non-nil": without it the conclusion's
; (equal event (:contact peer t)) fails.
(must-fail
 (assert-event (equal (fn-bpnp-receipt-contact-event *rs-st* *rs-local*)
                      (list :contact *rs-local* t))))
; Hypothesis "token below the journal bound": at the bound the same event
; answers the refusal, not the :persist of the :attempting record.
(defconst *rs-full*
  (fn-bpnf-with-base *rs-init*
                     (fn-bpn-state-with *rs-b1* (fn-bpn-machine-state-jobs *rs-b1*)
                                        (fn-bpn-machine-state-contacts *rs-b1*)
                                        nil nil *fn-bpn-machine-max-records*)))
(assert-event (equal (fn-bpnp-receipt-contact-event *rs-full* *rs-peer*)
                     (list :contact *rs-peer* t)))
(must-fail
 (assert-event (equal (car (car (fn-bpnf-answer-effects
                                 (fn-bpnp-step *rs-full*
                                               (list :base (list :contact *rs-peer* t))))))
                      :persist)))
