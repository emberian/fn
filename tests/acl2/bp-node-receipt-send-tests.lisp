; Teeth of books/bp-node-receipt-send.lisp: a reachable queued base job, the
; contact event `bp-node serve' asks for (fnn-bpnode-send-receipts), and one
; separating state per conjunct of fn-bpnp-receipt-contact-event-needs-a-
; queued-job and per hypothesis of fn-bpnp-receipt-contact-offers-the-queued-job,
; fn-bpnp-uncertain-receipt-transfer-keeps-the-job-owed and
; fn-bpnp-receipt-reoffer-after-uncertain.
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

; ---------------------------------------------------------------------
; Teeth of fn-bpnp-uncertain-receipt-transfer-keeps-the-job-owed and
; fn-bpnp-receipt-reoffer-after-uncertain (spec bp-node-machine 4.3.2).
; The reachable state is *rs-after*: the job's :attempting record is
; durable, its :cl-send ran, and the connection ended without an answer.
(defconst *rs-attempting-job*
  (fn-bpn-find-job *rs-key* (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-after*))))
(assert-event (equal (fn-bpn-job-status *rs-attempting-job*) :attempting))
(assert-event (fn-bpn-lifecycle-invariantp (fn-bpnf-base *rs-after*)))
(defconst *rs-tok2* (fn-bpn-machine-state-next-token (fn-bpnf-base *rs-after*)))

; The step's answer to an uncertain transfer of KEY on state ST owes the job:
; its one effect persists the :requeued record naming the transfer :uncertain.
(defun rs-owes-requeue-p (st key)
  (let ((tok (fn-bpn-machine-state-next-token (fn-bpnf-base st))))
    (equal (fn-bpnf-answer-effects
            (fn-bpnp-step st (list :base (list :forward-result key :uncertain))))
           (list (list :persist tok
                       (list :requeued tok (nth 0 key) (nth 1 key) (nth 2 key)
                             :uncertain :requeued))))))

; Witness of keystone (d).
(defconst *rs-u*
  (fn-bpnf-answer-state
   (fn-bpnp-step *rs-after* (list :base (list :forward-result *rs-key* :uncertain)))))
(assert-event (rs-owes-requeue-p *rs-after* *rs-key*))
(assert-event (equal (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-u*))
                     (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-after*))))
(assert-event (not (fn-bpn-machine-state-fenced (fn-bpnf-base *rs-u*))))
(assert-event (null (fn-bpnf-issued *rs-u*)))
(assert-event (not (fn-bpah-delivery-uncertainp *rs-u*)))
(defconst *rs-requeue-success*
  (list (list :transport (nth 0 *rs-key*) (nth 1 *rs-key*) (nth 2 *rs-key*) :attempted)
        (list :forward-refused (nth 0 *rs-key*) (nth 1 *rs-key*) (nth 2 *rs-key*)
              :uncertain)))
(assert-event (equal (fn-bpn-pending-success-effects
                      (fn-bpn-machine-state-pending (fn-bpnf-base *rs-u*)))
                     *rs-requeue-success*))

; Witness of keystone (e): the durable :requeued record queues the same job
; again, and the next contact offers it by its own identity.
(defconst *rs-r-ans*
  (fn-bpnp-step *rs-u* (list :base (list :persist-result *rs-tok2* :durable))))
(defconst *rs-r* (fn-bpnf-answer-state *rs-r-ans*))
(assert-event (equal (fn-bpnf-answer-effects *rs-r-ans*) *rs-requeue-success*))
(assert-event (equal (fn-bpn-find-job *rs-key* (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-r*)))
                     (fn-bpn-job-with-status *rs-attempting-job* :queued *rs-tok2*)))
(assert-event (equal (fn-bpn-job-wire
                      (fn-bpn-find-job *rs-key* (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-r*))))
                     (fn-bpn-job-wire *rs-job*)))
(assert-event (equal (fn-bpnp-receipt-contact-event *rs-r* *rs-peer*)
                     (list :contact *rs-peer* t)))
(defconst *rs-tok3* (fn-bpn-machine-state-next-token (fn-bpnf-base *rs-r*)))
(assert-event (equal (fn-bpnf-answer-effects
                      (fn-bpnp-step *rs-r* (list :base (list :contact *rs-peer* t))))
                     (list (list :persist *rs-tok3*
                                 (list :attempting *rs-tok3* (nth 0 *rs-key*)
                                       (nth 1 *rs-key*) (nth 2 *rs-key*))))))

; One must-fail per hypothesis of keystone (d); each separating state is
; *rs-after* with only that hypothesis falsified, and the positive assert
; beside it shows the step answered (no requeue owed), not that it errored.
;   nothing issued
(defconst *rs-x-issued* (fn-bpnf-with-issued *rs-after* '(0 0 0 :deferral nil :pending)))
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnp-step *rs-x-issued*
                                   (list :base (list :forward-result *rs-key* :uncertain))))))
(must-fail (assert-event (rs-owes-requeue-p *rs-x-issued* *rs-key*)))
;   no delivery uncertain
(defconst *rs-x-delivery* (update-nth 7 '(:delivery-uncertain 0) *rs-after*))
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnp-step *rs-x-delivery*
                                   (list :base (list :forward-result *rs-key* :uncertain))))))
(must-fail (assert-event (rs-owes-requeue-p *rs-x-delivery* *rs-key*)))
;   base not fenced
(defconst *rs-x-fenced*
  (fn-bpnf-with-base *rs-after*
                     (fn-bpn-state-with (fn-bpnf-base *rs-after*)
                                        (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-after*))
                                        (fn-bpn-machine-state-contacts (fn-bpnf-base *rs-after*))
                                        nil t *rs-tok2*)))
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnp-step *rs-x-fenced*
                                   (list :base (list :forward-result *rs-key* :uncertain))))))
(must-fail (assert-event (rs-owes-requeue-p *rs-x-fenced* *rs-key*)))
;   base not pending: the requeue itself in flight
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnp-step *rs-u*
                                   (list :base (list :forward-result *rs-key* :uncertain))))))
(must-fail (assert-event (rs-owes-requeue-p *rs-u* *rs-key*)))
;   a job with that key
(defconst *rs-x-key* (list '(119 111 114 107 45 50) (nth 1 *rs-key*) (nth 2 *rs-key*)))
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnp-step *rs-after*
                                   (list :base (list :forward-result *rs-x-key* :uncertain))))))
(must-fail (assert-event (rs-owes-requeue-p *rs-after* *rs-x-key*)))
;   the job is :attempting: the same job still :queued (before its contact)
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnp-step *rs-st*
                                   (list :base (list :forward-result *rs-key* :uncertain))))))
(must-fail (assert-event (rs-owes-requeue-p *rs-st* *rs-key*)))
;   token below the journal bound: at the bound the answer is the refusal
(defconst *rs-x-full*
  (fn-bpnf-with-base *rs-after*
                     (fn-bpn-state-with (fn-bpnf-base *rs-after*)
                                        (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-after*))
                                        (fn-bpn-machine-state-contacts (fn-bpnf-base *rs-after*))
                                        nil nil *fn-bpn-machine-max-records*)))
(assert-event (equal (car (car (fn-bpnf-answer-effects
                                (fn-bpnp-step *rs-x-full*
                                              (list :base (list :forward-result *rs-key* :uncertain))))))
                     :bundle-queue-refused))
(must-fail (assert-event (rs-owes-requeue-p *rs-x-full* *rs-key*)))
;   the machine state (keystone d) and the lifecycle invariant (keystone e):
;   a base whose configuration is not one.  The step's guard excludes it,
;   so these evaluate the logical definition with guard checking off: the
;   logical step answers nothing, and the job is never offered again.
(defconst *rs-x-malformed*
  (fn-bpnf-with-base *rs-after*
                     (fn-bpn-make-machine-state
                      nil (fn-bpn-machine-state-jobs (fn-bpnf-base *rs-after*))
                      nil nil nil *rs-tok2* 4 1048576)))
(assert-event (not (fn-bpn-machine-statep (fn-bpnf-base *rs-x-malformed*))))
(assert-event (null (with-guard-checking
                     :none
                     (fn-bpnf-answer-effects
                      (fn-bpnp-step *rs-x-malformed*
                                    (list :base (list :forward-result *rs-key*
                                                      :uncertain)))))))
(must-fail (assert-event (with-guard-checking
                          :none (rs-owes-requeue-p *rs-x-malformed* *rs-key*))))
(defun rs-reoffered-p (st key peer)
  (let* ((tok (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
         (s1 (fn-bpnf-answer-state
              (fn-bpnp-step st (list :base (list :forward-result key :uncertain)))))
         (s2 (fn-bpnf-answer-state
              (fn-bpnp-step s1 (list :base (list :persist-result tok :durable))))))
    (equal (fn-bpnp-receipt-contact-event s2 peer) (list :contact peer t))))
(assert-event (rs-reoffered-p *rs-after* *rs-key* *rs-peer*))
(must-fail (assert-event (with-guard-checking
                          :none (rs-reoffered-p *rs-x-malformed* *rs-key* *rs-peer*))))
; Keystone (e) under the other hypotheses (issued, uncertain delivery,
; fenced, not :attempting): the job is never queued again by the pair.
(must-fail (assert-event (rs-reoffered-p *rs-x-issued* *rs-key* *rs-peer*)))
(must-fail (assert-event (rs-reoffered-p *rs-x-delivery* *rs-key* *rs-peer*)))
(must-fail (assert-event (rs-reoffered-p *rs-x-fenced* *rs-key* *rs-peer*)))
(must-fail (assert-event (rs-reoffered-p *rs-x-full* *rs-key* *rs-peer*)))
