; Teeth of the contact-time keystones of PRF-103 over the selection the host
; asks (host/native/bp-service.lisp fnn-bpc-drive-contact calls
; fn-bpnjc-contact-next, equal to fn-bpnj-contact-next by
; fn-bpnjc-contact-next-is-the-head-scan): a reachable queued base job, the
; routed offer the host drives through fn-bpnj-step, the held answers (no
; route, no live hop, route changed), a reachable contact in which the job's
; transfer is not accepted and the threaded OFFERED closes the contact
; instead of offering it again; one must-fail per hypothesis of
; fn-bpnj-contact-offer-is-the-routed-hop.  Then the teeth of
; fn-bpn-apply-record-keeps-forwarded (books/bp-node-contact-driver).
(in-package "ACL2")
(include-book "../../books/bp-node-job-offer")
(include-book "../../books/bp-node-receive-boundary")
(include-book "must-fail-checked")

(defconst *cd-local* (cons :dtn '(47 47 102 110 45 97 47)))   ; dtn://fn-a/
(defconst *cd-peer* (cons :dtn '(47 47 102 110 45 98 47)))    ; dtn://fn-b/
(defconst *cd-config* (fn-bpn-config *cd-local* 3600000 2 32 1048576))
(defconst *cd-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *cd-node* '(100 116 110 58 47 47 102 110 45 97 47))
; The route queue time chose: the routed hop's contact port 4556 on
; loopback, this node's session parameters (fn-bprt-job-route).
(defconst *cd-table*
  (list (fn-bprt-route 100 "dtn://fn-b/" "relay" "dtn://relay/" 4556)))
(defconst *cd-route*
  (fn-bprt-job-route "dtn://fn-b/" *cd-table* *cd-node* 10 1024 1048576))
(assert-event (equal *cd-route*
                     (list :route '(49 50 55 46 48 46 48 46 49) 4556
                           *cd-node* 10 1024 1048576)))
(defconst *cd-enqueue*
  (list :enqueue '(119 111 114 107 45 49) '(97 116 116 101 109 112 116 45 49)
        0 7 *cd-route* *cd-peer* '(104 101 108 108 111) *cd-obs*))

(defconst *cd-b0* (fn-bpn-initial-machine-state *cd-config* 4 1048576))
(defconst *cd-b1*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state (fn-bpn-step *cd-b0* *cd-enqueue*))
                '(:persist-result 0 :durable))))
(defconst *cd-init* (fn-bpnf-initial-state *cd-config* 4 1048576))
(defconst *cd-st* (fn-bpnf-with-base *cd-init* *cd-b1*))
(defconst *cd-jobs* (fn-bpn-machine-state-jobs *cd-b1*))
(defconst *cd-job* (car *cd-jobs*))
(defconst *cd-key* (fn-bpn-job-key *cd-job*))
(defconst *cd-token* (fn-bpn-machine-state-next-token *cd-b1*))
(assert-event (fn-bpn-machine-statep *cd-b1*))
(assert-event (equal (len *cd-jobs*) 1))
(assert-event (equal (fn-bpn-job-status *cd-job*) :queued))
(assert-event (equal (fn-bpaj-eid-text *cd-peer*) "dtn://fn-b/"))

(defun cd-next (st routing offered)
  (fn-bpnj-contact-next st *cd-peer* routing offered))

; The conclusion of fn-bpnj-contact-offer-is-the-routed-hop, literally, at
; ST, ROUTING, OFFERED and the table TABLE its decision is read against.
(defun cd-routed-offer-p (st routing table offered)
  (let* ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
         (job (fn-bpnj-select jobs jobs *cd-peer* routing offered))
         (d (cd-next st routing offered))
         (decision (fn-bprt-send-decision (fn-bpn-job-route job)
                                          (fn-bpaj-eid-text *cd-peer*) table)))
    (and (fn-bpnp-receipt-contact-event st *cd-peer*)
         job
         (equal (fn-bpn-job-status job) :queued)
         (equal (fn-bpn-job-peer job) *cd-peer*)
         (not (member-equal (fn-bpn-job-key job) offered))
         (equal (cadr d) (list :contact-job *cd-peer* (fn-bpn-job-key job)))
         (equal (caddr d) (cons (fn-bpn-job-key job) offered))
         (equal (fn-bpn-nth 0 decision) :send)
         (equal (fn-bpn-nth 1 decision) (fn-bpn-job-route job))
         (equal (cadddr d) (fn-bpn-nth 3 decision)))))
; Its hypotheses, literally.
(defun cd-routed-offer-hyps-p (st routing table offered)
  (and (equal (car (cd-next st routing offered)) :offer)
       (equal routing (list :table table))))

; Positive witness: both hypotheses hold and the whole conclusion holds.
; The answer names the job and the relay's EID; the host drives the event
; through fn-bpnj-step, which persists this job's :attempting record and
; owes the :cl-send on port 4556, the relay's contact.
(defconst *cd-routing* (list :table *cd-table*))
(defconst *cd-d* (cd-next *cd-st* *cd-routing* nil))
(assert-event (equal *cd-d* (list :offer (list :contact-job *cd-peer* *cd-key*)
                                  (list *cd-key*) "dtn://relay/")))
(assert-event (cd-routed-offer-hyps-p *cd-st* *cd-routing* *cd-table* nil))
(assert-event (cd-routed-offer-p *cd-st* *cd-routing* *cd-table* nil))
(defconst *cd-ans* (fn-bpnj-step *cd-st* (cadr *cd-d*)))
(assert-event
 (and (equal (fn-bpnf-answer-effects *cd-ans*)
             (list (list :persist *cd-token*
                         (list :attempting *cd-token* (nth 0 *cd-key*)
                               (nth 1 *cd-key*) (nth 2 *cd-key*)))))
      (equal (fn-bpn-pending-success-effects
              (fn-bpn-machine-state-pending
               (fn-bpnf-base (fn-bpnf-answer-state *cd-ans*))))
             (list (list :cl-send *cd-route* *cd-peer* *cd-key*
                         (fn-bpn-job-wire *cd-job*))))))

; Hypothesis (car d) = :offer removed (routing kept equal to (:table TABLE)):
; each table below holds the job, and the conclusion fails.
;   route removed: :no-route
(assert-event (equal (cd-next *cd-st* '(:table nil) nil) (list :held *cd-key* :no-route)))
(assert-event (not (cd-routed-offer-hyps-p *cd-st* '(:table nil) nil nil)))
(must-fail-checked (assert-event (cd-routed-offer-p *cd-st* '(:table nil) nil nil)))
;   a boundary with no contact row: :no-live-hop
(defconst *cd-dark*
  (list (fn-bprt-route 100 "dtn://fn-b/" "dark" "dtn://dark/" 0)))
(assert-event (equal (cd-next *cd-st* (list :table *cd-dark*) nil)
                     (list :held *cd-key* :no-live-hop)))
(must-fail-checked (assert-event (cd-routed-offer-p *cd-st* (list :table *cd-dark*) *cd-dark* nil)))
;   the table now prefers another boundary: the durable route (4556) is not
;   the hop the table names (4557), so the job is held, sent to neither
(defconst *cd-moved*
  (cons (fn-bprt-route 50 "dtn://fn-b/" "relay-2" "dtn://relay-2/" 4557)
        *cd-table*))
(assert-event (equal (cd-next *cd-st* (list :table *cd-moved*) nil)
                     (list :held *cd-key* :route-changed)))
(must-fail-checked (assert-event (cd-routed-offer-p *cd-st* (list :table *cd-moved*) *cd-moved* nil)))
;   another destination's route does not route this peer
(defconst *cd-other*
  (list (fn-bprt-route 100 "dtn://fn-c/" "relay" "dtn://relay/" 4556)))
(assert-event (equal (cd-next *cd-st* (list :table *cd-other*) nil)
                     (list :held *cd-key* :no-route)))
(must-fail-checked (assert-event (cd-routed-offer-p *cd-st* (list :table *cd-other*) *cd-other* nil)))

; Hypothesis routing = (:table TABLE) removed (the offer kept): without
; routing the selection offers the job with no hop; read against a table
; that routes this peer nowhere the decision is not :send, and read against
; *cd-table* the offer does not carry the relay's EID.
(defconst *cd-d-nil* (cd-next *cd-st* nil nil))
(assert-event (equal *cd-d-nil* (list :offer (list :contact-job *cd-peer* *cd-key*)
                                      (list *cd-key*) nil)))
(assert-event (not (equal nil (list :table nil))))
(must-fail-checked (assert-event (cd-routed-offer-p *cd-st* nil nil nil)))
(assert-event (not (equal nil (list :table *cd-table*))))
(must-fail-checked (assert-event (cd-routed-offer-p *cd-st* nil *cd-table* nil)))

; ---------------------------------------------------------------------
; fn-bpnj-contact-offers-each-job-at-most-once, on a reachable contact.  The
; offer's :attempting record is durable, the :cl-send ran, and the
; connection ended without an answer (:uncertain); the durable :requeued
; record makes the job :queued again.
(defconst *cd-s1* (fn-bpnf-answer-state *cd-ans*))
(defconst *cd-s2*
  (fn-bpnf-answer-state
   (fn-bpnj-step *cd-s1* (list :base (list :persist-result *cd-token* :durable)))))
(defconst *cd-att* (fn-bpnj-attempt-token *cd-s2* *cd-key*))
(assert-event (natp *cd-att*))
(defconst *cd-tok2* (fn-bpn-machine-state-next-token (fn-bpnf-base *cd-s2*)))
(defconst *cd-s3*
  (fn-bpnf-answer-state
   (fn-bpnj-step *cd-s2* (list :job-result *cd-key* *cd-att* :uncertain))))
(defconst *cd-s4*
  (fn-bpnf-answer-state
   (fn-bpnj-step *cd-s3* (list :base (list :persist-result *cd-tok2* :durable)))))
(defconst *cd-jobs4* (fn-bpn-machine-state-jobs (fn-bpnf-base *cd-s4*)))
(assert-event (equal (fn-bpn-job-status (fn-bpn-find-job *cd-key* *cd-jobs4*)) :queued))
; The host threads OFFERED: the second question of this contact closes it.
(assert-event (equal (cd-next *cd-s4* *cd-routing* (list *cd-key*)) (list :close)))
; The literal conclusion over the reachable contact: one offer, no
; duplicate, none offered before.
(defconst *cd-offers* (fn-bpnj-contact-offers (list *cd-st* *cd-s4*) *cd-peer* *cd-routing* nil))
(assert-event (equal *cd-offers* (list *cd-key*)))
(assert-event (and (no-duplicatesp-equal *cd-offers*)
                   (not (member-equal *cd-key* nil))))
; With OFFERED already naming the key the contact offers nothing.
(assert-event (equal (fn-bpnj-contact-offers (list *cd-s4*) *cd-peer* *cd-routing*
                                             (list *cd-key*))
                     nil))
; Mutation witness (not the keystone's sequence): a driver that does not
; thread OFFERED asks both states with OFFERED empty and offers the key
; twice, which the conclusion forbids.
(assert-event (equal (car (cd-next *cd-s4* *cd-routing* nil)) :offer))
(must-fail-checked
 (assert-event (no-duplicatesp-equal
                (list (car (caddr (cd-next *cd-st* *cd-routing* nil)))
                      (car (caddr (cd-next *cd-s4* *cd-routing* nil)))))))

; ---------------------------------------------------------------------
; fn-bpn-apply-record-keeps-forwarded: the accepted transfer makes the job
; :forwarded; applying a record for it (here its own :expired and
; :requeued, both inapplicable) keeps it :forwarded.
(defconst *cd-a3*
  (fn-bpnf-answer-state
   (fn-bpnj-step *cd-s2* (list :job-result *cd-key* *cd-att* :accepted))))
(defconst *cd-a4*
  (fn-bpnf-base
   (fn-bpnf-answer-state
    (fn-bpnj-step *cd-a3* (list :base (list :persist-result *cd-tok2* :durable))))))
(defconst *cd-tok3* (fn-bpn-machine-state-next-token *cd-a4*))
(assert-event (equal (fn-bpn-job-status
                      (fn-bpn-find-job *cd-key* (fn-bpn-machine-state-jobs *cd-a4*)))
                     :forwarded))
(defun cd-status-after (st record)
  (fn-bpn-job-status
   (fn-bpn-find-job *cd-key*
                    (fn-bpn-machine-state-jobs (fn-bpn-apply-record st record)))))
(assert-event (equal (cd-status-after
                      *cd-a4* (list :requeued *cd-tok3* (nth 0 *cd-key*) (nth 1 *cd-key*)
                                    (nth 2 *cd-key*) :failed :requeued))
                     :forwarded))
; Hypothesis: the job is :forwarded.  The same :requeued record applied to
; the :attempting job of *cd-s2* makes it :queued.
(must-fail-checked
 (assert-event (equal (cd-status-after
                       (fn-bpnf-base *cd-s2*)
                       (list :requeued *cd-tok2* (nth 0 *cd-key*) (nth 1 *cd-key*)
                             (nth 2 *cd-key*) :failed :requeued))
                      :forwarded)))
