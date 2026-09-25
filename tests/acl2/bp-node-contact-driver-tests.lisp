; Teeth of books/bp-node-contact-driver.lisp (PRF-103): a reachable queued
; base job, the routed offer the host drives through fn-bpnp-step, the held
; answers (no route, no live hop, route changed), a reachable contact in
; which the job's transfer is not accepted and the contact closes instead of
; offering it again, and one must-fail per hypothesis of each keystone.
(in-package "ACL2")
(include-book "../../books/bp-node-contact-driver")
(include-book "../../books/bp-node-receive-boundary")
(include-book "std/testing/must-fail" :dir :system)

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
(defconst *cd-job* (fn-bpnp-contact-job *cd-st* *cd-peer*))
(defconst *cd-key* (fn-bpn-job-key *cd-job*))
(defconst *cd-token* (fn-bpn-machine-state-next-token *cd-b1*))
(assert-event (fn-bpn-machine-statep *cd-b1*))
(assert-event (equal (fn-bpn-job-status *cd-job*) :queued))
(assert-event (equal (fn-bpaj-eid-text *cd-peer*) "dtn://fn-b/"))

(defun cd-next (st table offered)
  (fn-bpnp-contact-next st *cd-peer* (list :table table) offered))

; The conclusion of fn-bpnp-contact-offer-is-the-routed-hop at ST and TABLE.
(defun cd-routed-offer-p (st table offered)
  (let* ((d (cd-next st table offered))
         (base (fn-bpnf-base st))
         (job (fn-bpnp-contact-job st *cd-peer*))
         (key (fn-bpn-job-key job))
         (token (fn-bpn-machine-state-next-token base))
         (dest (fn-bpaj-eid-text *cd-peer*))
         (decision (fn-bprt-send-decision (fn-bpn-job-route job) dest table))
         (ans (fn-bpnp-step st (cadr d)))
         (pending (fn-bpn-machine-state-pending
                   (fn-bpnf-base (fn-bpnf-answer-state ans)))))
    (and (equal (fn-bpnf-answer-effects ans)
                (list (list :persist token
                            (list :attempting token (nth 0 key)
                                  (nth 1 key) (nth 2 key)))))
         (equal (fn-bpn-pending-success-effects pending)
                (list (list :cl-send (fn-bpn-job-route job) *cd-peer* key
                            (fn-bpn-job-wire job))))
         (equal (car decision) :send)
         (equal (fn-bpn-job-route job) (cadr decision))
         (equal (caddr decision)
                (fn-bprt-next-hop dest table (fn-bprt-contactable table)))
         (equal (cadddr d) (cadddr decision)))))

; Witness: the routed offer.  The driver answers the contact event with the
; relay's EID; the step persists this job's :attempting record and owes the
; :cl-send on port 4556, the relay's contact.
(defconst *cd-d* (cd-next *cd-st* *cd-table* nil))
(assert-event (equal *cd-d* (list :offer (list :base (list :contact *cd-peer* t))
                                  (list *cd-key*) "dtn://relay/")))
(assert-event (cd-routed-offer-p *cd-st* *cd-table* nil))

; Hypothesis (car d) = :offer.  Route removed: the driver holds the job
; (:no-route), drives nothing, and the conclusion fails.
(assert-event (equal (cd-next *cd-st* nil nil) (list :held *cd-key* :no-route)))
(must-fail (assert-event (cd-routed-offer-p *cd-st* nil nil)))
; A boundary with no contact row: held, no live hop.
(defconst *cd-dark*
  (list (fn-bprt-route 100 "dtn://fn-b/" "dark" "dtn://dark/" 0)))
(assert-event (equal (cd-next *cd-st* *cd-dark* nil)
                     (list :held *cd-key* :no-live-hop)))
(must-fail (assert-event (cd-routed-offer-p *cd-st* *cd-dark* nil)))
; The table now prefers another boundary: the job's durable route (4556) is
; not the hop the table names (4557), so it is held, never sent to either.
(defconst *cd-moved*
  (cons (fn-bprt-route 50 "dtn://fn-b/" "relay-2" "dtn://relay-2/" 4557)
        *cd-table*))
(assert-event (equal (cd-next *cd-st* *cd-moved* nil)
                     (list :held *cd-key* :route-changed)))
(must-fail (assert-event (cd-routed-offer-p *cd-st* *cd-moved* nil)))
; Another destination's route does not route this peer.
(defconst *cd-other*
  (list (fn-bprt-route 100 "dtn://fn-c/" "relay" "dtn://relay/" 4556)))
(assert-event (equal (cd-next *cd-st* *cd-other* nil)
                     (list :held *cd-key* :no-route)))
; Hypothesis: token below the journal bound.  At the bound the driver still
; offers, and the step answers the refusal, not the :attempting record.
(defconst *cd-full*
  (fn-bpnf-with-base *cd-init*
                     (fn-bpn-state-with *cd-b1* (fn-bpn-machine-state-jobs *cd-b1*)
                                        (fn-bpn-machine-state-contacts *cd-b1*)
                                        nil nil *fn-bpn-machine-max-records*)))
(assert-event (equal (car (cd-next *cd-full* *cd-table* nil)) :offer))
(must-fail (assert-event (cd-routed-offer-p *cd-full* *cd-table* nil)))
; Hypothesis: a well-formed base.  A malformed base with the same queued
; job: the driver offers, and the logical step answers nothing.
(defconst *cd-malformed*
  (fn-bpnf-with-base *cd-init*
                     (fn-bpn-make-machine-state
                      nil (fn-bpn-machine-state-jobs *cd-b1*)
                      nil nil nil *cd-token* 4 1048576)))
(assert-event (not (fn-bpn-machine-statep (fn-bpnf-base *cd-malformed*))))
(assert-event (equal (car (cd-next *cd-malformed* *cd-table* nil)) :offer))
(must-fail (assert-event (with-guard-checking
                          :none (cd-routed-offer-p *cd-malformed* *cd-table* nil))))

; ---------------------------------------------------------------------
; Once per contact, on a reachable contact.  The offer's :attempting record
; is durable, the :cl-send ran, and the connection ended without an answer
; (:uncertain); the durable :requeued record makes the job :queued again.
(defconst *cd-s1* (fn-bpnf-answer-state (fn-bpnp-step *cd-st* (cadr *cd-d*))))
(defconst *cd-s2*
  (fn-bpnf-answer-state
   (fn-bpnp-step *cd-s1* (list :base (list :persist-result *cd-token* :durable)))))
(defconst *cd-tok2* (fn-bpn-machine-state-next-token (fn-bpnf-base *cd-s2*)))
(defconst *cd-s3*
  (fn-bpnf-answer-state
   (fn-bpnp-step *cd-s2* (list :base (list :forward-result *cd-key* :uncertain)))))
(defconst *cd-s4*
  (fn-bpnf-answer-state
   (fn-bpnp-step *cd-s3* (list :base (list :persist-result *cd-tok2* :durable)))))
(assert-event (equal (fn-bpn-job-status (fn-bpnp-contact-job *cd-s4* *cd-peer*))
                     :queued))
(assert-event (equal (fn-bpn-job-key (fn-bpnp-contact-job *cd-s4* *cd-peer*))
                     *cd-key*))
; The host threads OFFERED: the second question of this contact closes it.
(assert-event (equal (cd-next *cd-s4* *cd-table* (list *cd-key*)) (list :close)))
(assert-event (equal (fn-bpnp-contact-offers (list *cd-st* *cd-s4*) *cd-peer*
                                             (list :table *cd-table*) nil)
                     (list *cd-key*)))
; Without the threaded OFFERED the same state is offered again: the key
; would appear twice in the contact.
(must-fail (assert-event (equal (car (cd-next *cd-s4* *cd-table* nil)) :close)))
; The next contact (OFFERED empty again) offers it: it stays owed.
(assert-event (equal (car (cd-next *cd-s4* *cd-table* nil)) :offer))

; ---------------------------------------------------------------------
; fn-bpnp-contact-closes-only-when-nothing-owed-remains: witness *cd-s4*
; closing with the job in OFFERED; one state per hypothesis where the
; driver closes (or answers otherwise) and the job is not in OFFERED.
(defun cd-closes-with-key-offered-p (st offered)
  (let ((d (cd-next st *cd-table* offered)))
    (implies (and (not (equal (car d) :offer)) (not (equal (car d) :held)))
             (member-equal (fn-bpn-job-key (fn-bpnp-contact-job st *cd-peer*))
                           offered))))
(assert-event (cd-closes-with-key-offered-p *cd-s4* (list *cd-key*)))
;   nothing issued
(defconst *cd-issued* (fn-bpnf-with-issued *cd-s4* '(0 0 0 :deferral nil :pending)))
(must-fail (assert-event (cd-closes-with-key-offered-p *cd-issued* nil)))
;   no delivery uncertain
(defconst *cd-delivery* (update-nth 7 '(:delivery-uncertain 0) *cd-s4*))
(must-fail (assert-event (cd-closes-with-key-offered-p *cd-delivery* nil)))
;   base not fenced
(defconst *cd-fenced*
  (fn-bpnf-with-base *cd-init*
                     (fn-bpn-state-with (fn-bpnf-base *cd-s4*)
                                        (fn-bpn-machine-state-jobs (fn-bpnf-base *cd-s4*))
                                        nil nil t *cd-tok2*)))
(must-fail (assert-event (cd-closes-with-key-offered-p *cd-fenced* nil)))
;   base not pending: the state the offer leaves while its record is in flight
(must-fail (assert-event (cd-closes-with-key-offered-p *cd-s1* nil)))
;   peer is an EID
(must-fail
 (assert-event
  (let ((d (fn-bpnp-contact-next *cd-st* "dtn://fn-b/" (list :table *cd-table*) nil)))
    (implies (not (member (car d) '(:offer :held)))
             (member-equal (fn-bpn-job-key
                            (fn-bpnp-contact-job *cd-st* "dtn://fn-b/"))
                           nil)))))
; (A peer with no queued job closes with nothing owed: the job hypothesis.)
(assert-event (equal (fn-bpnp-contact-next *cd-st* *cd-local* (list :table *cd-table*) nil)
                     (list :close)))
(assert-event (null (fn-bpnp-contact-job *cd-st* *cd-local*)))

; ---------------------------------------------------------------------
; fn-bpn-apply-record-keeps-forwarded: the accepted transfer makes the job
; :forwarded; applying a record for it (here its own :expired and
; :requeued, both inapplicable) keeps it :forwarded.
(defconst *cd-a3*
  (fn-bpnf-answer-state
   (fn-bpnp-step *cd-s2* (list :base (list :forward-result *cd-key* :accepted)))))
(defconst *cd-a4*
  (fn-bpnf-base
   (fn-bpnf-answer-state
    (fn-bpnp-step *cd-a3* (list :base (list :persist-result *cd-tok2* :durable))))))
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
(must-fail
 (assert-event (equal (cd-status-after
                       (fn-bpnf-base *cd-s2*)
                       (list :requeued *cd-tok2* (nth 0 *cd-key*) (nth 1 *cd-key*)
                             (nth 2 *cd-key*) :failed :requeued))
                      :forwarded)))
