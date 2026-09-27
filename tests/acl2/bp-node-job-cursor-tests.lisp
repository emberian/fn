; Teeth of books/bp-node-job-cursor.lisp (PRF-226).  Reachable states from
; the lower machine's own events (the states of bp-node-job-offer-tests):
; two base jobs queued for one peer, the older one held by routing
; (:route-changed), the younger ready.  The contact's cursor offers the
; younger job, carries the held one, and after the offer's own records (the
; durable :attempting, the accepted transfer, the durable :finished) answers
; the held job without re-reading the list; the head scan answers the same
; at every ask.  One reachable witness per keystone, one hypothesis-removal
; witness per hypothesis.
(in-package "ACL2")
(include-book "../../books/bp-node-job-cursor")
(include-book "../../books/bp-node-receive-boundary")
(include-book "std/testing/must-fail" :dir :system)

(defconst *jc-local* (cons :dtn '(47 47 102 110 45 97 47)))   ; dtn://fn-a/
(defconst *jc-peer* (cons :dtn '(47 47 102 110 45 98 47)))    ; dtn://fn-b/
(defconst *jc-other* (cons :dtn '(47 47 102 110 45 99 47)))   ; dtn://fn-c/
(defconst *jc-config* (fn-bpn-config *jc-local* 3600000 2 32 1048576))
(defconst *jc-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *jc-node* '(100 116 110 58 47 47 102 110 45 97 47))
(defconst *jc-table*
  (list (fn-bprt-route 100 "dtn://fn-b/" "relay" "dtn://relay/" 4556)))
(defconst *jc-old-table*
  (list (fn-bprt-route 100 "dtn://fn-b/" "relay" "dtn://relay/" 4557)))
(defconst *jc-route*
  (fn-bprt-job-route "dtn://fn-b/" *jc-table* *jc-node* 10 1024 1048576))
(defconst *jc-old-route*
  (fn-bprt-job-route "dtn://fn-b/" *jc-old-table* *jc-node* 10 1024 1048576))

(defun jc-enqueue (work route sequence)
  (list :enqueue work '(97 49) 0 sequence route *jc-peer* '(104 105) *jc-obs*))

(defconst *jc-b0* (fn-bpn-initial-machine-state *jc-config* 4 1048576))
(defconst *jc-b1*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state
                 (fn-bpn-step *jc-b0* (jc-enqueue '(119 49) *jc-old-route* 7)))
                '(:persist-result 0 :durable))))
(defconst *jc-b2*
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state
                 (fn-bpn-step *jc-b1* (jc-enqueue '(119 50) *jc-route* 8)))
                '(:persist-result 1 :durable))))
(defconst *jc-st* (fn-bpnf-with-base (fn-bpnf-initial-state *jc-config* 4 1048576) *jc-b2*))
(defconst *jc-jobs* (fn-bpn-machine-state-jobs *jc-b2*))
(defconst *jc-key1* (list '(119 49) '(97 49) 0))
(defconst *jc-key2* (list '(119 50) '(97 49) 0))
(defconst *jc-job1* (fn-bpn-find-job *jc-key1* *jc-jobs*))
(defconst *jc-routing* (list :table *jc-table*))

;; The offer's own events: the durable :attempting record, the accepted
;; transfer naming its token, the durable :finished record.
(defconst *jc-st-done*
  (let* ((p (fn-bpnf-answer-state
             (fn-bpnj-step *jc-st* (list :contact-job *jc-peer* *jc-key2*))))
         (a (fn-bpnf-answer-state (fn-bpnj-step p '(:base (:persist-result 2 :durable)))))
         (f (fn-bpnf-answer-state (fn-bpnj-step a (list :job-result *jc-key2* 2 :accepted)))))
    (fn-bpnf-answer-state (fn-bpnj-step f '(:base (:persist-result 3 :durable))))))
(assert-event
 (and (equal (fn-bpn-job-status (fn-bpn-find-job *jc-key2* (fn-bpn-machine-state-jobs
                                                            (fn-bpnf-base *jc-st-done*))))
             :forwarded)
      (fn-bpnp-receipt-contact-event *jc-st-done* *jc-peer*)
      (fn-bpnjc-gatep *jc-st-done* *jc-peer*)))

;; ---------------------------------------------------------------------
;; fn-bpnjc-open-establishes-the-relation: an empty table names frontier 0,
;; a frontier of every job list; the opening cursor (0 0 nil) is related.
(defconst *jc-c0* (fn-bpnjc-contact-cursor nil *jc-peer*))
(assert-event
 (and (equal *jc-c0* '(0 0 nil))
      (fn-bpnjc-frontierp *jc-jobs* *jc-peer* (fn-bpnjc-frontier-of nil *jc-peer*))
      (fn-bpn-job-listp *jc-jobs*)
      (fn-bpnjc-contact-relp *jc-st* *jc-peer* *jc-routing* nil *jc-c0*)))
;; Without the frontier: a table naming 1 for the peer, whose first job is
;; queued for it (held), is not a frontier, and the cursor it opens is not
;; related (its prefix holds a held job the cursor does not carry).
(defconst *jc-bad-table* (list (cons *jc-peer* 1)))
(assert-event
 (and (fn-bpn-job-listp *jc-jobs*)
      (not (fn-bpnjc-frontierp *jc-jobs* *jc-peer* (fn-bpnjc-frontier-of *jc-bad-table* *jc-peer*)))
      (not (fn-bpnjc-contact-relp *jc-st* *jc-peer* *jc-routing* nil
                                  (fn-bpnjc-contact-cursor *jc-bad-table* *jc-peer*)))))

;; ---------------------------------------------------------------------
;; fn-bpnjc-contact-next-is-the-head-scan.  Witness: the first ask offers
;; KEY2 (the head scan's answer), advances the cursor to 2 and carries JOB1
;; as held.
(defconst *jc-r1* (fn-bpnjc-contact-next *jc-st* *jc-peer* *jc-routing* nil *jc-c0*))
(assert-event
 (and (fn-bpnjc-contact-relp *jc-st* *jc-peer* *jc-routing* nil *jc-c0*)
      (equal (car *jc-r1*)
             (list :offer (list :contact-job *jc-peer* *jc-key2*) (list *jc-key2*)
                   (fn-bpn-nth 1 (fn-bpnj-offerable (fn-bpn-find-job *jc-key2* *jc-jobs*)
                                                    *jc-peer* *jc-routing*))))
      (equal (car *jc-r1*) (fn-bpnj-contact-next *jc-st* *jc-peer* *jc-routing* nil))
      (equal (cdr *jc-r1*) (list 0 2 *jc-job1*))))
;; fn-bpnjc-offer-keeps-the-relation: the answer's cursor and OFFERED.
(assert-event
 (fn-bpnjc-contact-relp *jc-st* *jc-peer* *jc-routing* (list *jc-key2*) (cdr *jc-r1*)))
;; Hypothesis removal: the cursor (0 2 nil) with nothing offered is not
;; related (KEY2, ahead of it, is ready), and its answer (:close) is not the
;; head scan's (the offer of KEY2).
(assert-event
 (and (not (fn-bpnjc-contact-relp *jc-st* *jc-peer* *jc-routing* nil '(0 2 nil)))
      (equal (car (fn-bpnjc-contact-next *jc-st* *jc-peer* *jc-routing* nil '(0 2 nil)))
             '(:close))
      (not (equal (car (fn-bpnjc-contact-next *jc-st* *jc-peer* *jc-routing* nil '(0 2 nil)))
                  (fn-bpnj-contact-next *jc-st* *jc-peer* *jc-routing* nil)))))
(must-fail
 (thm (equal (car (fn-bpnjc-contact-next *jc-st* *jc-peer* *jc-routing* nil '(0 2 nil)))
             (fn-bpnj-contact-next *jc-st* *jc-peer* *jc-routing* nil))))

;; ---------------------------------------------------------------------
;; fn-bpnjc-drain-is-the-head-drain and fn-bpnjc-drain-visits-are-linear.
;; Witness: the contact asks at *jc-st* (offer KEY2), the offer's records
;; run, and it asks at *jc-st-done*: the cursor answers :held KEY1 from its
;; carried HELD without re-reading the two jobs; the head drain is the same;
;; the drain examined 2 positions, the job list's length.
(defconst *jc-sts* (list *jc-st* *jc-st-done*))
(assert-event
 (and (fn-bpnjc-contact-relp (car *jc-sts*) *jc-peer* *jc-routing* nil *jc-c0*)
      (fn-bpnjc-evolving-p *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*)
      (equal (fn-bpnjc-drain *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*)
             (fn-bpnjc-head-drain *jc-sts* *jc-peer* *jc-routing* nil))
      (equal (len (fn-bpnjc-drain *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*)) 2)
      (equal (car (cadr (fn-bpnjc-drain *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*))) :held)
      (equal (cadr (cadr (fn-bpnjc-drain *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*))) *jc-key1*)
      (equal (fn-bpnjc-drain-visits *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*) 2)
      (equal (len (fn-bpnjc-drain-last-jobs *jc-sts* *jc-peer* *jc-routing* nil *jc-c0*)) 2)))
;; Hypothesis removal (evolution): the machine replaces JOB1 ahead of the
;; cursor with a job of the same key on the table's route (ready, never
;; offered): not an evolution the relation survives; the cursor answers the
;; stale held job where the head scan offers KEY1.
(defconst *jc-job1-rerouted*
  (fn-bpn-make-job (fn-bpn-job-work-id *jc-job1*) (fn-bpn-job-attempt-id *jc-job1*)
                   (fn-bpn-job-generation *jc-job1*) (fn-bpn-job-sequence *jc-job1*)
                   (fn-bpn-job-age-anchor *jc-job1*) (fn-bpn-job-peer *jc-job1*)
                   *jc-route* (fn-bpn-job-bundle *jc-job1*) (fn-bpn-job-wire *jc-job1*)
                   (fn-bpn-job-status *jc-job1*) (fn-bpn-job-last-token *jc-job1*)))
(defconst *jc-st-bad*
  (let ((base (fn-bpnf-base *jc-st-done*)))
    (fn-bpnf-with-base
     *jc-st-done*
     (fn-bpn-state-with base
                        (fn-bpn-replace-job *jc-key1* *jc-job1-rerouted*
                                            (fn-bpn-machine-state-jobs base))
                        (fn-bpn-machine-state-contacts base)
                        (fn-bpn-machine-state-pending base)
                        (fn-bpn-machine-state-fenced base)
                        (fn-bpn-machine-state-next-token base)))))
(defconst *jc-sts-bad* (list *jc-st* *jc-st-bad*))
(assert-event
 (and (fn-bpnjc-contact-relp (car *jc-sts-bad*) *jc-peer* *jc-routing* nil *jc-c0*)
      (not (fn-bpnjc-evolving-p *jc-sts-bad* *jc-peer* *jc-routing* nil *jc-c0*))
      (not (equal (fn-bpnjc-drain *jc-sts-bad* *jc-peer* *jc-routing* nil *jc-c0*)
                  (fn-bpnjc-head-drain *jc-sts-bad* *jc-peer* *jc-routing* nil)))
      (equal (car (cadr (fn-bpnjc-head-drain *jc-sts-bad* *jc-peer* *jc-routing* nil))) :offer)))
;; Hypothesis removal (the relation at the first ask): the cursor (0 2 nil)
;; with the evolution intact still drains differently from the head scan.
(assert-event
 (and (not (fn-bpnjc-contact-relp (car *jc-sts*) *jc-peer* *jc-routing* nil '(0 2 nil)))
      (not (equal (fn-bpnjc-drain *jc-sts* *jc-peer* *jc-routing* nil '(0 2 nil))
                  (fn-bpnjc-head-drain *jc-sts* *jc-peer* *jc-routing* nil)))))

;; ---------------------------------------------------------------------
;; The frontier: the close advances another peer's frontier over the two
;; jobs (both settled for it) up to the contact's position, and the machine's
;; lifecycle record keeps it; for the peer itself the queued (held) JOB1
;; keeps the frontier at 0.
(defconst *jc-closed* (fn-bpnjc-contact-close nil *jc-st-done* *jc-other* '(0 2 nil)))
(assert-event
 (and (equal (fn-bpnjc-frontier-of *jc-closed* *jc-other*) 2)
      (fn-bpnjc-frontierp (fn-bpn-machine-state-jobs (fn-bpnf-base *jc-st-done*)) *jc-other* 2)
      (equal (fn-bpnjc-frontier-of
              (fn-bpnjc-contact-close nil *jc-st-done* *jc-peer* '(0 2 nil)) *jc-peer*)
             0)
      (fn-bpnjc-contact-relp *jc-st-done* *jc-other* *jc-routing* nil
                             (fn-bpnjc-contact-cursor *jc-closed* *jc-other*))))
;; Without the frontier's bound (the close's cursor ignored), 2 is not a
;; frontier for the peer: JOB1 is queued for it.
(assert-event
 (not (fn-bpnjc-frontierp (fn-bpn-machine-state-jobs (fn-bpnf-base *jc-st-done*)) *jc-peer* 2)))
