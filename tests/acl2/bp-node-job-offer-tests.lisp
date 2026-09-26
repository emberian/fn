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

;; -----------------------------------------------------------------------------
;; PRF-139 part 2: the single traversal (fn-bpnj-scan) is the two lookup scans.

(defconst *jo-j1* (fn-bpn-find-job *jo-key1* *jo-jobs*))
(defconst *jo-j2* (fn-bpn-find-job *jo-key2* *jo-jobs*))
;; A job carrying J's key with other bytes: never in a machine state (its
;; jobs satisfy fn-bpn-job-listp), used only for the corrupted-list witnesses.
(defun jo-twin (j)
  (fn-bpn-make-job (fn-bpn-job-work-id j) (fn-bpn-job-attempt-id j)
                   (fn-bpn-job-generation j) (fn-bpn-job-sequence j)
                   (fn-bpn-job-age-anchor j) (fn-bpn-job-peer j) (fn-bpn-job-route j)
                   (fn-bpn-job-bundle j) (append (fn-bpn-job-wire j) '(0))
                   (fn-bpn-job-status j) (fn-bpn-job-last-token j)))
(defconst *jo-j1t* (jo-twin *jo-j1*))
(defconst *jo-j2t* (jo-twin *jo-j2*))
(assert-event (and (equal (fn-bpn-job-key *jo-j1t*) *jo-key1*)
                   (equal (fn-bpn-job-key *jo-j2t*) *jo-key2*)
                   (not (equal *jo-j1t* *jo-j1*)) (not (equal *jo-j2t* *jo-j2*))
                   (fn-bpn-job-listp *jo-jobs*)
                   (not (fn-bpn-job-listp (list *jo-j2* *jo-j2t*)))))

;; KEYSTONE fn-bpnj-contact-next-is-the-two-scan-selection (no hypothesis):
;; reachable witnesses, each answer kind.  Held head, younger ready: :offer
;; of KEY2; KEY2 offered: :held KEY1; the pending state: :close.
(defun jo-two-scan (st peer routing offered)
  (let* ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
         (job (fn-bpnj-select jobs jobs peer routing offered))
         (held (fn-bpnj-held jobs jobs peer routing offered)))
    (cond ((not (fn-bpnp-receipt-contact-event st peer)) (list :close))
          (job (list :offer (list :contact-job peer (fn-bpn-job-key job))
                     (cons (fn-bpn-job-key job) offered)
                     (fn-bpn-nth 1 (fn-bpnj-offerable job peer routing))))
          (held (list :held (fn-bpn-job-key held)
                      (fn-bpn-nth 1 (fn-bpnj-offerable held peer routing))))
          (t (list :close)))))
(assert-event
 (and (equal (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* nil)
             (jo-two-scan *jo-st* *jo-peer* *jo-routing* nil))
      (equal (cadr (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* nil))
             (list :contact-job *jo-peer* *jo-key2*))
      (equal (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* (list *jo-key2*))
             (jo-two-scan *jo-st* *jo-peer* *jo-routing* (list *jo-key2*)))
      (equal (car (fn-bpnj-contact-next *jo-st* *jo-peer* *jo-routing* (list *jo-key2*)))
             :held)
      (equal (fn-bpnj-contact-next *jo-st-p* *jo-peer* *jo-routing* nil)
             (jo-two-scan *jo-st-p* *jo-peer* *jo-routing* nil))))

;; fn-bpnj-scan-finds-the-selected-job.  Witness: PRE = (KEY1's held job),
;; REST = (KEY2's ready job); PRE selects nothing; the scan's ready job is
;; KEY2's, as the lookup scan's.
(assert-event
 (and (equal *jo-jobs* (append (list *jo-j1*) (list *jo-j2*)))
      (not (fn-bpnj-select (list *jo-j1*) *jo-jobs* *jo-peer* *jo-routing* nil))
      (equal (car (fn-bpnj-scan (list *jo-j2*) *jo-jobs* *jo-peer* *jo-routing* nil nil))
             (fn-bpnj-select (list *jo-j2*) *jo-jobs* *jo-peer* *jo-routing* nil))
      (equal (car (fn-bpnj-scan (list *jo-j2*) *jo-jobs* *jo-peer* *jo-routing* nil nil))
             *jo-j2*)))
;; Without JOBS = PRE ++ REST (corrupted list): REST holds KEY2's twin, which
;; is not the entry the lookup reads; the lookup scan answers KEY2's job, the
;; scan nothing.  PRE (empty) selects nothing.
(assert-event
 (and (not (equal *jo-jobs* (append nil (list *jo-j2t*))))
      (not (fn-bpnj-select nil *jo-jobs* *jo-peer* *jo-routing* nil))
      (equal (fn-bpnj-select (list *jo-j2t*) *jo-jobs* *jo-peer* *jo-routing* nil) *jo-j2*)
      (not (equal (car (fn-bpnj-scan (list *jo-j2t*) *jo-jobs* *jo-peer* *jo-routing* nil nil))
                  (fn-bpnj-select (list *jo-j2t*) *jo-jobs* *jo-peer* *jo-routing* nil)))))
;; Without PRE selecting nothing (corrupted list, KEY2 twice): PRE's KEY2 job
;; is ready and shadows REST's twin.
(assert-event
 (let ((jobs (list *jo-j2* *jo-j2t*)))
   (and (equal jobs (append (list *jo-j2*) (list *jo-j2t*)))
        (fn-bpnj-select (list *jo-j2*) jobs *jo-peer* *jo-routing* nil)
        (not (equal (car (fn-bpnj-scan (list *jo-j2t*) jobs *jo-peer* *jo-routing* nil nil))
                    (fn-bpnj-select (list *jo-j2t*) jobs *jo-peer* *jo-routing* nil))))))

;; fn-bpnj-scan-finds-the-held-job.  Witness: KEY2 offered, PRE = (KEY1's
;; held job), HELD = that job, REST = (KEY2's job); nothing is ready; the
;; scan keeps KEY1's job.  And from PRE empty: the scan finds KEY1's job.
(assert-event
 (and (not (fn-bpnj-select *jo-jobs* *jo-jobs* *jo-peer* *jo-routing* (list *jo-key2*)))
      (equal (fn-bpnj-held (list *jo-j1*) *jo-jobs* *jo-peer* *jo-routing* (list *jo-key2*))
             *jo-j1*)
      (equal (cdr (fn-bpnj-scan (list *jo-j2*) *jo-jobs* *jo-peer* *jo-routing*
                                (list *jo-key2*) *jo-j1*))
             (or *jo-j1* (fn-bpnj-held (list *jo-j2*) *jo-jobs* *jo-peer* *jo-routing*
                                       (list *jo-key2*))))
      (equal (cdr (fn-bpnj-scan *jo-jobs* *jo-jobs* *jo-peer* *jo-routing* (list *jo-key2*) nil))
             *jo-j1*)))
;; Without JOBS = PRE ++ REST (corrupted): REST = (KEY1's twin); the lookup
;; scan answers KEY1's job, the scan nothing.  Nothing is ready; HELD is
;; PRE's (empty) held job.
(assert-event
 (and (not (equal *jo-jobs* (append nil (list *jo-j1t*))))
      (not (fn-bpnj-select *jo-jobs* *jo-jobs* *jo-peer* *jo-routing* (list *jo-key2*)))
      (equal nil (fn-bpnj-held nil *jo-jobs* *jo-peer* *jo-routing* (list *jo-key2*)))
      (not (equal (cdr (fn-bpnj-scan (list *jo-j1t*) *jo-jobs* *jo-peer* *jo-routing*
                                     (list *jo-key2*) nil))
                  (or nil (fn-bpnj-held (list *jo-j1t*) *jo-jobs* *jo-peer* *jo-routing*
                                        (list *jo-key2*)))))))
;; Without nothing ready (a list with KEY2 ahead of KEY1): the scan stops at
;; KEY2's ready job before reaching KEY1's held one.
(assert-event
 (let ((jobs (list *jo-j2* *jo-j1*)))
   (and (equal jobs (append nil jobs))
        (fn-bpnj-select jobs jobs *jo-peer* *jo-routing* nil)
        (equal nil (fn-bpnj-held nil jobs *jo-peer* *jo-routing* nil))
        (not (equal (cdr (fn-bpnj-scan jobs jobs *jo-peer* *jo-routing* nil nil))
                    (or nil (fn-bpnj-held jobs jobs *jo-peer* *jo-routing* nil)))))))
;; Without HELD = PRE's held job (corrupted, KEY1 twice): PRE's KEY1 job is
;; held, HELD is nil; the lookup scan answers PRE's job through the shadowed
;; twin, the scan nothing.
(assert-event
 (let ((jobs (list *jo-j1* *jo-j1t*)))
   (and (equal jobs (append (list *jo-j1*) (list *jo-j1t*)))
        (not (fn-bpnj-select jobs jobs *jo-peer* *jo-routing* (list *jo-key2*)))
        (not (equal nil (fn-bpnj-held (list *jo-j1*) jobs *jo-peer* *jo-routing* (list *jo-key2*))))
        (not (equal (cdr (fn-bpnj-scan (list *jo-j1t*) jobs *jo-peer* *jo-routing* (list *jo-key2*) nil))
                    (or nil (fn-bpnj-held (list *jo-j1t*) jobs *jo-peer* *jo-routing*
                                          (list *jo-key2*))))))))

;; fn-bpnj-unique-keys-make-every-job-its-own-entry.  Witness: the reachable
;; list; both jobs are their own entries.  Without unique keys: KEY2's twin
;; is a member but not its own entry.  Without membership: the twin against
;; the reachable list.
(assert-event
 (and (fn-bpn-job-listp *jo-jobs*)
      (fn-bpnj-own-entryp *jo-j1* *jo-jobs*) (fn-bpnj-own-entryp *jo-j2* *jo-jobs*)))
(assert-event
 (let ((jobs (list *jo-j2* *jo-j2t*)))
   (and (not (fn-bpn-job-listp jobs)) (member-equal *jo-j2t* jobs)
        (not (fn-bpnj-own-entryp *jo-j2t* jobs)))))
(assert-event
 (and (fn-bpn-job-listp *jo-jobs*) (not (member-equal *jo-j2t* *jo-jobs*))
      (not (fn-bpnj-own-entryp *jo-j2t* *jo-jobs*))))
