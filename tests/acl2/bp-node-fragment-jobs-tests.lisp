; Teeth for books/bp-node-fragment-jobs (PRF-121, item 3): the fragment
; family's rows and the job table agree, and kind-18 replacement consumes
; carriers only.
(in-package "ACL2")
(include-book "../../books/bp-node-fragment-jobs")
(include-book "bp-node-fragment-replacement-tests")
(include-book "bp-node-fragment-step-tests")
(include-book "std/testing/must-fail" :dir :system)

; Reachable positive witness: the plan fixture's held list (two fragments of
; one family, a fragment of another, and a non-fragment row) satisfies the
; relation; the family applies, consuming both fragments, each of which
; carried only the reassembly job; the whole row carries (:dispatch-pending)
; and the new held list satisfies the relation.
(assert-event (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list *bpnff-state*)))
(assert-event (equal (car *bpnfr-applied*) :ready))
(assert-event (equal (len (cadddr *bpnfr-applied*)) 2))
(assert-event
 (and (fn-bpnf-rows-job-onlyp (cadddr *bpnfr-applied*))
      (fn-bpnf-reassembly-job-onlyp (caddr *bpnfr-applied*))
      (fn-bpnf-family-jobs-agreep (cadr *bpnfr-applied*))))

; Hypothesis removal, the relation.  The same family with its offset-zero
; fragment carrying an unfinished forwarding job (kind-8 attempt in slot 13,
; next hop, (:forward-pending)).  The relation fails, the replacement still
; applies (it does not look at jobs), and the conclusion fails: the consumed
; rows include one whose forwarding job the replacement would erase.  The
; relation is what carries the guarantee.
(defconst *bpnfj-forwarding-p0*
  (update-nth 13 '(:attempt 3 0 1)
              (update-nth 12 '(:forward-pending)
                          (update-nth 11 '(:dtn "relay") *bpnff-p0*))))
(defun bpnfj-replace (new old xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (if (equal (car xs) old) new (car xs))
            (bpnfj-replace new old (cdr xs)))
    nil))
(defconst *bpnfj-forwarding-state*
  (fn-bpnf-state-with-arrival
   (fn-bpnf-base *bpnff-state*)
   (bpnfj-replace *bpnfj-forwarding-p0* *bpnff-p0*
               (fn-bpnf-held-list *bpnff-state*))
   nil nil nil nil nil 3 0 (fn-bpnf-next-arrival *bpnff-state*)))
(defconst *bpnfj-forwarding-applied*
  (fn-bpnf-family-apply *bpnfj-forwarding-state* *bpnfr-record* 7))
(assert-event (member-equal *bpnfj-forwarding-p0*
                            (fn-bpnf-held-list *bpnfj-forwarding-state*)))
(assert-event (not (fn-bpnf-family-jobs-agreep
                    (fn-bpnf-held-list *bpnfj-forwarding-state*))))
(assert-event (equal (car *bpnfj-forwarding-applied*) :ready))
(assert-event (member-equal *bpnfj-forwarding-p0*
                            (cadddr *bpnfj-forwarding-applied*)))
(assert-event (not (fn-bpnf-rows-job-onlyp
                    (cadddr *bpnfj-forwarding-applied*))))
(must-fail
 (assert-event (fn-bpnf-rows-job-onlyp (cadddr *bpnfj-forwarding-applied*))))

; Hypothesis removal, :ready.  A refused application (the anchor's arrival
; is not the record's) keeps the relation on the input but has no whole row
; carrying a job.
(defconst *bpnfj-fault* (fn-bpnf-family-apply *bpnff-state* *bpnfr-record* 8))
(assert-event (not (equal (car *bpnfj-fault*) :ready)))
(assert-event (not (fn-bpnf-reassembly-job-onlyp (caddr *bpnfj-fault*))))

;; The served state carries the credit counters recovery installs: USED,
;; one per received FNBS final (here the fixture's held rows), and DEBT, the
;; cold fn-bpnd-debt projection.  Without them the step refuses on credit.
(defun bpnfj-served (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-with-credit
   st (len (fn-bpnf-held-list st))
   (fn-bpnd-debt st (fn-bpn-config-node-id
                     (fn-bpn-machine-state-config (fn-bpnf-base st))))))
; The host-called step on the fragment-progress path: fn-bpnp-step on
; (:family 0 OBS) proposes kind 18 and keeps the held list; on the durable
; (:persist-result 3 0 :durable) it installs the replacement.  Both states
; satisfy the relation.
(defun bpnfj-proposal ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-step (bpnfj-served *bpnff-state*) (list :family 0 *bpnfs-live-observation*)))
(assert-event (equal (car (car (fn-bpnf-answer-effects (bpnfj-proposal))))
                     :persist-family))
(assert-event (fn-bpnf-family-issuedp (fn-bpnf-answer-state (bpnfj-proposal))))
(defun bpnfj-durable ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-step (fn-bpnf-answer-state (bpnfj-proposal))
                '(:persist-result 3 0 :durable)))
(assert-event (equal (car (car (fn-bpnf-answer-effects (bpnfj-durable))))
                     :family-ready))
(assert-event
 (and (fn-bpnf-family-jobs-agreep
       (fn-bpnf-held-list (fn-bpnf-answer-state (bpnfj-proposal))))
      (fn-bpnf-family-jobs-agreep
       (fn-bpnf-held-list (fn-bpnf-answer-state (bpnfj-durable))))
      (not (member-equal *bpnff-p0*
                         (fn-bpnf-held-list
                          (fn-bpnf-answer-state (bpnfj-durable)))))))
; Without the relation the served step installs a replacement that consumed
; the forwarding row.
(defun bpnfj-forwarding-durable ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-step
   (fn-bpnf-answer-state
    (fn-bpnp-step (bpnfj-served *bpnfj-forwarding-state*)
                  (list :family 0 *bpnfs-live-observation*)))
   '(:persist-result 3 0 :durable)))
(assert-event (equal (car (car (fn-bpnf-answer-effects
                                (bpnfj-forwarding-durable))))
                     :family-ready))
(assert-event (not (member-equal *bpnfj-forwarding-p0*
                                 (fn-bpnf-held-list
                                  (fn-bpnf-answer-state
                                   (bpnfj-forwarding-durable))))))
