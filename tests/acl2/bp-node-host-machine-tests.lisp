(in-package "ACL2")
(include-book "../../books/bp-node-host-machine")
(include-book "bp-node-machine-authorization-tests")
(include-book "must-fail-checked")

; The queued job of the authorization fixture: fn-bpn-step (the function the
; host calls) enqueued the obligation *bpna-key* = (work attempt 0) and, after the durable persist, queued it in
; *bpna-s-queued*.
(defconst *bpnhm-job*
  (fn-bpn-find-job *bpna-key* (fn-bpn-machine-state-jobs *bpna-s-queued*)))
(defconst *bpnhm-answer*
  (fn-bpn-host-existing-sequence *bpna-s-queued* *bpna-work* *bpna-attempt* 0))

; KEYSTONE teeth (PRF-1031,
; fn-bpn-host-existing-sequence-reuses-exactly-the-keyed-jobs-sequence): the
; positive witness with its complete antecedent by name, then the value; then
; an unqueued key (another generation), a malformed key and a state that is
; not a machine state answer :absent, which the recognizer refuses.
(assert-event
 (and (fn-bpn-machine-statep *bpna-s-queued*)
      (fn-bpn-keyp *bpna-key*)
      *bpnhm-job*
      (fn-bpp-timep (fn-bpn-job-sequence *bpnhm-job*))
      (fn-bpn-host-existing-sequence-p *bpnhm-answer*)
      (equal (fn-bpn-host-existing-sequence-value *bpnhm-answer*)
             (fn-bpn-job-sequence *bpnhm-job*))))
(assert-event
 (and (null (fn-bpn-find-job (list *bpna-work* *bpna-attempt* 1)
                             (fn-bpn-machine-state-jobs *bpna-s-queued*)))
      (equal (fn-bpn-host-existing-sequence
              *bpna-s-queued* *bpna-work* *bpna-attempt* 1)
             '(:absent))
      (not (fn-bpn-host-existing-sequence-p '(:absent)))
      (null (fn-bpn-host-existing-sequence-value '(:absent)))))
(assert-event
 (and (not (fn-bpn-keyp (list *bpna-work* :not-text 0)))
      (equal (fn-bpn-host-existing-sequence
              *bpna-s-queued* *bpna-work* :not-text 0)
             '(:absent))))
(assert-event
 (and (not (fn-bpn-machine-statep '(:corrupt)))
      (equal (fn-bpn-host-existing-sequence
              '(:corrupt) *bpna-work* *bpna-attempt* 0)
             '(:absent))))
(must-fail-checked
 (assert-event
  (fn-bpn-host-existing-sequence-p
   (fn-bpn-host-existing-sequence
    *bpna-s-queued* *bpna-work* *bpna-attempt* 1))))

; KEYSTONE teeth (PRF-1046,
; fn-bpn-host-lifecycle-recovery-agrees-with-the-replayed-machine).  The
; positive witness with its complete antecedent by name: the initial machine
; *bpna-s0* (its invariant holds, frontier 0); the observed namespace (a
; hidden stage, then the names of tokens 0 and 1) recovered over the records
; the machine persisted (*bpna-r0*, *bpna-r1*) is :ready; the replay of those
; records into *bpna-s0* is :ready.  Then the host's agreement is t and both
; frontiers are 2, the record count.
(defconst *bpnhm-names*
  (list ".interrupted-stage"
        (fn-bpn-lifecycle-record-name 0) (fn-bpn-lifecycle-record-name 1)))
(defconst *bpnhm-records* (list *bpna-r0* *bpna-r1*))
(defconst *bpnhm-recovery*
  (fn-bpn-lifecycle-recovery *bpnhm-names* *bpnhm-records*))
(defconst *bpnhm-replay* (fn-bpn-replay-records *bpna-s0* *bpnhm-records*))
(assert-event
 (and (fn-bpn-machine-invariantp *bpna-s0*)
      (equal (fn-bpn-machine-state-next-token *bpna-s0*) 0)
      (equal (car *bpnhm-recovery*) :ready)
      (equal (car *bpnhm-replay*) :ready)
      (consp *bpnhm-records*)
      (equal (fn-bpn-host-lifecycle-recovery-agrees-p
              *bpnhm-recovery* (nth 1 *bpnhm-replay*))
             t)
      (equal (fn-bpn-lifecycle-recovery-next-token *bpnhm-recovery*) 2)
      (equal (fn-bpn-machine-state-next-token (nth 1 *bpnhm-replay*)) 2)))

;; Tooth, hypothesis "the machine's frontier is 0": the machine that already
;; applied the first record (*bpna-s-queued*: invariant, frontier 1) with an
;; empty namespace and no records; the recovery is :ready (frontier 0), the
;; replay of nothing is :ready, and the host's agreement is nil.
(assert-event
 (and (fn-bpn-machine-invariantp *bpna-s-queued*)
      (equal (fn-bpn-machine-state-next-token *bpna-s-queued*) 1)
      (equal (car (fn-bpn-lifecycle-recovery nil nil)) :ready)
      (equal (car (fn-bpn-replay-records *bpna-s-queued* nil)) :ready)))
(must-fail-checked
 (assert-event
  (equal (fn-bpn-host-lifecycle-recovery-agrees-p
          (fn-bpn-lifecycle-recovery nil nil)
          (nth 1 (fn-bpn-replay-records *bpna-s-queued* nil)))
         t)))

;; Tooth, hypothesis "the recovery is :ready": a namespace with a gap (token
;; 0's name, then token 2's) over the same records is :fault, the machine and
;; the replay as in the witness; the agreement is nil.
(defconst *bpnhm-gap-recovery*
  (fn-bpn-lifecycle-recovery
   (list (fn-bpn-lifecycle-record-name 0) (fn-bpn-lifecycle-record-name 2))
   *bpnhm-records*))
(assert-event
 (and (fn-bpn-machine-invariantp *bpna-s0*)
      (equal (fn-bpn-machine-state-next-token *bpna-s0*) 0)
      (equal (car *bpnhm-gap-recovery*) :fault)
      (equal (car *bpnhm-replay*) :ready)))
(must-fail-checked
 (assert-event
  (equal (fn-bpn-host-lifecycle-recovery-agrees-p
          *bpnhm-gap-recovery* (nth 1 *bpnhm-replay*))
         t)))

;; Tooth, hypothesis "the replay is :ready": an initial machine whose octet
;; capacity (1) admits no queued job (invariant, frontier 0) refuses the first
;; record, so the replay is :fault and returns the machine at frontier 0; the
;; recovery is :ready as in the witness; the agreement is nil.
(defconst *bpnhm-tiny* (fn-bpn-initial-machine-state *bpna-config* 4 1))
(defconst *bpnhm-tiny-replay*
  (fn-bpn-replay-records *bpnhm-tiny* *bpnhm-records*))
(assert-event
 (and (fn-bpn-machine-invariantp *bpnhm-tiny*)
      (equal (fn-bpn-machine-state-next-token *bpnhm-tiny*) 0)
      (equal (car *bpnhm-recovery*) :ready)
      (equal (car *bpnhm-tiny-replay*) :fault)))
(must-fail-checked
 (assert-event
  (equal (fn-bpn-host-lifecycle-recovery-agrees-p
          *bpnhm-recovery* (nth 1 *bpnhm-tiny-replay*))
         t)))
