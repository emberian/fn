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
