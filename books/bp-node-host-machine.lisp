; The native BP service's existing-sequence reuse, in a certified book (was
; host/bp-node-machine-host.lisp's): the host asks whether a job with the
; obligation key (work attempt generation) already holds a creation
; sequence, and reuses it instead of reserving a new one
; (host/native/bp-obligation.lisp, host/native/bp-node.lisp).  Guard-verified
; shims over fn-bpn-existing-sequence (bp-node-machine, guards in
; bp-node-machine-guards), with the keystone.
(in-package "ACL2")
(include-book "bp-node-machine-guards")

(defun fn-bpn-host-existing-sequence (st work attempt generation)
  (declare (xargs :guard t))
  (if (fn-bpn-machine-statep st)
      (fn-bpn-existing-sequence st (list work attempt generation))
    (list :absent)))

(defun fn-bpn-host-existing-sequence-p (answer)
  (declare (xargs :guard t))
  (and (fn-bpn-existing-sequencep answer) t))

(defun fn-bpn-host-existing-sequence-value (answer)
  (declare (xargs :guard t))
  (if (fn-bpn-existing-sequencep answer) (nth 1 answer) nil))

; KEYSTONE.  Two-sided: the host sees an existing sequence exactly when the
; state is a machine state, the key is a well-formed obligation key, a job
; with that key is queued and its sequence is a creation time; then the value
; the host reuses is that job's sequence; otherwise the answer is :absent
; (or, for a queued job whose sequence is not a time, an :existing answer the
; recognizer refuses).  No sequence is invented for an unqueued obligation.
(defthm fn-bpn-host-existing-sequence-reuses-exactly-the-keyed-jobs-sequence
  (let* ((key (list work attempt generation))
         (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs st)))
         (answer (fn-bpn-host-existing-sequence st work attempt generation)))
    (and (iff (fn-bpn-host-existing-sequence-p answer)
              (and (fn-bpn-machine-statep st)
                   (fn-bpn-keyp key)
                   job
                   (fn-bpp-timep (fn-bpn-job-sequence job))))
         (implies (fn-bpn-host-existing-sequence-p answer)
                  (equal (fn-bpn-host-existing-sequence-value answer)
                         (fn-bpn-job-sequence job)))
         (implies (not (fn-bpn-host-existing-sequence-p answer))
                  (or (equal answer '(:absent))
                      (and (equal (car answer) :existing)
                           (not (fn-bpp-timep (fn-bpn-job-sequence job))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bpn-host-existing-sequence
                                   fn-bpn-host-existing-sequence-p
                                   fn-bpn-host-existing-sequence-value
                                   fn-bpn-existing-sequence
                                   fn-bpn-existing-sequencep)
                                  (fn-bpn-machine-statep fn-bpn-keyp
                                   fn-bpn-find-job fn-bpn-job-sequence
                                   fn-bpp-timep fn-bpn-machine-state-jobs)))))
