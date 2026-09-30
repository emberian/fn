; The native BP service's existing-sequence reuse, in a certified book (was
; host/bp-node-machine-host.lisp's): the host asks whether a job with the
; obligation key (work attempt generation) already holds a creation
; sequence, and reuses it instead of reserving a new one
; (host/native/bp-obligation.lisp, host/native/bp-node.lisp).  Guard-verified
; shims over fn-bpn-existing-sequence (bp-node-machine, guards in
; bp-node-machine-guards), with the keystone.
(in-package "ACL2")
(include-book "bp-node-machine-guards")
(include-book "bp-node-machine-codec")

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

; ---------------------------------------------------------------------------
; The lifecycle recovery agreement the host checks at open (PRF-1046).
; host/native/bp-service.lisp fnn-bps-open recovers the lifecycle namespace
; (fn-bpn-lifecycle-recovery over the observed names and the decoded records)
; and replays the same records into the initial machine (fn-bpn-restart-step,
; fn-bpn-replay-records); a disagreement between the two frontiers is a
; recovery/core contradiction (fnn-indeterminate), not a decision.  This
; wrapper was host/bp-node-machine-host.lisp's; it is an exact alias of the
; codec's predicate, guard-verified.
(defun fn-bpn-host-lifecycle-recovery-agrees-p (answer st)
  (declare (xargs :guard t))
  (fn-bpn-lifecycle-recovery-agrees-with-statep answer st))

(verify-guards fn-bpn-host-lifecycle-recovery-agrees-p)

(defthm fn-bpn-lifecycle-reverse-onto-len
  (equal (len (fn-bpn-lifecycle-reverse-onto xs acc))
         (+ (len xs) (len acc))))

(defthm fn-bpn-lifecycle-reverse-len
  (equal (len (fn-bpn-lifecycle-reverse xs)) (len xs)))

; The namespace plan's frontier counts its record names: every record name
; consumed advances the token once, hidden stages never do.
(defthm fn-bpn-lifecycle-namespace-plan-aux-frontier-counts-the-records
  (implies (and (natp token)
                (equal (car (fn-bpn-lifecycle-namespace-plan-aux
                             names token records stages))
                       :ready))
           (equal (nth 3 (fn-bpn-lifecycle-namespace-plan-aux
                          names token records stages))
                  (+ token
                     (len (nth 1 (fn-bpn-lifecycle-namespace-plan-aux
                                  names token records stages)))
                     (- (len records))))))

(defthm fn-bpn-lifecycle-namespace-plan-frontier-counts-the-records
  (implies (equal (car (fn-bpn-lifecycle-namespace-plan names)) :ready)
           (equal (nth 3 (fn-bpn-lifecycle-namespace-plan names))
                  (len (nth 1 (fn-bpn-lifecycle-namespace-plan names))))))

; A record binding pairs the names and the records one to one.
(defthm fn-bpn-lifecycle-record-bindingsp-pairs-the-records
  (implies (fn-bpn-lifecycle-record-bindingsp names records token)
           (and (true-listp records)
                (equal (len records) (len names)))))

; A completed replay advances the machine frontier once per record.
(defthm fn-bpn-replay-records-ready-advances-the-frontier-per-record
  (implies (and (natp (fn-bpn-machine-state-next-token st))
                (equal (car (fn-bpn-replay-records st records)) :ready))
           (equal (fn-bpn-machine-state-next-token
                   (nth 1 (fn-bpn-replay-records st records)))
                  (+ (fn-bpn-machine-state-next-token st) (len records))))
  :hints (("Goal" :induct (fn-bpn-replay-records st records)
           :in-theory (e/d (fn-bpn-replay-records)
                           (fn-bpn-apply-record fn-bpn-record-applicablep
                            fn-bpn-machine-state-next-token)))))

; KEYSTONE.  The namespace recovery and the record replay agree: for a
; :ready recovery of the observed names over the decoded records, and the
; initial machine (frontier 0) that replays those records to :ready, the
; host's agreement check answers t, and both frontiers are the record count.
; The host's "recovered namespace and machine frontier disagree" exit is
; unreachable when both recoveries succeed on the same records.
(defthm fn-bpn-host-lifecycle-recovery-agrees-with-the-replayed-machine
  (implies (and (fn-bpn-machine-invariantp base)
                (equal (fn-bpn-machine-state-next-token base) 0)
                (equal (car (fn-bpn-lifecycle-recovery names records)) :ready)
                (equal (car (fn-bpn-replay-records base records)) :ready))
           (and (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                        (fn-bpn-lifecycle-recovery names records)
                        (nth 1 (fn-bpn-replay-records base records)))
                       t)
                (equal (fn-bpn-lifecycle-recovery-next-token
                        (fn-bpn-lifecycle-recovery names records))
                       (len records))
                (equal (fn-bpn-machine-state-next-token
                        (nth 1 (fn-bpn-replay-records base records)))
                       (len records))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-bpn-host-lifecycle-recovery-agrees-p
                            fn-bpn-lifecycle-recovery-agrees-with-statep
                            fn-bpn-lifecycle-recovery
                            fn-bpn-lifecycle-recovery-next-token
                            fn-bpn-lifecycle-namespace-planp
                            fn-bpn-lifecycle-plan-record-names
                            fn-bpn-lifecycle-plan-next-token)
                           (fn-bpn-lifecycle-namespace-plan
                            fn-bpn-replay-records
                            fn-bpn-lifecycle-record-bindingsp
                            fn-bpn-machine-invariantp
                            fn-bpn-machine-statep
                            fn-bpn-machine-state-next-token))
           :use ((:instance fn-bpn-replay-records-preserves-machine-invariant
                            (st base))
                 (:instance fn-bpn-lifecycle-record-bindingsp-pairs-the-records
                            (names (nth 1 (fn-bpn-lifecycle-namespace-plan names)))
                            (token 0))
                 (:instance fn-bpn-replay-records-ready-advances-the-frontier-per-record
                            (st base))))
          ("Subgoal 1" :in-theory (enable fn-bpn-machine-invariantp))))
