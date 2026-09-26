; The run class is a function of ACL2's durable record (PRF-131 part 1).
;
; fn-bpnj-named-result-is-the-transport-outcome (PRF-120) says what the
; served step records for a named job result: :accepted proposes the
; :finished record, whose durable answer reports (:transport ... :forwarded);
; anything else proposes a :requeued record whose reason is :refused,
; :uncertain or :failed, and whose durable answer reports
; (:forward-refused W A G REASON).  host/native/bp-service.lisp records each
; effect of that answer with fn-bprc-effect-evidence (the :forward-refused
; arm of fnn-bps-drive-effects) and renders fn-bprc-run-exit-code
; (fnn-bps-exit-code).  The theorem below is that the class the host renders
; for that answer is the class of the transport outcome the record names: a
; connect that never produced a socket (:failed) is :not-connected, a lost
; connection (:uncertain) is :interrupted, never :fenced, and a refusal is
; :refused.
(in-package "ACL2")
(include-book "bp-run-class")
(include-book "bp-node-job-offer")

(defthm fn-bpnrc-class-of-a-job-result-answer
  (and (implies (equal effects (list (list :transport w a g :forwarded)))
                (equal (fn-bprc-class (fn-bprc-note-effects (fn-bprc-empty) effects))
                       :accepted))
       (implies (and (not (equal outcome :accepted))
                     (equal effects
                            (list (list :transport w a g :attempted)
                                  (list :forward-refused w a g
                                        (if (equal outcome :refused) :refused
                                          (if (equal outcome :uncertain) :uncertain
                                            :failed))))))
                (equal (fn-bprc-class (fn-bprc-note-effects (fn-bprc-empty) effects))
                       (fn-bprc-transfer-class outcome))))
  :rule-classes nil)

(defthm fn-bpnrc-job-result-class-is-the-transport-class
  (let* ((base (fn-bpnf-base st))
         (token (fn-bpn-machine-state-next-token base))
         (ans (fn-bpnj-step st (list :job-result key attempt outcome)))
         (pending (fn-bpn-machine-state-pending
                   (fn-bpnf-base (fn-bpnf-answer-state ans)))))
    (implies (and (fn-bpn-machine-statep base)
                  (not (fn-bpnf-issued st))
                  (not (fn-bpah-delivery-uncertainp st))
                  (not (fn-bpn-machine-state-fenced base))
                  (not (fn-bpn-machine-state-pending base))
                  (natp attempt)
                  (equal (fn-bpnj-attempt-token st key) attempt)
                  (< token *fn-bpn-machine-max-records*))
             (equal (fn-bprc-class
                     (fn-bprc-note-effects (fn-bprc-empty)
                                           (fn-bpn-pending-success-effects pending)))
                    (fn-bprc-transfer-class outcome))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-named-result-is-the-transport-outcome)
                 (:instance fn-bpnrc-class-of-a-job-result-answer
                  (effects (fn-bpn-pending-success-effects
                            (fn-bpn-machine-state-pending
                             (fn-bpnf-base
                              (fn-bpnf-answer-state
                               (fn-bpnj-step st (list :job-result key attempt outcome)))))))
                  (w (nth 0 key)) (a (nth 1 key)) (g (nth 2 key))))
           :in-theory (union-theories '((:e fn-bprc-transfer-class))
                                      (theory 'minimal-theory))))
  :rule-classes nil)
