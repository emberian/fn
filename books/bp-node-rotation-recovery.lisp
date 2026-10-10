; Machine-level recovery of the published BP rotation checkpoint.
(in-package "ACL2")
(include-book "bp-node-rotation")
(include-book "bp-node-job-offer")
(include-book "bp-recovery-profile")
(set-verify-guards-eagerness 0)

(defthm fn-bpnj-recovery-is-the-progress-step-by-definition
  (implies (equal (fn-cbor-ag-car event) :recover-fnbs)
           (equal (fn-bpnj-step st event) (fn-bpnp-step st event)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-step fn-bpnj-unnamed-result-p (:e equal)) (theory 'minimal-theory)))))

(defthm fn-bprpf-admitted-recovery-is-the-event-by-definition
  (implies (and (fn-bpnpf-profilep profile)
                (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 (fn-bpn-nth 4 event))
                                       (fn-bpnpf-adu-octets profile)))
           (equal (fn-bprpf-admit-recovery event profile) event))
  :hints (("Goal" :in-theory (enable fn-bprpf-admit-recovery))))

(local
 (defthm fn-bpnr-author-step-of-recovery
   (implies (equal (fn-cbor-ag-car event) :recover-fnbs)
            (equal (fn-bpn-report-author-step st event)
                   (fn-bpnf-recover-fnbs-step
                    st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                    (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpn-report-author-step fn-bpn-report-step
                          fn-bpnf-fragment-step fn-bpnf-step (:e equal))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnr-proof-answer-fields
   (and (equal (fn-bpnf-answer-state (fn-bpnf-answer st effects)) st)
        (equal (fn-bpnf-answer-effects (fn-bpnf-answer st effects)) effects))
   :hints (("Goal" :in-theory (enable fn-bpnf-answer-state fn-bpnf-answer-effects
                                     fn-bpnf-answer fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defthm fn-bpnr-runtime-writers-keep-base
   (and (equal (fn-bpnf-base (fn-bpnp-with-runtime st sessions image)) (fn-bpnf-base st))
        (equal (fn-bpnf-base (fn-bpnp-with-credit st used debt)) (fn-bpnf-base st))
        (equal (fn-bpnf-base (fn-bpnp-with-waits st waits)) (fn-bpnf-base st)))
   :hints (("Goal" :in-theory (enable fn-bpnf-base fn-bpn-nth fn-cbor-ag-car
                                     fn-bpnp-with-runtime fn-bpnp-with-credit fn-bpnp-with-waits)))))

(defthm fn-bpnp-recovery-keeps-foundation-base-and-effects
  (implies (and (equal (fn-cbor-ag-car event) :recover-fnbs)
                (or (not (fn-bpnp-domain-recover-eventp event))
                    (fn-bpnp-clock-domain-admitsp event))
                (equal (car (car (fn-bpnf-answer-effects
                                 (fn-bpnf-recover-fnbs-step
                                  st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                                  (fn-bpn-nth 3 event) (fn-bpn-nth 4 event)))))
                       :restart-ready))
           (let ((inner (fn-bpnf-recover-fnbs-step
                         st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                         (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
             (and (equal (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnp-step st event)))
                         (fn-bpnf-base (fn-bpnf-answer-state inner)))
                  (equal (fn-bpnf-answer-effects (fn-bpnp-step st event))
                         (fn-bpnf-answer-effects inner)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-preserve-runtime-answer
                         fn-bpnp-delegate-with-credit fn-bpnr-author-step-of-recovery
                         fn-bpnp-credit-proposal-kind fn-bpnp-conflict-held
                         fn-bpnr-runtime-writers-keep-base fn-bpnr-proof-answer-fields
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         natp zp (:e zp) (:e binary-+) (:e unary--) (:e natp) (:e equal))
                       (theory 'minimal-theory)))))

(defthm fn-bpn-restart-own-seed-is-ready-fast
  (implies (and (fn-bpn-machine-statep st)
                (<= (fn-bpn-machine-state-next-token st)
                    *fn-bpn-machine-max-records*))
           (equal (car (fn-bpn-answer-effects
                        (fn-bpn-restart-step-from
                         st nil :ready (fn-bpn-machine-state-jobs st)
                         (fn-bpn-machine-state-next-token st))))
                  (list :restart-ready (len (fn-bpn-machine-state-jobs st)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-machine-statep-components)
                 (:instance fn-bpn-seeded-machine-state-is-a-machine-state
                            (config (fn-bpn-machine-state-config st))
                            (max-jobs (fn-bpn-machine-state-max-jobs st))
                            (max-octets (fn-bpn-machine-state-max-octets st))
                            (jobs (fn-bpn-machine-state-jobs st))
                            (token (fn-bpn-machine-state-next-token st)))
                 (:instance fn-bpn-seeded-machine-state-accessors
                            (config (fn-bpn-machine-state-config st))
                            (max-jobs (fn-bpn-machine-state-max-jobs st))
                            (max-octets (fn-bpn-machine-state-max-octets st))
                            (jobs (fn-bpn-machine-state-jobs st))
                            (token (fn-bpn-machine-state-next-token st))))
           :in-theory (union-theories
                       '(fn-bpn-restart-step-from fn-bpn-restart-seed-fitsp
                         fn-bpn-restart-replay-step fn-bpn-replay-records
                         fn-bpn-answer-constructor-accessors fn-bpn-machine-u64p
                         fn-bpn-seeded-machine-state-accessors
                         natp len nth car-cons cdr-cons zp (:e zp) (:e binary-+))
                       (theory 'minimal-theory)))))

(defthm fn-bpn-restart-own-seed-keeps-limits
  (implies (fn-bpn-machine-statep st)
           (let ((out (fn-bpn-answer-state
                       (fn-bpn-restart-step-from
                        st nil :ready (fn-bpn-machine-state-jobs st)
                        (fn-bpn-machine-state-next-token st)))))
             (and (equal (fn-bpn-machine-state-max-jobs out)
                         (fn-bpn-machine-state-max-jobs st))
                  (equal (fn-bpn-machine-state-max-octets out)
                         (fn-bpn-machine-state-max-octets st)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-machine-statep-components)
                 (:instance fn-bpn-seeded-machine-state-is-a-machine-state
                            (config (fn-bpn-machine-state-config st))
                            (max-jobs (fn-bpn-machine-state-max-jobs st))
                            (max-octets (fn-bpn-machine-state-max-octets st))
                            (jobs (fn-bpn-machine-state-jobs st))
                            (token (fn-bpn-machine-state-next-token st))))
           :in-theory
           (union-theories
            '(fn-bpn-restart-step-from fn-bpn-restart-replay-step
              fn-bpn-replay-records fn-bpn-resolve-orphans-step fn-bpn-propose
              fn-bpn-answer-constructor-accessors fn-bpn-state-with-accessors
              fn-bpn-seeded-machine-state-accessors
              nth car-cons cdr-cons zp (:e zp) (:e equal) (:e binary-+))
            (theory 'minimal-theory)))))

(defun fn-bpnr-recovery-replayp (old-epoch new-epoch replay max-jobs max-octets)
  (declare (xargs :guard t))
  (and (true-listp replay) (equal (len replay) 5)
       (equal (car replay) :ready)
       (fn-bphs-handoffs-p (fn-bpn-nth 2 replay))
       (let ((prior (fn-bpn-nth 3 replay)))
         (and (or (null prior)
                  (and (consp prior) (natp (car prior)) (natp (cdr prior))))
              (or (null prior) (< (car prior) new-epoch))))
       (fn-frame-natp new-epoch) (natp old-epoch) (< old-epoch new-epoch)
       (natp (fn-bpn-nth 4 replay))
       (<= (fn-bpn-nth 4 replay) (1+ *fn-frame-max-nat*))
       (<= (fn-bpnf-held-arrival-frontier (fn-bpn-nth 1 replay))
           (fn-bpn-nth 4 replay))
       (fn-bpnf-recovery-heldp (fn-bpn-nth 1 replay) max-jobs max-octets)))

(defthm fn-bpnr-foundation-installs-admissible-replay
  (let ((restart (fn-bpn-restart-step-from
                  (fn-bpnf-base st) records :ready
                  (fn-bpn-machine-state-jobs (fn-bpnf-base st))
                  (fn-bpn-machine-state-next-token (fn-bpnf-base st)))))
    (implies
     (and (equal (car (fn-bpn-answer-effects restart))
                 (list :restart-ready
                       (len (fn-bpn-machine-state-jobs (fn-bpn-answer-state restart)))))
          (fn-bpnr-recovery-replayp
           (fn-bpnf-epoch st) epoch replay
           (fn-bpn-machine-state-max-jobs (fn-bpn-answer-state restart))
           (fn-bpn-machine-state-max-octets (fn-bpn-answer-state restart))))
     (and (equal (fn-bpnf-base (fn-bpnf-answer-state
                               (fn-bpnf-recover-fnbs-step st epoch records :ready replay)))
                 (fn-bpn-answer-state restart))
          (equal (car (fn-bpnf-answer-effects
                       (fn-bpnf-recover-fnbs-step st epoch records :ready replay)))
                 (list :restart-ready (len (fn-bpn-nth 1 replay)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-recovery-replayp fn-bpnf-recover-fnbs-step
                         fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                         fn-bpnf-base fn-bpnf-state-with-arrival fn-bpn-nth fn-cbor-ag-car
                         car-cons cdr-cons zp natp (:e zp) (:e natp)
                         (:e binary-+) (:e unary--) (:e <) (:e equal))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-no-record-recovery-is-ready
  (implies
   (and (fn-bpn-machine-invariantp (fn-bpnf-base st))
        (fn-bpnr-recovery-replayp
         (fn-bpnf-epoch st) epoch replay
         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
         (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
   (equal (car (fn-bpnf-answer-effects
                (fn-bpnf-recover-fnbs-step st epoch nil :ready replay)))
          (list :restart-ready (len (fn-bpn-nth 1 replay)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-machine-invariant-components (st (fn-bpnf-base st)))
                 (:instance fn-bpn-restart-own-seed-is-ready-fast (st (fn-bpnf-base st)))
                 (:instance fn-bpn-restart-own-seed-keeps-limits (st (fn-bpnf-base st)))
                 (:instance fn-bpn-restart-step-from-of-own-seed-keeps-owed-work (st (fn-bpnf-base st)))
                 (:instance fn-bpnr-foundation-installs-admissible-replay (records nil)))
           :in-theory (theory 'minimal-theory))))

; Abbreviations of the file read and constructor in fnn-bps-open.
(defun fn-bpnr-published-plan (st generation ck)
  (declare (xargs :guard t))
  (let ((budget (fn-bpnr-depth-budget
                 (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))))
    (fn-bpnr-selection-plan
     t (fn-bpnr-checkpoint-octets
        (fn-bpn-nth 4 (car (fn-bpnf-answer-effects
                            (fn-bpnp-rotate-step st generation ck)))) budget)
     budget)))

(defun fn-bpnr-open-fresh (st)
  (declare (xargs :guard t))
  (fn-bpnf-initial-state (fn-bpn-machine-state-config (fn-bpnf-base st))
                        (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
                        (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))

(defthm fn-bpnr-published-plan-is-the-rotation-checkpoint
  (implies (equal (car (car (fn-bpnf-answer-effects
                            (fn-bpnp-rotate-step st generation ck))))
                  :persist-checkpoint)
           (equal (fn-bpnr-published-plan st generation ck)
                  (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-rotate-step-proposes-only-own-projection)
                 (:instance fn-bpnr-selection-plan-of-octets
                            (ck (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))
                            (budget (fn-bpnr-depth-budget
                                     (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))))
                 (:instance fn-bpnr-rotation-checkpoint-is-a-checkpoint
                            (e (fn-bpnf-epoch st))))
           :in-theory (union-theories
                       '(fn-bpnr-published-plan fn-bpnr-checkpoint-of-statep
                         fn-bpnp-rotation-quiescentp fn-frame-natp)
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-open-fresh-fields
  (implies (fn-bpn-machine-statep (fn-bpnf-base st))
           (let ((fresh (fn-bpnr-open-fresh st)))
             (and (fn-bpn-machine-statep (fn-bpnf-base fresh))
                  (null (fn-bpn-machine-state-pending (fn-bpnf-base fresh)))
                  (equal (fn-bpn-machine-state-max-jobs (fn-bpnf-base fresh))
                         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))
                  (equal (fn-bpn-machine-state-max-octets (fn-bpnf-base fresh))
                         (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))
                  (equal (fn-bpnf-epoch fresh) 0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-machine-statep-components (st (fn-bpnf-base st)))
                 (:instance fn-bpn-initial-machine-state-has-invariant
                            (config (fn-bpn-machine-state-config (fn-bpnf-base st)))
                            (max-jobs (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))
                            (max-octets (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
                 (:instance fn-bpn-machine-invariant-components
                            (st (fn-bpn-initial-machine-state
                                 (fn-bpn-machine-state-config (fn-bpnf-base st))
                                 (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
                                 (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))))
           :in-theory (union-theories
                       '(fn-bpnr-open-fresh fn-bpnf-initial-state
                         fn-bpnf-state fn-bpnf-state-with-arrival
                         fn-bpnf-base fn-bpnf-epoch fn-bpn-nth fn-cbor-ag-car
                         fn-bpn-initial-machine-state-is-quiescent
                         fn-bpn-limits-of-initial-machine-state
                         car-cons cdr-cons zp natp (:e zp) (:e natp)
                         (:e binary-+) (:e unary--) (:e equal) (:e fn-bpn-machine-statep))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-selected-open-seed-fields
  (implies
   (and (fn-bpnr-checkpointp ckk)
        (fn-bpn-machine-invariantp (fn-bpnf-base st))
        (equal (fn-bpnr-checkpoint-jobs ckk)
               (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
        (equal (fn-bpnr-checkpoint-next-token ckk)
               (fn-bpn-machine-state-next-token (fn-bpnf-base st))))
   (let ((seeded (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (list :selected ckk))))
     (and (fn-bpn-machine-invariantp (fn-bpnf-base seeded))
          (equal (fn-bpnf-epoch seeded) 0)
          (equal (fn-bpn-machine-state-max-jobs (fn-bpnf-base seeded))
                 (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))
          (equal (fn-bpn-machine-state-max-octets (fn-bpnf-base seeded))
                 (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-seed-state-over-a-selected-checkpoint
                            (fresh (fn-bpnr-open-fresh st)) (other (fn-bpnf-base st)))
                 (:instance fn-bpnr-open-fresh-fields)
                 (:instance fn-bpn-machine-invariant-components (st (fn-bpnf-base st))))
           :in-theory
           (union-theories
            '(fn-bpnr-seed-state fn-bpnr-replay-base fn-bpnf-with-base
              fn-bpnf-state-with-arrival fn-bpnf-base fn-bpnf-epoch
              fn-bpnr-plan-checkpoint fn-bpn-machine-invariantp
              fn-bpn-state-with-accessors fn-bpn-nth fn-cbor-ag-car
              fn-bpnr-open-fresh-fields
              car-cons cdr-cons zp natp (:e zp) (:e natp)
              (:e binary-+) (:e unary--) (:e equal))
            (theory 'minimal-theory)))))

(defthm fn-bpnr-selected-event-without-rows
  (implies (and (fn-bpnr-checkpointp ckk)
                (equal (fn-bpnf-epoch seeded) 0)
                (equal (fn-bpnr-checkpoint-prior ckk) (cons e 0))
                (natp e))
           (equal (fn-bpnr-recover-auto-event seeded nil :ready nil (list :selected ckk))
                  (list :recover-fnbs (+ 1 e) nil :ready
                        (list :ready (fn-bpnr-checkpoint-held ckk)
                              (fn-bpnr-checkpoint-handoffs ckk) (cons e 0)
                              (fn-bpnr-checkpoint-next-arrival ckk)) 0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnr-recover-auto-event fn-bpnr-replay-from
                            fn-bpnf-family-replay-rows-aux fn-bpnr-plan-checkpoint
                            fn-bpn-nth fn-cbor-ag-car)
                           (fn-bpnr-checkpointp fn-bpnr-replay-base)))))

; PREMISE-EXCESS-D: the replay premise of the two restart keystones below,
; carried as an invariant of the host's BP state.  The host writes that
; state only at the open (fn-bpnr-seed-state over fn-bpnf-initial-state,
; host/native/bp-service.lisp) and through fn-bpnj-step.  Every arm that
; changes the held list, the handoffs, the arrival frontier or the epoch
; either proposes an operation (the counter moves past zero) or settles an
; issued one; only a validated recovery writes the counter back to zero.  So
; while the counter is zero, nothing but an uncertain fence is outstanding
; and the state's own projection replays whenever its successor epoch is a
; frame natural; that is exactly what a rotation needs.
(defun fn-bpnr-own-replayp (st)
  (declare (xargs :guard t))
  (fn-bpnr-recovery-replayp
   0 (+ 1 (fn-bpnf-epoch st))
   (list :ready (fn-bpnf-held-list st) (fn-bpnf-handoffs st)
         (cons (fn-bpnf-epoch st) 0) (fn-bpnf-next-arrival st))
   (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
   (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))

(defun fn-bpnr-replay-readyp (st)
  (declare (xargs :guard t))
  (and (natp (fn-bpnf-next-op st))
       (implies (equal (fn-bpnf-next-op st) 0)
                (and (or (null (fn-bpnf-issued st))
                         (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain))
                     (implies (fn-frame-natp (+ 1 (fn-bpnf-epoch st)))
                              (fn-bpnr-own-replayp st))))))

; What the keystones read: a ready state that rotates replays its own
; projection.
(defthm fn-bpnr-rotating-ready-state-replays
  (implies (and (fn-bpnr-replay-readyp st)
                (equal (car (car (fn-bpnf-answer-effects
                                  (fn-bpnp-rotate-step st generation ck))))
                       :persist-checkpoint))
           (fn-bpnr-recovery-replayp
            0 (+ 1 (fn-bpnf-epoch st))
            (list :ready (fn-bpnf-held-list st) (fn-bpnf-handoffs st)
                  (cons (fn-bpnf-epoch st) 0) (fn-bpnf-next-arrival st))
            (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
            (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-rotate-step-proposes-only-own-projection))
           :in-theory (union-theories '(fn-bpnr-replay-readyp fn-bpnr-own-replayp
                                        fn-bpnp-rotation-quiescentp)
                                      (theory 'minimal-theory)))))

; Establishment at the host open (bp-service.lisp, fnn-bps-open).
(defthm fn-bpnr-open-is-replay-ready
  (let ((st (fn-bpnr-seed-state (fn-bpnf-initial-state config max-held max-octets) plan)))
    (implies st (fn-bpnr-replay-readyp st)))
  :rule-classes nil)

; Preservation by the one host-called step, one lemma per arm.
(encapsulate
  ()
(local
 (defmacro fn-bpnr-ready-arm (arm call fns theory)
   `(defthm ,(intern-in-package-of-symbol
              (concatenate 'string "FN-BPNR-READY-ARM-" (symbol-name arm))
              'fn-bpnr-ready-arm)
      (implies (fn-bpnr-replay-readyp st)
               (fn-bpnr-replay-readyp (fn-bpnf-answer-state ,call)))
      :hints (("Goal" :do-not-induct t
               :in-theory (union-theories ',fns (theory ',theory)))))))
(local
 (defmacro fn-bpnr-ready-limits (step call)
   `(defthm ,(intern-in-package-of-symbol
              (concatenate 'string "FN-BPNR-READY-" (symbol-name step) "-KEEPS-LIMITS")
              'fn-bpnr-ready-limits)
      (and (equal (fn-bpn-machine-state-max-jobs (fn-bpn-answer-state ,call))
                  (fn-bpn-machine-state-max-jobs b))
           (equal (fn-bpn-machine-state-max-octets (fn-bpn-answer-state ,call))
                  (fn-bpn-machine-state-max-octets b))))))
(local
 (defthm fn-bpnr-ready-bpn-nth-is-nth
   (equal (fn-bpn-nth n xs) (nth n xs))
   :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car nth)))))
(local
 (deftheory fn-bpnr-ready-theory
   (union-theories
    '(fn-bpnr-replay-readyp fn-bpnr-own-replayp fn-bpnr-ready-bpn-nth-is-nth
      fn-bpnf-base fn-bpnf-held-list fn-bpnf-outcomes fn-bpnf-handoffs
      fn-bpnf-correlation fn-bpnf-issued fn-bpnf-waits fn-bpnf-epoch
      fn-bpnf-next-op fn-bpnf-next-arrival
      fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
      fn-bpnf-state-with-arrival fn-bpnf-with-issued fn-bpnf-with-base
      fn-bpnp-with-runtime fn-bpnp-with-credit fn-bpnp-with-waits fn-bpnp-with-issued
      nth-update-nth nth-0-cons nth-add1 car-cons cdr-cons
      natp natp-compound-recognizer zp fix nfix
      (:e zp) (:e natp) (:e equal) (:e binary-+) (:e nth) (:e not)
      (:e fn-frame-natp))
    (theory 'minimal-theory))))
(local (fn-bpnr-ready-arm rotate (fn-bpnp-rotate-step st g ck)
                    (fn-bpnp-rotate-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm rotation-persist (fn-bpnp-rotation-persist-step st e o r)
                    (fn-bpnp-rotation-persist-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm deferral-persist (fn-bpnp-deferral-persist-step st e o r)
                    (fn-bpnp-deferral-persist-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm operator-resume (fn-bpnp-operator-resume-step st a b)
                    (fn-bpnp-operator-resume-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm forward-result-propose (fn-bpnp-forward-result-propose-step st a b c d e)
                    (fn-bpnp-forward-result-propose-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm dispatch-persist (fn-bpnp-dispatch-persist-step st e o r)
                    (fn-bpnp-dispatch-persist-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm attempt-persist (fn-bpnp-attempt-persist-step st e o r)
                    (fn-bpnp-attempt-persist-step) fn-bpnr-ready-theory))
(local (fn-bpnr-ready-arm forward-result-persist (fn-bpnp-forward-result-persist-step st e o r)
                    (fn-bpnp-forward-result-persist-step) fn-bpnr-ready-theory))
(local
 (deftheory fn-bpnr-ready-theory2
   (union-theories '(true-listp-update-nth true-listp fn-bpnf-operation (:e true-listp))
                   (theory 'fn-bpnr-ready-theory))))
(local (fn-bpnr-ready-arm clock-fence (fn-bpnp-clock-domain-fence st plan)
                    (fn-bpnp-clock-domain-fence) fn-bpnr-ready-theory2))
(local (fn-bpnr-ready-arm conflict-persist (fn-bpnp-conflict-persist-step st e o r)
                    (fn-bpnp-conflict-persist-step) fn-bpnr-ready-theory2))
(local (fn-bpnr-ready-limits bpnj-start-job (fn-bpnj-start-job (fn-bpnj-open-base b peer) peer key)))
(local
 (deftheory fn-bpnr-ready-theory3
   (union-theories '(fn-bpnp-with-next-issued fn-bpnj-with-base fn-bpnp-sessions fn-bpnp-pending-image fn-bpnp-used fn-bpnp-debt fn-bpnp-waits)
                   (theory 'fn-bpnr-ready-theory2))))
(local (fn-bpnr-ready-arm busy-delivery (fn-bpnp-busy-delivery-step st e o key obs b)
                    (fn-bpnp-busy-delivery-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm conflict-propose (fn-bpnp-conflict-propose-step st event h)
                    (fn-bpnp-conflict-propose-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm busy-resume (fn-bpnp-busy-resume-step st a b)
                    (fn-bpnp-busy-resume-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-limits bpn-enqueue (fn-bpn-enqueue-step b a1 a2 a3 a4 a5 a6 a7 a8)))
(local (fn-bpnr-ready-limits bpn-contact (fn-bpn-contact-step b a1 a2)))
(local (fn-bpnr-ready-limits bpn-start-one (fn-bpn-start-one b a1)))
(local (fn-bpnr-ready-limits bpn-persist-result (fn-bpn-persist-result-step b a1 a2)))
(local (fn-bpnr-ready-limits bpn-forward-result (fn-bpn-forward-result-step b a1 a2)))
(local (fn-bpnr-ready-limits bpn-clock (fn-bpn-clock-step b a1)))
(local (fn-bpnr-ready-arm deliver (fn-bpah-deliver-step st key node)
                    (fn-bpah-deliver-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm deliver-result (fn-bpah-deliver-result-step st e m key s d)
                    (fn-bpah-deliver-result-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm persist-delivery (fn-bpah-persist-delivery-step st e o r)
                    (fn-bpah-persist-delivery-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm family-propose (fn-bpnf-family-propose-step st a obs)
                    (fn-bpnf-family-propose-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm family-persist (fn-bpnf-family-persist-step st e o r)
                    (fn-bpnf-family-persist-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm fj-propose (fn-bpfj-propose-step st a obs job limit)
                    (fn-bpfj-propose-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm fj-persist (fn-bpfj-persist-step st e o r job limit)
                    (fn-bpfj-persist-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm delete-propose (fn-bpn-report-delete-propose-step st obs en)
                    (fn-bpn-report-delete-propose-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm delete-persist (fn-bpn-report-delete-persist-step st e o r)
                    (fn-bpn-report-delete-persist-step) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-arm start-one (fn-bpnp-start-one st peer session mru obs b ordered)
                    (fn-bpnp-start-one) fn-bpnr-ready-theory3))
(local (fn-bpnr-ready-limits bpn-propose (fn-bpn-propose b r s f u)))
(local (fn-bpnr-ready-limits bpn-resolve-orphans (fn-bpn-resolve-orphans-step b)))
(local
 (defthm fn-bpnr-ready-bpn-restart-keeps-limits
   (implies (fn-bpn-machine-statep b)
   (and (equal (fn-bpn-machine-state-max-jobs (fn-bpn-answer-state (fn-bpn-restart-step b a1 a2)))
               (fn-bpn-machine-state-max-jobs b))
        (equal (fn-bpn-machine-state-max-octets (fn-bpn-answer-state (fn-bpn-restart-step b a1 a2)))
               (fn-bpn-machine-state-max-octets b))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpn-machine-statep-components (st b))
                  (:instance fn-bpn-seeded-machine-state-is-a-machine-state
                             (config (fn-bpn-machine-state-config b))
                             (max-jobs (fn-bpn-machine-state-max-jobs b))
                             (max-octets (fn-bpn-machine-state-max-octets b))
                             (jobs nil) (token 0))
                  (:instance fn-bpn-seeded-machine-state-accessors
                             (config (fn-bpn-machine-state-config b))
                             (max-jobs (fn-bpn-machine-state-max-jobs b))
                             (max-octets (fn-bpn-machine-state-max-octets b))
                             (jobs nil) (token 0)))
            :in-theory (union-theories
                        '(fn-bpn-restart-step fn-bpn-restart-step-from fn-bpn-restart-replay-step
                          fn-bpn-answer-constructor-accessors fn-bpn-state-with-accessors
                          fn-bpn-replay-records-keeps-config-and-limits
                          fn-bpnr-ready-bpn-resolve-orphans-keeps-limits
                          (:e fn-bpn-job-listp) (:e len) (:e fn-bpn-jobs-octets) (:e fn-bpn-machine-u64p)
                          natp posp fn-bpn-machine-limitp)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-bpnr-ready-bpn-step-keeps-limits
   (and (equal (fn-bpn-machine-state-max-jobs (fn-bpn-answer-state (fn-bpn-step b e)))
               (fn-bpn-machine-state-max-jobs b))
        (equal (fn-bpn-machine-state-max-octets (fn-bpn-answer-state (fn-bpn-step b e)))
               (fn-bpn-machine-state-max-octets b)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpn-step fn-bpn-dispatch fn-bpn-answer-constructor-accessors
                          fn-bpnr-ready-bpn-enqueue-keeps-limits fn-bpnr-ready-bpn-contact-keeps-limits
                          fn-bpnr-ready-bpn-start-one-keeps-limits fn-bpnr-ready-bpn-persist-result-keeps-limits
                          fn-bpnr-ready-bpn-forward-result-keeps-limits fn-bpnr-ready-bpn-clock-keeps-limits
                          fn-bpnr-ready-bpn-restart-keeps-limits)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-bpnr-ready-arm-recover
   (implies (fn-bpnr-replay-readyp st)
            (fn-bpnr-replay-readyp
             (fn-bpnf-answer-state (fn-bpnf-recover-fnbs-step st ne br sr rr))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-bpnf-recover-fnbs-step fn-bpnr-recovery-replayp
                                         fn-frame-natp (:e fn-frame-natp) (:e fn-bphs-handoffs-p)
                                         len (:e len) (:e fn-bpnf-held-arrival-frontier))
                                       (theory 'fn-bpnr-ready-theory3))))))
(local
 (defthm fn-bpnr-ready-answer-state-of-answer
   (equal (fn-bpnf-answer-state (fn-bpnf-answer s e)) s)
   :hints (("Goal" :in-theory (enable fn-bpnf-answer-state fn-bpnf-answer fn-bpn-nth)))))
(local
 (deftheory fn-bpnr-ready-theory4
   (union-theories
    '(fn-bpnr-ready-answer-state-of-answer
      fn-bpnr-ready-bpn-step-keeps-limits fn-bpnr-ready-bpnj-start-job-keeps-limits fn-bpnr-ready-bpn-propose-keeps-limits
      fn-bpnr-ready-arm-deliver fn-bpnr-ready-arm-deliver-result fn-bpnr-ready-arm-persist-delivery fn-bpnr-ready-arm-recover
      fn-bpnr-ready-arm-family-propose fn-bpnr-ready-arm-family-persist fn-bpnr-ready-arm-fj-propose fn-bpnr-ready-arm-fj-persist
      fn-bpnr-ready-arm-delete-propose fn-bpnr-ready-arm-delete-persist fn-bpnr-ready-arm-start-one
      fn-bpnr-ready-arm-rotate fn-bpnr-ready-arm-rotation-persist fn-bpnr-ready-arm-clock-fence fn-bpnr-ready-arm-conflict-persist
      fn-bpnr-ready-arm-busy-delivery fn-bpnr-ready-arm-deferral-persist fn-bpnr-ready-arm-conflict-propose
      fn-bpnr-ready-arm-operator-resume fn-bpnr-ready-arm-busy-resume fn-bpnr-ready-arm-forward-result-propose
      fn-bpnr-ready-arm-dispatch-persist fn-bpnr-ready-arm-attempt-persist fn-bpnr-ready-arm-forward-result-persist
      fn-bpn-answer-constructor-accessors)
    (set-difference-theories (theory 'fn-bpnr-ready-theory3)
                             '(fn-bpnf-answer fn-bpnf-answer-state)))))
(local (fn-bpnr-ready-arm foundation (fn-bpnf-step st event)
                    (fn-bpnf-step) fn-bpnr-ready-theory4))
(local (fn-bpnr-ready-arm queue-report (fn-bpn-report-queue-step st a s r obs)
                    (fn-bpn-report-queue-step) fn-bpnr-ready-theory4))
(local (fn-bpnr-ready-arm fragment (fn-bpnf-fragment-step st event)
                    (fn-bpnf-fragment-step fn-bpnr-ready-arm-foundation fn-bpnr-ready-arm-queue-report) fn-bpnr-ready-theory4))
(local (fn-bpnr-ready-arm report (fn-bpn-report-step st event)
                    (fn-bpn-report-step fn-bpnr-ready-arm-foundation fn-bpnr-ready-arm-fragment fn-bpnr-ready-arm-queue-report fn-bpnr-ready-arm-fragment) fn-bpnr-ready-theory4))
(local (fn-bpnr-ready-arm report-author (fn-bpn-report-author-step st event)
                    (fn-bpn-report-author-step fn-bpnr-ready-arm-report fn-bpnr-ready-arm-queue-report fn-bpnr-ready-arm-queue-report fn-bpnr-ready-arm-fragment fn-bpnr-ready-arm-report) fn-bpnr-ready-theory4))
(local
 (defthm fn-bpnr-ready-via-with-credit
   (equal (fn-bpnr-replay-readyp (fn-bpnp-with-credit x u d)) (fn-bpnr-replay-readyp x))
   :hints (("Goal" :in-theory (union-theories '(fn-bpnp-with-credit) (theory 'fn-bpnr-ready-theory2))))))
(local
 (defthm fn-bpnr-ready-via-with-waits
   (equal (fn-bpnr-replay-readyp (fn-bpnp-with-waits x w)) (fn-bpnr-replay-readyp x))
   :hints (("Goal" :in-theory (union-theories '(fn-bpnp-with-waits) (theory 'fn-bpnr-ready-theory2))))))
(local
 (defthm fn-bpnr-ready-via-with-runtime
   (equal (fn-bpnr-replay-readyp (fn-bpnp-with-runtime x s p)) (fn-bpnr-replay-readyp x))
   :hints (("Goal" :in-theory (union-theories '(fn-bpnp-with-runtime) (theory 'fn-bpnr-ready-theory2))))))
(local
 (deftheory fn-bpnr-ready-theory5
   (union-theories '(fn-bpnr-ready-via-with-credit fn-bpnr-ready-via-with-waits fn-bpnr-ready-via-with-runtime
                     fn-bpnr-ready-arm-queue-report fn-bpnr-ready-arm-fragment fn-bpnr-ready-arm-report fn-bpnr-ready-arm-report-author)
                   (set-difference-theories (theory 'fn-bpnr-ready-theory4)
                                            '(fn-bpnp-with-credit fn-bpnp-with-waits fn-bpnp-with-runtime)))))
(local (fn-bpnr-ready-arm credit-refusal (fn-bpnp-credit-refusal st event kind)
                    (fn-bpnp-credit-refusal) fn-bpnr-ready-theory5))
(local (fn-bpnr-ready-arm delegate (fn-bpnp-delegate-with-credit st event)
                    (fn-bpnp-delegate-with-credit fn-bpnr-ready-arm-credit-refusal) fn-bpnr-ready-theory5))
(local
 (defthm fn-bpnr-ready-arm-preserve
   (implies (fn-bpnr-replay-readyp (fn-bpnf-answer-state a))
            (fn-bpnr-replay-readyp (fn-bpnf-answer-state (fn-bpnp-preserve-runtime-answer a st rec))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-bpnp-preserve-runtime-answer) (theory 'fn-bpnr-ready-theory5))))))
(local (fn-bpnr-ready-arm routed-start (fn-bpnp-routed-start st peer session mru obs via b)
                    (fn-bpnp-routed-start) fn-bpnr-ready-theory5))
(local (fn-bpnr-ready-arm transit-dispatch (fn-bpnp-transit-dispatch-step st h peer node)
                    (fn-bpnp-transit-dispatch-step) fn-bpnr-ready-theory5))
(local (fn-bpnr-ready-arm progress (fn-bpnp-progress-step st node obs routes gen b)
                    (fn-bpnp-progress-step fn-bpnr-ready-arm-transit-dispatch) fn-bpnr-ready-theory5))
(local
 (deftheory fn-bpnr-ready-theory6
   (union-theories '(fn-bpnr-ready-arm-credit-refusal fn-bpnr-ready-arm-delegate fn-bpnr-ready-arm-preserve fn-bpnr-ready-arm-progress
                     fn-bpnr-ready-arm-routed-start fn-bpnr-ready-arm-transit-dispatch)
                   (theory 'fn-bpnr-ready-theory5))))
(local (fn-bpnr-ready-arm bpnp-step (fn-bpnp-step st event)
                    (fn-bpnp-step) fn-bpnr-ready-theory6))
(local (fn-bpnr-ready-arm contact (fn-bpnj-contact-job-step st peer key)
                    (fn-bpnj-contact-job-step fn-bpnj-with-base) fn-bpnr-ready-theory6))
(local (fn-bpnr-ready-arm result (fn-bpnj-result-step st key token outcome)
                    (fn-bpnj-result-step fn-bpnr-ready-arm-bpnp-step) fn-bpnr-ready-theory6))
(defthm fn-bpnj-step-preserves-replay-readiness
  (implies (fn-bpnr-replay-readyp st)
           (fn-bpnr-replay-readyp (fn-bpnf-answer-state (fn-bpnj-step st event))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-bpnj-step fn-bpnr-ready-arm-bpnp-step fn-bpnr-ready-arm-contact fn-bpnr-ready-arm-result)
                                      (theory 'fn-bpnr-ready-theory6))))))

(defthm fn-bpnr-rotation-foundation-restart-is-ready-bound
  (implies
   (and (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
        (fn-bpn-machine-invariantp (fn-bpnf-base st))
        (fn-bpnr-replay-readyp st)
        (equal seeded (fn-bpnr-seed-state
                       (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)))
        (equal event (fn-bpnr-recover-auto-event seeded nil :ready nil
                                                (fn-bpnr-published-plan st generation ck))))
   (equal (car (fn-bpnf-answer-effects
                (fn-bpnf-recover-fnbs-step
                 seeded (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                 (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
          (list :restart-ready (len (fn-bpnf-held-list st)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-rotating-ready-state-replays)
                 (:instance fn-bpnp-rotate-step-proposes-only-own-projection)
                 (:instance fn-bpnr-rotation-checkpoint-is-a-checkpoint (e (fn-bpnf-epoch st)))
                 (:instance fn-bpnr-rotation-checkpoint-fields (e (fn-bpnf-epoch st)))
                 (:instance fn-bpnr-published-plan-is-the-rotation-checkpoint)
                 (:instance fn-bpnr-selected-open-seed-fields
                            (ckk (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st))))
                 (:instance fn-bpnr-selected-event-without-rows
                            (ckk (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))
                            (e (fn-bpnf-epoch st)))
                 (:instance fn-bpnr-no-record-recovery-is-ready
                            (st seeded) (epoch (fn-bpn-nth 1 event))
                            (replay (fn-bpn-nth 4 event))))
           :in-theory (union-theories
                       '(fn-bpnr-checkpoint-of-statep fn-bpnp-rotation-quiescentp
                         fn-frame-natp fn-bpn-nth fn-cbor-ag-car
                         car-cons cdr-cons zp natp (:e zp) (:e natp)
                         (:e binary-+) (:e unary--) (:e equal))
                       (theory 'minimal-theory)))))

(defthm fn-bprpf-admission-preserves-admitted-event-by-definition
  (implies (or (not (equal (fn-bpn-nth 0 (fn-bpn-nth 4 event)) :ready))
               (and (fn-bpnpf-profilep profile)
                    (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 (fn-bpn-nth 4 event))
                                           (fn-bpnpf-adu-octets profile))))
           (equal (fn-bprpf-admit-recovery event profile) event))
  :hints (("Goal" :in-theory (union-theories '(fn-bprpf-admit-recovery)
                                           (theory 'minimal-theory)))))

(defthm fn-bpnj-rotation-restart-succeeds-bound
  (implies
   (and (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
        (fn-bpn-machine-invariantp (fn-bpnf-base st))
        (fn-bpnr-replay-readyp st)
        (equal plan (fn-bpnr-published-plan st generation ck))
        (equal fresh (fn-bpnr-open-fresh st))
        (equal seeded (fn-bpnr-seed-state fresh plan))
        (equal event (fn-bpnr-recover-auto-event seeded nil :ready nil plan))
        (or (not (equal (fn-bpn-nth 0 (fn-bpn-nth 4 event)) :ready))
            (and (fn-bpnpf-profilep profile)
                 (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 (fn-bpn-nth 4 event))
                                        (fn-bpnpf-adu-octets profile))))
        (equal served (append (fn-bprpf-admit-recovery event profile) (list domain)))
        (fn-bpnp-clock-domain-admitsp served)
        (equal answer (fn-bpnj-step seeded served)))
   (and (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
        (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
        (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
        (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                (fn-bpn-lifecycle-recovery-from nil nil (fn-bpnr-plan-start-token plan))
                (fn-bpnf-base (fn-bpnf-answer-state answer))) t)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnr-rotation-foundation-restart-is-ready-bound)
                 (:instance fn-bpnp-rotation-restart-keeps-owed-work)
                 (:instance fn-bpnr-open-fresh-fields)
                 (:instance fn-bpn-machine-invariant-components (st (fn-bpnf-base st)))
                 (:instance fn-bprpf-admission-preserves-admitted-event-by-definition)
                 (:instance fn-bpnj-recovery-is-the-progress-step-by-definition (st seeded) (event served))
                 (:instance fn-bpnp-recovery-keeps-foundation-base-and-effects
                            (st seeded) (event served)))
           :in-theory (union-theories
                       '(fn-bpnr-published-plan fn-bpnr-recover-auto-event
                         fn-bpn-nth fn-cbor-ag-car binary-append
                         car-cons cdr-cons zp natp (:e zp) (:e natp)
                         (:e binary-+) (:e unary--) (:e equal))
                       (theory 'minimal-theory)))))

; KEYSTONE: successful restart through the host-called job dispatcher.
(defthm fn-bpnj-rotation-restart-succeeds-with-owed-work
  (let* ((plan (fn-bpnr-published-plan st generation ck))
         (fresh (fn-bpnr-open-fresh st))
         (seeded (fn-bpnr-seed-state fresh plan))
         (event (fn-bpnr-recover-auto-event seeded nil :ready nil plan))
         (served (append (fn-bprpf-admit-recovery event profile) (list domain)))
         (answer (fn-bpnj-step seeded served)))
    (implies (and (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
                  (fn-bpn-machine-invariantp (fn-bpnf-base st))
                  (fn-bpnr-replay-readyp st)
                  (or (not (equal (fn-bpn-nth 0 (fn-bpn-nth 4 event)) :ready))
            (and (fn-bpnpf-profilep profile)
             (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 (fn-bpn-nth 4 event))
                                    (fn-bpnpf-adu-octets profile))))
                  (fn-bpnp-clock-domain-admitsp served))
      (and (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
        (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
        (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
        (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                (fn-bpn-lifecycle-recovery-from nil nil (fn-bpnr-plan-start-token plan))
                (fn-bpnf-base (fn-bpnf-answer-state answer))) t))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpnj-rotation-restart-succeeds-bound
                          (plan (fn-bpnr-published-plan st generation ck))
                          (fresh (fn-bpnr-open-fresh st))
                          (seeded (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)))
                          (event (fn-bpnr-recover-auto-event (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)) nil :ready nil (fn-bpnr-published-plan st generation ck)))
                          (served (append (fn-bprpf-admit-recovery (fn-bpnr-recover-auto-event (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)) nil :ready nil (fn-bpnr-published-plan st generation ck)) profile) (list domain)))
                          (answer (fn-bpnj-step (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)) (append (fn-bprpf-admit-recovery (fn-bpnr-recover-auto-event (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)) nil :ready nil (fn-bpnr-published-plan st generation ck)) profile) (list domain))))))
           :in-theory (theory 'minimal-theory))))

;; PREMISE-EXCESS-D: the host establishes fn-bpnp-clock-domain-admitsp.
;; host/native/bp-service.lisp builds the served recovery event as the
;; profile-admitted recover-auto event with ACL2's clock-domain plan appended
;; (fn-bphp-recover-auto-event, equal to fn-bpnr-recover-auto-event by
;; fn-bphp-recover-auto-event-is-bpnr).  Of that event the premise of the
;; rotation-restart keystones above holds exactly when the plan is :same, or
;; :initialize over a namespace with no lifecycle records and no received
;; rows; a :fence plan never admits.
(local
 (defthm fn-bpnp-cdm-admit-recovery-keeps-the-shape
   (implies (and (true-listp e) (equal (len e) 6))
            (and (true-listp (fn-bprpf-admit-recovery e profile))
                 (equal (len (fn-bprpf-admit-recovery e profile)) 6)
                 (equal (nth 2 (fn-bprpf-admit-recovery e profile)) (nth 2 e))
                 (equal (nth 5 (fn-bprpf-admit-recovery e profile)) (nth 5 e))))
   :hints (("Goal" :in-theory (enable fn-bprpf-admit-recovery)))))

(local
 (defthm fn-bpnp-cdm-recover-event-shape
   (and (true-listp (fn-bpnr-recover-auto-event st records sequence rows gplan))
        (equal (len (fn-bpnr-recover-auto-event st records sequence rows gplan)) 6)
        (equal (nth 2 (fn-bpnr-recover-auto-event st records sequence rows gplan)) records)
        (equal (nth 5 (fn-bpnr-recover-auto-event st records sequence rows gplan)) (len rows)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-bpnr-recover-auto-event)
                                       (theory 'ground-zero))))))

(local
 (defthm fn-bpnp-cdm-bpn-nth-is-nth
   (implies (natp n) (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car nth)))))

(local
 (defthm fn-bpnp-cdm-same-plan-carries-a-boot-id
   (let ((plan (fn-bpnf-clock-domain-plan saved present observed legacy lock final-absent)))
     (implies (equal (fn-bpnf-clock-domain-plan-status plan) :same)
              (consp (nth 1 plan))))
   :hints (("Goal" :in-theory (enable fn-bpnf-clock-domain-plan
                                      fn-bpnf-clock-domain-plan-status
                                      fn-bpcd-observed-id fn-bpcd-boot-idp)))))

(local
 (defthm fn-bpnp-cdm-nth-of-append
   (implies (natp n)
            (equal (nth n (append a b))
                   (if (< n (len a)) (nth n a) (nth (- n (len a)) b))))
   :hints (("Goal" :induct (nth n a) :in-theory (enable nth append len)))))

(defthm fn-bpnp-hosted-recovery-admits-the-same-or-a-fresh-domain
  (let ((plan (fn-bpnf-clock-domain-plan saved present observed legacy lock final-absent))
        (event (fn-bprpf-admit-recovery
                (fn-bpnr-recover-auto-event st records sequence rows gplan) profile)))
    (implies (or (equal (fn-bpnf-clock-domain-plan-status plan) :same)
                 (and (equal (fn-bpnf-clock-domain-plan-status plan) :initialize)
                      (null records)
                      (equal (len rows) 0)))
             (fn-bpnp-clock-domain-admitsp (append event (list plan)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnp-clock-domain-admitsp fn-cbor-ag-car
                            fn-bpnf-clock-domain-plan-status)
                           (fn-bpnf-clock-domain-plan fn-bprpf-admit-recovery
                            fn-bpnr-recover-auto-event))
           :use ((:instance fn-bpnp-cdm-same-plan-carries-a-boot-id)
                 (:instance fn-bpnp-cdm-admit-recovery-keeps-the-shape
                            (e (fn-bpnr-recover-auto-event st records sequence rows gplan)))))))

(defthm fn-bpnp-hosted-recovery-admits-only-the-same-or-a-fresh-domain
  (let ((plan (fn-bpnf-clock-domain-plan saved present observed legacy lock final-absent))
        (event (fn-bprpf-admit-recovery
                (fn-bpnr-recover-auto-event st records sequence rows gplan) profile)))
    (implies (fn-bpnp-clock-domain-admitsp (append event (list plan)))
             (or (equal (fn-bpnf-clock-domain-plan-status plan) :same)
                 (and (equal (fn-bpnf-clock-domain-plan-status plan) :initialize)
                      (null records)
                      (equal (len rows) 0)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnp-clock-domain-admitsp fn-cbor-ag-car
                            fn-bpnf-clock-domain-plan-status)
                           (fn-bpnf-clock-domain-plan fn-bprpf-admit-recovery
                            fn-bpnr-recover-auto-event))
           :use ((:instance fn-bpnp-cdm-admit-recovery-keeps-the-shape
                            (e (fn-bpnr-recover-auto-event st records sequence rows gplan)))))))
