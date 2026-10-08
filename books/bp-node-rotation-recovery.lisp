; Machine-level recovery of the published BP rotation checkpoint.
(in-package "ACL2")
(include-book "bp-node-rotation")
(include-book "bp-node-job-offer")
(include-book "bp-recovery-profile")
(set-verify-guards-eagerness 0)

(defthm fn-bpnj-recovery-is-the-progress-step
  (implies (equal (fn-cbor-ag-car event) :recover-fnbs)
           (equal (fn-bpnj-step st event) (fn-bpnp-step st event)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-step fn-bpnj-unnamed-result-p (:e equal)) (theory 'minimal-theory)))))

(defthm fn-bprpf-admitted-recovery-is-the-event
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

(defthm fn-bpnr-rotation-foundation-restart-is-ready-bound
  (implies
   (and (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
        (fn-bpn-machine-invariantp (fn-bpnf-base st))
        (fn-bpnr-recovery-replayp
         0 (+ 1 (fn-bpnf-epoch st))
         (list :ready (fn-bpnf-held-list st) (fn-bpnf-handoffs st)
               (cons (fn-bpnf-epoch st) 0) (fn-bpnf-next-arrival st))
         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
         (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))
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
           :use ((:instance fn-bpnp-rotate-step-proposes-only-own-projection)
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

(defthm fn-bprpf-admission-preserves-admitted-event
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
        (fn-bpnr-recovery-replayp
         0 (+ 1 (fn-bpnf-epoch st))
         (list :ready (fn-bpnf-held-list st) (fn-bpnf-handoffs st)
               (cons (fn-bpnf-epoch st) 0) (fn-bpnf-next-arrival st))
         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
         (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))
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
                 (:instance fn-bprpf-admission-preserves-admitted-event)
                 (:instance fn-bpnj-recovery-is-the-progress-step (st seeded) (event served))
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
                  (fn-bpnr-recovery-replayp
         0 (+ 1 (fn-bpnf-epoch st))
         (list :ready (fn-bpnf-held-list st) (fn-bpnf-handoffs st)
               (cons (fn-bpnf-epoch st) 0) (fn-bpnf-next-arrival st))
         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
         (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))
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
