; Equality of recovered base machines, including owed jobs, across rotation.
; Received rows may follow the checkpoint; lifecycle records here are the
; bounded history covered by its seed. The conclusion includes success of
; both served recoveries.
(in-package "ACL2")
(include-book "bp-node-rotation-recovery")
(set-verify-guards-eagerness 0)


(defthm fn-bpn-restart-step-from-uses-config-and-limits-by-definition
  (implies (and (equal (fn-bpn-machine-state-config a) (fn-bpn-machine-state-config b))
                (equal (fn-bpn-machine-state-max-jobs a) (fn-bpn-machine-state-max-jobs b))
                (equal (fn-bpn-machine-state-max-octets a) (fn-bpn-machine-state-max-octets b)))
           (equal (fn-bpn-restart-step-from a records seq jobs token)
                  (fn-bpn-restart-step-from b records seq jobs token)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                             '(fn-bpn-restart-step-from fn-bpn-state-with)
                             (theory 'minimal-theory)))))

(defthm fn-bpnr-selected-seed-keeps-config-and-limits
  (implies (and (fn-bpnr-checkpointp ck)
                (fn-bpn-machine-statep (fn-bpnf-base fresh))
                (fn-bpn-machine-statep (fn-bpnr-replay-base ck (fn-bpnf-base fresh))))
           (let ((seeded (fn-bpnr-seed-state fresh (list :selected ck))))
             (and (equal (fn-bpn-machine-state-config (fn-bpnf-base seeded))
                         (fn-bpn-machine-state-config (fn-bpnf-base fresh)))
                  (equal (fn-bpn-machine-state-max-jobs (fn-bpnf-base seeded))
                         (fn-bpn-machine-state-max-jobs (fn-bpnf-base fresh)))
                  (equal (fn-bpn-machine-state-max-octets (fn-bpnf-base seeded))
                         (fn-bpn-machine-state-max-octets (fn-bpnf-base fresh))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnr-seed-state fn-bpnr-plan-checkpoint
                         fn-bpnr-replay-base fn-bpn-state-with-accessors
                         fn-bpnf-with-base fn-bpnf-state-with-arrival fn-bpnf-base
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         zp natp (:e zp) (:e natp) (:e binary-+) (:e unary--) (:e equal))
                       (theory 'minimal-theory)))))

(defthm fn-bpnr-initial-replay-properties
 (implies (and (fn-bpn-machine-statep base)
               (<= (len records) *fn-bpn-machine-max-records*))
   (let ((rep (nth 1 (fn-bpn-replay-records (fn-bpn-initial-machine-state
          (fn-bpn-machine-state-config base)
          (fn-bpn-machine-state-max-jobs base)
          (fn-bpn-machine-state-max-octets base)) records))))
     (and (fn-bpn-machine-invariantp rep)
          (equal (fn-bpn-machine-state-config rep) (fn-bpn-machine-state-config base))
          (equal (fn-bpn-machine-state-max-jobs rep) (fn-bpn-machine-state-max-jobs base))
          (equal (fn-bpn-machine-state-max-octets rep) (fn-bpn-machine-state-max-octets base)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bpn-machine-statep-components (st base))
                (:instance fn-bpn-initial-machine-state-has-invariant (config (fn-bpn-machine-state-config base))
         (max-jobs (fn-bpn-machine-state-max-jobs base))
         (max-octets (fn-bpn-machine-state-max-octets base)))
                (:instance fn-bpn-next-token-of-initial-machine-state (config (fn-bpn-machine-state-config base))
         (max-jobs (fn-bpn-machine-state-max-jobs base))
         (max-octets (fn-bpn-machine-state-max-octets base)))
                (:instance fn-bpn-limits-of-initial-machine-state (config (fn-bpn-machine-state-config base))
         (max-jobs (fn-bpn-machine-state-max-jobs base))
         (max-octets (fn-bpn-machine-state-max-octets base)))
                (:instance fn-bpn-config-of-initial-machine-state (config (fn-bpn-machine-state-config base))
         (max-jobs (fn-bpn-machine-state-max-jobs base))
         (max-octets (fn-bpn-machine-state-max-octets base)))
                (:instance fn-bpn-replay-records-preserves-machine-invariant (st (fn-bpn-initial-machine-state
          (fn-bpn-machine-state-config base)
          (fn-bpn-machine-state-max-jobs base)
          (fn-bpn-machine-state-max-octets base))))
                (:instance fn-bpn-replay-records-keeps-config-and-limits (st (fn-bpn-initial-machine-state
          (fn-bpn-machine-state-config base)
          (fn-bpn-machine-state-max-jobs base)
          (fn-bpn-machine-state-max-octets base)))))
          :in-theory (union-theories '((:e binary-+)) (theory 'minimal-theory)))))

(defthm fn-bpnr-open-fresh-base-is-initial-by-definition
 (equal (fn-bpnf-base (fn-bpnr-open-fresh st))
        (fn-bpn-initial-machine-state
         (fn-bpn-machine-state-config (fn-bpnf-base st))
         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
         (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
 :hints (("Goal" :in-theory (union-theories
                            '(fn-bpnr-open-fresh fn-bpnf-initial-state fn-bpnf-state
                              fn-bpnf-state-with-arrival fn-bpnf-base fn-bpn-nth fn-cbor-ag-car
                              car-cons cdr-cons zp natp (:e zp) (:e natp)
                              (:e binary-+) (:e unary--) (:e equal))
                            (theory 'minimal-theory)))))

(defthm fn-bpn-initial-state-has-no-jobs
 (null (fn-bpn-machine-state-jobs (fn-bpn-initial-machine-state config jobs octets)))
 :hints (("Goal" :in-theory (enable fn-bpn-initial-machine-state))))

(defthm fn-bpnr-open-fresh-empty-base
 (implies (fn-bpn-machine-statep (fn-bpnf-base st))
          (and (null (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnr-open-fresh st))))
               (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnr-open-fresh st))) 0)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bpn-machine-statep-components (st (fn-bpnf-base st)))
                (:instance fn-bpn-next-token-of-initial-machine-state
                           (config (fn-bpn-machine-state-config (fn-bpnf-base st)))
                           (max-jobs (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))
                           (max-octets (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
                (:instance fn-bpnr-open-fresh-base-is-initial-by-definition)
                (:instance fn-bpn-initial-state-has-no-jobs
                           (config (fn-bpn-machine-state-config (fn-bpnf-base st)))
                           (jobs (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))
                           (octets (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))))
          :in-theory (theory 'minimal-theory))))

(defthm fn-bpnr-selected-open-seed-fields-from-bound
  (implies
   (and (fn-bpnr-checkpointp ckk)
        (fn-bpn-machine-statep (fn-bpnf-base st))
        (<= (fn-bpn-machine-state-next-token (fn-bpnf-base st)) *fn-bpn-machine-max-records*)
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


(defthm fn-bpnr-published-restart-equals-full-restart
 (implies
  (and (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
       (equal fresh (fn-bpnr-open-fresh st))
       (<= (len records) *fn-bpn-machine-max-records*)
       (equal replay
              (fn-bpn-replay-records
               (fn-bpn-initial-machine-state
                (fn-bpn-machine-state-config (fn-bpnf-base fresh))
                (fn-bpn-machine-state-max-jobs (fn-bpnf-base fresh))
                (fn-bpn-machine-state-max-octets (fn-bpnf-base fresh))) records))
       (equal (car replay) :ready)
       (equal (fn-bpn-machine-state-jobs (fn-bpnf-base st))
              (fn-bpn-machine-state-jobs (nth 1 replay)))
       (equal (fn-bpn-machine-state-next-token (fn-bpnf-base st))
              (fn-bpn-machine-state-next-token (nth 1 replay)))
       (equal seeded (fn-bpnr-seed-state fresh (fn-bpnr-published-plan st generation ck))))
  (equal (fn-bpn-restart-step-from
          (fn-bpnf-base seeded) nil :ready
          (fn-bpn-machine-state-jobs (fn-bpnf-base seeded))
          (fn-bpn-machine-state-next-token (fn-bpnf-base seeded)))
         (fn-bpn-restart-step (fn-bpnf-base fresh) records :ready)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bpnp-rotate-step-proposes-only-own-projection)
                (:instance fn-bpnr-published-plan-is-the-rotation-checkpoint)
                (:instance fn-bpnr-rotation-checkpoint-is-a-checkpoint (e (fn-bpnf-epoch st)))
                (:instance fn-bpnr-rotation-checkpoint-fields (e (fn-bpnf-epoch st)))
                (:instance fn-bpnr-open-fresh-fields)
                (:instance fn-bpnr-seed-state-over-a-selected-checkpoint
                           (ckk (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))
                           (other (fn-bpnf-base st)))
                (:instance fn-bpnr-replay-base-is-a-machine-state
                           (ck (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))
                           (base (fn-bpnf-base fresh)) (other (fn-bpnf-base st)))
                (:instance fn-bpnr-selected-seed-keeps-config-and-limits
                           (ck (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st))))
                (:instance fn-bpn-restart-step-from-uses-config-and-limits-by-definition
                           (a (fn-bpnf-base seeded)) (b (fn-bpnf-base fresh))
                           (records nil) (seq :ready)
                           (jobs (fn-bpn-machine-state-jobs (nth 1 replay)))
                           (token (fn-bpn-machine-state-next-token (nth 1 replay))))
                (:instance fn-bpn-restart-from-the-replayed-seed-is-the-restart
                           (st (fn-bpnf-base fresh))))
          :in-theory (union-theories
                      '(fn-bpnr-checkpoint-of-statep fn-bpnp-rotation-quiescentp
                        fn-frame-natp)
                      (theory 'minimal-theory)))))

(defthm fn-bpnr-equal-restarts-give-equal-recovered-bases
 (implies
  (and (fn-bpn-machine-invariantp (fn-bpnf-base b))
       (equal (fn-bpn-restart-step-from
               (fn-bpnf-base a) records :ready
               (fn-bpn-machine-state-jobs (fn-bpnf-base a))
               (fn-bpn-machine-state-next-token (fn-bpnf-base a)))
              (fn-bpn-restart-step-from
               (fn-bpnf-base b) nil :ready
               (fn-bpn-machine-state-jobs (fn-bpnf-base b))
               (fn-bpn-machine-state-next-token (fn-bpnf-base b))))
       (fn-bpnr-recovery-replayp (fn-bpnf-epoch a) ae ap
                               (fn-bpn-machine-state-max-jobs (fn-bpnf-base b))
                               (fn-bpn-machine-state-max-octets (fn-bpnf-base b)))
       (fn-bpnr-recovery-replayp (fn-bpnf-epoch b) be bp
                               (fn-bpn-machine-state-max-jobs (fn-bpnf-base b))
                               (fn-bpn-machine-state-max-octets (fn-bpnf-base b))))
  (let ((aa (fn-bpnf-recover-fnbs-step a ae records :ready ap))
        (ba (fn-bpnf-recover-fnbs-step b be nil :ready bp)))
    (and (equal (fn-bpnf-base (fn-bpnf-answer-state aa))
                (fn-bpnf-base (fn-bpnf-answer-state ba)))
         (equal (car (car (fn-bpnf-answer-effects aa))) :restart-ready)
         (equal (car (car (fn-bpnf-answer-effects ba))) :restart-ready))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bpn-machine-invariant-components (st (fn-bpnf-base b)))
                (:instance fn-bpn-restart-own-seed-is-ready-fast (st (fn-bpnf-base b)))
                (:instance fn-bpn-restart-own-seed-keeps-limits (st (fn-bpnf-base b)))
                (:instance fn-bpn-restart-step-from-of-own-seed-keeps-owed-work (st (fn-bpnf-base b)))
                (:instance fn-bpnr-foundation-installs-admissible-replay
                           (st a) (epoch ae) (replay ap))
                (:instance fn-bpnr-foundation-installs-admissible-replay
                           (st b) (epoch be) (replay bp) (records nil)))
          :in-theory (union-theories '(car-cons) (theory 'minimal-theory)))))

(defthm fn-bpnj-six-field-recovery-keeps-foundation-answer
 (implies
  (equal (car (car (fn-bpnf-answer-effects
                   (fn-bpnf-recover-fnbs-step st epoch records :ready replay))))
         :restart-ready)
  (let ((answer (fn-bpnj-step st (list :recover-fnbs epoch records :ready replay count)))
        (inner (fn-bpnf-recover-fnbs-step st epoch records :ready replay)))
    (and (equal (fn-bpnf-base (fn-bpnf-answer-state answer))
                (fn-bpnf-base (fn-bpnf-answer-state inner)))
         (equal (fn-bpnf-answer-effects answer) (fn-bpnf-answer-effects inner)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bpnj-recovery-is-the-progress-step-by-definition
                           (event (list :recover-fnbs epoch records :ready replay count)))
                (:instance fn-bpnp-recovery-keeps-foundation-base-and-effects
                           (event (list :recover-fnbs epoch records :ready replay count))))
          :in-theory (union-theories
                      '(fn-bpnp-domain-recover-eventp fn-bpn-nth fn-cbor-ag-car
                        len true-listp car-cons cdr-cons zp natp (:e zp) (:e natp)
                        (:e binary-+) (:e unary--) (:e equal) (:e true-listp))
                      (theory 'minimal-theory)))))

(defthm fn-bpnr-checkpoint-recovery-equals-full-machine-bound
 (implies
  (and (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
       (equal fresh (fn-bpnr-open-fresh st))
       (<= (len records) *fn-bpn-machine-max-records*)
       (equal replay
              (fn-bpn-replay-records
               (fn-bpn-initial-machine-state
                (fn-bpn-machine-state-config (fn-bpnf-base fresh))
                (fn-bpn-machine-state-max-jobs (fn-bpnf-base fresh))
                (fn-bpn-machine-state-max-octets (fn-bpnf-base fresh))) records))
       (equal (car replay) :ready)
       (equal (fn-bpn-machine-state-jobs (fn-bpnf-base st))
              (fn-bpn-machine-state-jobs (nth 1 replay)))
       (equal (fn-bpn-machine-state-next-token (fn-bpnf-base st))
              (fn-bpn-machine-state-next-token (nth 1 replay)))
       (equal projected (fn-bpnr-seed-state fresh
                         (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
       (equal expected (fn-bpnr-recover-auto-event
                        projected nil :ready suffix
                        (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
       (equal full-event (fn-bpnr-recover-auto-event fresh records :ready
                                                   (append rows0 suffix) '(:none)))
       (fn-bpnr-recovery-replayp
        (fn-bpnf-epoch fresh) (fn-bpn-nth 1 full-event) (fn-bpn-nth 4 full-event)
        (fn-bpn-machine-state-max-jobs (fn-bpnf-base projected))
        (fn-bpn-machine-state-max-octets (fn-bpnf-base projected)))
       (fn-bpnr-recovery-replayp
        (fn-bpnf-epoch projected) (fn-bpn-nth 1 expected) (fn-bpn-nth 4 expected)
        (fn-bpn-machine-state-max-jobs (fn-bpnf-base projected))
        (fn-bpn-machine-state-max-octets (fn-bpnf-base projected)))
       (equal plan (fn-bpnr-published-plan st generation ck))
       (equal seeded (fn-bpnr-seed-state fresh plan))
       (equal event (fn-bpnr-recover-auto-event seeded nil :ready suffix plan)))
  (let ((full-answer (fn-bpnj-step fresh full-event))
        (checkpoint-answer (fn-bpnj-step seeded event)))
    (and (equal (fn-bpnf-base (fn-bpnf-answer-state checkpoint-answer))
                (fn-bpnf-base (fn-bpnf-answer-state full-answer)))
         (equal (car (car (fn-bpnf-answer-effects checkpoint-answer))) :restart-ready)
         (equal (car (car (fn-bpnf-answer-effects full-answer))) :restart-ready))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bpnp-rotate-step-proposes-only-own-projection)
                (:instance fn-bpnr-published-plan-is-the-rotation-checkpoint)
                (:instance fn-bpnr-rotation-checkpoint-is-a-checkpoint (e (fn-bpnf-epoch st)))
                (:instance fn-bpnr-rotation-checkpoint-fields (e (fn-bpnf-epoch st)))
                (:instance fn-bpnr-open-fresh-fields)
                (:instance fn-bpnr-open-fresh-empty-base)
                (:instance fn-bpnr-initial-replay-properties (base (fn-bpnf-base fresh)))
                (:instance fn-bpn-machine-invariant-components (st (nth 1 replay)))
                (:instance fn-bpnr-selected-open-seed-fields-from-bound
                           (ckk (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st))))
                (:instance fn-bpnr-published-restart-equals-full-restart)
                (:instance fn-bpnr-equal-restarts-give-equal-recovered-bases
                           (a fresh) (b seeded)
                           (ae (fn-bpn-nth 1 full-event)) (ap (fn-bpn-nth 4 full-event))
                           (be (fn-bpn-nth 1 event)) (bp (fn-bpn-nth 4 event)))
                (:instance fn-bpnj-six-field-recovery-keeps-foundation-answer
                           (st fresh) (epoch (fn-bpn-nth 1 full-event))
                           (replay (fn-bpn-nth 4 full-event)) (count (fn-bpn-nth 5 full-event)))
                (:instance fn-bpnj-six-field-recovery-keeps-foundation-answer
                           (st seeded) (epoch (fn-bpn-nth 1 event)) (records nil)
                           (replay (fn-bpn-nth 4 event)) (count (fn-bpn-nth 5 event))))
          :in-theory (union-theories
                      '(fn-bpnr-checkpoint-of-statep fn-bpnp-rotation-quiescentp
                        fn-frame-natp fn-bpn-restart-step fn-bpnr-recover-auto-event
                        fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                        zp natp (:e zp) (:e natp) (:e binary-+) (:e unary--) (:e equal))
                      (theory 'minimal-theory)))))

(defthm fn-bpnr-checkpoint-recovery-equals-full-machine
  (let* ((fresh (fn-bpnr-open-fresh st))
         (replay (fn-bpn-replay-records
               (fn-bpn-initial-machine-state
                (fn-bpn-machine-state-config (fn-bpnf-base fresh))
                (fn-bpn-machine-state-max-jobs (fn-bpnf-base fresh))
                (fn-bpn-machine-state-max-octets (fn-bpnf-base fresh))) records))
         (projected (fn-bpnr-seed-state fresh
                         (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
         (expected (fn-bpnr-recover-auto-event
                        projected nil :ready suffix
                        (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
         (full-event (fn-bpnr-recover-auto-event fresh records :ready (append rows0 suffix) '(:none)))
         (plan (fn-bpnr-published-plan st generation ck))
         (seeded (fn-bpnr-seed-state fresh plan))
         (event (fn-bpnr-recover-auto-event seeded nil :ready suffix plan)))
    (implies (and (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint)
                  (<= (len records) *fn-bpn-machine-max-records*)
                  (equal (car replay) :ready)
                  (equal (fn-bpn-machine-state-jobs (fn-bpnf-base st))
              (fn-bpn-machine-state-jobs (nth 1 replay)))
                  (equal (fn-bpn-machine-state-next-token (fn-bpnf-base st))
              (fn-bpn-machine-state-next-token (nth 1 replay)))
                  (fn-bpnr-recovery-replayp
        (fn-bpnf-epoch fresh) (fn-bpn-nth 1 full-event) (fn-bpn-nth 4 full-event)
        (fn-bpn-machine-state-max-jobs (fn-bpnf-base projected))
        (fn-bpn-machine-state-max-octets (fn-bpnf-base projected)))
                  (fn-bpnr-recovery-replayp
        (fn-bpnf-epoch projected) (fn-bpn-nth 1 expected) (fn-bpn-nth 4 expected)
        (fn-bpn-machine-state-max-jobs (fn-bpnf-base projected))
        (fn-bpn-machine-state-max-octets (fn-bpnf-base projected))))
      (let ((full-answer (fn-bpnj-step fresh full-event))
        (checkpoint-answer (fn-bpnj-step seeded event)))
    (and (equal (fn-bpnf-base (fn-bpnf-answer-state checkpoint-answer))
                (fn-bpnf-base (fn-bpnf-answer-state full-answer)))
         (equal (car (car (fn-bpnf-answer-effects checkpoint-answer))) :restart-ready)
         (equal (car (car (fn-bpnf-answer-effects full-answer))) :restart-ready)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpnr-checkpoint-recovery-equals-full-machine-bound
                          (fresh (fn-bpnr-open-fresh st))
                          (replay (fn-bpn-replay-records
               (fn-bpn-initial-machine-state
                (fn-bpn-machine-state-config (fn-bpnf-base (fn-bpnr-open-fresh st)))
                (fn-bpn-machine-state-max-jobs (fn-bpnf-base (fn-bpnr-open-fresh st)))
                (fn-bpn-machine-state-max-octets (fn-bpnf-base (fn-bpnr-open-fresh st)))) records))
                          (projected (fn-bpnr-seed-state (fn-bpnr-open-fresh st)
                         (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
                          (expected (fn-bpnr-recover-auto-event
                        (fn-bpnr-seed-state (fn-bpnr-open-fresh st)
                         (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))) nil :ready suffix
                        (list :selected (fn-bpnr-rotation-checkpoint ck (fn-bpnf-epoch st)))))
                          (full-event (fn-bpnr-recover-auto-event (fn-bpnr-open-fresh st) records :ready (append rows0 suffix) '(:none)))
                          (plan (fn-bpnr-published-plan st generation ck))
                          (seeded (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)))
                          (event (fn-bpnr-recover-auto-event (fn-bpnr-seed-state (fn-bpnr-open-fresh st) (fn-bpnr-published-plan st generation ck)) nil :ready suffix (fn-bpnr-published-plan st generation ck)))))
           :in-theory (theory 'minimal-theory))))
