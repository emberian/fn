; Connect the operator-local key view to the actual Store completion path.
(in-package "ACL2")
(include-book "hybrid-lifecycle")
(include-book "store-node-resolution")

(defun fn-hls-current-enrollment (s requested)
  (declare (xargs :guard t))
  (fn-hl-current-enrollment requested (fn-sn-keyring-snapshots s)))

; Identity completion is the sole live Store update of the carried snapshot
; list. This projection exposes the exact identity interpreter result to the
; host-facing selector without validating the full Store on a served path.
(defthm fn-hls-finish-identity-current-enrollment
  (equal (fn-hls-current-enrollment
          (fn-sn-finish-identity s files record node) requested)
         (fn-hl-current-enrollment
          requested
          (fn-stxk-context-snapshots
           (fn-replay-identity-step (fn-sn-identity-context s) record))))
  :hints (("Goal" :in-theory
           (e/d (fn-hls-current-enrollment fn-sn-finish-identity)
                (fn-hl-current-enrollment fn-replay-identity-step
                 fn-stxk-p fn-stxe-p fn-stxa-p)))))

(defthm fn-hls-current-enrollment-of-with-consumer
  (equal (fn-hls-current-enrollment (fn-sn-with-consumer s consumer) requested)
         (fn-hls-current-enrollment s requested))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

(defthm fn-hls-current-enrollment-of-with-topic
  (equal (fn-hls-current-enrollment (fn-sn-with-topic s topic) requested)
         (fn-hls-current-enrollment s requested))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

(defthm fn-hls-finish-snapshot-current-enrollment
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxk-p (fn-sn-completion-record s))
                (not (fn-store-retention-event-p
                      (fn-sn-completion-record s)))
                (not (fn-cpe-eventp (fn-sn-completion-record s)))
                (not (fn-th-topic-eventp (fn-sn-completion-record s))))
           (equal
            (fn-hls-current-enrollment (fn-sn-finish s) requested)
            (fn-hl-current-enrollment
             requested
             (fn-stxk-context-snapshots
              (fn-replay-identity-step
               (fn-sn-identity-context s)
               (fn-sn-completion-record s))))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-completion-enabledp fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp
                 fn-hls-current-enrollment fn-hl-current-enrollment
                 fn-replay-identity-step
                 fn-sn-finish-identity)))))

; A kind-3 record starts with a numeric Store sequence. Retention, consumer
; and topic events use disjoint leading tags. Keep their codecs closed in the
; completed-snapshot proof below.
(defthm fn-hls-snapshot-has-numeric-first-field
  (implies (fn-stxk-p event) (natp (car event)))
  :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxk-shapep
                                     fn-stxk-sequence fn-record-uint32p))))

(defthm fn-hls-snapshot-disjoint-from-other-store-events
  (implies (fn-stxk-p event)
           (and (not (fn-store-retention-event-p event))
                (not (fn-cpe-eventp event))
                (not (fn-th-topic-eventp event))))
  :hints (("Goal"
           :use (fn-hls-snapshot-has-numeric-first-field
                 (:instance fn-th-topic-event-is-not-stxk))
           :in-theory
           (e/d (fn-store-retention-event-p fn-store-event-nth
                  fn-cpe-eventp fn-cp-nth)
                (fn-stxk-p fn-th-topic-eventp)))))

; This is the completed Store-node statement: the same per-principal selector
; the host calls reads exactly the snapshot history returned by the identity
; interpreter for the durable event. The premise is the actual finish gate,
; not a hypothetical successful snapshot application.
(defthm fn-hls-finish-snapshot-from-maintained-state
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxk-p (fn-sn-completion-record s)))
           (equal
            (fn-hls-current-enrollment (fn-sn-finish s) requested)
            (fn-hl-current-enrollment
             requested
             (fn-stxk-context-snapshots
              (fn-replay-identity-step
               (fn-sn-identity-context s)
               (fn-sn-completion-record s))))))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s)))
                 (:instance fn-hls-finish-snapshot-current-enrollment))
           :in-theory
           (disable fn-sn-finish fn-hls-current-enrollment
                    fn-hl-current-enrollment fn-replay-identity-step
                    fn-stxk-p fn-sn-completion-enabledp))))

; A keyring snapshot changes the prospective local authority, not a recorded
; kind-4 verdict. The identity context used for one completion starts with no
; newly emitted verdicts, and the snapshot arm emits none.
(defthm fn-hls-snapshot-identity-step-has-no-new-verdict
  (implies (fn-stxk-p event)
           (equal (fn-stxk-context-verdicts
                   (fn-replay-identity-step
                    (fn-sn-identity-context s) event))
                  nil))
  :hints (("Goal" :in-theory
           (e/d (fn-replay-identity-step fn-sn-identity-context
                  fn-stxk-apply-snapshot fn-stxk-fault fn-stxk-context)
                (fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-hsig-keyring-snapshot-value
                 fn-replay-identity-advance)))))

(defthm fn-hls-finish-identity-snapshot-keeps-verdicts
  (implies (fn-stxk-p record)
           (equal (fn-sn-verdicts
                   (fn-sn-finish-identity s files record node))
                  (fn-sn-verdicts s)))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish-identity fn-replay-verdict-pairs)
                (fn-stxk-p fn-replay-identity-step
                 fn-sn-identity-context)))))

(defthm fn-hls-finish-snapshot-keeps-historical-verdicts
  (implies (fn-stxk-p (fn-sn-completion-record s))
           (equal (fn-sn-verdicts (fn-sn-finish s))
                  (fn-sn-verdicts s)))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-completion-enabledp fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-store-retention-event-p fn-cpe-eventp
                 fn-th-topic-eventp fn-sn-finish-identity)))))

; The derived event index is unrelated to author authority. Recovery installs
; the exact identity replay context through fn-sn-update-replayed before the
; topic, event-index and consumer projections are layered around it.
(defthm fn-hls-current-enrollment-of-with-event-index
  (equal (fn-hls-current-enrollment
          (fn-sn-with-event-index s event-index) requested)
         (fn-hls-current-enrollment s requested))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

(defthm fn-hls-current-enrollment-of-update-replayed
  (equal (fn-hls-current-enrollment
          (fn-sn-update-replayed s files node index identity-context)
          requested)
         (fn-hl-current-enrollment
          requested (fn-stxk-context-snapshots identity-context)))
  :hints (("Goal" :in-theory (enable fn-hls-current-enrollment))))

; A successful recovery recomputes the local author view from durable Store
; records. The phase premises identify the actual crash/replay branch; a
; pre-publication candidate is absent from those records, while a published
; kind-3 event is replayed even if live finish never ran.
(defthm fn-hls-successful-recover-current-enrollment
  (implies
   (and (fn-sn-statep s)
        (equal (fn-sf-phase (fn-sn-files s)) :replaying)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-recover s))) :recovering))
   (equal
    (fn-hls-current-enrollment (fn-sn-recover s) requested)
    (fn-hl-current-enrollment
     requested
     (fn-stxk-context-snapshots
      (fn-replay-identity
       (fn-sf-records
        (fn-sf-recover (fn-sn-files s)
                       (fn-sn-groups s) (fn-sn-capacity s))))))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sn-recover)
                (fn-sn-statep fn-sf-recover fn-replay-identity
                 fn-hls-current-enrollment fn-hl-current-enrollment
                 fn-cpe-projection-replay fn-th-prefix-project)))))

(defthm fn-hls-successful-recover-historical-verdicts
  (implies
   (and (fn-sn-statep s)
        (equal (fn-sf-phase (fn-sn-files s)) :replaying)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-recover s))) :recovering))
   (equal
    (fn-sn-verdicts (fn-sn-recover s))
    (fn-replay-verdict-pairs
     (fn-stxk-context-verdicts
      (fn-replay-identity
       (fn-sf-records
        (fn-sf-recover (fn-sn-files s)
                       (fn-sn-groups s) (fn-sn-capacity s))))))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sn-recover)
                (fn-sn-statep fn-sf-recover fn-replay-identity
                 fn-cpe-projection-replay fn-th-prefix-project)))))
