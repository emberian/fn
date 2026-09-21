; Totality boundaries for actual FNFD emission.  The abstract feed keeps
; natural counters; the port profile below is the separate finite wire domain.
(in-package "ACL2")
(include-book "feed-correspondence")
(local (include-book "arithmetic/top" :dir :system))
; Keep the codec entry point closed globally.  Port acceptance calls it as the
; executable boundary; opening it while proving unrelated tuple facts creates
; a large eleven-kind case split.  Individual transition proofs name exactly
; the vocabulary they need in their hints.
(local (in-theory (enable fn-feed-invariants-vocabulary)))

; The new timed retry record carries precisely the observation consumed by the
; live back-off transition.  This bridge is what makes the following drop
; record admissible after its preceding retry, rather than merely well formed.
(defthm fn-feed-apply-live-retry-is-back-off
  (implies (fn-feedp f)
           (equal
            (fn-feed-apply-record
             f :feed-retry
             (list (fn-feed-peer f) msgid
                   (fn-feed-state-attempt
                    (fn-feed-state-of msgid (fn-feed-queue f)))
                   code (nfix (fn-clock-monotonic obs))))
            (fn-feed-back-off f msgid obs)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-apply-record fn-feed-back-off fn-clock-observation
     fn-clock-monotonic fn-feed-record-peer fn-feed-record-msgid
     fn-feed-record-nat fn-frame-item)
    (fn-feedp fn-feed-with-queue fn-feed-with-backoff fn-feed-queue-requeue
     fn-feed-backoff-delay fn-feed-find fn-feed-state-of
     fn-feed-state-inflightp))
           :use ((:instance fn-feed-back-off-uses-only-monotonic-observation
                            (msgid msgid))))))

; Every batch actually selected by a parsed reply is admissible in the replay
; state it starts from.  This is over the emitter used by the owner wrapper,
; rather than the legacy reply-record convenience constructor.
(defthm fn-feed-observe-records-are-driven
  (implies (and (fn-feedp f)
                (fn-feed-journalp (fn-feed-observe-records f response obs)))
           (fn-feed-drivenp f (fn-feed-observe-records f response obs)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-observe-records fn-feed-drivenp fn-feed-record-drivenp fn-feed-journalp
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values
     fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat fn-frame-item
     fn-feed-back-off fn-feed-give-up fn-feed-retry-exhaustedp)
    (fn-feedp fn-feed-journal-entryp fn-feed-apply-record fn-feed-state-of
     fn-feed-state-inflightp fn-feed-offeredp fn-feed-droppedp
     fn-feed-state-attempt fn-feed-find fn-feed-with-queue fn-feed-with-backoff
     fn-feed-queue-requeue fn-feed-backoff-delay))
           :use ((:instance fn-feed-apply-live-retry-is-back-off
                            (msgid (fn-feed-response-msgid response))
                            (code (fn-feed-response-code response)))))))

; Port readiness contains the journal grammar check; its extra payload test is
; what separates an abstractly well-formed feed record from one FNFD can emit.
(defthm fn-feed-record-portp-implies-journal-entryp
  (implies (fn-feed-record-portp entry)
           (fn-feed-journal-entryp entry))
  :hints (("Goal" :in-theory (enable fn-feed-record-portp))))

(defthm fn-feed-records-portp-implies-journalp
  (implies (fn-feed-records-portp records)
           (fn-feed-journalp records))
  :hints (("Goal" :induct (fn-feed-records-portp records)
           :in-theory (enable fn-feed-records-portp fn-feed-journalp))))

; This port-profile version is the live emitter theorem used before record
; publication: any accepted reply batch is both replay-admissible and finite
; enough to serialize.  The all-natural feed remains a separate model.
(defthm fn-feed-observe-port-records-are-driven
  (implies (and (fn-feedp f)
                (fn-feed-records-portp (fn-feed-observe-records f response obs)))
           (fn-feed-drivenp f (fn-feed-observe-records f response obs)))
  :hints (("Goal" :use ((:instance fn-feed-observe-records-are-driven)
                         (:instance fn-feed-records-portp-implies-journalp
                                    (records (fn-feed-observe-records f response obs)))))))

; This is deliberately a direct boundary check, not a separately proved
; approximation to encoding.  The host-specific sealing bridge still needs
; its own equation to this ACL2 subject.
(defthm fn-feed-record-portp-uses-bounded-encoder
  (implies (fn-feed-record-portp entry)
           (not (equal (fn-feed-encode (fn-feed-journal-kind entry)
                                       (fn-feed-journal-values entry)
                                       *fn-feed-port-digest*)
                       :bad)))
  :hints (("Goal" :in-theory (enable fn-feed-record-portp))))

; These are definition bridges for the approved port-step tuple.  They name
; the exact existing transition/effect subjects an owner adapter must equate
; to its host-facing calls; no host adoption is claimed by this proof book.
(defthm fn-feed-live-port-step-accepted-unfolds
  (implies (and (fn-feedp f)
                (fn-feed-records-portp (fn-feed-live-records f event)))
           (and (equal (fn-feed-port-step-status (fn-feed-live-port-step f event))
                       :accepted)
                (equal (fn-feed-port-step-feed (fn-feed-live-port-step f event))
                       (fn-feed-live-next f event))
                (equal (fn-feed-port-step-records (fn-feed-live-port-step f event))
                       (fn-feed-live-records f event))
                (equal (fn-feed-port-step-effects (fn-feed-live-port-step f event))
                       (fn-feed-live-effects f event))))
  :hints (("Goal" :in-theory (enable fn-feed-live-port-step
                                      fn-feed-port-step-status
                                      fn-feed-port-step-feed
                                      fn-feed-port-step-records
                                      fn-feed-port-step-effects))))

(defthm fn-feed-live-port-step-refusal-preserves-work
  (implies (not (and (fn-feedp f)
                     (fn-feed-records-portp (fn-feed-live-records f event))))
           (and (equal (fn-feed-port-step-status (fn-feed-live-port-step f event))
                       :refused)
                (equal (fn-feed-port-step-feed (fn-feed-live-port-step f event)) f)
                (equal (fn-feed-port-step-records (fn-feed-live-port-step f event)) nil)
                (equal (fn-feed-port-step-effects (fn-feed-live-port-step f event)) nil)))
  :hints (("Goal" :in-theory (enable fn-feed-live-port-step
                                      fn-feed-port-step-status
                                      fn-feed-port-step-feed
                                      fn-feed-port-step-records
                                      fn-feed-port-step-effects))))

(in-theory (disable fn-feed-observe-records-are-driven))
