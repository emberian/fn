; Live feed transitions, their actual emitted records, and replay. Connection
; identity alone is transient; attempts, entry ticks, backoff and the queue
; survive in the durable projection. This is logical correspondence, not a
; theorem about physical files or socket acknowledgements.
(in-package "ACL2")
(include-book "peer-feed-invariants")
(include-book "feed-events")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable fn-feed-vocabulary fn-feed-invariants-vocabulary)))

(defthm fn-feed-projection-is-idempotent
  (equal (fn-feed-durable-projection (fn-feed-durable-projection f))
         (fn-feed-durable-projection f))
  :hints (("Goal" :in-theory (enable fn-feed-durable-projection fn-feed-with-conn))))

(defthm fn-feedp-of-durable-projection
  (implies (fn-feedp f) (fn-feedp (fn-feed-durable-projection f)))
  :hints (("Goal" :in-theory (enable fn-feed-durable-projection fn-feed-with-conn
                                    fn-feedp))))

(defthm fn-feed-projection-ignores-connection
  (equal (fn-feed-durable-projection (fn-feed-with-conn f conn))
         (fn-feed-durable-projection f))
  :hints (("Goal" :in-theory (enable fn-feed-durable-projection fn-feed-with-conn))))

(defthm fn-feed-enqueue-records-reconstruct-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-enqueue-records f msgid tick)))
                  (fn-feed-durable-projection (fn-feed-enqueue f msgid tick))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-replay fn-feed-apply-record fn-feed-enqueue-records
     fn-feed-enqueue fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values fn-frame-item)
    (fn-feedp fn-feed-durable-projection fn-feed-with-queue)))))

(defthm fn-feed-valid-numeric-components
  (implies (fn-feedp f)
           (and (posp (fn-feed-next-attempt f))
                (natp (fn-feed-backoff-until f))))
  :hints (("Goal" :in-theory (enable fn-feedp))))

(defthm fn-feed-tick-records-reconstruct-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-tick-records f obs)))
                  (fn-feed-durable-projection (mv-nth 0 (fn-feed-tick-step f obs)))))
  :hints (("Goal" :use fn-feed-selection-is-queued
           :in-theory (e/d
    (fn-feed-replay fn-feed-apply-record fn-feed-tick-records
     fn-feed-tick-step fn-feed-offer fn-feed-selection
     fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values fn-frame-item)
    (fn-feedp fn-feed-durable-projection fn-feed-next-attempt fn-feed-offered)))))

(defthm fn-feed-lost-records-reconstruct-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-lost-records f obs)))
                  (fn-feed-durable-projection (fn-feed-lost f obs))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-replay fn-feed-apply-record fn-feed-lost-records fn-feed-lost
     fn-clock-observation fn-clock-monotonic
     fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values fn-frame-item)
    (fn-feedp fn-feed-durable-projection fn-feed-with-backoff fn-feed-with-conn
     fn-feed-with-queue fn-feed-queue-requeue-inflight fn-feed-backoff-delay)))))

(defthm fn-feed-restart-records-reconstruct-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-restart-records f)))
                  (fn-feed-durable-projection (fn-feed-restart f))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-replay fn-feed-apply-record fn-feed-restart-records
     fn-feed-record-peer fn-feed-journal-entry fn-feed-journal-kind
     fn-feed-journal-values fn-frame-item)
    (fn-feedp fn-feed-durable-projection fn-feed-restart)))))

(defthm fn-feed-back-off-uses-only-monotonic-observation
  (equal (fn-feed-back-off f msgid
           (fn-clock-observation (nfix (fn-clock-monotonic obs)) 0 0 nil))
         (fn-feed-back-off f msgid obs))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-back-off fn-clock-observation fn-clock-monotonic)
    (fn-feedp fn-feed-with-queue fn-feed-with-backoff fn-feed-backoff-delay
     fn-feed-queue-requeue fn-feed-find fn-feed-state-of fn-feed-state-inflightp)))))

; The retry transition is deliberately a no-op when the reply does not name
; this feed's one in-flight entry.  This is the branch actual record emission
; suppresses, so it is a transition fact rather than a record-side premise.
(defthm fn-feed-back-off-without-inflight-is-identity
  (implies (and (fn-feedp f)
                (not (fn-feed-state-inflightp
                      (fn-feed-state-of msgid (fn-feed-queue f)))))
           (equal (fn-feed-back-off f msgid obs) f))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-back-off fn-feed-state-of fn-feed-find)
    (fn-feedp fn-feed-with-queue fn-feed-with-backoff fn-feed-backoff-delay
     fn-feed-queue-requeue fn-feed-state-inflightp)))))

; A parsed peer reply and its durable record batch move the same persistent
; feed fields.  Article octets affect only the command effect of a successful
; send, never the feed state recorded here.
(defthm fn-feed-observe-records-reconstruct-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-observe-records f response obs)))
                  (fn-feed-durable-projection
                   (mv-nth 0 (fn-feed-observe f response article obs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d
    (fn-feed-replay fn-feed-apply-record fn-feed-observe-records
     fn-feed-observe fn-feed-send fn-feed-done fn-feed-give-up fn-feed-back-off
     fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values fn-frame-item)
    (fn-feedp fn-feed-durable-projection fn-feed-lost
     fn-feed-lost-records fn-feed-retry-exhaustedp fn-feed-queue-set-state
     fn-feed-with-queue fn-feed-state-of fn-feed-state-inflightp
     fn-feed-offeredp fn-feed-droppedp fn-feed-state-attempt fn-feed-find
     fn-feed-sent fn-feed-response-code fn-feed-response-msgid))
    :use ((:instance fn-feed-back-off-without-inflight-is-identity
                     (msgid (fn-feed-response-msgid response)))
          (:instance fn-feed-back-off-uses-only-monotonic-observation
                     (msgid (fn-feed-response-msgid response)))))))

(defthm fn-feed-with-conn-preserves-feedp
  (implies (and (fn-feedp f) (or (null conn) (natp conn)))
           (fn-feedp (fn-feed-with-conn f conn)))
  :hints (("Goal" :in-theory (enable fn-feed-with-conn fn-feedp))))

; Article bytes determine a send effect, while the feed state records only the
; accepted response and attempt.  This lets the journal-side reply batch omit
; the bytes without introducing a second response state machine.
(defthm fn-feed-observe-projection-independent-of-article
  (equal (fn-feed-durable-projection
          (mv-nth 0 (fn-feed-observe f response article-a obs)))
         (fn-feed-durable-projection
          (mv-nth 0 (fn-feed-observe f response article-b obs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d
    (fn-feed-observe fn-feed-send fn-feed-durable-projection fn-feed-with-conn)
    (fn-feedp fn-feed-with-queue fn-feed-state-of fn-feed-offeredp
     fn-feed-sent fn-feed-response-code fn-feed-response-msgid)))))

(defthm fn-feed-live-next-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-live-next f event)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-live-next fn-feed-with-conn)
    (fn-feedp fn-feed-enqueue fn-feed-tick-step fn-feed-observe fn-feed-lost
     fn-feed-restart mv-nth))
           :use ((:instance fn-feed-with-conn-preserves-feedp
                            (conn (fn-frame-item 1 event)))))))

; This is the bridge from the event shape selected by the owner to the exact
; one-step live transition.  Connection events have no records because the
; durable projection deliberately forgets only their socket identity.
(defthm fn-feed-live-records-reconstruct-step
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-live-records f event)))
                  (fn-feed-durable-projection (fn-feed-live-next f event))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-live-records fn-feed-live-next)
    (fn-feedp fn-feed-durable-projection fn-feed-enqueue-records
     fn-feed-tick-records fn-feed-observe-records fn-feed-lost-records
     fn-feed-enqueue fn-feed-tick-step fn-feed-observe
     fn-feed-lost fn-feed-restart fn-feed-with-conn mv-nth))
           :use ((:instance fn-feed-observe-records-reconstruct-live
                            (response (fn-frame-item 1 event))
                            (article (fn-frame-item 2 event))
                            (obs (fn-frame-item 3 event)))))))

; Replay has no connection input.  This is the two-state congruence required
; to concatenate separately emitted live batches into one persisted fold.
(defthm fn-feed-apply-record-on-projection
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-apply-record (fn-feed-durable-projection f) kind values))
                  (fn-feed-durable-projection (fn-feed-apply-record f kind values))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-apply-record fn-feed-durable-projection fn-feed-with-conn
     fn-feed-enqueue fn-feed-done fn-feed-back-off fn-feed-lost
     fn-feed-give-up fn-feed-restart fn-feed-with-queue fn-feed-with-backoff)
    (fn-feedp fn-feed-queue-set-state fn-feed-queue-requeue
     fn-feed-queue-requeue-inflight fn-feed-queue-settle fn-feed-find
     fn-feed-state-of fn-feed-state-inflightp fn-feed-offeredp fn-feed-droppedp
     fn-feed-state-attempt fn-feed-backoff-delay))
           :use ((:instance fn-feedp-of-durable-projection)))))

(defthm fn-feed-projection-equal-implies-persistent-fields
  (implies (equal (fn-feed-durable-projection f)
                  (fn-feed-durable-projection g))
           (and (equal (fn-feed-peer f) (fn-feed-peer g))
                (equal (fn-feed-limits-of f) (fn-feed-limits-of g))
                (equal (fn-feed-queue f) (fn-feed-queue g))
                (equal (fn-feed-contact f) (fn-feed-contact g))
                (equal (fn-feed-backoff-until f) (fn-feed-backoff-until g))
                (equal (fn-feed-next-attempt f) (fn-feed-next-attempt g))))
  :hints (("Goal" :in-theory (enable fn-feed-durable-projection fn-feed-with-conn
                                      (:d fn-feed-make) (:d fn-feed-peer)
                                      (:d fn-feed-limits-of) (:d fn-feed-queue)
                                      (:d fn-feed-contact) (:d fn-feed-backoff-until)
                                      (:d fn-feed-next-attempt) fn-bp-nth))))

(defthm fn-feed-apply-record-respects-projection
  (implies (and (fn-feedp f) (fn-feedp g)
                (equal (fn-feed-durable-projection f)
                       (fn-feed-durable-projection g)))
           (equal (fn-feed-durable-projection (fn-feed-apply-record f kind values))
                  (fn-feed-durable-projection (fn-feed-apply-record g kind values))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d
    (fn-feed-apply-record fn-feed-durable-projection fn-feed-with-conn
     fn-feed-enqueue fn-feed-done fn-feed-back-off fn-feed-lost
     fn-feed-give-up fn-feed-restart fn-feed-with-queue fn-feed-with-backoff)
    (fn-feedp fn-feed-queue-set-state fn-feed-queue-requeue
     fn-feed-queue-requeue-inflight fn-feed-queue-settle fn-feed-find
     fn-feed-state-of fn-feed-state-inflightp fn-feed-offeredp fn-feed-droppedp
     fn-feed-state-attempt fn-feed-backoff-delay))
           :use ((:instance fn-feed-projection-equal-implies-persistent-fields)))))

(local (defun fn-feed-pair-replay-induct (f g records)
         (if (atom records) (list f g)
           (fn-feed-pair-replay-induct
            (fn-feed-apply-record f (fn-feed-journal-kind (car records))
                                  (fn-feed-journal-values (car records)))
            (fn-feed-apply-record g (fn-feed-journal-kind (car records))
                                  (fn-feed-journal-values (car records)))
            (cdr records)))))

(defthm fn-feed-replay-respects-projection
  (implies (and (fn-feedp f) (fn-feedp g)
                (equal (fn-feed-durable-projection f)
                       (fn-feed-durable-projection g)))
           (equal (fn-feed-durable-projection (fn-feed-replay f records))
                  (fn-feed-durable-projection (fn-feed-replay g records))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-feed-pair-replay-induct f g records)
           :in-theory (e/d (fn-feed-replay)
            (fn-feedp fn-feed-durable-projection fn-feed-apply-record)))
          ("Subgoal *1/2" :use ((:instance fn-feed-apply-record-respects-projection
                            (kind (fn-feed-journal-kind (car records)))
                            (values (fn-feed-journal-values (car records))))))))

(defthm fn-feed-replay-on-projection
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay (fn-feed-durable-projection f) records))
                  (fn-feed-durable-projection (fn-feed-replay f records))))
  :hints (("Goal" :use ((:instance fn-feed-replay-respects-projection
                                     (g (fn-feed-durable-projection f)))))))

(defthm fn-feed-live-batch-replay-tail
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay (fn-feed-replay f (fn-feed-live-records f event)) tail))
                  (fn-feed-durable-projection
                   (fn-feed-replay (fn-feed-live-next f event) tail))))
  :hints (("Goal" :use
           ((:instance fn-feed-live-records-reconstruct-step)
            (:instance fn-feed-replay-preserves-feedp
                       (es (fn-feed-live-records f event)))
            (:instance fn-feed-live-next-preserves-feedp)
            (:instance fn-feed-replay-respects-projection
                       (f (fn-feed-replay f (fn-feed-live-records f event)))
                       (g (fn-feed-live-next f event))
                       (records tail))))))

; A finite event sequence is run by the same live functions that supply each
; persisted batch.  The result establishes the durable projection of the
; actual fold; it says nothing about physical write success.
(defthm fn-feed-generated-history-reconstructs-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-live-history f events)))
                  (fn-feed-durable-projection (fn-feed-live-run f events))))
  :hints (("Goal" :induct (fn-feed-live-run f events)
           :in-theory (e/d (fn-feed-live-run fn-feed-live-history fn-feed-replay)
            (fn-feedp fn-feed-live-next fn-feed-live-records
             fn-feed-durable-projection)))
          ("Subgoal *1/2" :use
           ((:instance fn-feed-live-batch-replay-tail
                       (event (car events))
                       (tail (fn-feed-live-history
                              (fn-feed-live-next f (car events)) (cdr events))))))))

; Each actual enqueue batch is admissible to the replay state it starts from;
; an already-present/full-queue enqueue emits nothing, which is driven too.
(defthm fn-feed-enqueue-records-are-driven
  (implies (and (fn-feedp f)
                (fn-feed-journalp (fn-feed-enqueue-records f msgid tick)))
           (fn-feed-drivenp f (fn-feed-enqueue-records f msgid tick)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-enqueue-records fn-feed-drivenp fn-feed-record-drivenp fn-feed-journalp
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values
     fn-feed-record-peer fn-feed-record-msgid fn-frame-item)
    (fn-feedp fn-feed-journal-entryp fn-feed-apply-record fn-feed-find
     fn-feed-namep fn-feed-max-queue fn-feed-limits-of fn-feed-queue)))))

(defthm fn-feed-tick-records-are-driven
  (implies (and (fn-feedp f)
                (fn-feed-journalp (fn-feed-tick-records f obs)))
           (fn-feed-drivenp f (fn-feed-tick-records f obs)))
  :hints (("Goal" :use fn-feed-selection-is-queued
           :in-theory (e/d
    (fn-feed-tick-records fn-feed-selection fn-feed-drivenp fn-feed-record-drivenp
     fn-feed-journalp fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values
     fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat fn-frame-item)
    (fn-feedp fn-feed-journal-entryp fn-feed-apply-record fn-feed-state-of
     fn-feed-inflight-count fn-feed-next-attempt)))))

(defthm fn-feed-lost-records-are-driven
  (implies (and (fn-feedp f)
                (fn-feed-journalp (fn-feed-lost-records f obs)))
           (fn-feed-drivenp f (fn-feed-lost-records f obs)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-lost-records fn-feed-drivenp fn-feed-record-drivenp fn-feed-journalp
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values
     fn-feed-record-peer fn-feed-record-msgid fn-frame-item)
    (fn-feedp fn-feed-journal-entryp fn-feed-apply-record)))))

(defthm fn-feed-restart-records-are-driven
  (implies (and (fn-feedp f)
                (fn-feed-journalp (fn-feed-restart-records f)))
           (fn-feed-drivenp f (fn-feed-restart-records f)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-restart-records fn-feed-drivenp fn-feed-record-drivenp fn-feed-journalp
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values
     fn-feed-record-peer fn-feed-record-msgid fn-frame-item)
    (fn-feedp fn-feed-journal-entryp fn-feed-apply-record)))))
