; UNPROVED continuation draft, not a certifiable root.
; Load only after books/feed-correspondence in development.
; Observe theorem currently fails; later forms have not been attempted.
(defthm fn-feed-observe-records-reconstruct-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-observe-records f response obs)))
                  (fn-feed-durable-projection
                   (mv-nth 0 (fn-feed-observe f response article obs)))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-replay fn-feed-apply-record fn-feed-observe-records
     fn-feed-observe fn-feed-send fn-feed-done fn-feed-give-up
     fn-feed-record-peer fn-feed-record-msgid fn-feed-record-nat
     fn-feed-journal-entry fn-feed-journal-kind fn-feed-journal-values fn-frame-item)
    (fn-feedp fn-feed-durable-projection fn-feed-back-off fn-feed-lost
     fn-feed-lost-records fn-feed-retry-exhaustedp fn-feed-queue-set-state
     fn-feed-with-queue fn-feed-state-of fn-feed-state-inflightp
     fn-feed-offeredp fn-feed-droppedp fn-feed-state-attempt fn-feed-find
     fn-feed-sent fn-feed-response-code fn-feed-response-msgid)))))

(defthm fn-feed-live-next-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-live-next f event)))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-live-next fn-feed-with-conn)
    (fn-feedp fn-feed-enqueue fn-feed-tick-step fn-feed-observe fn-feed-lost
     fn-feed-restart mv-nth)))))

(defthm fn-feed-live-records-reconstruct-step
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-live-records f event)))
                  (fn-feed-durable-projection (fn-feed-live-next f event))))
  :hints (("Goal" :in-theory (e/d
    (fn-feed-live-records fn-feed-live-next)
    (fn-feedp fn-feed-durable-projection fn-feed-enqueue-records
     fn-feed-tick-records fn-feed-observe-records fn-feed-lost-records
     fn-feed-restart-records fn-feed-enqueue fn-feed-tick-step fn-feed-observe
     fn-feed-lost fn-feed-restart fn-feed-with-conn mv-nth)))))

; Replay does not consult the socket identity. This is the transport boundary
; needed to splice separately emitted live steps into a single persisted fold.
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
     fn-feed-state-attempt fn-feed-backoff-delay)))))

(defthm fn-feed-replay-on-projection
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay (fn-feed-durable-projection f) records))
                  (fn-feed-durable-projection (fn-feed-replay f records))))
  :hints (("Goal" :induct (fn-feed-replay f records)
           :in-theory (e/d (fn-feed-replay)
            (fn-feedp fn-feed-durable-projection fn-feed-apply-record)))))

; The live machine allocates attempts and updates queue/backoff itself. Its
; emitted finite history reconstructs every one of those durable fields.
(defthm fn-feed-generated-history-reconstructs-live
  (implies (fn-feedp f)
           (equal (fn-feed-durable-projection
                   (fn-feed-replay f (fn-feed-live-history f events)))
                  (fn-feed-durable-projection (fn-feed-live-run f events))))
  :hints (("Goal" :induct (fn-feed-live-run f events)
           :in-theory (e/d (fn-feed-live-run fn-feed-live-history)
            (fn-feedp fn-feed-live-next fn-feed-live-records
             fn-feed-durable-projection fn-feed-replay)))))

; Grammar encodability is the only additional history hypothesis here. State
; admissibility, including attempt matching and the one-in-flight rule, is a
; conclusion about the real emitters, rather than a supplied drivenp premise.
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
