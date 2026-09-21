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
