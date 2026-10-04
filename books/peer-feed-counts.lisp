; S9 count relation support: the carried UNDELIVERED is the queue's length
; and the RETRY-DROPPED tally is a natural, through every live and replayed
; transition.  Every entry the queue holds is owed delivery (a given-up entry
; leaves it, rp-feed-dropped-holds-capacity), so the length is the peer's
; pending work and no fold over the queue's states is carried.
(in-package "ACL2")
(include-book "feed-events")

(local (in-theory (enable fn-fct-retry-drop-bit)))

; Successful enqueue appends one entry.
(defthm fn-fct-enqueue-tally-delta
  (implies (true-listp queue)
           (equal (len (append queue (list (fn-feed-entry id :queued a k l))))
                  (+ 1 (len queue))))
  :hints (("Goal" :induct (len queue))))

; Uses the same first-match lookup as the actual queue mutation. No
; distinctness assumption is needed: each mutation changes one first match.
(defthm fn-fct-retire-tally-delta
  (implies (consp (fn-feed-find id queue))
           (equal (+ 1 (len (fn-feed-queue-retire queue id)))
                  (len queue)))
  :hints (("Goal" :induct (fn-feed-queue-retire queue id))))

(defthm fn-fct-set-state-tally-delta
  (equal (len (fn-feed-queue-set-state queue id st))
         (len queue))
  :hints (("Goal" :induct (fn-feed-queue-set-state queue id st))))

; Loss and restart touch only offered/sent entries.
(defthm fn-fct-settle-tally-preserved
  (equal (len (fn-feed-queue-settle queue)) (len queue))
  :hints (("Goal" :induct (fn-feed-queue-settle queue))))

(defthm fn-fct-loss-tally-preserved
  (equal (len (fn-feed-queue-requeue-inflight queue tick)) (len queue))
  :hints (("Goal" :induct (fn-feed-queue-requeue-inflight queue tick))))

(defthm fn-fct-requeue-tally-preserved
  (equal (len (fn-feed-queue-requeue queue id tick)) (len queue))
  :hints (("Goal" :induct (fn-feed-queue-requeue queue id tick))))

(defthm fn-fct-count-relation-of-counted-make
  (equal (fn-feed-count-relationp
          (fn-feed-make-counted p l q c b n a u d))
         (and (equal u (len q))
              (natp d)))
  :hints (("Goal" :in-theory (enable fn-feed-count-relationp))))

(defthm fn-fct-count-relation-of-counted-queue-update
  (equal (fn-feed-count-relationp (fn-feed-with-queue-counted f q u d))
         (and (equal u (len q))
              (natp d)))
  :hints (("Goal" :in-theory (enable fn-feed-with-queue-counted))))

(defthm fn-fct-open-has-exact-counts
  (and (fn-feed-count-relationp (fn-feed-open peer limits contact conn))
       (equal (fn-feed-undelivered (fn-feed-open peer limits contact conn)) 0)
       (equal (fn-feed-retry-dropped (fn-feed-open peer limits contact conn)) 0))
  :hints (("Goal" :in-theory (enable fn-feed-open))))

(defthm fn-fct-enqueue-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-enqueue f id tick)))
  :hints (("Goal" :in-theory (e/d (fn-feed-enqueue fn-feed-count-relationp)
                                  (fn-feedp fn-feed-namep)))))

(defthm fn-fct-give-up-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-give-up f id reason)))
  :hints (("Goal"
           :use ((:instance fn-fct-retire-tally-delta
                            (queue (fn-feed-queue f))))
           :in-theory (e/d (fn-feed-give-up fn-feed-count-relationp)
                           (fn-feedp fn-feed-queue-retire
                            fn-fct-retire-tally-delta)))))

(defthm fn-fct-inflight-lookup-is-present
  (implies (fn-feed-state-inflightp (fn-feed-state-of id queue))
           (consp (fn-feed-find id queue)))
  :hints (("Goal" :in-theory (enable fn-feed-state-of fn-feed-entry-state
                                     fn-feed-state-inflightp
                                     fn-feed-offeredp fn-feed-sentp))))

(defthm fn-fct-done-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-done f id)))
  :hints (("Goal"
           :use ((:instance fn-fct-retire-tally-delta
                            (queue (fn-feed-queue f))))
           :in-theory (e/d (fn-feed-done fn-feed-count-relationp)
                           (fn-feedp fn-feed-state-inflightp
                            fn-feed-queue-retire
                            fn-fct-retire-tally-delta)))))

(defthm fn-fct-carried-counts-queue-update
  (implies (and (fn-feed-count-relationp f)
                (equal (len q) (len (fn-feed-queue f))))
           (fn-feed-count-relationp
            (fn-feed-with-queue-preserving-counts f q)))
  :hints (("Goal" :in-theory (enable fn-feed-count-relationp
                                     fn-feed-with-queue-preserving-counts))))

(defthm fn-fct-connection-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-with-conn f conn)))
  :hints (("Goal" :in-theory (enable fn-feed-with-conn
                                     fn-feed-count-relationp))))

(defthm fn-fct-backoff-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (and (fn-feed-count-relationp (fn-feed-with-backoff f until))
                (fn-feed-count-relationp (fn-feed-without-backoff f))))
  :hints (("Goal" :in-theory (enable fn-feed-with-backoff
                                     fn-feed-without-backoff
                                     fn-feed-count-relationp))))

(defthm fn-fct-restart-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-restart f)))
  :hints (("Goal" :in-theory (e/d (fn-feed-restart)
                                   (fn-feed-without-backoff fn-feed-with-conn
                                    fn-feed-with-queue-preserving-counts)))))

(defthm fn-fct-lost-requeue-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-lost-requeue f obs)))
  :hints (("Goal" :in-theory (e/d (fn-feed-lost-requeue)
                                   (fn-feed-with-backoff fn-feed-with-conn
                                    fn-feed-inflight-entry
                                    fn-feed-with-queue-preserving-counts)))))

(defthm fn-fct-lost-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-lost f obs)))
  :hints (("Goal" :in-theory (e/d (fn-feed-lost)
                                   (fn-feed-lost-requeue fn-feed-give-up
                                    fn-feed-retry-exhaustedp fn-feed-inflight-entry)))))

(defthm fn-fct-offer-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (mv-nth 0 (fn-feed-offer f id))))
  :hints (("Goal"
           :in-theory (e/d (fn-feed-offer fn-feed-count-relationp)
                           (fn-feedp fn-feed-queue-set-state)))))

(defthm fn-fct-send-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (mv-nth 0 (fn-feed-send f id article))))
  :hints (("Goal"
           :in-theory (e/d (fn-feed-send fn-feed-count-relationp
                            fn-feed-with-queue-preserving-counts
                            fn-feed-with-queue-counted)
                           (fn-feedp fn-feed-queue-set-state)))))

(defthm fn-fct-retry-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-back-off f id obs)))
  :hints (("Goal" :in-theory (e/d (fn-feed-back-off)
                                   (fn-feed-with-backoff fn-feed-with-conn
                                    fn-feed-with-queue-preserving-counts
                                    fn-feed-state-inflightp)))))

(defthm fn-fct-observe-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp
            (mv-nth 0 (fn-feed-observe f response article obs))))
  :hints (("Goal" :in-theory (e/d (fn-feed-observe)
                                   (mv-nth fn-feedp fn-feed-done fn-feed-send
                                    fn-feed-back-off fn-feed-reply-class
                                    fn-feed-lost)))))

(defthm fn-fct-tick-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (mv-nth 0 (fn-feed-tick-step f obs))))
  :hints (("Goal" :in-theory (e/d (fn-feed-tick-step)
                                   (mv-nth fn-feed-selection fn-feed-offer)))))

(defthm fn-fct-apply-record-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-apply-record f kind values)))
  :hints (("Goal"
           :in-theory (e/d (fn-feed-apply-record fn-feed-count-relationp
                            fn-feed-with-queue-preserving-counts
                            fn-feed-with-queue-counted)
                           (fn-feedp fn-feed-queue-set-state fn-feed-enqueue
                            fn-feed-done fn-feed-back-off fn-feed-lost
                            fn-feed-lost-requeue
                            fn-feed-give-up fn-feed-restart)))))

(defthm fn-fct-replay-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-replay f entries)))
  :hints (("Goal" :induct (fn-feed-replay f entries)
                  :in-theory (enable fn-feed-replay))))

(defthm fn-fct-live-next-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-live-next f event)))
  :hints (("Goal" :in-theory (e/d (fn-feed-live-next)
                                   (mv-nth fn-feed-enqueue fn-feed-tick-step
                                    fn-feed-observe fn-feed-lost fn-feed-restart
                                    fn-feed-with-conn)))))

; Exact host-reachable FNFD port subject. Refusals preserve the original
; feed; accepted events preserve derived counts through actual live arms.
(defthm fn-fct-live-port-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp
            (fn-feed-port-step-feed (fn-feed-live-port-step f event))))
  :hints (("Goal" :in-theory (e/d (fn-feed-live-port-step
                                   fn-feed-port-step-feed fn-frame-item)
                                  (fn-feed-live-records fn-feed-live-next
                                   fn-feed-live-effects fn-feed-records-portp
                                   fn-feedp)))))

(in-theory (disable fn-fct-retry-drop-bit))
