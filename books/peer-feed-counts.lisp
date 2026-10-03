; S9 count relation support. Model folds are cold/reference functions only;
; the served counted constructor and owner aggregate are not activated here.
(in-package "ACL2")
(include-book "feed-events")

(local (in-theory (enable fn-fct-retry-drop-bit fn-fct-retry-drops-model
                          fn-fct-pending-model)))

(defthm fn-fct-retry-drops-within-undelivered
  (and (natp (fn-fct-retry-drops-model queue))
       (<= (fn-fct-retry-drops-model queue) (len queue))))

; Successful enqueue appends one queued entry, not one retry-bound drop.
(defthm fn-fct-enqueue-tally-delta
  (implies (true-listp queue)
           (and (equal (len (append queue (list (fn-feed-entry id :queued a k))))
                       (+ 1 (len queue)))
                (equal (fn-fct-retry-drops-model
                        (append queue (list (fn-feed-entry id :queued a k))))
                       (fn-fct-retry-drops-model queue))))
  :hints (("Goal" :induct (len queue))))

; Uses the same first-match lookup as the actual queue mutation. No
; distinctness assumption is needed: each mutation changes one first match.
(defthm fn-fct-retire-tally-delta
  (implies (consp (fn-feed-find id queue))
           (and (equal (+ 1 (len (fn-feed-queue-retire queue id)))
                       (len queue))
                (equal (+ (fn-fct-retry-drops-model
                           (fn-feed-queue-retire queue id))
                          (fn-fct-retry-drop-bit (fn-feed-state-of id queue)))
                       (fn-fct-retry-drops-model queue))))
  :hints (("Goal" :induct (fn-feed-queue-retire queue id)
                  :in-theory (enable fn-feed-state-of))))

(defthm fn-fct-set-state-tally-delta
  (implies (consp (fn-feed-find id queue))
           (and (equal (len (fn-feed-queue-set-state queue id st))
                       (len queue))
                (equal (+ (fn-fct-retry-drops-model
                           (fn-feed-queue-set-state queue id st))
                          (fn-fct-retry-drop-bit (fn-feed-state-of id queue)))
                       (+ (fn-fct-retry-drops-model queue)
                          (fn-fct-retry-drop-bit st)))))
  :hints (("Goal" :induct (fn-feed-queue-set-state queue id st)
                  :in-theory (enable fn-feed-state-of))))

; A dropped operator/peer-removal entry stays pending. This equation
; explicitly preserves that old S9 meaning rather than counting all drops.
(defthm fn-fct-other-drop-stays-pending
  (implies (and (consp (fn-feed-find id queue))
                (not (equal st '(:dropped :retry-bound)))
                (not (equal (fn-feed-state-of id queue)
                            '(:dropped :retry-bound))))
           (equal (fn-fct-pending-model
                   (fn-feed-queue-set-state queue id st))
                  (fn-fct-pending-model queue)))
  :hints (("Goal" :use fn-fct-set-state-tally-delta
                  :in-theory (disable fn-fct-set-state-tally-delta
                                      fn-feed-queue-set-state))))

; Loss and restart touch only offered/sent entries, never a retry drop.
(defthm fn-fct-settle-tally-preserved
  (and (equal (len (fn-feed-queue-settle queue)) (len queue))
       (equal (fn-fct-retry-drops-model (fn-feed-queue-settle queue))
              (fn-fct-retry-drops-model queue)))
  :hints (("Goal" :induct (fn-feed-queue-settle queue)
                  :in-theory (enable fn-feed-state-inflightp
                                     fn-feed-offeredp fn-feed-sentp))))

(defthm fn-fct-loss-tally-preserved
  (and (equal (len (fn-feed-queue-requeue-inflight queue tick)) (len queue))
       (equal (fn-fct-retry-drops-model
               (fn-feed-queue-requeue-inflight queue tick))
              (fn-fct-retry-drops-model queue)))
  :hints (("Goal" :induct (fn-feed-queue-requeue-inflight queue tick)
                  :in-theory (enable fn-feed-state-inflightp
                                     fn-feed-offeredp fn-feed-sentp))))

(defthm fn-fct-requeue-tally-preserved
  (implies (not (equal (fn-feed-state-of id queue) '(:dropped :retry-bound)))
           (and (equal (len (fn-feed-queue-requeue queue id tick)) (len queue))
                (equal (fn-fct-retry-drops-model
                        (fn-feed-queue-requeue queue id tick))
                       (fn-fct-retry-drops-model queue))))
  :hints (("Goal" :induct (fn-feed-queue-requeue queue id tick)
                  :in-theory (enable fn-feed-state-of))))

(defthm fn-fct-count-relation-of-counted-make
  (equal (fn-feed-count-relationp
          (fn-feed-make-counted p l q c b n a u d))
         (and (equal u (len q))
              (equal d (fn-fct-retry-drops-model q))))
  :hints (("Goal" :in-theory (enable fn-feed-count-relationp))))

(defthm fn-fct-count-relation-of-counted-queue-update
  (equal (fn-feed-count-relationp (fn-feed-with-queue-counted f q u d))
         (and (equal u (len q))
              (equal d (fn-fct-retry-drops-model q))))
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
                                  (fn-feedp fn-feed-namep
                                   fn-fct-retry-drops-model)))))

(defthm fn-fct-give-up-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-give-up f id reason)))
  :hints (("Goal"
           :use ((:instance fn-fct-set-state-tally-delta
                            (queue (fn-feed-queue f))
                            (st (fn-feed-dropped reason)))
                 (:instance fn-fct-retry-drops-within-undelivered
                            (queue (fn-feed-queue f))))
           :in-theory (e/d (fn-feed-give-up fn-feed-count-relationp
                            fn-feed-droppedp fn-feed-dropped)
                           (fn-feedp fn-fct-retry-drops-model
                            fn-feed-queue-set-state fn-fct-set-state-tally-delta
                            fn-fct-retry-drops-within-undelivered)))))

(defthm fn-fct-inflight-is-not-retry-drop
  (implies (fn-feed-state-inflightp st)
           (and (not (equal st '(:dropped :retry-bound)))
                (equal (fn-fct-retry-drop-bit st) 0)))
  :hints (("Goal" :in-theory (enable fn-feed-state-inflightp
                                      fn-feed-offeredp fn-feed-sentp))))

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
                            (queue (fn-feed-queue f)))
                 (:instance fn-fct-retry-drops-within-undelivered
                            (queue (fn-feed-queue f))))
           :in-theory (e/d (fn-feed-done fn-feed-count-relationp)
                           (fn-feedp fn-feed-state-inflightp
                            fn-fct-retry-drops-model fn-feed-queue-retire
                            fn-fct-retire-tally-delta
                            fn-fct-retry-drops-within-undelivered)))))

(defthm fn-fct-carried-counts-queue-update
  (implies (and (fn-feed-count-relationp f)
                (equal (len q) (len (fn-feed-queue f)))
                (equal (fn-fct-retry-drops-model q)
                       (fn-fct-retry-drops-model (fn-feed-queue f))))
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

(defthm fn-fct-queued-lookup-is-present
  (implies (equal (fn-feed-state-of id queue) :queued)
           (consp (fn-feed-find id queue)))
  :hints (("Goal" :in-theory (enable fn-feed-state-of fn-feed-entry-state))))

(defthm fn-fct-set-nondropped-state-preserves-counts
  (implies (and (consp (fn-feed-find id queue))
                (equal (fn-fct-retry-drop-bit (fn-feed-state-of id queue)) 0)
                (equal (fn-fct-retry-drop-bit st) 0))
           (and (equal (len (fn-feed-queue-set-state queue id st)) (len queue))
                (equal (fn-fct-retry-drops-model
                        (fn-feed-queue-set-state queue id st))
                       (fn-fct-retry-drops-model queue))))
  :hints (("Goal" :use fn-fct-set-state-tally-delta
                  :in-theory (disable fn-fct-set-state-tally-delta
                                      fn-feed-queue-set-state))))

(defthm fn-fct-offer-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (mv-nth 0 (fn-feed-offer f id))))
  :hints (("Goal"
           :use ((:instance fn-fct-set-nondropped-state-preserves-counts
                            (queue (fn-feed-queue f))
                            (st (fn-feed-offered (fn-feed-next-attempt f)))))
           :in-theory (e/d (fn-feed-offer fn-feed-count-relationp
                            fn-fct-retry-drop-bit fn-feed-offered)
                           (fn-feedp fn-feed-queue-set-state
                            fn-fct-set-nondropped-state-preserves-counts
                            fn-fct-retry-drops-model)))))

(defthm fn-fct-send-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (mv-nth 0 (fn-feed-send f id article))))
  :hints (("Goal"
           :use ((:instance fn-fct-set-nondropped-state-preserves-counts
                            (queue (fn-feed-queue f))
                            (st (fn-feed-sent
                                 (fn-feed-state-attempt
                                  (fn-feed-state-of id (fn-feed-queue f)))))))
           :in-theory (e/d (fn-feed-send fn-feed-count-relationp
                            fn-feed-with-queue-preserving-counts
                            fn-feed-with-queue-counted fn-fct-retry-drop-bit
                            fn-feed-offeredp fn-feed-sent)
                           (fn-feedp fn-feed-queue-set-state
                            fn-fct-set-nondropped-state-preserves-counts
                            fn-fct-retry-drops-model)))))

(defthm fn-fct-retry-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp (fn-feed-back-off f id obs)))
  :hints (("Goal" :in-theory (e/d (fn-feed-back-off fn-feed-state-of)
                                   (fn-feed-with-backoff fn-feed-with-conn
                                    fn-feed-with-queue-preserving-counts
                                    fn-feed-state-inflightp
                                    fn-fct-retry-drops-model)))))

(defthm fn-fct-offered-lookup-is-inflight
  (implies (fn-feed-offeredp (fn-feed-state-of id queue))
           (fn-feed-state-inflightp (fn-feed-state-of id queue)))
  :hints (("Goal" :in-theory (enable fn-feed-state-inflightp))))

(defthm fn-fct-observe-preserves-count-relation
  (implies (fn-feed-count-relationp f)
           (fn-feed-count-relationp
            (mv-nth 0 (fn-feed-observe f response article obs))))
  :hints (("Goal" :in-theory (e/d (fn-feed-observe)
                                   (mv-nth fn-feedp fn-feed-done fn-feed-send
                                    fn-feed-back-off fn-feed-give-up
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
           :use ((:instance fn-fct-set-nondropped-state-preserves-counts
                            (id (fn-feed-record-msgid values))
                            (queue (fn-feed-queue f))
                            (st (fn-feed-offered (fn-feed-record-nat 2 values))))
                 (:instance fn-fct-set-nondropped-state-preserves-counts
                            (id (fn-feed-record-msgid values))
                            (queue (fn-feed-queue f))
                            (st (fn-feed-sent (fn-feed-record-nat 2 values)))))
           :in-theory (e/d (fn-feed-apply-record fn-feed-count-relationp
                            fn-feed-with-queue-preserving-counts
                            fn-feed-with-queue-counted fn-fct-retry-drop-bit
                            fn-feed-offered fn-feed-sent fn-feed-offeredp)
                           (fn-feedp fn-feed-queue-set-state fn-feed-enqueue
                            fn-feed-done fn-feed-back-off fn-feed-lost
                            fn-feed-give-up fn-feed-restart
                            fn-fct-set-nondropped-state-preserves-counts
                            fn-fct-retry-drops-model)))))

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

(in-theory (disable fn-fct-retry-drop-bit fn-fct-retry-drops-model
                    fn-fct-pending-model))
