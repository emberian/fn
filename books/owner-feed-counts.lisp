; S9 aggregate relation for actual per-peer FNFD mutations. Logical folds
; are reference/cold vocabulary; served installers consume the carried delta.
(in-package "ACL2")
(include-book "owner-retire-cursor")
(include-book "peer-feed-counts")

(defun fn-ofct-table-relationp (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (and (fn-feed-count-relationp (fn-own-feed-entry-feed (car tbl)))
           (fn-ofct-table-relationp (cdr tbl)))
    t))

(local
 (defthm fn-ofct-queue-tallies-partition
   (equal (+ (fn-fct-retry-drops-model q) (fn-orc-queue-pending-model q))
          (len q))
   :hints (("Goal" :induct (len q)
                   :in-theory (enable fn-fct-retry-drops-model
                                      fn-fct-retry-drop-bit
                                      fn-orc-queue-pending-model)))))

(defthm fn-ofct-feed-count-is-the-reference-pending
  (implies (fn-feed-count-relationp f)
           (equal (fn-own-feed-pending-of f)
                  (fn-orc-queue-pending-model (fn-feed-queue f))))
  :hints (("Goal" :use ((:instance fn-ofct-queue-tallies-partition
                                   (q (fn-feed-queue f))))
                  :in-theory (e/d (fn-own-feed-pending-of
                                   fn-feed-count-relationp)
                                  (fn-orc-queue-pending-model
                                   fn-fct-retry-drops-model
                                   fn-ofct-queue-tallies-partition)))))

(defthm fn-ofct-table-count-is-the-reference-pending
  (implies (fn-ofct-table-relationp tbl)
           (equal (fn-own-feed-table-pending-model tbl)
                  (fn-orc-table-pending-model tbl)))
  :hints (("Goal" :induct (len tbl)
                  :in-theory (enable fn-own-feed-table-pending-model
                                     fn-orc-table-pending-model))))

; First-match replacement adds the new peer's pending and removes the old
; peer's pending. An absent peer has no old contribution. No table equality
; or fold is executed by the delta consumed by an installer.
(defthm fn-ofct-put-has-exact-aggregate-delta
  (equal (fn-own-feed-table-pending-model (fn-own-feed-put peer record new tbl))
         (+ (fn-own-feed-table-pending-model tbl)
            (fn-own-feed-pending-delta
             (fn-own-feed-find peer tbl) new)))
  :hints (("Goal" :induct (fn-own-feed-put peer record new tbl)
                  :in-theory (enable fn-own-feed-table-pending-model
                                     fn-own-feed-pending-delta
                                     fn-own-feed-put fn-own-feed-find
                                     fn-own-feed-entry-of
                                     fn-own-feed-entry-feed fn-own-feed-pending-of))))

(defthm fn-ofct-enqueue-all-counted-has-the-original-table
  (equal (car (fn-own-feed-enqueue-all-counted names tbl id tick pending))
         (fn-own-feed-enqueue-all names tbl id tick))
  :hints (("Goal" :induct (fn-own-feed-enqueue-all-counted names tbl id tick pending)
                  :in-theory (enable fn-own-feed-enqueue-all-counted
                                     fn-own-feed-enqueue-all))))

(defthm fn-ofct-enqueue-all-counted-preserves-aggregate
  (implies (equal pending (fn-own-feed-table-pending-model tbl))
           (equal (cdr (fn-own-feed-enqueue-all-counted names tbl id tick pending))
                  (fn-own-feed-table-pending-model
                   (car (fn-own-feed-enqueue-all-counted names tbl id tick pending)))))
  :hints (("Goal" :induct (fn-own-feed-enqueue-all-counted names tbl id tick pending)
                  :in-theory (enable fn-own-feed-enqueue-all-counted
                                     fn-own-feed-find))))

(defthm fn-ofct-port-peer-has-exact-aggregate-delta
  (equal (fn-own-feed-table-pending-model
          (fn-own-feed-port-table (fn-own-feed-port-peer peer tbl event)))
         (+ (fn-own-feed-table-pending-model tbl)
            (fn-own-feed-port-pending-delta
             (fn-own-feed-port-peer peer tbl event))))
  :hints (("Goal" :in-theory
           (e/d (fn-own-feed-port-peer fn-own-feed-port-result
                 fn-own-feed-port-result-counted fn-own-feed-port-table
                 fn-own-feed-port-pending-delta fn-frame-item
                 fn-own-feed-find fn-own-feed-pending-delta)
                (fn-feed-live-port-step fn-own-feed-table-pending-model
                 fn-own-feed-put fn-own-feed-entry-of fn-own-feed-pending-of)))))

(defthm fn-ofct-found-feed-has-count-relation
  (implies (and (fn-ofct-table-relationp tbl)
                (fn-own-feed-entry-of peer tbl))
           (fn-feed-count-relationp (fn-own-feed-entry-feed
                                    (fn-own-feed-entry-of peer tbl))))
  :hints (("Goal" :induct (fn-own-feed-entry-of peer tbl)
                  :in-theory (enable fn-ofct-table-relationp
                                     fn-own-feed-entry-of))))

(defthm fn-ofct-put-preserves-table-count-relation
  (implies (and (fn-ofct-table-relationp tbl)
                (fn-feed-count-relationp new))
           (fn-ofct-table-relationp (fn-own-feed-put peer record new tbl)))
  :hints (("Goal" :induct (fn-own-feed-put peer record new tbl)
                  :in-theory (enable fn-ofct-table-relationp fn-own-feed-put
                                     fn-own-feed-entry fn-own-feed-entry-feed))))

(defthm fn-ofct-enqueue-all-counted-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp
            (car (fn-own-feed-enqueue-all-counted names tbl id tick pending))))
  :hints (("Goal" :induct (fn-own-feed-enqueue-all-counted names tbl id tick pending)
           :in-theory (e/d (fn-own-feed-enqueue-all-counted)
                            (fn-own-feed-enqueue-all fn-own-feed-entry-of fn-own-feed-put
                             fn-ofct-table-relationp fn-feed-enqueue
                             fn-ofct-enqueue-all-counted-has-the-original-table)))))

(defthm fn-ofct-port-peer-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp
            (fn-own-feed-port-table (fn-own-feed-port-peer peer tbl event))))
  :hints (("Goal" :in-theory
           (e/d (fn-own-feed-port-peer fn-own-feed-port-result
                 fn-own-feed-port-result-counted fn-own-feed-port-table
                 fn-frame-item)
                (fn-feed-live-port-step fn-feed-port-step-feed
                 fn-feed-port-step-records fn-feed-port-step-effects
                 fn-own-feed-put fn-own-feed-entry-of
                 fn-ofct-table-relationp)))))

(defthm fn-ofct-replay-peer-has-exact-aggregate-delta
  (equal (fn-own-feed-table-pending-model
          (fn-own-feed-port-table (fn-own-feed-port-replay-peer peer tbl entries)))
         (+ (fn-own-feed-table-pending-model tbl)
            (fn-own-feed-port-pending-delta
             (fn-own-feed-port-replay-peer peer tbl entries))))
  :hints (("Goal" :in-theory
           (e/d (fn-own-feed-port-replay-peer fn-own-feed-port-result
                 fn-own-feed-port-result-counted fn-own-feed-port-table
                 fn-own-feed-port-pending-delta fn-frame-item
                 fn-own-feed-find fn-own-feed-pending-delta)
                (fn-feed-replay fn-own-feed-table-pending-model
                 fn-own-feed-put fn-own-feed-entry-of fn-own-feed-pending-of)))))

(defthm fn-ofct-replay-peer-preserves-table-count-relation
  (implies (fn-ofct-table-relationp tbl)
           (fn-ofct-table-relationp
            (fn-own-feed-port-table (fn-own-feed-port-replay-peer peer tbl entries))))
  :hints (("Goal" :in-theory
           (e/d (fn-own-feed-port-replay-peer fn-own-feed-port-result
                 fn-own-feed-port-result-counted fn-own-feed-port-table fn-frame-item)
                (fn-feed-replay fn-own-feed-put fn-own-feed-entry-of
                 fn-ofct-table-relationp)))))

(in-theory (disable fn-ofct-table-relationp))
