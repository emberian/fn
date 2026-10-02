; Productive outbound NNTP feed transitions (W6b).
; Host subjects: fn-own-feed-port-tick-peer in fn-owner-feed-tick, and
; fn-own-feed-port-observe-peer in fn-owner-feed-octets.
;
; PRF-1055 proves offer progress (CHECK/IHAVE), not article handoff.
; PRF-1062 proves the requested article is handed to the local transport
; as an effect, with a matching :feed-sent FNFD record and attempt retained.
; The host journals the publication before writing its rendered command.
; These core effects do not establish socket success, remote acceptance,
; remote durability, or remote processing. Native execution evidence names
; the matching image separately. The actual caller obtains the article
; octets via fn-ofa-feed-article, not an arena handle.
; PRF-1056 keeps quiet admission and explicit refusal distinct.
;
; Teeth assert complete literal antecedents/conclusions, remove each
; hypothesis with all retained hypotheses checked, and keep a mutant
; :feed-offer record separate from the required :feed-sent record.

(in-package "ACL2")
(include-book "owner-feed")
(include-book "peer-feed-invariants")

; The tick's named premises, as fn-feed-selection decides them.
(defun fn-pct-selectablep (f obs)
  (declare (xargs :guard t))
  (and (fn-feedp f)
       (fn-clock-observationp obs)
       (fn-sched-contact-holdsp (fn-feed-contact f) obs)
       (natp (fn-feed-conn f))
       (<= (nfix (fn-feed-backoff-until f)) (nfix (fn-clock-monotonic obs)))
       (equal (fn-feed-inflight-count (fn-feed-queue f)) 0)
       (if (fn-feed-head-queued (fn-feed-queue f)) t nil)))

(defthm fn-pct-selection-when-selectable-by-definition
  (implies (fn-pct-selectablep f obs)
           (equal (fn-feed-selection f obs) (fn-feed-head-queued (fn-feed-queue f))))
  :hints (("Goal" :in-theory (enable fn-feed-selection fn-pct-selectablep))))

(local
 (defthm fn-pct-next-attempt-natural
   (implies (fn-feedp f) (natp (fn-feed-next-attempt f)))
   :hints (("Goal" :in-theory (enable fn-feedp)))))
(local
 (defthm fn-pct-selected-is-queued
   (implies (fn-pct-selectablep f obs)
            (equal (fn-feed-state-of (fn-feed-head-queued (fn-feed-queue f))
                                    (fn-feed-queue f)) :queued))
   :hints (("Goal" :use (fn-feed-selection-is-queued fn-pct-selection-when-selectable-by-definition)
            :in-theory (e/d (fn-pct-selectablep)
                             (fn-feed-selection fn-feedp fn-feed-state-of
                              fn-pct-selection-when-selectable-by-definition))))))
(local
 (defthm fn-pct-selected-present
   (implies (fn-pct-selectablep f obs)
            (consp (fn-feed-find (fn-feed-head-queued (fn-feed-queue f))
                                 (fn-feed-queue f))))
   :hints (("Goal" :use fn-pct-selected-is-queued
            :in-theory (e/d (fn-feed-state-of fn-feed-entry-state fn-frame-item)
                             (fn-feed-find fn-pct-selectablep))))))

(local
 (defthm fn-pct-feed-requires-entry
   (implies (fn-feedp (fn-own-feed-entry-feed e)) e)
   :rule-classes :forward-chaining
   :hints (("Goal" :cases (e)
            :in-theory (enable fn-feedp fn-own-feed-entry-feed fn-feed-shapep)))))

; PRF-1055.  The local completion.
(defthm fn-pct-tick-offers-the-queued-article
  (let* ((e (fn-own-feed-entry-of peer tbl))
         (f (fn-own-feed-entry-feed e))
         (msgid (fn-feed-head-queued (fn-feed-queue f)))
         (attempt (fn-feed-next-attempt f))
         (result (fn-own-feed-port-tick-peer peer tbl obs))
         (g (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feed-port-table result)))))
    (implies (and (fn-pct-selectablep f obs)
                  (fn-feed-records-portp (fn-feed-tick-records f obs)))
             (and (equal (fn-own-feed-port-status result) :accepted)
                  (equal (fn-own-feed-port-effects result)
                         (list (cons peer
                                     (list (list :command (fn-feed-conn f)
                                                 (fn-feed-offer-line
                                                  msgid (fn-feed-streamingp (fn-feed-limits-of f))))))))
                  (equal (fn-own-feed-port-records result)
                         (list (fn-feed-journal-entry
                                :feed-offer
                                (list (fn-feed-peer f) msgid attempt
                                      (nfix (fn-clock-monotonic obs))))))
                  (equal (fn-feed-state-of msgid (fn-feed-queue g)) (fn-feed-offered attempt))
                  (equal (fn-feed-next-attempt g) (+ 1 attempt)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pct-selection-when-selectable-by-definition
                            (f (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))))
                 (:instance fn-pct-selected-is-queued
                            (f (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))))
                 (:instance fn-pct-selected-present
                            (f (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))))
                 (:instance fn-pct-next-attempt-natural
                            (f (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl)))))
           :in-theory (union-theories
                       '(fn-own-feed-port-tick-peer fn-own-feed-port-peer
                         fn-feed-live-port-step fn-feed-live-next fn-feed-live-records
                         fn-feed-live-effects fn-feed-tick-step fn-feed-tick-records
                         fn-feed-offer fn-own-feed-port-result fn-own-feed-port-status
                         fn-own-feed-port-table fn-own-feed-port-records fn-own-feed-port-effects
                         fn-feed-port-step-status fn-feed-port-step-feed
                         fn-feed-port-step-records fn-feed-port-step-effects
                         fn-frame-item fn-pct-selectablep fn-feed-offered
                         fn-pct-feed-requires-entry
                         fn-own-feed-entry-of-of-put-same fn-own-feed-entry-feed-of-entry-scoped
                         fn-feed-queue-of-fn-feed-make fn-feed-next-attempt-of-fn-feed-make
                         fn-feed-queue-of-counted-make fn-feed-next-attempt-of-counted-make
                         fn-feed-state-of-of-set-state-same
                         fn-pct-selected-is-queued fn-pct-selected-present
                         fn-pct-next-attempt-natural fn-pct-selection-when-selectable-by-definition
                         car-cons cdr-cons
                         natp nfix not)
                       (union-theories (theory 'minimal-theory)
                                       (executable-counterpart-theory :here))))))

; PRF-1056.  Nothing is handed and nothing is recorded otherwise: with no
; selection (no contact, connection down, backoff pending, an offer in
; flight, nothing queued) the tick is accepted quiet and the feed is kept;
; a table entry whose feed is not a feed, or whose record batch is not
; portable, is refused with the table unchanged.  A refusal preserves every
; unit of queued work and exposes neither a record nor an effect.
(defthm fn-pct-tick-hands-nothing-otherwise
  (let* ((e (fn-own-feed-entry-of peer tbl))
         (f (fn-own-feed-entry-feed e))
         (result (fn-own-feed-port-tick-peer peer tbl obs)))
    (and (implies (and (fn-feedp f) (null (fn-feed-selection f obs)))
                  (and (equal (fn-own-feed-port-status result) :accepted)
                       (null (fn-own-feed-port-effects result))
                       (null (fn-own-feed-port-records result))
                       (equal (fn-own-feed-entry-feed
                               (fn-own-feed-entry-of peer (fn-own-feed-port-table result)))
                              f)))
         (implies (and e (or (not (fn-feedp f))
                             (not (fn-feed-records-portp (fn-feed-tick-records f obs)))))
                  (and (equal (fn-own-feed-port-status result) :refused)
                       (equal (fn-own-feed-port-table result) tbl)
                       (null (fn-own-feed-port-effects result))
                       (null (fn-own-feed-port-records result))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-own-feed-port-tick-peer fn-own-feed-port-peer
                            fn-feed-live-port-step fn-feed-live-next fn-feed-live-records
                            fn-feed-live-effects fn-feed-tick-step fn-feed-tick-records
                            fn-own-feed-port-result fn-own-feed-port-status
                            fn-own-feed-port-table fn-own-feed-port-records fn-own-feed-port-effects
                            fn-own-feed-entry-of-of-put-same fn-pct-feed-requires-entry)
                           (fn-feed-selection fn-feedp fn-feed-offer fn-feed-records-portp
                            fn-feed-journal-entry)))))

; PRF-1062. A 335/238 requests the article.  The actual host-called port
; emits its octets and a matching :feed-sent record, without completing the
; remote acceptance obligation.  The article argument comes from
; fn-ofa-feed-article in fn-owner-feed-octets; it is not a payload handle.
(defthm fn-pct-requested-article-is-handed-to-the-local-transport
  (let* ((e (fn-own-feed-entry-of peer tbl))
         (f (fn-own-feed-entry-feed e))
         (msgid (fn-feed-response-msgid response))
         (attempt (fn-feed-state-attempt (fn-feed-state-of msgid (fn-feed-queue f))))
         (result (fn-own-feed-port-observe-peer peer tbl response article obs))
         (g (fn-own-feed-entry-feed
             (fn-own-feed-entry-of peer (fn-own-feed-port-table result)))))
    (implies (and (fn-feedp f)
                  (member-equal (fn-feed-response-code response) '(335 238))
                  (fn-feed-offeredp (fn-feed-state-of msgid (fn-feed-queue f)))
                  (natp (fn-feed-conn f))
                  (fn-feed-records-portp (fn-feed-observe-records f response obs)))
             (and (equal (fn-own-feed-port-status result) :accepted)
                  (equal (fn-own-feed-port-effects result)
                         (list (cons peer
                                     (list (list :command (fn-feed-conn f)
                                                 (if (fn-feed-streamingp (fn-feed-limits-of f))
                                                     (append (fn-feed-takethis-line msgid) article)
                                                   article))))))
                  (equal (fn-own-feed-port-records result)
                         (list (fn-feed-journal-entry
                                :feed-sent (list (fn-feed-peer f) msgid attempt))))
                  (equal (fn-feed-state-of msgid (fn-feed-queue g))
                         (fn-feed-sent attempt))
                  (equal (fn-feed-next-attempt g) (fn-feed-next-attempt f)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-feed-find-is-consp-when-the-state-is-a-state
                            (msgid (fn-feed-response-msgid response))
                            (xs (fn-feed-queue
                                 (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))))) )
           :in-theory (e/d
                       (fn-own-feed-port-observe-peer fn-own-feed-port-peer
                        fn-own-feed-port-result fn-own-feed-port-status
                        fn-own-feed-port-table fn-own-feed-port-records fn-own-feed-port-effects
                        fn-feed-port-step-status fn-feed-port-step-feed
                        fn-feed-port-step-records fn-feed-port-step-effects
                        fn-feed-live-port-step fn-feed-live-next fn-feed-live-records
                        fn-feed-live-effects fn-feed-observe fn-feed-observe-records
                        fn-feed-send fn-feed-with-queue fn-feed-state-of-of-set-state-same
                        fn-pct-feed-requires-entry)
                       (fn-own-feed-entry-of fn-own-feed-put fn-feedp fn-feed-state-of
                        fn-feed-state-attempt fn-feed-response-code fn-feed-response-msgid
                        fn-feed-queue-set-state fn-feed-offeredp fn-feed-sent
                        fn-feed-journal-entry fn-feed-records-portp fn-feed-takethis-line
                        fn-feed-back-off fn-feed-lost fn-feed-done)))))
