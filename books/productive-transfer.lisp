; fn: the productive TRANSFER, the LOCAL completion (lane
; productive-read-transfer, row W6b, 2026-09-30; PRF-1055
; fn-pct-tick-hands-the-article-to-the-transport, PRF-1056
; fn-pct-tick-hands-nothing-otherwise).
;
; WIP -- DRAFT STATEMENTS, NOT YET REPL-ADMITTED (wind-down 2026-09-30).
; The successor admits them in proof_repl (LANEDUMP.md NEXT) before this
; book goes into the Makefile.
;
; THREE THINGS KEPT APART (GPT-6 section D: READ/TRANSFER local vs remote):
;   LOCAL COMPLETION (this book): the article is handed to the transport and
;     the obligation is recorded.  The subject is fn-own-feed-port-tick-peer
;     PEER TBL OBS, which host/owner-host.lisp fn-owner-feed-tick calls once
;     per peer tick: under the named premises the tick's effect is ONE
;     :command on the peer's connection carrying the offer line (IHAVE or
;     CHECK, by the peer's streaming form) for the head queued Message-ID,
;     its record batch is exactly the :feed-offer FNFD record (peer, msgid,
;     attempt, tick) -- the obligation the host journals before it sends
;     (fn-feed-live-port-step: no record, no effect) -- and the queue entry
;     is in flight at that attempt.  The article was queued by
;     fn-own-feed-durable at the durable acceptance (PRF-1001's o9), which
;     books/owner.lisp calls once per submission.
;   REMOTE DELIVERY: the peer's reply line drives fn-own-feed-port-observe-peer
;     (335/238: the article's octets are sent, fn-feed-send; 235/239 and the
;     refusals: done; 431/436: back off).  Not proved here; the peer's
;     behaviour is a premise, not a theorem.
;   THE PEER'S PROCESSING: what the peer does with the article after 235/239
;     is the peer's own lifecycle (its prefix 1), outside this node's claim.
; ASSUMED PEER / CONTACT BEHAVIOUR, each a named hypothesis below:
;   the contact holds at OBS (fn-sched-contact-holdsp: the operator's
;   contact window), the transport connection is up (a natural conn: the
;   host dialled and the peer accepted the connection), the backoff has
;   elapsed, nothing is in flight (the peer answered the previous offer).

(in-package "ACL2")
(include-book "owner-feed")

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

; PRF-1055.  The local completion.
(defthm fn-pct-tick-hands-the-article-to-the-transport
  (let* ((e (fn-own-feed-entry-of peer tbl))
         (f (fn-own-feed-entry-feed e))
         (msgid (fn-feed-head-queued (fn-feed-queue f)))
         (attempt (fn-feed-next-attempt f))
         (result (fn-own-feed-port-tick-peer peer tbl obs))
         (g (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feed-port-table result)))))
    (implies (and e
                  (fn-pct-selectablep f obs)
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
           :use (fn-pct-selection-when-selectable-by-definition)
           :in-theory (e/d (fn-own-feed-port-tick-peer fn-own-feed-port-peer
                            fn-feed-live-port-step fn-feed-live-next fn-feed-live-records
                            fn-feed-live-effects fn-feed-tick-step fn-feed-tick-records
                            fn-feed-offer fn-own-feed-port-result fn-own-feed-port-status
                            fn-own-feed-port-table fn-own-feed-port-records fn-own-feed-port-effects
                            fn-own-feed-entry-of-of-put-same fn-pct-selectablep)
                           (fn-feed-selection fn-feedp fn-feed-offer-line fn-feed-journal-entry
                            fn-feed-head-queued fn-feed-state-of fn-feed-queue-set-state
                            fn-feed-inflight-count fn-sched-contact-holdsp fn-feed-records-portp)))))

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
    (and (implies (and e (fn-feedp f) (null (fn-feed-selection f obs)))
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
                            fn-own-feed-entry-of-of-put-same)
                           (fn-feed-selection fn-feedp fn-feed-offer fn-feed-records-portp
                            fn-feed-journal-entry)))))
