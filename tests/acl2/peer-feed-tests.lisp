; fn: the outbound feed cluster's one test book (docs/proof-style.md sec. 6).
;
; Order: witnesses, the scenarios of specs/peering.md sec. 3 (a two-article
; feed to one peer with a 431 retry, a 435 duplicate, and a crash between the
; `sent' record and its outcome resolved by a CHECK), then the teeth: one
; concrete violating value per hypothesis of each keystone.

(in-package "ACL2")
(include-book "../../books/peer-feed-invariants")
(include-book "std/testing/assert-bang" :dir :system)

; -----------------------------------------------------------------------------
; Witnesses
;
; Non-degenerate: two articles, a peer with room for four, a retry bound of
; three, a streaming peer (CHECK/TAKETHIS) and a contact that holds.

(defconst *ff-peer* '(105 110 110))                       ; "inn"
(defconst *ff-a* '(60 97 64 102 110 62))                  ; "<a@fn>"
(defconst *ff-b* '(60 98 64 102 110 62))                  ; "<b@fn>"
(defconst *ff-c* '(60 99 64 102 110 62))                  ; "<c@fn>"

(defconst *ff-limits* (fn-feed-limits 4 1000 3 t))
(defconst *ff-contact* (fn-sched-contact "inn" 0 1000000))
(defconst *ff-obs* (fn-clock-observation 10 0 0 nil))
(defconst *ff-obs-later* (fn-clock-observation 500000 0 0 nil))

(assert-event (fn-feed-namep *ff-peer*))
(assert-event (fn-feed-namep *ff-a*))
(assert-event (fn-feed-limitsp *ff-limits*))
(assert-event (fn-sched-contactp *ff-contact*))
(assert-event (fn-clock-observationp *ff-obs*))
(assert-event (fn-sched-contact-holdsp *ff-contact* *ff-obs*))

(defconst *ff0* (fn-feed-open *ff-peer* *ff-limits* *ff-contact* 7))
(assert-event (fn-feedp *ff0*))
(assert-event (equal (fn-feed-conn *ff0*) 7))
(assert-event (null (fn-feed-queue *ff0*)))

; Two durable local acceptances, in order.
(defconst *ff1* (fn-feed-enqueue (fn-feed-enqueue *ff0* *ff-a* 1) *ff-b* 2))
(assert-event (fn-feedp *ff1*))
(assert-event (equal (len (fn-feed-queue *ff1*)) 2))
(assert-event (equal (fn-feed-state-of *ff-a* (fn-feed-queue *ff1*)) :queued))
(assert-event (equal (fn-feed-state-of *ff-b* (fn-feed-queue *ff1*)) :queued))

; Enqueue is refused, with the feed unchanged, for a Message-ID already queued.
(assert-event (equal (fn-feed-enqueue *ff1* *ff-a* 3) *ff1*))

; -----------------------------------------------------------------------------
; Scenario 1: the first offer is a CHECK for the head entry (FIFO)

(assert-event (equal (fn-feed-selection *ff1* *ff-obs*) *ff-a*))

(defconst *ff2* (mv-nth 0 (fn-feed-tick-step *ff1* *ff-obs*)))
(defconst *ff2-fx* (mv-nth 1 (fn-feed-tick-step *ff1* *ff-obs*)))

(assert-event (fn-feedp *ff2*))
(assert-event (equal *ff2-fx*
                     (list (list :command 7 (fn-feed-check-line *ff-a*)))))
(assert-event (fn-feed-offeredp (fn-feed-state-of *ff-a* (fn-feed-queue *ff2*))))
(assert-event (equal (fn-feed-state-attempt
                      (fn-feed-state-of *ff-a* (fn-feed-queue *ff2*)))
                     1))
(assert-event (equal (fn-feed-next-attempt *ff2*) 2))

; Nothing else is selected while an entry is in flight.
(assert-event (null (fn-feed-selection *ff2* *ff-obs*)))

; -----------------------------------------------------------------------------
; Scenario 2: 238, TAKETHIS, 239.  The entry finishes; the attempt id is the
; offer's, not a new one.

(defconst *ff3* (mv-nth 0 (fn-feed-observe *ff2* (fn-feed-response 238 *ff-a*)
                                           '(65 10) *ff-obs*)))
(defconst *ff3-fx* (mv-nth 1 (fn-feed-observe *ff2* (fn-feed-response 238 *ff-a*)
                                              '(65 10) *ff-obs*)))
(assert-event (fn-feed-sentp (fn-feed-state-of *ff-a* (fn-feed-queue *ff3*))))
(assert-event (equal (fn-feed-state-attempt
                      (fn-feed-state-of *ff-a* (fn-feed-queue *ff3*)))
                     1))
(assert-event (equal *ff3-fx*
                     (list (list :command 7
                                 (append (fn-feed-takethis-line *ff-a*)
                                         '(65 10))))))

(defconst *ff4* (mv-nth 0 (fn-feed-observe *ff3* (fn-feed-response 239 *ff-a*)
                                           nil *ff-obs*)))
(assert-event (equal (fn-feed-state-of *ff-a* (fn-feed-queue *ff4*)) :done))
(assert-event (equal (fn-feed-inflight-count (fn-feed-queue *ff4*)) 0))

; A finished entry is never selected again; the next selection is the second
; article.
(assert-event (equal (fn-feed-selection *ff4* *ff-obs*) *ff-b*))

; -----------------------------------------------------------------------------
; Scenario 3: 431 on the second article -- backoff, then a retry, then 435
; (the peer already has it), which finishes the entry just as 239 would.

(defconst *ff5* (mv-nth 0 (fn-feed-tick-step *ff4* *ff-obs*)))
(assert-event (fn-feed-offeredp (fn-feed-state-of *ff-b* (fn-feed-queue *ff5*))))

(defconst *ff6* (mv-nth 0 (fn-feed-observe *ff5* (fn-feed-response 431 *ff-b*)
                                           nil *ff-obs*)))
(assert-event (equal (fn-feed-state-of *ff-b* (fn-feed-queue *ff6*)) :queued))
(assert-event (equal (fn-feed-entry-attempts
                      (fn-feed-find *ff-b* (fn-feed-queue *ff6*)))
                     1))
; The backoff deadline moved out by the peer's base delay and the selection is
; refused until the clock passes it.
(assert-event (equal (fn-feed-backoff-until *ff6*) 1010))
(assert-event (null (fn-feed-selection *ff6* *ff-obs*)))
(assert-event (equal (fn-feed-selection *ff6* *ff-obs-later*) *ff-b*))

(defconst *ff7* (mv-nth 0 (fn-feed-tick-step *ff6* *ff-obs-later*)))
(assert-event (equal (fn-feed-state-attempt
                      (fn-feed-state-of *ff-b* (fn-feed-queue *ff7*)))
                     2))
(defconst *ff8* (mv-nth 0 (fn-feed-observe *ff7* (fn-feed-response 435 *ff-b*)
                                           nil *ff-obs-later*)))
(assert-event (equal (fn-feed-state-of *ff-b* (fn-feed-queue *ff8*)) :done))
(assert-event (null (fn-feed-selection *ff8* *ff-obs-later*)))

; -----------------------------------------------------------------------------
; Scenario 4: the crash between `sent' and its outcome, resolved by a CHECK
;
; The journal is the five records the host wrote before the kill: enqueue,
; enqueue, offer, sent -- and no outcome.  Replaying it and restarting leaves
; the third article queued with its attempt retired, so the next command is a
; CHECK and never a TAKETHIS.

(defconst *ff-journal*
  (list (fn-feed-journal-entry :feed-enqueue (list *ff-peer* *ff-a* 1))
        (fn-feed-journal-entry :feed-enqueue (list *ff-peer* *ff-b* 2))
        (fn-feed-journal-entry :feed-enqueue (list *ff-peer* *ff-c* 3))
        (fn-feed-journal-entry :feed-offer (list *ff-peer* *ff-a* 1 4))
        (fn-feed-journal-entry :feed-outcome (list *ff-peer* *ff-a* 1 239))
        (fn-feed-journal-entry :feed-offer (list *ff-peer* *ff-b* 2 5))
        (fn-feed-journal-entry :feed-sent (list *ff-peer* *ff-b* 2))))

(assert-event (fn-feed-journalp *ff-journal*))
(assert-event (fn-feed-drivenp *ff0* *ff-journal*))

(defconst *ff-replayed* (fn-feed-replay *ff0* *ff-journal*))
(assert-event (fn-feedp *ff-replayed*))
(assert-event (equal (fn-feed-state-of *ff-a* (fn-feed-queue *ff-replayed*))
                     :done))
(assert-event (fn-feed-sentp (fn-feed-state-of *ff-b*
                                               (fn-feed-queue *ff-replayed*))))
(assert-event (equal (fn-feed-state-of *ff-c* (fn-feed-queue *ff-replayed*))
                     :queued))

; The restart fences the in-flight entry.  Non-degenerate: something WAS in
; flight, and it is the entry the next command names.
(assert-event (fn-feed-inflightp *ff-b* *ff-replayed*))

(defconst *ff-restarted*
  (fn-feed-with-conn (fn-feed-restart *ff-replayed*) 9))
(assert-event (fn-feedp *ff-restarted*))
(assert-event (equal (fn-feed-inflight-count (fn-feed-queue *ff-restarted*)) 0))
(assert-event (equal (fn-feed-state-of *ff-b* (fn-feed-queue *ff-restarted*))
                     :queued))

; The first command after the restart is a CHECK of the formerly in-flight
; Message-ID, never a TAKETHIS.
(assert-event (equal (fn-feed-selection *ff-restarted* *ff-obs*) *ff-b*))
(defconst *ff-restart-fx*
  (mv-nth 1 (fn-feed-tick-step *ff-restarted* *ff-obs*)))
(assert-event (equal *ff-restart-fx*
                     (list (list :command 9 (fn-feed-check-line *ff-b*)))))
(assert-event (fn-feed-command-offersp
               (fn-frame-item 2 (car *ff-restart-fx*)) *ff-b*))
(assert-event (not (fn-feed-takethis-linep
                    (fn-frame-item 2 (car *ff-restart-fx*)) *ff-b*)))

; And the peer's own history answers: a 438 finishes the entry with no second
; copy transferred.
(defconst *ff-after-restart* (mv-nth 0 (fn-feed-tick-step *ff-restarted*
                                                          *ff-obs*)))
(defconst *ff-settled*
  (mv-nth 0 (fn-feed-observe *ff-after-restart*
                             (fn-feed-response 438 *ff-b*) nil *ff-obs*)))
(assert-event (equal (fn-feed-state-of *ff-b* (fn-feed-queue *ff-settled*))
                     :done))

; The whole journal, replayed, settles to the same queue states as the live
; feed it came from: replay determinism, on ground values.
(assert-event (equal (fn-feed-queue (fn-feed-settle *ff-replayed*))
                     (fn-feed-queue (fn-feed-restart *ff-replayed*))))
(assert-event
 (equal (fn-feed-replay *ff0* *ff-journal*)
        (fn-feed-replay (fn-feed-replay *ff0* (take 4 *ff-journal*))
                        (nthcdr 4 *ff-journal*))))

; -----------------------------------------------------------------------------
; Scenario 5: the retry bound drops the entry WITH its reason

(defconst *ff-lim1* (fn-feed-limits 4 1000 1 t))
(defconst *ff-tight* (fn-feed-enqueue
                      (fn-feed-open *ff-peer* *ff-lim1* *ff-contact* 7)
                      *ff-a* 1))
(defconst *ff-tight-offered* (mv-nth 0 (fn-feed-tick-step *ff-tight* *ff-obs*)))
(defconst *ff-tight-dropped*
  (mv-nth 0 (fn-feed-observe *ff-tight-offered*
                             (fn-feed-response 436 *ff-a*) nil *ff-obs*)))
(assert-event (fn-feed-droppedp
               (fn-feed-state-of *ff-a* (fn-feed-queue *ff-tight-dropped*))))
(assert-event (equal (fn-feed-state-reason
                      (fn-feed-state-of *ff-a*
                                        (fn-feed-queue *ff-tight-dropped*)))
                     :retry-bound))
(assert-event (null (fn-feed-selection *ff-tight-dropped* *ff-obs-later*)))

; -----------------------------------------------------------------------------
; Scenario 6: a 400 loses the connection; nothing is dropped

(defconst *ff-lost* (fn-feed-lost *ff5* *ff-obs*))
(assert-event (fn-feedp *ff-lost*))
(assert-event (null (fn-feed-conn *ff-lost*)))
(assert-event (equal (fn-feed-state-of *ff-b* (fn-feed-queue *ff-lost*))
                     :queued))
(assert-event (equal (len (fn-feed-queue *ff-lost*))
                     (len (fn-feed-queue *ff5*))))
(assert-event (null (fn-feed-selection *ff-lost* *ff-obs-later*)))

; -----------------------------------------------------------------------------
; The FNFD codec on ground records

(defconst *ff-digest* (make-list 32 :initial-element 0))
(assert-event (fn-frame-digestp *ff-digest*))

(assert-event (fn-feed-record-okp :feed-offer (list *ff-peer* *ff-a* 1 4)))
(assert-event (fn-feed-record-okp :feed-outcome (list *ff-peer* *ff-a* 1 239)))
(assert-event (fn-feed-record-okp :feed-drop
                                  (list *ff-peer* *ff-a* :retry-bound)))
(assert-event (fn-feed-record-okp :feed-restart (list *ff-peer*)))

; A code outside the closed outcome enumeration is not a record.
(assert-event (not (fn-feed-record-okp :feed-outcome
                                       (list *ff-peer* *ff-a* 1 999))))
; A drop reason outside the closed enumeration is not a record.
(assert-event (not (fn-feed-record-okp :feed-drop
                                       (list *ff-peer* *ff-a* :because))))
; An empty Message-ID is not `fn-frame-textp' and so is not a record.
(assert-event (not (fn-feed-record-okp :feed-offer (list *ff-peer* nil 1 4))))

(assert-event
 (equal (fn-feed-decode (fn-feed-encode :feed-outcome
                                        (list *ff-peer* *ff-a* 1 239)
                                        *ff-digest*)
                        *ff-digest*)
        (fn-frame-ok *fn-feed-magic* *fn-frame-version* :feed-outcome
                     (list *ff-peer* *ff-a* 1 239))))

; Canonicality on ground values: two different records never share octets.
(assert-event
 (not (equal (fn-feed-encode :feed-outcome (list *ff-peer* *ff-a* 1 239)
                             *ff-digest*)
             (fn-feed-encode :feed-outcome (list *ff-peer* *ff-a* 1 438)
                             *ff-digest*))))

; -----------------------------------------------------------------------------
; Teeth (docs/proof-style.md sec. 5): one concrete violating value per
; hypothesis.  Each is an `assert-event' on the negated conclusion, never a
; general negated `must-fail'.

; `fn-feed-at-most-one-accepted-outcome' -- drop `fn-feed-drivenp'.  A
; fabricated journal with two 239 outcomes for one attempt is well-formed
; (`fn-feed-journalp') and counts two; it is not driven, and that is the
; hypothesis doing the work.
(defconst *ff-forged-journal*
  (list (fn-feed-journal-entry :feed-enqueue (list *ff-peer* *ff-a* 1))
        (fn-feed-journal-entry :feed-offer (list *ff-peer* *ff-a* 1 2))
        (fn-feed-journal-entry :feed-outcome (list *ff-peer* *ff-a* 1 239))
        (fn-feed-journal-entry :feed-outcome (list *ff-peer* *ff-a* 1 239))))
(assert-event (fn-feed-journalp *ff-forged-journal*))
(assert-event (not (fn-feed-drivenp *ff0* *ff-forged-journal*)))
(assert-event (equal (fn-feed-count-accepted *ff-peer* *ff-a*
                                             *ff-forged-journal*)
                     2))

; `fn-feed-at-most-one-accepted-outcome' -- drop `fn-feedp'.  A forged feed
; whose queue holds the same Message-ID twice is not `fn-feedp'; the second
; entry is invisible to `fn-feed-state-of', so the fold's "once done, always
; done" argument has no purchase on it.
(defconst *ff-forged-feed*
  (fn-feed-make *ff-peer* *ff-limits*
                (list (fn-feed-entry *ff-a* :done 0 0)
                      (fn-feed-entry *ff-a* :queued 0 0))
                *ff-contact* 0 7 1))
(assert-event (not (fn-feedp *ff-forged-feed*)))
(assert-event (not (fn-feed-distinctp (fn-feed-queue *ff-forged-feed*))))
(assert-event (equal (fn-feed-state-of *ff-a* (fn-feed-queue *ff-forged-feed*))
                     :done))

; `fn-feed-restart-emits-no-transfer' -- drop `fn-feedp'.  A forged feed with
; TWO entries in flight is not `fn-feedp'; settle it by hand on one entry only
; and the other still emits a TAKETHIS, which is exactly the blind
; retransmission the restart rule forbids.
(defconst *ff-two-inflight*
  (fn-feed-make *ff-peer* *ff-limits*
                (list (fn-feed-entry *ff-a* (fn-feed-offered 1) 0 0)
                      (fn-feed-entry *ff-b* (fn-feed-offered 2) 0 0))
                *ff-contact* 0 7 3))
(assert-event (not (fn-feedp *ff-two-inflight*)))
(assert-event (equal (fn-feed-inflight-count (fn-feed-queue *ff-two-inflight*))
                     2))
(assert-event (equal (fn-feed-restart *ff-two-inflight*) *ff-two-inflight*))
(assert-event (consp (mv-nth 1 (fn-feed-send
                                (fn-feed-restart *ff-two-inflight*)
                                *ff-a* '(65 10)))))

; `fn-feed-selection-is-queued' -- drop the contact hypothesis inside the
; selection: the same feed with an observation OUTSIDE the contact window
; selects nothing, so the offer the scheduler's window gates really is gated.
(defconst *ff-outside* (fn-clock-observation 2000000 0 0 nil))
(assert-event (not (fn-sched-contact-holdsp *ff-contact* *ff-outside*)))
(assert-event (null (fn-feed-selection *ff1* *ff-outside*)))

; `fn-feed-selection' -- drop the connection.  A feed with no connection
; selects nothing however well the contact holds.
(assert-event (null (fn-feed-selection (fn-feed-with-conn *ff1* nil) *ff-obs*)))

; `fn-feed-drop-needs-a-drop-record' -- the separating witness.  Replaying the
; journal WITHOUT its drop record leaves the entry queued, not dropped: the
; drop is in the record, not in the machine.
(defconst *ff-drop-journal*
  (list (fn-feed-journal-entry :feed-enqueue (list *ff-peer* *ff-a* 1))
        (fn-feed-journal-entry :feed-drop (list *ff-peer* *ff-a* :retry-bound))))
(assert-event (fn-feed-drivenp *ff0* *ff-drop-journal*))
(assert-event (fn-feed-droppedp
               (fn-feed-state-of *ff-a*
                                 (fn-feed-queue (fn-feed-replay
                                                 *ff0* *ff-drop-journal*)))))
(assert-event (fn-feed-has-drop-recordp *ff-peer* *ff-a* *ff-drop-journal*))
(assert-event (not (fn-feed-droppedp
                    (fn-feed-state-of *ff-a*
                                      (fn-feed-queue
                                       (fn-feed-replay
                                        *ff0* (take 1 *ff-drop-journal*)))))))
(assert-event (not (fn-feed-has-drop-recordp *ff-peer* *ff-a*
                                             (take 1 *ff-drop-journal*))))

; `fn-feed-back-off-does-not-lower-the-deadline' -- the separating witness.
; The delay grows with the attempt count and is clamped at the ceiling, so a
; peer record with a large base cannot make the feed spin.
(assert-event (equal (fn-feed-backoff-delay 1000 0) 1000))
(assert-event (equal (fn-feed-backoff-delay 1000 1) 2000))
(assert-event (equal (fn-feed-backoff-delay 1000 2) 4000))
(assert-event (equal (fn-feed-backoff-delay 1000 40) *fn-feed-max-backoff*))
(assert-event (equal (fn-feed-backoff-delay (+ 1 *fn-feed-max-backoff*) 0)
                     *fn-feed-max-backoff*))

; `fn-feed-enqueue' -- the queue bound is real: a fifth article is refused and
; the feed is unchanged (no silent drop, no growth past the peer's max-queue).
(defconst *ff-full*
  (fn-feed-enqueue
   (fn-feed-enqueue
    (fn-feed-enqueue (fn-feed-enqueue *ff0* '(60 49 62) 1) '(60 50 62) 2)
    '(60 51 62) 3)
   '(60 52 62) 4))
(assert-event (equal (len (fn-feed-queue *ff-full*)) 4))
(assert-event (equal (fn-feed-enqueue *ff-full* '(60 53 62) 5) *ff-full*))
