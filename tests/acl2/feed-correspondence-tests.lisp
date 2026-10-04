(in-package "ACL2")
(include-book "../../books/feed-events")
(include-book "must-fail-checked")

(defconst *fn-feed-ct-peer* '(105 110 110))
(defconst *fn-feed-ct-a* '(60 97 64 102 110 62))
(defconst *fn-feed-ct-b* '(60 98 64 102 110 62))
(defconst *fn-feed-ct-obs* (fn-clock-observation 10 0 0 nil))
(defconst *fn-feed-ct-open*
  (fn-feed-open *fn-feed-ct-peer* (fn-feed-limits 4 1000 2 t)
                (fn-sched-contact "inn" 0 1000000) 7))
(defconst *fn-feed-ct-queued*
  (fn-feed-enqueue *fn-feed-ct-open* *fn-feed-ct-a* 1))
(defconst *fn-feed-ct-offered*
  (fn-feed-live-next *fn-feed-ct-queued* (list :tick *fn-feed-ct-obs*)))
(defconst *fn-feed-ct-retry*
  (fn-feed-live-next *fn-feed-ct-offered*
    (list :reply (fn-feed-response 431 *fn-feed-ct-a*) nil *fn-feed-ct-obs*)))
; Normal enqueue -> offer -> 431: the live run keeps the tick and sets the
; deadline, and the record it journals is a :feed-retry carrying the tick.
; A :feed-outcome with a retry code (the pre-6.6.0 shape, which lost both) is
; no record at all, so a journal carrying one is invalid evidence at the scan.
(assert-event (fn-feedp *fn-feed-ct-offered*))
(assert-event (equal (fn-feed-backoff-until *fn-feed-ct-retry*) 1010))
(assert-event (equal (fn-feed-entry-tick
  (fn-feed-find *fn-feed-ct-a* (fn-feed-queue *fn-feed-ct-retry*))) 10))
(assert-event (equal (fn-feed-journal-kind
  (car (fn-feed-observe-records *fn-feed-ct-offered*
         (fn-feed-response 431 *fn-feed-ct-a*) *fn-feed-ct-obs*))) :feed-retry))
(assert-event (not (fn-feed-record-okp :feed-outcome
                     (list *fn-feed-ct-peer* *fn-feed-ct-a* 1 431))))

; A loss with no in-flight entry still changes backoff. The previous emitter
; returned no record for this reachable open -> enqueue -> socket-close run.
(assert-event (equal (fn-feed-inflight-count (fn-feed-queue *fn-feed-ct-queued*)) 0))
(must-fail-checked (assert-event
 (equal (fn-feed-durable-projection *fn-feed-ct-queued*)
        (fn-feed-durable-projection (fn-feed-lost *fn-feed-ct-queued* *fn-feed-ct-obs*)))))

; S053 (inspection sweep 2026-10-03): a loss that reaches the retry bound
; (2 here) journals the :feed-lost and then a :feed-drop naming the entry,
; and the replay of the two is the live loss; a loss under the bound
; journals the :feed-lost alone.
(defconst *fn-feed-ct-lost1*
  (fn-feed-lost *fn-feed-ct-offered* *fn-feed-ct-obs*))
(assert-event
 (equal (fn-feed-lost-records *fn-feed-ct-offered* *fn-feed-ct-obs*)
        (list (fn-feed-journal-entry :feed-lost (list *fn-feed-ct-peer* 10)))))
(defconst *fn-feed-ct-reoffered*
  (fn-feed-live-next (fn-feed-with-conn *fn-feed-ct-lost1* 7)
                     (list :tick (fn-clock-observation 5000 0 0 nil))))
(assert-event
 (equal (fn-feed-lost-records *fn-feed-ct-reoffered* (fn-clock-observation 5000 0 0 nil))
        (list (fn-feed-journal-entry :feed-lost (list *fn-feed-ct-peer* 5000))
              (fn-feed-journal-entry :feed-drop
                                     (list *fn-feed-ct-peer* *fn-feed-ct-a* :retry-bound)))))
(assert-event
 (equal (fn-feed-durable-projection
         (fn-feed-replay *fn-feed-ct-reoffered*
                         (fn-feed-lost-records *fn-feed-ct-reoffered*
                                               (fn-clock-observation 5000 0 0 nil))))
        (fn-feed-durable-projection
         (fn-feed-lost *fn-feed-ct-reoffered* (fn-clock-observation 5000 0 0 nil)))))
; The give-up retires <a> in the same step (rp-feed-dropped-holds-capacity):
; no entry is left behind to hold the peer's queue slot.
(assert-event
 (not (consp
       (fn-feed-find *fn-feed-ct-a*
                     (fn-feed-queue (fn-feed-lost *fn-feed-ct-reoffered*
                                                  (fn-clock-observation 5000 0 0 nil)))))))
(assert-event
 (equal (fn-feed-undelivered (fn-feed-lost *fn-feed-ct-reoffered*
                                           (fn-clock-observation 5000 0 0 nil)))
        0))
; Teeth: the :feed-lost record alone (no drop record) does not replay to the
; live loss once the bound is reached.
(assert-event
 (not (equal (fn-feed-durable-projection
              (fn-feed-replay *fn-feed-ct-reoffered*
                              (take 1 (fn-feed-lost-records *fn-feed-ct-reoffered*
                                                            (fn-clock-observation 5000 0 0 nil)))))
             (fn-feed-durable-projection
              (fn-feed-lost *fn-feed-ct-reoffered* (fn-clock-observation 5000 0 0 nil))))))

; Repeated go-ahead after sending is a reachable peer input. It has no live
; effect and must not append a second, undriven :feed-sent record.
(defconst *fn-feed-ct-sent*
  (fn-feed-live-next *fn-feed-ct-offered*
    (list :reply (fn-feed-response 238 *fn-feed-ct-a*) '(65 13 10) *fn-feed-ct-obs*)))
(assert-event (null (fn-feed-observe-records *fn-feed-ct-sent*
  (fn-feed-response 238 *fn-feed-ct-a*) *fn-feed-ct-obs*)))
(must-fail-checked (assert-event (fn-feed-drivenp *fn-feed-ct-sent*
  (list (fn-feed-journal-entry :feed-sent
          (list *fn-feed-ct-peer* *fn-feed-ct-a* 1))))))

(defconst *fn-feed-ct-events*
 (list
  (list :enqueue *fn-feed-ct-a* 1)
  (list :enqueue *fn-feed-ct-b* 2)
  (list :tick (fn-clock-observation 10 0 0 nil))
  (list :reply (fn-feed-response 238 *fn-feed-ct-a*) '(65 13 10)
        (fn-clock-observation 11 0 0 nil))
  (list :reply (fn-feed-response 431 *fn-feed-ct-a*) nil
        (fn-clock-observation 12 0 0 nil))
  (list :tick (fn-clock-observation 2000 0 0 nil))
  (list :reply (fn-feed-response 431 *fn-feed-ct-a*) nil
        (fn-clock-observation 2001 0 0 nil))
  (list :tick (fn-clock-observation 5000 0 0 nil))
  (list :lost (fn-clock-observation 5001 0 0 nil))
  (list :restart)
  (list :connect 8)
  (list :tick (fn-clock-observation 7000 0 0 nil))
  (list :reply (fn-feed-response 238 *fn-feed-ct-a*) '(65 13 10)
        (fn-clock-observation 7001 0 0 nil))
  (list :reply (fn-feed-response 239 *fn-feed-ct-a*) nil
        (fn-clock-observation 7002 0 0 nil))
  (list :tick (fn-clock-observation 7003 0 0 nil))
  (list :reply (fn-feed-response 238 *fn-feed-ct-b*) '(66 13 10)
        (fn-clock-observation 7004 0 0 nil))
  (list :reply (fn-feed-response 239 *fn-feed-ct-b*) nil
        (fn-clock-observation 7005 0 0 nil))))
(defconst *fn-feed-ct-history*
 (fn-feed-live-history *fn-feed-ct-open* *fn-feed-ct-events*))
(defconst *fn-feed-ct-final* (fn-feed-live-run *fn-feed-ct-open* *fn-feed-ct-events*))
(assert-event (fn-feed-live-serializablep *fn-feed-ct-open* *fn-feed-ct-events*))
(assert-event (fn-feed-drivenp *fn-feed-ct-open* *fn-feed-ct-history*))
(assert-event (equal (fn-feed-durable-projection *fn-feed-ct-final*)
 (fn-feed-durable-projection (fn-feed-replay *fn-feed-ct-open* *fn-feed-ct-history*))))
; Two 431s at a retry bound of two, then a loss: <a> is still delivered
; (rp-feed-defer-drop; before 2026-10-04 the second 431 dropped it), and
; then <b>.
(assert-event (not (consp (fn-feed-find *fn-feed-ct-a* (fn-feed-queue *fn-feed-ct-final*)))))
(assert-event (not (consp (fn-feed-find *fn-feed-ct-b* (fn-feed-queue *fn-feed-ct-final*)))))
(assert-event (equal (fn-feed-retry-dropped *fn-feed-ct-final*) 0))
(assert-event (equal (fn-feed-count-accepted *fn-feed-ct-peer* *fn-feed-ct-a*
                                             *fn-feed-ct-history*)
                     1))
(assert-event (not (fn-feed-has-drop-recordp *fn-feed-ct-peer* *fn-feed-ct-a*
                                             *fn-feed-ct-history*)))
; The loss at 5001 set the deadline to 6001 in the first run's clock; the
; :restart forgets it (lane time-bars, PRF-385: a new process's clock), and
; nothing after it backed off.
(assert-event (equal (fn-feed-backoff-until *fn-feed-ct-final*) 0))
(assert-event (equal (fn-feed-next-attempt *fn-feed-ct-final*) 6))

; rp-feed-defer-drop: a deferral's records are its :feed-retry alone, at any
; attempt count -- never a :feed-drop.
(defconst *fn-feed-ct-tight-offered*
  (fn-feed-live-next
   (fn-feed-enqueue (fn-feed-open *fn-feed-ct-peer* (fn-feed-limits 4 1000 1 t)
                                  (fn-sched-contact "inn" 0 1000000) 7)
                    *fn-feed-ct-a* 1)
   (list :tick *fn-feed-ct-obs*)))
(assert-event
 (equal (fn-feed-observe-records *fn-feed-ct-tight-offered*
                                 (fn-feed-response 436 *fn-feed-ct-a*) *fn-feed-ct-obs*)
        (list (fn-feed-journal-entry
               :feed-retry (list *fn-feed-ct-peer* *fn-feed-ct-a* 1 436 10)))))

; rp-feed-reply-msgid: a reply naming an entry not in flight writes the
; loss's records and replays to the live loss; it writes no outcome.  Here
; `239 <b>' arrives while <a> is in flight at a bound of one, so the loss
; gives <a> up -- with its :feed-drop, never an accepted outcome for either.
(defconst *fn-feed-ct-two-offered*
  (fn-feed-live-next
   (fn-feed-enqueue (fn-feed-enqueue (fn-feed-open *fn-feed-ct-peer* (fn-feed-limits 4 1000 1 t)
                                                   (fn-sched-contact "inn" 0 1000000) 7)
                                     *fn-feed-ct-a* 1)
                    *fn-feed-ct-b* 2)
   (list :tick *fn-feed-ct-obs*)))
(assert-event (equal (fn-feed-reply-class *fn-feed-ct-two-offered*
                                          (fn-feed-response 239 *fn-feed-ct-b*))
                     :lost))
(assert-event
 (equal (fn-feed-observe-records *fn-feed-ct-two-offered*
                                 (fn-feed-response 239 *fn-feed-ct-b*) *fn-feed-ct-obs*)
        (list (fn-feed-journal-entry :feed-lost (list *fn-feed-ct-peer* 10))
              (fn-feed-journal-entry :feed-drop
                                     (list *fn-feed-ct-peer* *fn-feed-ct-a* :retry-bound)))))
(assert-event
 (equal (fn-feed-durable-projection
         (fn-feed-replay *fn-feed-ct-two-offered*
                         (fn-feed-observe-records *fn-feed-ct-two-offered*
                                                  (fn-feed-response 239 *fn-feed-ct-b*)
                                                  *fn-feed-ct-obs*)))
        (fn-feed-durable-projection
         (fn-feed-live-next *fn-feed-ct-two-offered*
                            (list :reply (fn-feed-response 239 *fn-feed-ct-b*) nil
                                  *fn-feed-ct-obs*)))))
; <b> is still owed: the stray answer accepted nothing.
(assert-event
 (consp (fn-feed-find *fn-feed-ct-b*
                      (fn-feed-queue
                       (fn-feed-live-next *fn-feed-ct-two-offered*
                                          (list :reply (fn-feed-response 239 *fn-feed-ct-b*)
                                                nil *fn-feed-ct-obs*))))))
