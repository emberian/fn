(in-package "ACL2")
(include-book "../../books/feed-events")
(include-book "std/testing/must-fail" :dir :system)

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
(defconst *fn-feed-ct-old-retry-record*
  (fn-feed-journal-entry :feed-outcome
    (list *fn-feed-ct-peer* *fn-feed-ct-a* 1 431)))

; Executable legacy counterexample: normal enqueue -> offer -> 431. The old
; history lost both the remembered tick and the deadline, not merely conn.
(assert-event (fn-feedp *fn-feed-ct-offered*))
(assert-event (equal (fn-feed-backoff-until *fn-feed-ct-retry*) 1010))
(assert-event (equal (fn-feed-entry-tick
  (fn-feed-find *fn-feed-ct-a* (fn-feed-queue *fn-feed-ct-retry*))) 10))
(assert-event (equal (fn-feed-backoff-until
  (fn-feed-replay *fn-feed-ct-offered* (list *fn-feed-ct-old-retry-record*))) 0))
(must-fail (assert-event
 (equal (fn-feed-durable-projection *fn-feed-ct-retry*)
        (fn-feed-durable-projection (fn-feed-replay *fn-feed-ct-offered*
          (list *fn-feed-ct-old-retry-record*))))))

; A loss with no in-flight entry still changes backoff. The previous emitter
; returned no record for this reachable open -> enqueue -> socket-close run.
(assert-event (equal (fn-feed-inflight-count (fn-feed-queue *fn-feed-ct-queued*)) 0))
(must-fail (assert-event
 (equal (fn-feed-durable-projection *fn-feed-ct-queued*)
        (fn-feed-durable-projection (fn-feed-lost *fn-feed-ct-queued* *fn-feed-ct-obs*)))))

; Repeated go-ahead after sending is a reachable peer input. It has no live
; effect and must not append a second, undriven :feed-sent record.
(defconst *fn-feed-ct-sent*
  (fn-feed-live-next *fn-feed-ct-offered*
    (list :reply (fn-feed-response 238 *fn-feed-ct-a*) '(65 13 10) *fn-feed-ct-obs*)))
(assert-event (null (fn-feed-observe-records *fn-feed-ct-sent*
  (fn-feed-response 238 *fn-feed-ct-a*) *fn-feed-ct-obs*)))
(must-fail (assert-event (fn-feed-drivenp *fn-feed-ct-sent*
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
  (list :reply (fn-feed-response 238 *fn-feed-ct-b*) '(66 13 10)
        (fn-clock-observation 7001 0 0 nil))
  (list :reply (fn-feed-response 239 *fn-feed-ct-b*) nil
        (fn-clock-observation 7002 0 0 nil))))
(defconst *fn-feed-ct-history*
 (fn-feed-live-history *fn-feed-ct-open* *fn-feed-ct-events*))
(defconst *fn-feed-ct-final* (fn-feed-live-run *fn-feed-ct-open* *fn-feed-ct-events*))
(assert-event (fn-feed-live-serializablep *fn-feed-ct-open* *fn-feed-ct-events*))
(assert-event (fn-feed-drivenp *fn-feed-ct-open* *fn-feed-ct-history*))
(assert-event (equal (fn-feed-durable-projection *fn-feed-ct-final*)
 (fn-feed-durable-projection (fn-feed-replay *fn-feed-ct-open* *fn-feed-ct-history*))))
(assert-event (equal (fn-feed-state-of *fn-feed-ct-a* (fn-feed-queue *fn-feed-ct-final*))
                     (fn-feed-dropped :retry-bound)))
(assert-event (equal (fn-feed-state-of *fn-feed-ct-b* (fn-feed-queue *fn-feed-ct-final*)) :done))
(assert-event (equal (fn-feed-backoff-until *fn-feed-ct-final*) 6001))
(assert-event (equal (fn-feed-next-attempt *fn-feed-ct-final*) 5))
(assert-event (equal (fn-feed-entry-attempts
  (fn-feed-find *fn-feed-ct-a* (fn-feed-queue *fn-feed-ct-final*))) 2))
