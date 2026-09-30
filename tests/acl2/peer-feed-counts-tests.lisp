; S9 exact count relation: reachable live/replay and separately labeled corruption.
(in-package "ACL2")
(include-book "../../books/peer-feed-counts")

(defconst *fct-limits* (fn-feed-limits 20 10 3 t))
(defconst *fct-id* '(60 97 62))
(defconst *fct-id2* '(60 98 62))
(defconst *fct-open* (fn-feed-open '(112) *fct-limits*
                                       (fn-sched-contact "p" 0 1000000) 7))
(defconst *fct-enqueue* (fn-feed-enqueue *fct-open* *fct-id* 0))
(defconst *fct-offer* (mv-let (next effects) (fn-feed-offer *fct-enqueue* *fct-id*)
                       (declare (ignore effects)) next))
(defconst *fct-send* (mv-let (next effects) (fn-feed-send *fct-offer* *fct-id* '(13 10))
                      (declare (ignore effects)) next))
(defconst *fct-retry* (fn-feed-back-off *fct-send* *fct-id*
                                      (fn-clock-observation 1 0 0 nil)))
(defconst *fct-restart* (fn-feed-restart *fct-offer*))
(defconst *fct-drop* (fn-feed-give-up *fct-retry* *fct-id* :retry-bound))
(defconst *fct-operator-drop*
  (fn-feed-give-up *fct-retry* *fct-id* :operator))

; Reachable positive: constant empty-open establishes the complete conclusion.
(assert-event
 (and (fn-feed-count-relationp *fct-open*)
      (equal (fn-feed-undelivered *fct-open*) 0)
      (equal (fn-feed-retry-dropped *fct-open*) 0)))

; Reachable positives assert literal antecedents and conclusions, then counts.
(assert-event
 (and (fn-feed-count-relationp *fct-open*)
      (fn-feed-count-relationp *fct-enqueue*)
      (equal (fn-feed-undelivered *fct-enqueue*) 1)
      (equal (fn-feed-retry-dropped *fct-enqueue*) 0)))
(assert-event
 (and (fn-feed-count-relationp *fct-enqueue*)
      (fn-feed-count-relationp *fct-offer*)
      (equal (fn-feed-undelivered *fct-offer*) 1)
      (equal (fn-feed-retry-dropped *fct-offer*) 0)))
(assert-event
 (and (fn-feed-count-relationp *fct-offer*)
      (fn-feed-count-relationp *fct-send*)
      (equal (fn-feed-undelivered *fct-send*) 1)))
(assert-event
 (and (fn-feed-count-relationp *fct-send*)
      (fn-feed-count-relationp *fct-retry*)
      (equal (fn-feed-undelivered *fct-retry*) 1)
      (equal (fn-feed-retry-dropped *fct-retry*) 0)))
(assert-event
 (and (fn-feed-count-relationp *fct-offer*)
      (fn-feed-count-relationp *fct-restart*)
      (equal (fn-feed-undelivered *fct-restart*) 1)
      (equal (fn-feed-retry-dropped *fct-restart*) 0)
      (equal (fn-feed-state-of *fct-id* (fn-feed-queue *fct-restart*)) :queued)))
(assert-event
 (and (fn-feed-count-relationp *fct-send*)
      (fn-feed-count-relationp
       (fn-feed-lost *fct-send* (fn-clock-observation 1 0 0 nil)))))
(assert-event
 (and (fn-feed-count-relationp *fct-send*)
      (fn-feed-count-relationp (fn-feed-done *fct-send* *fct-id*))
      (equal (fn-feed-undelivered (fn-feed-done *fct-send* *fct-id*)) 0)))
(assert-event
 (and (fn-feed-count-relationp *fct-retry*)
      (fn-feed-count-relationp *fct-drop*)
      (equal (fn-feed-undelivered *fct-drop*) 1)
      (equal (fn-feed-retry-dropped *fct-drop*) 1)
      (equal (fn-fct-pending-model (fn-feed-queue *fct-drop*)) 0)))
(assert-event
 (and (fn-feed-count-relationp *fct-retry*)
      (fn-feed-count-relationp *fct-operator-drop*)
      (equal (fn-feed-undelivered *fct-operator-drop*) 1)
      (equal (fn-feed-retry-dropped *fct-operator-drop*) 0)
      (equal (fn-fct-pending-model (fn-feed-queue *fct-operator-drop*)) 1)))

; Refused duplicate/absent mutations neither invent nor retire work.
(assert-event
 (and (equal (fn-feed-enqueue *fct-enqueue* *fct-id* 99) *fct-enqueue*)
      (equal (fn-feed-done *fct-enqueue* *fct-id*) *fct-enqueue*)
      (equal (fn-feed-give-up *fct-drop* *fct-id* :retry-bound) *fct-drop*)
      (equal (fn-feed-give-up *fct-enqueue* *fct-id2* :retry-bound) *fct-enqueue*)))

(defconst *fct-history*
  (list (fn-feed-journal-entry :feed-enqueue (list '(112) *fct-id* 0))
        (fn-feed-journal-entry :feed-offer (list '(112) *fct-id* 1 0))
        (fn-feed-journal-entry :feed-sent (list '(112) *fct-id* 1))
        (fn-feed-journal-entry :feed-retry (list '(112) *fct-id* 1 431 1))
        (fn-feed-journal-entry :feed-restart (list '(112)))
        (fn-feed-journal-entry :feed-drop (list '(112) *fct-id* :retry-bound))))
(assert-event
 (and (fn-feed-count-relationp *fct-open*)
      (fn-feed-count-relationp (fn-feed-replay *fct-open* *fct-history*))
      (equal (fn-feed-undelivered (fn-feed-replay *fct-open* *fct-history*)) 1)
      (equal (fn-feed-retry-dropped (fn-feed-replay *fct-open* *fct-history*)) 1)))

; Corrupted-state hypothesis-removal: omit count relation from enqueue.
; Base shape/state validity still holds; the omitted hypothesis and the
; conclusion are both affirmatively false. No reachability claim is made.
(defconst *fct-corrupt*
  (fn-feed-make-counted '(112) *fct-limits*
                        (fn-feed-queue *fct-enqueue*) nil 0 7 1 0 0))
(assert-event
 (and (fn-feedp *fct-corrupt*)
      (not (fn-feed-count-relationp *fct-corrupt*))
      (not (fn-feed-count-relationp
            (fn-feed-enqueue *fct-corrupt* *fct-id2* 1)))))

; Actual port slice: durable-enqueue model event, contact tick, interrupted
; transfer, restart/reconnect, then a peer final outcome. Each transition
; maintains counts, while a retry-bound drop remains undelivered but stops
; pending work. Durable acceptance itself remains the owner seam.
(defconst *fct-port-enqueued*
  (fn-feed-port-step-feed
   (fn-feed-live-port-step *fct-open* (list :enqueue *fct-id* 0))))
(defconst *fct-port-tick-event* (list :tick (fn-clock-observation 5 0 0 nil)))
(defconst *fct-port-offered*
  (fn-feed-port-step-feed (fn-feed-live-port-step *fct-port-enqueued*
                                                 *fct-port-tick-event*)))
(assert-event
 (and (fn-feed-count-relationp *fct-port-enqueued*)
      (equal (fn-feed-selection *fct-port-enqueued*
                                (fn-clock-observation 5 0 0 nil)) *fct-id*)
      (fn-feed-count-relationp *fct-port-offered*)
      (fn-feed-count-relationp
       (fn-feed-port-step-feed
        (fn-feed-live-port-step *fct-port-enqueued* *fct-port-tick-event*)))
      (equal (fn-feed-undelivered *fct-port-offered*) 1)
      (equal (fn-feed-retry-dropped *fct-port-offered*) 0)))
(assert-event
 (and (fn-feed-count-relationp *fct-port-offered*)
      (mv-let (next effects)
          (fn-feed-observe *fct-port-offered* (fn-feed-response 435 *fct-id*)
                            nil (fn-clock-observation 6 0 0 nil))
        (declare (ignore effects))
        (and (fn-feed-count-relationp next)
             (equal (fn-feed-undelivered next) 0)))))
(assert-event
 (and (fn-feed-count-relationp *fct-open*)
      (fn-feed-count-relationp
       (fn-feed-live-next *fct-open* (list :enqueue *fct-id* 0)))))

; Corrupted-state hypothesis-removal for each carried transition: a one-unit
; overcount survives mutations that do not re-establish the carried relation.
(defun fct-overcount (f)
  (declare (xargs :guard t))
  (fn-feed-make-counted (fn-feed-peer f) (fn-feed-limits-of f) (fn-feed-queue f)
                        (fn-feed-contact f) (fn-feed-backoff-until f)
                        (fn-feed-conn f) (fn-feed-next-attempt f)
                        (+ 1 (nfix (fn-feed-undelivered f)))
                        (fn-feed-retry-dropped f)))
(defconst *fct-bad-q* (fct-overcount *fct-port-enqueued*))
(defconst *fct-bad-o* (fct-overcount *fct-port-offered*))
(defconst *fct-bad-s* (fct-overcount *fct-send*))
(assert-event
 (and (fn-feedp *fct-bad-q*) (fn-feedp *fct-bad-o*) (fn-feedp *fct-bad-s*)
      (not (fn-feed-count-relationp *fct-bad-q*))
      (not (fn-feed-count-relationp *fct-bad-o*))
      (not (fn-feed-count-relationp *fct-bad-s*))
      (not (fn-feed-count-relationp (fn-feed-enqueue *fct-bad-q* *fct-id2* 1)))
      (not (fn-feed-count-relationp (fn-feed-give-up *fct-bad-q* *fct-id* :retry-bound)))
      (not (fn-feed-count-relationp (fn-feed-done *fct-bad-s* *fct-id*)))
      (not (fn-feed-count-relationp (fn-feed-restart *fct-bad-o*)))
      (not (fn-feed-count-relationp
            (fn-feed-lost *fct-bad-o* (fn-clock-observation 7 0 0 nil))))
      (not (fn-feed-count-relationp
            (fn-feed-back-off *fct-bad-o* *fct-id* (fn-clock-observation 7 0 0 nil))))
      (mv-let (next effects) (fn-feed-offer *fct-bad-q* *fct-id*)
        (declare (ignore effects)) (not (fn-feed-count-relationp next)))
      (mv-let (next effects) (fn-feed-send *fct-bad-o* *fct-id* '(13 10))
        (declare (ignore effects)) (not (fn-feed-count-relationp next)))
      (mv-let (next effects)
          (fn-feed-observe *fct-bad-o* (fn-feed-response 435 *fct-id*)
                            nil (fn-clock-observation 7 0 0 nil))
        (declare (ignore effects)) (not (fn-feed-count-relationp next)))
      (not (fn-feed-count-relationp (fn-feed-replay *fct-bad-q* *fct-history*)))
      (not (fn-feed-count-relationp
            (fn-feed-port-step-feed
             (fn-feed-live-port-step *fct-bad-q* *fct-port-tick-event*))))))
