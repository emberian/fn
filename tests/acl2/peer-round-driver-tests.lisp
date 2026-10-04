(in-package "ACL2")
(include-book "../../books/peer-round-driver")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(defconst *prd-active* '((:pull (65)) (:pull (66)) (:catch-up (67))))
; PRF-1260 antecedent and whole ordered visit conclusion.
(assert-event (and (true-listp *prd-active*)
                   (subsetp-equal *prd-active* *prd-active*)
                   (equal (fn-prd-sweep *prd-active* *prd-active*) *prd-active*)))
; Retained subset hypothesis is needed: an absent round cannot be selected.
(defconst *prd-absent* '((:pull (65)) (:pull (68)) (:catch-up (67))))
(assert-event (and (true-listp *prd-absent*)
                   (not (subsetp-equal *prd-absent* *prd-active*))
                   (not (equal (fn-prd-sweep *prd-active* *prd-absent*) *prd-absent*))))
(assert-event (equal (fn-prd-select *prd-active* *prd-active*)
                     '((:pull (65)) ((:pull (66)) (:catch-up (67))))))
(assert-event (equal (fn-prd-select *prd-active* (cdr *prd-active*))
                     '((:pull (66)) ((:catch-up (67))))))
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) :write 9 10 nil)
                     '(:io :write)))
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) :write 10 10 nil)
                     '(:lost :timeout)))
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) nil 10 nil nil)
                     '(:effect (:remote 1))))
(assert-event (equal (fn-prd-read-limit nil) 512))
(assert-event (equal (fn-prd-write-end 500 2000) 1012))
(assert-event (not (fn-prd-loss-class-ok :read "fnn-store-indeterminate")))
(assert-event (not (fn-prd-loss-class-ok :read "unknown-io-subclass")))
(assert-event (fn-prd-loss-class-ok :dial "fnn-peer-dial-error"))

; Push selection retains write before later framer events and offers.
(assert-event (equal (fn-prd-feed-action nil t t t 9 10) :write))
(assert-event (equal (fn-prd-feed-action nil t t t 10 10) :timeout))
(assert-event (equal (fn-prd-feed-action :tls nil t nil 9 10) :tls))
(assert-event (equal (fn-prd-feed-action nil nil t t 11 nil) :reply))
(assert-event (equal (fn-prd-feed-action nil nil nil t 11 nil) :offer))
(assert-event (equal (fn-prd-feed-action nil nil nil nil 11 nil) :read))
;; The reply wait: past it the link is lost; a retained reply drains first.
(assert-event (equal (fn-prd-feed-action nil nil nil t 11 10) :timeout))
(assert-event (equal (fn-prd-feed-action nil nil nil nil 10 10) :timeout))
(assert-event (equal (fn-prd-feed-action nil nil t t 11 10) :reply))
(assert-event (equal (fn-prd-feed-action nil nil nil t 9 10) :offer))
(assert-event (equal (fn-prd-feed-action nil nil nil nil 9 10) :read))
(assert-event (equal (fn-prd-write-quantum-end 65500 100000 65536) 100000))
(assert-event (equal (fn-prd-write-end 512 (fn-prd-write-quantum-end 0 2000 600)) 600))

; Teeth: fn-prd-round-past-deadline-is-lost. An unfinished round at its
; deadline is lost even with a pending write, effect and event.
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) :write 9 10 9)
                     '(:lost :round-deadline)))
; Each retained hypothesis matters: a finished round finishes; one millisecond
; before the deadline the I/O continues; no deadline is no round bound.
(assert-event (equal (fn-prd-action t nil nil nil 9 nil 9) '(:finish)))
(assert-event (equal (fn-prd-action nil '((:remote 1)) nil :write 8 10 9) '(:io :write)))
(assert-event (equal (fn-prd-action nil nil nil nil 9 nil nil) '(:read)))
(assert-event (equal (fn-prd-round-deadline 5) 600005))
(assert-event (equal (fn-prd-flight-quantum) 256))

; The keystones' declared teeth (TEETH CONTRACT v1), from the witnesses above.
(defteeth fn-prd-sweep-visits-all-admitted-rounds
  :claim (((listed (true-listp remaining))
           (admitted (subsetp-equal remaining active)))
          (equal (fn-prd-sweep active remaining) remaining))
  :subject fn-prd-sweep
  :witness ((active *prd-active*) (remaining *prd-active*))
  :breaks ((listed ((active *prd-active*) (remaining (append *prd-active* 7)))
                   :logical "an improper REMAINING is outside subsetp-equal's guard; its logical value is t and the sweep drops the terminator")
           (admitted ((active *prd-active*) (remaining *prd-absent*))))
  :mutations ((reordered
               (:conclusion (equal (fn-prd-sweep active remaining) (reverse remaining)))
               ((active *prd-active*) (remaining *prd-active*))
               :fault "a sweep that visits the admitted rounds out of their order")))

(defteeth fn-prd-round-past-deadline-is-lost
  :claim (((unfinished (not done))
           (deadline-set (natp round-deadline))
           (past (<= round-deadline (nfix now))))
          (equal (fn-prd-action done effects events io now deadline round-deadline)
                 '(:lost :round-deadline)))
  :subject fn-prd-action
  :witness ((done nil) (effects '((:remote 1))) (events '((:local 2))) (io :write)
            (now 9) (deadline 10) (round-deadline 9))
  :breaks ((unfinished ((done t) (effects nil) (events nil) (io nil)
                        (now 9) (deadline nil) (round-deadline 9)))
           (deadline-set ((done nil) (effects nil) (events nil) (io nil)
                          (now 9) (deadline nil) (round-deadline nil))
                         :logical "a round without a deadline carries NIL, outside <='s guard in the retained hypothesis PAST, whose logical value holds")
           (past ((done nil) (effects '((:remote 1))) (events nil) (io :write)
                  (now 8) (deadline 10) (round-deadline 9))))
  :mutations ((timeout-word
               (:conclusion (equal (fn-prd-action done effects events io now deadline round-deadline)
                                   '(:lost :timeout)))
               ((done nil) (effects '((:remote 1))) (events '((:local 2))) (io :write)
                (now 9) (deadline 10) (round-deadline 9))
               :fault "a round past its deadline reported as a per-I/O timeout")
              (early-deadline
               (:hypothesis past (<= round-deadline (+ 1 (nfix now))))
               ((done nil) (effects '((:remote 1))) (events nil) (io :write)
                (now 8) (deadline 10) (round-deadline 9))
               :fault "a deadline taken one millisecond early, losing a round still inside its budget")))


; S145 for the pull worker: ACL2's pause (fn-prd-pause-ms).  A table row is
; (PEER NEXT INTERVAL BUSY).
(defconst *prd-sched* '(((65) 5000 1000 nil) ((66) 1500 1000 t) ((67) 2400 1000 nil)))
(assert-event (equal (fn-prd-next-due-wait *prd-sched* 1000 nil) 1400))
(assert-event (equal (fn-prd-pause-ms nil *prd-sched* 1000) 1000))
(assert-event (equal (fn-prd-pause-ms nil *prd-sched* 2000) 400))
(assert-event (equal (fn-prd-pause-ms nil *prd-sched* 2395) 10))
(assert-event (equal (fn-prd-pause-ms nil nil 0) 1000))
(assert-event (equal (fn-prd-pause-ms '((:pull (65))) *prd-sched* 1000) 10))

(defteeth fn-prd-pause-is-bounded
  :claim (()
          (and (<= (fn-prd-idle-ms) (fn-prd-pause-ms active tbl now))
               (<= (fn-prd-pause-ms active tbl now) (fn-prd-idle-max-ms))))
  :subject fn-prd-pause-ms
  :witness ((active nil) (tbl *prd-sched*) (now 2000))
  :breaks ()
  :mutations ((the-old-poll
               (:conclusion (equal (fn-prd-pause-ms active tbl now) (fn-prd-idle-ms)))
               ((active nil) (tbl *prd-sched*) (now 2000))
               :fault "an idle worker that polls every 10 ms (2,466 transit holds in 13 s on d5b0b9100)")))

(defteeth fn-prd-pause-polls-while-a-round-runs
  :claim (((admitted (consp active)))
          (equal (fn-prd-pause-ms active tbl now) (fn-prd-idle-ms)))
  :subject fn-prd-pause-ms
  :witness ((active '((:pull (65)))) (tbl *prd-sched*) (now 1000))
  :breaks ((admitted ((active nil) (tbl *prd-sched*) (now 1000))))
  :mutations ((sleeps-a-second
               (:conclusion (equal (fn-prd-pause-ms active tbl now) (fn-prd-idle-max-ms)))
               ((active '((:pull (65)))) (tbl *prd-sched*) (now 1000))
               :fault "a worker that sleeps a second between the I/O polls of an admitted round")))

(defteeth fn-prd-pause-never-sleeps-past-a-due-round
  :claim (((listed (member-equal row tbl))
           (schedulable (fn-prd-row-schedulablep row)))
          (<= (fn-prd-pause-ms active tbl now)
              (max (fn-prd-idle-ms) (fn-prd-row-wait row now))))
  :subject fn-prd-pause-ms
  :witness ((row '((67) 2400 1000 nil)) (active nil) (tbl *prd-sched*) (now 2000))
  :breaks ((listed ((row '((68) 2100 1000 nil)) (active nil) (tbl *prd-sched*) (now 2000)))
           (schedulable ((row '((66) 1500 1000 t)) (active nil) (tbl *prd-sched*) (now 1000))))
  :mutations ((wakes-early
               (:conclusion (< (fn-prd-pause-ms active tbl now)
                               (max (fn-prd-idle-ms) (fn-prd-row-wait row now))))
               ((row '((67) 2400 1000 nil)) (active nil) (tbl *prd-sched*) (now 2000))
               :fault "a pause that always wakes before the earliest round is due, re-reading both plan tables for nothing")))
