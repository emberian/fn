(in-package "ACL2")
(include-book "../../books/owner-feed-live-carried")

(defconst *ofcv-limits* (fn-feed-limits 20 10 3 t))
(defconst *ofcv-empty*
  (fn-feed-open '(112) *ofcv-limits* (fn-sched-contact "p" 0 1000000) 7))
(defconst *ofcv-enqueue-event* '(:enqueue (60 97 62) 0))
(defconst *ofcv-step*
  (fn-feed-live-port-step-carried *ofcv-empty* *ofcv-enqueue-event*))
; Reachable complete boundary result, not merely a tally field.
(assert-event
 (and (fn-feedp *ofcv-empty*) (fn-feed-count-relationp *ofcv-empty*)
      (equal *ofcv-step* (fn-fcv-raw-live-port-step *ofcv-empty* *ofcv-enqueue-event*))
      (equal *ofcv-step* (fn-feed-live-port-step *ofcv-empty* *ofcv-enqueue-event*))
      (equal (fn-feed-port-step-status *ofcv-step*) :accepted)
      (equal (fn-feed-undelivered (fn-feed-port-step-feed *ofcv-step*)) 1)
      (consp (fn-feed-port-step-records *ofcv-step*))))
(defconst *ofcv-queued* (fn-feed-port-step-feed *ofcv-step*))
(defconst *ofcv-tick* (list :tick (fn-clock-observation 7 0 0 nil)))
(assert-event
 (and (fn-feedp *ofcv-queued*) (fn-feed-count-relationp *ofcv-queued*)
      (equal (fn-fcv-raw-live-port-step *ofcv-queued* *ofcv-tick*)
             (fn-feed-live-port-step *ofcv-queued* *ofcv-tick*))
      (consp (fn-feed-port-step-effects
              (fn-feed-live-port-step-carried *ofcv-queued* *ofcv-tick*)))))

(defconst *ofcv-peer*
  (fn-cfg-peer-make "p" "p.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defconst *ofcv-table*
  (fn-own-feed-install-one "p" (fn-cfg-peer-rows *ofcv-peer*) nil))
(assert-event
 (and (fn-own-feed-tablep *ofcv-table*) (fn-ofct-table-relationp *ofcv-table*)
      (equal (fn-own-feed-port-peer-carried "p" *ofcv-table* *ofcv-enqueue-event*)
             (fn-own-feed-port-peer "p" *ofcv-table* *ofcv-enqueue-event*))
      (equal (fn-own-feed-port-pending-delta
              (fn-own-feed-port-peer-carried "p" *ofcv-table* *ofcv-enqueue-event*)) 1)))

; Hypothesis-removal witnesses for the raw boundary equivalence.
; Corrupted contact omits only the feed invariant; derived counts still hold.
(defconst *ofcv-invalid*
  (fn-feed-make-counted '(112) *ofcv-limits* nil :invalid 0 7 1 0 0))
(assert-event
 (with-guard-checking :none
  (and (not (fn-feedp *ofcv-invalid*))
       (fn-feed-count-relationp *ofcv-invalid*)
       (not (equal (fn-fcv-raw-live-port-step *ofcv-invalid* *ofcv-enqueue-event*)
                   (fn-feed-live-port-step *ofcv-invalid* *ofcv-enqueue-event*))))))
; Corrupted cached occupancy omits only the count relation. The base feed
; remains valid, while the raw branch correctly relies on its carried count.
(defconst *ofcv-overcount*
  (fn-feed-make-counted '(112) *ofcv-limits* nil
                        (fn-feed-contact *ofcv-empty*) 0 7 1 20 0))
(assert-event
 (with-guard-checking :none
  (and (fn-feedp *ofcv-overcount*)
       (not (fn-feed-count-relationp *ofcv-overcount*))
       (not (equal (fn-fcv-raw-live-port-step *ofcv-overcount* *ofcv-enqueue-event*)
                   (fn-feed-live-port-step *ofcv-overcount* *ofcv-enqueue-event*))))))
; The complete durable target fold, including duplicate target names.
(assert-event
 (and (fn-own-feed-tablep *ofcv-table*) (fn-ofct-table-relationp *ofcv-table*)
      (equal (fn-own-feed-enqueue-all-carried '("p" "p") *ofcv-table* '(60 97 62) 0 0)
             (fn-own-feed-enqueue-all-counted '("p" "p") *ofcv-table* '(60 97 62) 0 0))
      (equal (cdr (fn-own-feed-enqueue-all-counted-carried
                   '("p" "p") *ofcv-table* '(60 97 62) 0 0)) 1)))
