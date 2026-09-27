; Teeth for books/clock-reading.lisp (packet C).
(in-package "ACL2")
(include-book "../../books/clock-reading")
(include-book "../../books/nntp-responses")

; One DTN epoch in the tree.
(assert-event (equal *fn-clkr-dtn-epoch-unix-ms* *fn-nntp-unix-dtn-offset-ms*))

; REACHABLE: a lab host reading 2026-09-27T12:00:00.123456789Z with a 500 ms
; bound: has-wall, the wall the milliseconds past 2000-01-01.
(defconst *clkr-ns* (+ (* 1790510400 1000000000) 123456789))
(defconst *clkr-obs* (fn-clkr-observation-of-ns 5000000000 *clkr-ns* 500 t))
(assert-event (fn-clock-observationp *clkr-obs*))
(assert-event (fn-clock-has-wall *clkr-obs*))
(assert-event (equal (fn-clock-wall *clkr-obs*) (- 1790510400123 946684800000)))
(assert-event (equal (fn-clock-wall-error *clkr-obs*) 500))
(assert-event (equal (fn-clock-monotonic *clkr-obs*) 5000))
; The epoch itself is usable (wall 0); one millisecond before it is not.
(assert-event (fn-clock-has-wall (fn-clkr-observation-of-ns 0 (* 946684800000 1000000) 1 t)))
(assert-event (equal (fn-clock-wall (fn-clkr-observation-of-ns 0 (* 946684800000 1000000) 1 t)) 0))
(assert-event (not (fn-clock-has-wall
                    (fn-clkr-observation-of-ns 0 (* 946684799999 1000000) 1 t))))
; Each conjunct of usability, removed, takes the wall away.
(assert-event (not (fn-clock-has-wall (fn-clkr-observation-of-ns 0 *clkr-ns* 500 nil))))
(assert-event (not (fn-clock-has-wall (fn-clkr-observation-of-ns 0 -1 500 t))))
(assert-event (not (fn-clock-has-wall (fn-clkr-observation-of-ns 0 *clkr-ns* -5 t))))
(assert-event (not (fn-clock-has-wall (fn-clkr-observation-of-ns 0 *clkr-ns* :unknown t))))
; A malformed monotonic counter is 0, still an observation.
(assert-event (fn-clock-observationp (fn-clkr-observation-of-ns :bad *clkr-ns* 500 t)))
; No wall: the uncertain expiry decision's input.
(assert-event (equal (fn-clock-wall (fn-clkr-observation-of-ns 0 *clkr-ns* 500 nil)) 0))
