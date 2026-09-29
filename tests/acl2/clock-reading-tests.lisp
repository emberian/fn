; Teeth for books/clock-reading.lisp (packet C).
(in-package "ACL2")
(include-book "../../books/clock-reading")
(include-book "../../books/nntp-responses")
(include-book "must-fail-checked")

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

;;; KEYSTONE fn-clkr-wall-reading-is-the-ns-decision (PRF-305, the served
;;; reading: host/native/io.lisp fnn-owner-wall-milliseconds hands
;;; gettimeofday's seconds and microseconds to fn-otm-wall-reading).
(defconst *clkt-off* (floor *fn-clkr-dtn-epoch-unix-ms* 1000))

;; Reachable positive: a 2026 reading has its wall, the milliseconds past the
;; epoch; the second before the epoch has none.
(defthm clkt-wall-reading-positive
  (and (integerp 1790000000) (natp 123456) (equal *clkt-off* 946684800)
       (equal (fn-otm-wall-reading 1790000000 123456 *clkt-off*)
              (list (- 1790000000123 *fn-clkr-dtn-epoch-unix-ms*) t))
       (equal (fn-clkr-ms-of-ns (+ (* 1000000000 1790000000) (* 1000 123456))) 1790000000123)
       (equal (fn-otm-wall-reading 946684799 999999 *clkt-off*) (list 0 nil))
       (< (fn-clkr-ms-of-ns (+ (* 1000000000 946684799) (* 1000 999999)))
          *fn-clkr-dtn-epoch-unix-ms*))
  :rule-classes nil)

;; Without (integerp seconds): a half second past a 2026 second is a natural
;; count of nanoseconds after the epoch, but the reading has no wall.
(defthm clkt-wall-reading-integerp-hypotheses
  (and (not (integerp 3580000001/2)) (natp 0) (equal *clkt-off* 946684800)
       (natp (* 1000000000 3580000001/2))
       (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns (* 1000000000 3580000001/2)))
       (not (cadr (fn-otm-wall-reading 3580000001/2 0 *clkt-off*))))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-reading-without-integerp
   (let ((w (fn-otm-wall-reading 3580000001/2 0 *clkt-off*))
         (ns (* 1000000000 3580000001/2)))
     (iff (cadr w) (and (natp ns) (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns)))))
   :rule-classes nil))

;; Without (natp microseconds): a negative sub-second part.
(defthm clkt-wall-reading-natp-hypotheses
  (and (integerp 1790000000) (not (natp -1000)) (equal *clkt-off* 946684800)
       (natp (+ (* 1000000000 1790000000) (* 1000 -1000)))
       (not (cadr (fn-otm-wall-reading 1790000000 -1000 *clkt-off*))))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-reading-without-natp
   (let ((w (fn-otm-wall-reading 1790000000 -1000 *clkt-off*))
         (ns (+ (* 1000000000 1790000000) (* 1000 -1000))))
     (iff (cadr w) (and (natp ns) (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns)))))
   :rule-classes nil))

;; Without the offset: at offset 0 the wall is Unix milliseconds, not the
;; milliseconds past the DTN epoch.
(defthm clkt-wall-reading-offset-hypotheses
  (and (integerp 1790000000) (natp 0) (not (equal 0 *clkt-off*))
       (cadr (fn-otm-wall-reading 1790000000 0 0))
       (not (equal (car (fn-otm-wall-reading 1790000000 0 0))
                   (- (fn-clkr-ms-of-ns (* 1000000000 1790000000)) *fn-clkr-dtn-epoch-unix-ms*))))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-reading-without-offset
   (equal (car (fn-otm-wall-reading 1790000000 0 0))
          (- (fn-clkr-ms-of-ns (* 1000000000 1790000000)) *fn-clkr-dtn-epoch-unix-ms*))
   :rule-classes nil))
