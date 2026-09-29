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
;;; gettimeofday's seconds and microseconds to fn-otm-wall-reading, whose
;;; epoch is ACL2's constant).
(assert-event (equal *fn-clkr-dtn-epoch-unix-ms* (* 1000 *fn-otm-dtn-epoch-unix-seconds*)))

;; Reachable positive: a 2026 reading has its wall, the milliseconds past the
;; epoch; the second before the epoch has none.
(defthm clkt-wall-reading-positive
  (and (integerp 1790000000) (natp 123456)
       (equal (fn-otm-wall-reading 1790000000 123456)
              (list (- 1790000000123 *fn-clkr-dtn-epoch-unix-ms*) t))
       (equal (fn-clkr-ms-of-ns (+ (* 1000000000 1790000000) (* 1000 123456))) 1790000000123)
       (equal (fn-otm-wall-reading 946684799 999999) (list 0 nil))
       (< (fn-clkr-ms-of-ns (+ (* 1000000000 946684799) (* 1000 999999)))
          *fn-clkr-dtn-epoch-unix-ms*))
  :rule-classes nil)

;; Without (integerp seconds): a half second past a 2026 second is a natural
;; count of nanoseconds after the epoch, but the reading has no wall.
(defthm clkt-wall-reading-integerp-hypotheses
  (and (not (integerp 3580000001/2)) (natp 0)
       (natp (* 1000000000 3580000001/2))
       (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns (* 1000000000 3580000001/2)))
       (not (cadr (fn-otm-wall-reading 3580000001/2 0))))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-reading-without-integerp
   (let ((w (fn-otm-wall-reading 3580000001/2 0))
         (ns (* 1000000000 3580000001/2)))
     (iff (cadr w) (and (natp ns) (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns)))))
   :rule-classes nil))

;; Without (natp microseconds): a negative sub-second part.
(defthm clkt-wall-reading-natp-hypotheses
  (and (integerp 1790000000) (not (natp -1000))
       (natp (+ (* 1000000000 1790000000) (* 1000 -1000)))
       (not (cadr (fn-otm-wall-reading 1790000000 -1000))))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-reading-without-natp
   (let ((w (fn-otm-wall-reading 1790000000 -1000))
         (ns (+ (* 1000000000 1790000000) (* 1000 -1000))))
     (iff (cadr w) (and (natp ns) (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns)))))
   :rule-classes nil))

;;; KEYSTONE fn-clkr-wall-seconds-is-the-ns-decision (PRF-305, the genesis's
;;; creation time: host/native/io.lisp fnn-genesis-octets hands gettimeofday's
;;; reading to fn-otm-wall-seconds).

;; Reachable positive: 5.25 s past the epoch is 5 whole seconds, the ns
;; decision's wall floored; the second before the epoch has no wall and is 0.
(defthm clkt-wall-seconds-positive
  (and (integerp 946684805) (natp 250000)
       (equal (fn-otm-wall-seconds 946684805 250000) 5)
       (natp (+ (* 1000000000 946684805) (* 1000 250000)))
       (<= *fn-clkr-dtn-epoch-unix-ms*
           (fn-clkr-ms-of-ns (+ (* 1000000000 946684805) (* 1000 250000))))
       (equal (floor (- (fn-clkr-ms-of-ns (+ (* 1000000000 946684805) (* 1000 250000)))
                        *fn-clkr-dtn-epoch-unix-ms*)
                     1000)
              5)
       (integerp 946684799) (natp 999999)
       (equal (fn-otm-wall-seconds 946684799 999999) 0)
       (< (fn-clkr-ms-of-ns (+ (* 1000000000 946684799) (* 1000 999999)))
          *fn-clkr-dtn-epoch-unix-ms*))
  :rule-classes nil)

;; Without (integerp seconds): 2.5 s past the epoch is a natural count of
;; nanoseconds whose decision is 2 seconds, but the reading answers 0.
(defthm clkt-wall-seconds-integerp-hypotheses
  (and (not (integerp 1893369605/2)) (natp 0)
       (equal (fn-otm-wall-seconds 1893369605/2 0) 0)
       (natp (* 1000000000 1893369605/2))
       (equal (floor (- (fn-clkr-ms-of-ns (* 1000000000 1893369605/2))
                        *fn-clkr-dtn-epoch-unix-ms*)
                     1000)
              2))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-seconds-without-integerp
   (implies (natp microseconds)
            (let ((ns (+ (* 1000000000 seconds) (* 1000 microseconds))))
              (equal (fn-otm-wall-seconds seconds microseconds)
                     (if (and (natp ns)
                              (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns)))
                         (floor (- (fn-clkr-ms-of-ns ns) *fn-clkr-dtn-epoch-unix-ms*)
                                1000)
                       0))))
   :rule-classes nil))

;; Without (natp microseconds): 2 s past the epoch less a whole second of
;; negative microseconds is 1 s by the ns decision; the reading answers 0.
(defthm clkt-wall-seconds-natp-hypotheses
  (and (integerp 946684802) (not (natp -1000000))
       (equal (fn-otm-wall-seconds 946684802 -1000000) 0)
       (natp (+ (* 1000000000 946684802) (* 1000 -1000000)))
       (equal (floor (- (fn-clkr-ms-of-ns (+ (* 1000000000 946684802) (* 1000 -1000000)))
                        *fn-clkr-dtn-epoch-unix-ms*)
                     1000)
              1))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-wall-seconds-without-natp
   (implies (integerp seconds)
            (let ((ns (+ (* 1000000000 seconds) (* 1000 microseconds))))
              (equal (fn-otm-wall-seconds seconds microseconds)
                     (if (and (natp ns)
                              (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns)))
                         (floor (- (fn-clkr-ms-of-ns ns) *fn-clkr-dtn-epoch-unix-ms*)
                                1000)
                       0))))
   :rule-classes nil))

;;; KEYSTONE fn-clkr-monotonic-readings-are-the-ns-decision (PRF-305, the
;;; served monotonic readings: fnn-owner-monotonic-ms and its siblings hand
;;; SBCL's tick counter and rate to fn-otm-monotonic-ms; fnn-bp-monotonic-now
;;; hands CLOCK_BOOTTIME's seconds and nanoseconds to fn-otm-boottime-ms).

;; Reachable positive, the tick counter: SBCL's rate (1000000 ticks a
;; second), 5.0019 seconds of ticks is 5001 ms, the ns decision's figure.
(defthm clkt-monotonic-ticks-positive
  (and (natp 5001900) (posp 1000000) (integerp (/ 1000000000 1000000))
       (equal (fn-otm-monotonic-ms 5001900 1000000) 5001)
       (equal (fn-clkr-ms-of-ns (* 5001900 (/ 1000000000 1000000))) 5001))
  :rule-classes nil)

;; Reachable positive, CLOCK_BOOTTIME: 12 s and 345678901 ns is 12345 ms.
(defthm clkt-monotonic-boottime-positive
  (and (natp 12) (natp 345678901)
       (equal (fn-otm-boottime-ms 12 345678901) 12345)
       (equal (fn-clkr-ms-of-ns (+ (* 12 1000000000) 345678901)) 12345))
  :rule-classes nil)

;; Without (integerp (/ 1000000000 units)): at 3 ticks a second a tick is not
;; a whole number of nanoseconds; 1 tick is 333 ms, but its nanoseconds
;; (1000000000/3) are not a natural, and fn-clkr-ms-of-ns answers 0.
(defthm clkt-monotonic-ticks-rate-hypotheses
  (and (natp 1) (posp 3) (not (integerp (/ 1000000000 3)))
       (equal (fn-otm-monotonic-ms 1 3) 333)
       (equal (fn-clkr-ms-of-ns (* 1 (/ 1000000000 3))) 0))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-monotonic-ticks-without-rate
   (implies (and (natp ticks) (posp units))
            (equal (fn-otm-monotonic-ms ticks units)
                   (fn-clkr-ms-of-ns (* ticks (/ 1000000000 units)))))
   :rule-classes nil))

;; Without (natp ticks): a fractional counter of 2000001/2 ticks at 1000000 a
;; second is a natural count of nanoseconds (1000000500 ns, 1000 ms) but not a
;; counter reading, and fn-otm-monotonic-ms answers 0.
(defthm clkt-monotonic-ticks-natp-hypotheses
  (and (not (natp 2000001/2)) (posp 1000000) (integerp (/ 1000000000 1000000))
       (equal (fn-otm-monotonic-ms 2000001/2 1000000) 0)
       (equal (fn-clkr-ms-of-ns (* 2000001/2 (/ 1000000000 1000000))) 1000))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-monotonic-ticks-without-natp
   (implies (and (posp units) (integerp (/ 1000000000 units)))
            (equal (fn-otm-monotonic-ms ticks units)
                   (fn-clkr-ms-of-ns (* ticks (/ 1000000000 units)))))
   :rule-classes nil))

;; Without (posp units): at a rate of 1/2 (not a positive integer) a tick is
;; 2000000000 ns (2000 ms) but the counter answers 0.
(defthm clkt-monotonic-ticks-posp-hypotheses
  (and (natp 1) (not (posp 1/2)) (integerp (/ 1000000000 1/2))
       (equal (fn-otm-monotonic-ms 1 1/2) 0)
       (equal (fn-clkr-ms-of-ns (* 1 (/ 1000000000 1/2))) 2000))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-monotonic-ticks-without-posp
   (implies (and (natp ticks) (integerp (/ 1000000000 units)))
            (equal (fn-otm-monotonic-ms ticks units)
                   (fn-clkr-ms-of-ns (* ticks (/ 1000000000 units)))))
   :rule-classes nil))

;; Without (natp seconds) / (natp nanoseconds) on CLOCK_BOOTTIME: a negative
;; seconds field with a natural total (-1 s + 2000000000 ns = 1000 ms) is not
;; a reading and answers 0; likewise a negative nanoseconds field.
(defthm clkt-monotonic-boottime-natp-hypotheses
  (and (not (natp -1)) (natp 2000000000)
       (equal (fn-otm-boottime-ms -1 2000000000) 0)
       (equal (fn-clkr-ms-of-ns (+ (* -1 1000000000) 2000000000)) 1000)
       (natp 2) (not (natp -1000000000))
       (equal (fn-otm-boottime-ms 2 -1000000000) 0)
       (equal (fn-clkr-ms-of-ns (+ (* 2 1000000000) -1000000000)) 1000))
  :rule-classes nil)

(must-fail-checked
 (defthm clkt-monotonic-boottime-without-seconds-natp
   (implies (natp nanoseconds)
            (equal (fn-otm-boottime-ms seconds nanoseconds)
                   (fn-clkr-ms-of-ns (+ (* seconds 1000000000) nanoseconds))))
   :rule-classes nil))

(must-fail-checked
 (defthm clkt-monotonic-boottime-without-nanoseconds-natp
   (implies (natp seconds)
            (equal (fn-otm-boottime-ms seconds nanoseconds)
                   (fn-clkr-ms-of-ns (+ (* seconds 1000000000) nanoseconds))))
   :rule-classes nil))
