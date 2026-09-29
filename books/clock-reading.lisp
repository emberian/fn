; fn: a host's raw clock reading becomes a clock observation in ACL2 (lane
; host-decisions-2, 2026-09-27; packet C of
; planning/evidence/host-decisions-2026-09-27.md).
;
; host/bp-ingress-host.lisp fn-bpi-host-observation (the lab BP ingress,
; Python-bridge only) converted nanoseconds to milliseconds, moved the wall
; reading to the DTN epoch and decided has-wall (a reading, not before the
; epoch, with a natural error bound) in host code.  That decision is the
; observation's meaning, so it is here; the host passes its counters and
; relays the observation.
;
; This book has the prefix `fn-clkr-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "clock")
(include-book "clock-wall-reading")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; 2000-01-01T00:00:00Z in Unix milliseconds (the DTN epoch, the served wall
; reading's own constant in books/clock-wall-reading.lisp; the same figure as
; books/nntp-responses.lisp *fn-nntp-unix-dtn-offset-ms*, asserted equal in
; tests/acl2/clock-reading-tests.lisp).
(defconst *fn-clkr-dtn-epoch-unix-ms* (* 1000 *fn-otm-dtn-epoch-unix-seconds*))
(defconst *fn-clkr-ns-per-ms* 1000000)

(defun fn-clkr-ms-of-ns (ns)
  (declare (xargs :guard t))
  (if (natp ns) (floor ns *fn-clkr-ns-per-ms*) 0))

(defthm fn-clkr-ms-of-ns-is-natural
  (natp (fn-clkr-ms-of-ns ns))
  :rule-classes :type-prescription)

; Whether the reading is a usable wall clock: the host says it has one, the
; reading is a natural at or after the DTN epoch, and the error bound is a
; natural.
(defun fn-clkr-wall-usablep (wall-ns wall-error-ms has-wall)
  (declare (xargs :guard t))
  (and has-wall (natp wall-ns)
       (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns wall-ns))
       (natp wall-error-ms)
       t))

; THE OBSERVATION the host relays (host/bp-ingress-host.lisp
; fn-bpi-host-observation): milliseconds on both counters, the wall on the
; DTN epoch, each field held to the clock's range; without a usable wall,
; has-wall nil (fn-clock-expiry-decision answers :uncertain for it).
(defun fn-clkr-observation-of-ns (monotonic-ns wall-ns wall-error-ms has-wall)
  (declare (xargs :guard t))
  (let ((usable (fn-clkr-wall-usablep wall-ns wall-error-ms has-wall)))
    (fn-clock-observation
     (min (fn-clkr-ms-of-ns monotonic-ns) *fn-clock-max*)
     (if usable
         (min (- (fn-clkr-ms-of-ns wall-ns) *fn-clkr-dtn-epoch-unix-ms*) *fn-clock-max*)
       0)
     (if usable (min wall-error-ms *fn-clock-max*) 0)
     usable)))

; KEYSTONE.  Every reading, however malformed, is a clock observation; it
; has a wall exactly when the reading is usable, and then its wall is the
; reading's milliseconds past the DTN epoch (within the clock's range) and
; its error the host's bound (within range).
(defthm fn-clkr-observation-of-ns-decides-the-wall
  (let ((obs (fn-clkr-observation-of-ns monotonic-ns wall-ns wall-error-ms has-wall)))
    (and (fn-clock-observationp obs)
         (iff (fn-clock-has-wall obs)
              (and has-wall (natp wall-ns)
                   (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns wall-ns))
                   (natp wall-error-ms)))
         (implies (fn-clock-has-wall obs)
                  (and (equal (fn-clock-wall obs)
                              (min (- (fn-clkr-ms-of-ns wall-ns) *fn-clkr-dtn-epoch-unix-ms*)
                                   *fn-clock-max*))
                       (equal (fn-clock-wall-error obs)
                              (min wall-error-ms *fn-clock-max*))))))
  :hints (("Goal" :in-theory (e/d (fn-clock-observationp fn-clock-observation-shapep fn-clock-observation
                                   fn-clock-timep fn-clock-monotonic fn-clock-wall
                                   fn-clock-wall-error fn-clock-has-wall)
                                  (fn-clkr-ms-of-ns)))))

; KEYSTONE (PRF-305, the served reading).  fn-clkr-observation-of-ns's only
; caller, host/bp-ingress-host.lisp, is not loaded by the served images; the
; served wall reading is host/native/io.lisp fnn-owner-wall-milliseconds and
; fnn-store-prepare-observation, which hand gettimeofday's seconds and
; microseconds to fn-otm-wall-reading (books/clock-wall-reading.lisp), whose
; epoch is its own constant.  That decision is this book's: the reading has
; a wall exactly when its nanoseconds are at or after the epoch, and the wall
; is the milliseconds past it (fn-clkr-ms-of-ns, fn-clkr-wall-usablep's
; clock conjuncts).
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-clkr-ms-of-ns-of-a-reading
   (implies (and (integerp seconds) (natp microseconds))
            (equal (floor (+ (* 1000000000 seconds) (* 1000 microseconds)) 1000000)
                   (+ (* 1000 seconds) (floor microseconds 1000))))))

(defthm fn-clkr-wall-reading-is-the-ns-decision
  (implies (and (integerp seconds) (natp microseconds))
           (let ((w (fn-otm-wall-reading seconds microseconds))
                 (ns (+ (* 1000000000 seconds) (* 1000 microseconds))))
             (and (iff (cadr w)
                       (and (natp ns)
                            (<= *fn-clkr-dtn-epoch-unix-ms* (fn-clkr-ms-of-ns ns))))
                  (equal (car w)
                         (if (cadr w)
                             (- (fn-clkr-ms-of-ns ns) *fn-clkr-dtn-epoch-unix-ms*)
                           0)))))
  :hints (("Goal" :in-theory (enable fn-otm-wall-reading fn-clkr-ms-of-ns))))

; KEYSTONE (PRF-305, the served monotonic readings).  The owner, the store's
; prepare and the feed ports hand SBCL's tick counter and its rate to
; fn-otm-monotonic-ms (host/native/owner.lisp fnn-owner-monotonic-ms,
; host/native/io.lisp fnn-store-prepare-observation and
; fnn-bridge-config-initial, host/native/feed-service.lisp fnn-feed-now); the
; BP node hands CLOCK_BOOTTIME's seconds and nanoseconds to
; fn-otm-boottime-ms (host/native/bp.lisp fnn-bp-monotonic-now).  Each is
; fn-clkr-ms-of-ns of the reading in nanoseconds: for the tick counter, when
; a tick is a whole number of nanoseconds (SBCL's rate is 1000000).
(local
 (defthm fn-clkr-floor-of-scaled-ticks
   (implies (and (natp ticks) (posp units) (integerp (/ 1000000000 units)))
            (equal (floor (* ticks (/ 1000000000 units)) 1000000)
                   (floor (* ticks 1000) units)))))

(defthm fn-clkr-monotonic-readings-are-the-ns-decision
  (and (implies (and (natp ticks) (posp units) (integerp (/ 1000000000 units)))
                (equal (fn-otm-monotonic-ms ticks units)
                       (fn-clkr-ms-of-ns (* ticks (/ 1000000000 units)))))
       (implies (and (natp seconds) (natp nanoseconds))
                (equal (fn-otm-boottime-ms seconds nanoseconds)
                       (fn-clkr-ms-of-ns (+ (* seconds 1000000000) nanoseconds)))))
  :hints (("Goal" :in-theory (enable fn-otm-monotonic-ms fn-otm-boottime-ms
                                     fn-clkr-ms-of-ns))))
