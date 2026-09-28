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

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; 2000-01-01T00:00:00Z in Unix milliseconds (the DTN epoch; the same figure as
; books/nntp-responses.lisp *fn-nntp-unix-dtn-offset-ms*, asserted equal in
; tests/acl2/clock-reading-tests.lisp).
(defconst *fn-clkr-dtn-epoch-unix-ms* 946684800000)
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
