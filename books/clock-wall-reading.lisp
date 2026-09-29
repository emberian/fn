; fn: the wall clock's validity, ACL2's (lane time-model-2, 2026-09-27; N3
; of lane proto-determinism, planning/evidence/proto-determinism-2026-09-27.md;
; PRF-322).  A book of its own so the DTN image (host/native/build-dtn.lisp),
; whose store operations read the wall clock through the same host function
; (host/native/io.lisp fnn-owner-wall-milliseconds), includes it without
; the owner's scheduler.
(in-package "ACL2")
;; N3 (lane proto-determinism): the wall clock's validity is ACL2's.  The
;; host hands gettimeofday's SECONDS and MICROSECONDS since the Unix epoch
;; and ACL2 answers (WALL-MS HAS-WALL): the milliseconds since the node's
;; 2000-01-01 base (the DTN epoch, RFC 9171 4.2.6), usable when not before
;; it; the host compares nothing.  PRF-305 (assurance-hygiene-5): the epoch's
;; offset is this book's constant; the host no longer computes it.

; 2000-01-01T00:00:00Z in Unix seconds.
(defconst *fn-otm-dtn-epoch-unix-seconds* 946684800)

(defun fn-otm-wall-reading (seconds microseconds)
  (declare (xargs :guard t))
  (let ((wall (+ (* 1000 (- (ifix seconds) *fn-otm-dtn-epoch-unix-seconds*))
                 (floor (nfix microseconds) 1000))))
    (if (and (integerp seconds) (natp microseconds) (<= 0 wall))
        (list wall t)
      (list 0 nil))))

(defthm fn-otm-wall-reading-shape
  (let ((w (fn-otm-wall-reading seconds microseconds)))
    (and (natp (car w))
         (booleanp (cadr w))
         (implies (not (cadr w)) (equal (car w) 0)))))

;; PRF-305 (assurance-hygiene-5): the monotonic milliseconds are ACL2's too.
;; The host hands its raw counter and ACL2 converts it.
;;
;; A tick counter (SBCL get-internal-real-time) at UNITS ticks per second
;; (internal-time-units-per-second): the whole milliseconds it has counted.
(defun fn-otm-monotonic-ms (ticks units)
  (declare (xargs :guard t))
  (if (and (natp ticks) (posp units))
      (floor (* ticks 1000) units)
    0))

(defthm fn-otm-monotonic-ms-is-natural
  (natp (fn-otm-monotonic-ms ticks units))
  :rule-classes :type-prescription)

;; A clock_gettime reading (SECONDS, NANOSECONDS), Linux CLOCK_BOOTTIME for
;; the BP node: the whole milliseconds since the clock's origin.
(defun fn-otm-boottime-ms (seconds nanoseconds)
  (declare (xargs :guard t))
  (if (and (natp seconds) (natp nanoseconds))
      (floor (+ (* seconds 1000000000) nanoseconds) 1000000)
    0))

(defthm fn-otm-boottime-ms-is-natural
  (natp (fn-otm-boottime-ms seconds nanoseconds))
  :rule-classes :type-prescription)
