; fn: the wall clock's validity, ACL2's (lane time-model-2, 2026-09-27; N3
; of lane proto-determinism, planning/evidence/proto-determinism-2026-09-27.md;
; PRF-308).  A book of its own so the DTN image (host/native/build-dtn.lisp),
; whose store operations read the wall clock through the same host function
; (host/native/io.lisp fnn-owner-wall-milliseconds), includes it without
; the owner's scheduler.
(in-package "ACL2")
;; N3 (lane proto-determinism): the wall clock's validity is ACL2's.  The
;; host hands gettimeofday's SECONDS and MICROSECONDS since the Unix epoch
;; (and the epoch OFFSET of the node's 2000-01-01 base, a protocol constant)
;; and ACL2 answers (WALL-MS HAS-WALL): the milliseconds since the base,
;; usable when not before it; the host compares nothing.
(defun fn-otm-wall-reading (seconds microseconds offset)
  (declare (xargs :guard t))
  (let ((wall (+ (* 1000 (- (ifix seconds) (ifix offset)))
                 (floor (nfix microseconds) 1000))))
    (if (and (integerp seconds) (natp microseconds) (<= 0 wall))
        (list wall t)
      (list 0 nil))))

(defthm fn-otm-wall-reading-shape
  (let ((w (fn-otm-wall-reading seconds microseconds offset)))
    (and (natp (car w))
         (booleanp (cadr w))
         (implies (not (cadr w)) (equal (car w) 0)))))

