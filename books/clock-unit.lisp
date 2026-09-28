; fn: a clock reading carries its unit (lane invite-clock, 2026-09-28;
; PRF-374; planning/design-time-model-2026-09-27.md, the recorded time model).
;
; books/clock.lisp's observation is unit-less by shape.  Bug M1 (lane
; node-migrate): `account invite' on a stopped node handed a configuration
; record's stamp, then the SECONDS projection of an observation, to an
; expiry computed in milliseconds, so every such code was already expired.
; A reading names its unit, and a decision that adds a duration to it
; converts both to one named unit here, never at the call site.
;
; Since PRF-378 (lane clock-units-2) a configuration record's stamp is in
; the owner clock's unit, milliseconds (books/config.lisp fn-cfg-stampp,
; books/owner-config.lisp fn-ocfg-config-stamp), so the two named units
; below agree; :seconds stays a unit a reading may name.
; tools/clock_unit_check.py flags clock arithmetic outside this book.
(in-package "ACL2")
(include-book "clock")

; The units a reading may be in, and the milliseconds in one of each.
(defun fn-clock-unitp (u)
  (declare (xargs :guard t))
  (or (eq u :milliseconds) (eq u :seconds)))

(defun fn-clock-unit-milliseconds (u)
  (declare (xargs :guard t))
  (if (eq u :seconds) 1000 1))

; The owner's clock and a configuration record's stamp, by name.
(defconst *fn-clock-owner-unit* :milliseconds)
(defconst *fn-clock-record-stamp-unit* :milliseconds)

(defun fn-clock-reading (unit obs)
  (declare (xargs :guard t))
  (list :fn-clock-reading unit obs))

(defun fn-clock-reading-unit (r)
  (declare (xargs :guard t))
  (and (consp r) (consp (cdr r)) (cadr r)))

(defun fn-clock-reading-observation (r)
  (declare (xargs :guard t))
  (and (consp r) (consp (cdr r)) (consp (cddr r)) (caddr r)))

(defun fn-clock-readingp (r)
  (declare (xargs :guard t))
  (and (true-listp r)
       (equal (len r) 3)
       (eq (car r) :fn-clock-reading)
       (fn-clock-unitp (cadr r))
       (fn-clock-observation-shapep (caddr r))))

; The upper end of the reading's wall error interval, in milliseconds, or
; nil when the reading claims no usable wall clock.
(defun fn-clock-reading-latest-milliseconds (r)
  (declare (xargs :guard t))
  (let ((obs (fn-clock-reading-observation r)))
    (if (and (fn-clock-readingp r)
             (fn-clock-has-wall obs)
             (natp (fn-clock-wall obs))
             (natp (fn-clock-wall-error obs)))
        (* (fn-clock-unit-milliseconds (fn-clock-reading-unit r))
           (+ (fn-clock-wall obs) (fn-clock-wall-error obs)))
      nil)))

; A duration in whole seconds, in milliseconds.
(defun fn-clock-seconds-in-milliseconds (seconds)
  (declare (xargs :guard t))
  (* 1000 (nfix seconds)))

(defthm fn-clock-reading-latest-milliseconds-type
  (or (null (fn-clock-reading-latest-milliseconds r))
      (natp (fn-clock-reading-latest-milliseconds r)))
  :rule-classes :type-prescription)

; The two readings a decision meets, and what each's upper end is.
(defthm fn-clock-reading-latest-milliseconds-of-an-owner-reading
  (implies (and (fn-clock-has-wall obs)
                (natp (fn-clock-wall obs))
                (natp (fn-clock-wall-error obs))
                (fn-clock-observation-shapep obs))
           (equal (fn-clock-reading-latest-milliseconds
                   (fn-clock-reading *fn-clock-owner-unit* obs))
                  (+ (fn-clock-wall obs) (fn-clock-wall-error obs)))))

(defthm fn-clock-reading-latest-milliseconds-of-a-record-stamp-reading
  (implies (and (fn-clock-has-wall obs)
                (natp (fn-clock-wall obs))
                (natp (fn-clock-wall-error obs))
                (fn-clock-observation-shapep obs))
           (equal (fn-clock-reading-latest-milliseconds
                   (fn-clock-reading *fn-clock-record-stamp-unit* obs))
                  (+ (fn-clock-wall obs) (fn-clock-wall-error obs)))))

; A reading with no wall claim has no upper end: every decision that needs
; one refuses (fail closed).
(defthm fn-clock-reading-latest-milliseconds-without-a-wall
  (implies (not (fn-clock-has-wall obs))
           (equal (fn-clock-reading-latest-milliseconds
                   (fn-clock-reading unit obs))
                  nil)))

(in-theory (disable fn-clock-reading fn-clock-reading-unit
                    fn-clock-reading-observation fn-clock-readingp
                    fn-clock-reading-latest-milliseconds))
