; The actual serialized reader producer classifies its core-produced step.
; This reads only the eight-cell spine, never scans retained effects or lines.
(in-package "ACL2")
(include-book "served-step")

(defun fn-rrd-at (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (consp x)
     (if (zp n) (car x) (fn-rrd-at (- n 1) (cdr x)))
   nil))

(defun fn-rrd-widthp (x n)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
   (and (consp x) (fn-rrd-widthp (cdr x) (- n 1)))))

(defun fn-rrd-step-disposition (step)
 (declare (xargs :guard t))
 (cond
  ((not (and (fn-rrd-widthp step 8)
             (eq (fn-rrd-at 0 step) :served-step)
             (natp (fn-rrd-at 5 step)))) :unavailable-step)
  ((or (fn-rrd-at 1 step) (fn-rrd-at 2 step) (fn-rrd-at 3 step)
       (fn-rrd-at 4 step) (fn-rrd-at 6 step) (fn-rrd-at 7 step))
   :response)
  (t :parser-progress)))

; A constructor equation; the actual producer supplies the domain carry.
(defthm fn-rrd-step-disposition-of-make-unfolds
 (equal (fn-rrd-step-disposition (fn-splan-step-make e c s u n r x))
        (if (or e c s u r x) :response :parser-progress))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-rrd-step-disposition fn-rrd-widthp fn-rrd-at fn-splan-step-make
     nfix natp zp car-cons cdr-cons)))))
