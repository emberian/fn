(in-package "ACL2")

(include-book "rev-onto")

(defun fn-wire-octetp (x)
  (and (integerp x) (<= 0 x) (<= x 255)))

(defun fn-wire-octet-listp (xs)
  (if (consp xs)
      (and (fn-wire-octetp (car xs))
           (fn-wire-octet-listp (cdr xs)))
    (null xs)))

(defun fn-wire-octet-linesp (lines)
  (if (consp lines)
      (and (fn-wire-octet-listp (car lines))
           (fn-wire-octet-linesp (cdr lines)))
    (null lines)))

(defun fn-wire-list-length-onto (xs n)
  (declare (xargs :guard (natp n)))
  (if (consp xs)
      (fn-wire-list-length-onto (cdr xs) (+ 1 n))
    n))

(defun fn-wire-line-cost (line)
  (declare (xargs :guard t))
  (+ 2 (fn-wire-list-length line)))

(defun fn-wire-lines-size-loop (rev acc)
  (declare (xargs :guard (natp acc) :verify-guards nil))
  (if (consp rev)
      (fn-wire-lines-size-loop (cdr rev) (+ (fn-wire-line-cost (car rev)) acc))
    acc))

(defun fn-wire-lines-size (lines)
  (declare (xargs :guard (fn-wire-octet-linesp lines)
                  :verify-guards nil))
  (mbe :logic
       (if (consp lines)
           (+ (fn-wire-line-cost (car lines))
              (fn-wire-lines-size (cdr lines)))
         0)
       :exec (fn-wire-lines-size-loop (fn-ag-rev-onto lines nil) 0)))

(local
 (defthm fn-wire-lines-size-loop-of-rev-onto
   (equal (fn-wire-lines-size-loop (fn-ag-rev-onto lines zs) 0)
          (fn-wire-lines-size-loop zs (fn-wire-lines-size lines)))
   :hints (("Goal" :induct (fn-ag-rev-onto lines zs)
                   :in-theory (union-theories '(fn-wire-lines-size-loop fn-wire-lines-size fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(defthm fn-wire-lines-size-cons
  (equal (fn-wire-lines-size (cons line lines))
         (+ (fn-wire-line-cost line) (fn-wire-lines-size lines))))

(verify-guards fn-wire-octetp)

(verify-guards fn-wire-octet-listp)

(verify-guards fn-wire-octet-linesp)

(verify-guards fn-wire-lines-size-loop)

(verify-guards fn-wire-lines-size)
