(in-package "ACL2")
(include-book "../../books/def-fold-visits")
(include-book "must-fail-checked")

(defun fv-t-loop (xs)
  (if (consp xs) (fv-t-loop (cdr xs)) nil))
(def-fold-visits fv-t-loop :leaves nil)
(defthm fv-t-loop-counts-every-invocation
  (equal (fv-t-loop-fold-visits xs) (+ 1 (len xs))))
(assert-event (equal (fv-t-loop-fold-visits '(a b c)) 4))

(defun fv-t-wrap (xs)
  (let ((n (len xs)))
    (if (zp n) nil (list (fv-t-loop xs) (fv-t-loop (cdr xs))))))
(def-fold-visits fv-t-wrap :leaves nil)
(assert-event
 (and (equal (fv-t-wrap-fold-visits nil) 1)
      (equal (fv-t-wrap-fold-visits '(a b c)) 8)))

(defun fv-t-logic-only (xs)
  (if (consp xs) (fv-t-logic-only (cdr xs)) nil))
(defun fv-t-mbe (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (fv-t-logic-only xs) :exec nil))
(def-fold-visits fv-t-mbe :leaves nil)
(assert-event (equal (fv-t-mbe-fold-visits '(a b c)) 1))

(defun fv-t-unknown (xs) (len xs))
(defun fv-t-with-leaf (xs) (fv-t-unknown xs))
(must-fail-checked
 (def-fold-visits fv-t-with-leaf :leaves nil)
 :unchecked "The generator must reject an undeclared semantic leaf.")
(def-fold-visits fv-t-with-leaf :leaves (fv-t-unknown))
(assert-event (equal (fv-t-with-leaf-fold-visits '(a b c)) 1))

(def-fold-visits-check fv-t-loop)
(def-fold-visits-check fv-t-wrap)
(def-fold-visits-check fv-t-mbe)
(def-fold-visits-check fv-t-with-leaf)

; A changed source receipt cannot silently validate a stale observer.
(local (table fn-fold-visits 'fv-t-with-leaf '(stale (fv-t-unknown))))
(local
 (must-fail-checked
  (def-fold-visits-check fv-t-with-leaf)
  :unchecked "The source receipt is deliberately stale; the checker must refuse."))
