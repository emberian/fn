(include-book "records-invariants")
(include-book "def-loop")

(def-loop fn-cfg-rows-without-key (rows a)
  :shape :map :over rows :elt r
  :keep (equal (fn-cfg-row-a r) a) :keep-order :skip-first
  :body r)

(defun fn-cfg-rows-keyed-p (rows a)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (equal (fn-cfg-row-a (car rows)) a)
           (fn-cfg-rows-keyed-p (cdr rows) a))
    t))
