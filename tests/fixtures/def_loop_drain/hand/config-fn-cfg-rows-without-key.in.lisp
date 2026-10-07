(include-book "records-invariants")

(defun fn-cfg-rows-without-key-loop (rows a acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (fn-cfg-rows-without-key-loop (cdr rows) a
       (if (not (equal (fn-cfg-row-a (car rows)) a)) (cons (car rows) acc) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-cfg-rows-without-key (rows a)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (if (equal (fn-cfg-row-a (car rows)) a)
               (fn-cfg-rows-without-key (cdr rows) a)
             (cons (car rows) (fn-cfg-rows-without-key (cdr rows) a)))
         nil)
       :exec (fn-cfg-rows-without-key-loop rows a nil)))

(defthm fn-cfg-rows-without-key-loop-is-rev-onto
  (equal (fn-cfg-rows-without-key-loop rows a acc)
         (fn-ag-rev-onto acc (fn-cfg-rows-without-key rows a)))
  :hints (("Goal" :induct (fn-cfg-rows-without-key-loop rows a acc)
                  :in-theory (union-theories
                              '(fn-cfg-rows-without-key-loop fn-cfg-rows-without-key fn-ag-rev-onto not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-cfg-rows-without-key
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cfg-rows-without-key fn-ag-rev-onto fn-cfg-rows-without-key-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-cfg-rows-keyed-p (rows a)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (equal (fn-cfg-row-a (car rows)) a)
           (fn-cfg-rows-keyed-p (cdr rows) a))
    t))
