; Shared projection laws for both the declared core and extracted child products.
(in-package "ACL2")
(include-book "columns")
(defun fn2-core-lens-read-events (reader children)
 (declare (xargs :verify-guards nil))
 (if (endp children) nil
  (let* ((writer (caar children)) (update (fn2-columns-pre "UPDATE-" writer)))
   (cons `(defthm ,(fn2-columns-sym reader
                    (concatenate 'string "-OF-" (symbol-name update)))
            (equal (,reader (,update p c))
                   ,(if (eq reader writer) 'p `(,reader c)))
            :hints (("Goal" :in-theory (enable ,reader ,update))))
         (fn2-core-lens-read-events reader (cdr children))))))
(defun fn2-core-lens-missing-events (events world)
 (declare (xargs :verify-guards nil))
 (if (atom events) nil
  (append (and (not (getpropc (cadar events) 'theorem nil world)) (list (car events)))
          (fn2-core-lens-missing-events (cdr events) world))))
