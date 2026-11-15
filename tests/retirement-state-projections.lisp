; Test snapshots materialized from the existing column declarations.
(in-package "ACL2")
(include-book "../books/columns")
(defun fn2-riud-projection-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((name (car names))
         (schema (cdr (assoc-eq name (fn2-decl-rows :columns world))))
         (fields (append (fn2-columns-fields name (fn2-decl-get :columns schema))
                         `((,(fn2-columns-sym name "-ROWS") :type (integer 0 ,(- (fn2-decl-get :rows-bound schema) 1)) :initially 0))
                         (fn2-decl-get :extra-fields schema))))
   (append (fn2-columns-reference-events name (fn2-columns-sym name "-REF") fields)
           (fn2-riud-projection-events (cdr names) world)))))
