; Test-only complete state projections from the actual column declarations.
(in-package "ACL2")
(include-book "../books/alloc")
(defmacro fn2-alloc-test-reference-events (name)
 `(make-event
   (let* ((name ',name)
          (schema (cdr (assoc-eq name (fn2-decl-rows :columns (w state)))))
          (fields (append (fn2-columns-fields name (fn2-decl-get :columns schema))
                          (list (list (fn2-columns-sym name "-ROWS") :type
                                      (list 'integer 0 (- (fn2-decl-get :rows-bound schema) 1)) :initially 0))
                          (fn2-decl-get :extra-fields schema))))
    (cons 'progn (fn2-columns-reference-events name (fn2-columns-sym name "-REF") fields)))))
(fn2-alloc-test-reference-events fn2-extents)
(fn2-alloc-test-reference-events fn2-alloc-edges)
