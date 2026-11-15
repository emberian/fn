; Schema-owned single-row reset. Extra arrays/counters and other rows survive;
; callers decide when their exact lifetime permits resetting a row.
(in-package "ACL2")
(include-book "columns")
(defun fn2-columns-row-reset-fields (cols)
 (declare (xargs :verify-guards nil))
 (if (atom cols) nil
  (cons (list (caar cols) (if (eq (cadar cols) :link) '*fn2-none* 0))
        (fn2-columns-row-reset-fields (cdr cols)))))
(defun fn2-columns-row-reset-event (name world)
 (declare (xargs :verify-guards nil))
 (let* ((schema (cdr (assoc-eq name (fn2-decl-rows :columns world))))
        (cols (fn2-decl-get :columns schema))
        (fn (fn2-columns-sym name "-RESET-ROW"))
        (p (fn2-columns-sym name "P"))
        (wfp (fn2-columns-sym name "-WFP"))
        (rows (fn2-columns-sym name "-ROWS")))
  (if (not schema) (er hard 'fn2-columns-row-reset-event "Missing columns schema ~x0." name)
   `(progn
     (defun ,fn (row ,name)
      (declare (xargs :stobjs ,name :guard (and (,p ,name) (,wfp ,name))))
      (if (not (and (natp row) (< row (,rows ,name)))) ,name
       (let* ,(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name 'row
                (fn2-columns-row-reset-fields cols)) ,name)))
     (,(fn2-columns-sym name "-PRESERVES") ,fn (row ,name))))))
