; Schema-only snapshot generation for focused child fixtures. Traversal
; definitions and termination hints come from the representation generator.
(in-package "ACL2")
(include-book "../books/columns")

(defun fn2-test-snapshot-fields (name world)
  (declare (xargs :verify-guards nil))
  (let ((schema (cdr (assoc-eq name (fn2-decl-rows :columns world)))))
    (if (not schema)
        (er hard 'fn2-test-snapshot-fields "No columns schema for ~x0." name)
      (append (fn2-columns-fields name (fn2-decl-get :columns schema))
              (list (list (fn2-columns-sym name "-ROWS")))
              (fn2-decl-get :extra-fields schema)))))
(defun fn2-test-snapshot-renames (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((old (fn2-columns-col-name (caar fields) :logical-snapshot)))
      (append (and (fn2-columns-arrayp (car fields))
                   (list (cons old (fn2-columns-pre "FN2-TEST-" old))))
              (fn2-test-snapshot-renames (cdr fields))))))
(defun fn2-test-snapshot-find-definition (name form)
  (declare (xargs :verify-guards nil))
  (cond ((atom form) nil)
        ((and (eq (car form) 'defun) (eq (cadr form) name)) form)
        (t (or (fn2-test-snapshot-find-definition name (car form))
               (fn2-test-snapshot-find-definition name (cdr form))))))
(defun fn2-test-snapshot-array-events (name fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((arrayp (fn2-columns-arrayp (car fields)))
           (fn (fn2-columns-col-name (caar fields) :logical-snapshot))
           ; One field per invocation keeps the representation generator in
           ; snapshot mode: its next-field default also emits copy/diff.
           (generated (and arrayp
                        (fn2-columns-traversals name name (list (car fields)) '(:snapshot))))
           (definition (and arrayp (fn2-test-snapshot-find-definition fn generated))))
      (if (and arrayp (not definition))
          (er hard 'fn2-test-snapshot-array-events "Missing generated snapshot definition ~x0." fn)
        ; Proof fixtures need the exact generated function and termination
        ; hints, not hundreds of served-operation registry updates.
        (append (and arrayp (list definition))
                (fn2-test-snapshot-array-events name (cdr fields)))))))
(defun fn2-test-column-snapshot-events (child world)
  (declare (xargs :verify-guards nil))
  (let* ((fields (fn2-test-snapshot-fields child world))
         (renames (fn2-test-snapshot-renames fields))
         (table (fn2-columns-sym 'fn2-test-table-snapshot- (symbol-name child))))
    (append
     (sublis renames (fn2-test-snapshot-array-events child fields))
     `((defun ,table (,child)
         (declare (xargs :stobjs ,child :verify-guards nil))
         (list ,@(sublis renames (fn2-columns-snapshot-calls child fields))))))))
