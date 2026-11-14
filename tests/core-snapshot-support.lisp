; Complete ordinary snapshots around real stobj execution. Reuse the
; representation's traversal generator without loading a reference machine.
(in-package "ACL2")
(include-book "../books/assembly-init")

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
(defun fn2-test-core-snapshot-events (children world)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (let* ((field (caar children)) (child (cadar children))
           (fields (fn2-test-snapshot-fields child world))
           (renames (fn2-test-snapshot-renames fields))
           (table (fn2-columns-sym 'fn2-test-table-snapshot- (symbol-name child)))
           (name (fn2-columns-sym 'fn2-test-snapshot- (symbol-name child))))
      (append
       (sublis renames (fn2-test-snapshot-array-events child fields))
       `((defun ,table (,child)
           (declare (xargs :stobjs ,child :verify-guards nil))
           (list ,@(sublis renames (fn2-columns-snapshot-calls child fields))))
         (defun ,name (fn2-core)
               (declare (xargs :stobjs fn2-core :verify-guards nil))
               (stobj-let ((,child (,field fn2-core))) (snapshot)
                 (,table ,child) snapshot)))
       (fn2-test-core-snapshot-events (cdr children) world)))))
(defun fn2-test-core-snapshot-runes (children world)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (append (strip-cdrs (fn2-test-snapshot-renames
                         (fn2-test-snapshot-fields (cadar children) world)))
            (fn2-test-core-snapshot-runes (cdr children) world))))
(defun fn2-test-core-snapshot-calls (children)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (cons `(,(fn2-columns-sym 'fn2-test-snapshot- (symbol-name (cadar children))) fn2-core)
          (fn2-test-core-snapshot-calls (cdr children)))))
(make-event
 (let ((events (fn2-test-core-snapshot-events *fn2-core-children* (w state)))
       (runes (fn2-test-core-snapshot-runes *fn2-core-children* (w state))))
   (value `(progn
             (encapsulate ()
               (local (in-theory nil))
               ,@events)
             (in-theory (disable ,@runes))))))
(make-event
 (value `(defun fn2-test-core-snapshot (fn2-core)
           (declare (xargs :stobjs fn2-core :verify-guards nil))
           (list ,@(fn2-test-core-snapshot-calls *fn2-core-children*)))))
