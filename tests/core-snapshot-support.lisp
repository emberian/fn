; Complete ordinary snapshots around real stobj execution. Reuse the
; representation's traversal generator without loading a reference machine.
(in-package "ACL2")
(include-book "../books/assembly-init")
(include-book "column-snapshot-support")

(defun fn2-test-core-snapshot-events (children world)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (let* ((field (caar children)) (child (cadar children))
           (table (fn2-columns-sym 'fn2-test-table-snapshot- (symbol-name child)))
           (name (fn2-columns-sym 'fn2-test-snapshot- (symbol-name child))))
      (append
       (fn2-test-column-snapshot-events child world)
       `((defun ,name (fn2-core)
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
             (local (deftheory fn2-test-snapshot-base-theory (current-theory :here)))
             (encapsulate ()
               (local (in-theory nil))
               ,@events)
             (local (in-theory (theory 'fn2-test-snapshot-base-theory)))
             (in-theory (disable ,@runes))))))
(make-event
 (value `(defun fn2-test-core-snapshot (fn2-core)
           (declare (xargs :stobjs fn2-core :verify-guards nil))
           (list ,@(fn2-test-core-snapshot-calls *fn2-core-children*)))))
