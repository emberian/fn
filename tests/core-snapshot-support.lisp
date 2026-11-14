; Complete ordinary snapshots around real stobj execution. Reuse the
; representation's generated snapshot traversals; no state alias escapes.
(in-package "ACL2")
(include-book "../books/assembly-reference-children-b")

(defun fn2-test-core-snapshot-events (children)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (let* ((field (caar children)) (child (cadar children))
           (name (fn2-columns-sym 'fn2-test-snapshot- (symbol-name child))))
      (cons `(defun ,name (fn2-core)
               (declare (xargs :stobjs fn2-core :verify-guards nil))
               (stobj-let ((,child (,field fn2-core))) (snapshot)
                 (,(fn2-columns-sym child "-LOGICAL-SNAPSHOT") ,child) snapshot))
            (fn2-test-core-snapshot-events (cdr children))))))
(defun fn2-test-core-snapshot-calls (children)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (cons `(,(fn2-columns-sym 'fn2-test-snapshot- (symbol-name (cadar children))) fn2-core)
          (fn2-test-core-snapshot-calls (cdr children)))))
(make-event
 (value (cons 'progn (fn2-test-core-snapshot-events *fn2-core-children*))))
(make-event
 (value `(defun fn2-test-core-snapshot (fn2-core)
           (declare (xargs :stobjs fn2-core :verify-guards nil))
           (list ,@(fn2-test-core-snapshot-calls *fn2-core-children*)))))
