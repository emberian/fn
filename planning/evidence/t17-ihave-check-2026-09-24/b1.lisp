(progn
(defun pixb-arts (n acc)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n) acc
    (pixb-arts (- n 1)
               (cons (fn-make-article (concatenate 'string "<t17-" (coerce (explode-atom n 10) 'string) "@example.invalid>")
                                      nil nil nil nil nil)
                     acc))))
(defun pixb-binds (arts)
  (declare (xargs :verify-guards nil))
  (if (consp arts) (cons (fn-node-make-binding (fn-article-msgid (car arts)) "s" "o") (pixb-binds (cdr arts))) nil))
(defun pixb-node (arts)
  (declare (xargs :verify-guards nil))
  (fn-node-make-state (fn-make-state nil nil arts 0 nil nil) nil nil
                      (pixb-binds arts)))
)
