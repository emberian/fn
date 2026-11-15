(defmacro fn2-event-archive-operation (name children outputs &rest body)
 `(progn
   (defun ,name ,children
    (declare (xargs :stobjs ,children
     :guard (and ,@(fn2-checkpoint-root1-child-hyps children))))
    ,@body)
   (fn2-checkpoint-root1-preserves ,name ,children
    :hyps ,(fn2-checkpoint-root1-child-hyps children)
    :specs ,(append (fn2-checkpoint-root1-child-specs outputs 1)
                   (fn2-checkpoint-root1-extra-specs outputs 1)))
   (defcost ,(fn2-columns-sym name "-OP") :child ,name :answers t
    :bytes (* 2 *fn2-run-layout-max-entry-bytes*)
    :tables ,(fn2-checkpoint-root1-child-tables children)
    :doc "Bounded internal canonical-member staging through the actual run writer.")))

