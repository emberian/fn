; Shared checkpoint child domain/table/frame generators. Root1 and terminal
; disposal consume the same actual definitions, with no wrapper twins.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)

(defun fn2-checkpoint-root1-child-hyps (children)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (list* (list (fn2-columns-sym (car children) "P") (car children))
         (list (fn2-columns-sym (car children) "-WFP") (car children))
         (fn2-checkpoint-root1-child-hyps (cdr children)))))

(defun fn2-checkpoint-root1-child-tables (children)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (cons (intern-in-package-of-symbol
         (concatenate 'string "FN2-CORE-" (subseq (symbol-name (car children)) 4)) 'fn2-core)
        (fn2-checkpoint-root1-child-tables (cdr children)))))

(defun fn2-checkpoint-root1-child-specs (children n)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (let* ((s (car children)) (base (concatenate 'string "-" (subseq (symbol-name s) 4))))
   (append (list (list (concatenate 'string base "-TYPE") (fn2-columns-sym s "P") n)
                 (list (concatenate 'string base "-WFP") (fn2-columns-sym s "-WFP") n)
                 (list (concatenate 'string base "-ROWS") (fn2-columns-sym s "-ROWS") n :frame s))
           (fn2-checkpoint-root1-child-specs (cdr children) (+ n 1))))))
