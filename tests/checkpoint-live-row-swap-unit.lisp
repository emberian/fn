; Actual shared row operations only. This supplies the whole row-model guard,
; not publication/hold/adoption authority. Prepared; ACL2 not run here.
(in-package "ACL2")
(include-book "../books/checkpoint-live-adoption")
(defun fn2-live-row-fixture-setters (name cols)
 (declare (xargs :verify-guards nil))
 (if (atom cols) nil
  (append
   (list (list name (list (fn2-columns-col-name name (fn2-columns-pre "SET-" (caar cols))) 0 0 name))
         (list name (list (fn2-columns-col-name name (fn2-columns-pre "SET-" (caar cols))) 1 1 name)))
   (fn2-live-row-fixture-setters name (cdr cols)))))
(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-checkpoint-summary) (w state)))))
  (value
   `(defun fn2-live-row-fixture-body (fn2-checkpoint-summary)
     (declare (xargs :stobjs fn2-checkpoint-summary :verify-guards nil))
     (let* ((fn2-checkpoint-summary (fn2-checkpoint-summary-init 2 fn2-checkpoint-summary))
            ,@(fn2-live-row-fixture-setters 'fn2-checkpoint-summary cols)
            (fn2-checkpoint-summary (update-fn2-checkpoint-summary-descriptori 0 11 fn2-checkpoint-summary))
            (fn2-checkpoint-summary (update-fn2-checkpoint-summary-descriptori 32 19 fn2-checkpoint-summary))
            (fn2-checkpoint-summary (update-fn2-checkpoint-summary-next-tag 33 fn2-checkpoint-summary))
            (left (fn2-checkpoint-summary-row-snapshot 0 fn2-checkpoint-summary))
            (right (fn2-checkpoint-summary-row-snapshot 1 fn2-checkpoint-summary))
            (antecedent (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
                             (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                             (< 1 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))))
            (fn2-checkpoint-summary (fn2-checkpoint-summary-swap-rows 0 1 fn2-checkpoint-summary))
            (rows-swapped (and (equal left (fn2-checkpoint-summary-row-snapshot 1 fn2-checkpoint-summary))
                               (equal right (fn2-checkpoint-summary-row-snapshot 0 fn2-checkpoint-summary))))
            (globals-unchanged (and (= (fn2-checkpoint-summary-descriptori 0 fn2-checkpoint-summary) 11)
                                    (= (fn2-checkpoint-summary-descriptori 32 fn2-checkpoint-summary) 19)
                                    (= (fn2-checkpoint-summary-next-tag fn2-checkpoint-summary) 33)))
            (fn2-checkpoint-summary (fn2-live-adoption-swap-descriptors 0 fn2-checkpoint-summary)))
      (mv (and antecedent rows-swapped globals-unchanged (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
               (= (fn2-checkpoint-summary-descriptori 0 fn2-checkpoint-summary) 19)
               (= (fn2-checkpoint-summary-descriptori 32 fn2-checkpoint-summary) 11)
               (= (fn2-checkpoint-summary-next-tag fn2-checkpoint-summary) 33)) fn2-checkpoint-summary))))))
(assert-event
 (with-local-stobj fn2-checkpoint-summary
  (mv-let (ok fn2-checkpoint-summary) (fn2-live-row-fixture-body fn2-checkpoint-summary) ok)))
