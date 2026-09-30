; The actual arena finish obtains tables and ORIGINAL context annotation
; from one summary decode. The existing result remains the first value.
(in-package "ACL2")
(include-book "store-checkpoint-share")
(include-book "store-checkpoint-size-reader")
(local (in-theory (disable (tau-system))))
(defun fn-sckas-finish (rest s i b fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
  :guard-hints (("Goal" :use ((:instance fn-sctsr-load-existing-result-true-listp
                              (plan rest)))
                 :in-theory (disable fn-sctsr-load
                                     fn-sctsr-load-existing-result-true-listp)))))
 (if (not (equal i b)) (mv (list :refused :arena) nil nil)
  (mv-let (loaded info region) (fn-sctsr-load rest fn-octets)
   (if (not (eq (car loaded) :ok)) (mv loaded nil nil)
    (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr loaded))) s))
     (mv (list :refused :close) nil nil)
     (mv (fn-sshr-share loaded) info region))))))
(in-theory (disable fn-sckas-finish))
