(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-otm-disk-effect (e l440 l441)
  (declare (xargs :guard t))
  (cond ((equal e *fn-otm-generic-440*) (fn-nntp-reply-effect l440))
        ((equal e *fn-otm-generic-441*) (fn-nntp-reply-effect l441))
        (t e)))

(defun fn-otm-disk-effects-loop (effects l440 l441 acc)
  (declare (xargs :guard t))
  (if (consp effects)
      (fn-otm-disk-effects-loop (cdr effects) l440 l441
                                (cons (fn-otm-disk-effect (car effects) l440 l441) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-otm-disk-effects (effects l440 l441)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp effects)
                  (cons (cond ((equal (car effects) *fn-otm-generic-440*) (fn-nntp-reply-effect l440))
                              ((equal (car effects) *fn-otm-generic-441*) (fn-nntp-reply-effect l441))
                              (t (car effects)))
                        (fn-otm-disk-effects (cdr effects) l440 l441))
                nil)
       :exec (fn-otm-disk-effects-loop effects l440 l441 nil)))

(defthm fn-otm-disk-effects-loop-is-rev-onto
  (equal (fn-otm-disk-effects-loop effects l440 l441 acc)
         (fn-ag-rev-onto acc (fn-otm-disk-effects effects l440 l441)))
  :hints (("Goal" :induct (fn-otm-disk-effects-loop effects l440 l441 acc)
                  :in-theory (union-theories
                              '(fn-otm-disk-effects-loop fn-otm-disk-effects
                                fn-ag-rev-onto car-cons cdr-cons fn-otm-disk-effect)
                              (theory 'minimal-theory)))))

(verify-guards fn-otm-disk-effects
  :hints (("Goal" :in-theory (union-theories
                              '(fn-otm-disk-effects fn-ag-rev-onto
                                fn-otm-disk-effects-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))
