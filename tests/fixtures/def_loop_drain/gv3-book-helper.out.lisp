(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(defun fn-otm-disk-effect (e l440 l441)
  (declare (xargs :guard t))
  (cond ((equal e *fn-otm-generic-440*) (fn-nntp-reply-effect l440))
        ((equal e *fn-otm-generic-441*) (fn-nntp-reply-effect l441))
        (t e)))

(def-loop fn-otm-disk-effects (effects l440 l441)
  :shape :map :over effects :elt e
  :body (if (equal e *fn-otm-generic-440*)
            (fn-nntp-reply-effect l440)
            (if (equal e *fn-otm-generic-441*) (fn-nntp-reply-effect l441) e)))

