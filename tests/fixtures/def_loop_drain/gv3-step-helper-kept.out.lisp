(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(defun fn-cll-key-values-step (x rest)
  (declare (xargs :guard t))
  (fn-cll-append *fn-cll-key-word* (fn-cll-append x rest)))

(def-loop fn-cll-key-values (keys)
  :shape :foldr :over keys :elt k
  :combine (fn-cll-append *fn-cll-key-word* (fn-cll-append k acc)) :init nil
  :rev fn-ag-rev-onto)

(defthm fn-cll-key-values-step-of-nil
  (equal (fn-cll-key-values-step nil rest) (fn-cll-append *fn-cll-key-word* (fn-cll-append nil rest))))
