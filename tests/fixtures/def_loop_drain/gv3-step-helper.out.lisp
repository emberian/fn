(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-cll-key-values (keys)
  :shape :foldr :over keys :elt k
  :combine (fn-cll-append *fn-cll-key-word* (fn-cll-append k acc)) :init nil
  :rev fn-ag-rev-onto)

