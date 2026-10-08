(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-ng-len (xs)
  :shape :foldr :over xs :elt x
  :combine (1+ acc) :init 0
  :rev fn-ag-rev-onto
  :loop-guard (rationalp acc))

