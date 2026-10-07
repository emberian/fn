(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-pb-upto-semicolon (r)
  :shape :foldr :over r :elt e
  :combine (if (equal e 59) nil (if (equal acc :no) :no (cons e acc))) :init :no
  :rev fn-ag-rev-onto)

