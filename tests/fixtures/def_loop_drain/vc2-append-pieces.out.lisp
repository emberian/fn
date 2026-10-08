(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-nntp-append-pieces (pieces)
  :shape :concat :over pieces :elt p
  :body p
  :rev fn-ag-rev-onto)

(local
 (defthm fn-nntp-append-pieces-revappend-rev-onto
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

