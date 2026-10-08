(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-orc-rewrite-rows (rows ctx fn-arena)
  :shape :map :over rows :elt r :stobjs fn-arena
  :body (fn-orc-rewrite-row r ctx fn-arena))

