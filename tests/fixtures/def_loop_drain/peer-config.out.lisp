(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-cfg-peer-names (peers)
  :shape :map :over peers :elt p
  :keep (equal (fn-cfg-row-b p) "path-identity")
  :body (fn-cfg-row-a p))

