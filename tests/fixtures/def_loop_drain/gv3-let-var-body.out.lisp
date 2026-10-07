(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-bpnp-prune-waits (waits held)
  :shape :map :over waits :elt w
  :let ((row w) (key (fn-bpn-nth 1 row)))
  :keep (fn-bpnf-find-held key held)
  :body row)

