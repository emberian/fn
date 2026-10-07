(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-bpnp-attempt-replace (arrival record held)
  :shape :map :over held :elt h
  :stop (equal arrival (fn-bpn-nth 3 h))
  :stop-value (if (true-listp h) (cons (fn-bpnp-attempted-held h record) (cdr held)) nil)
  :body h)

