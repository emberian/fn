(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-fps-other-slot-rows (rows row)
  :shape :map :over rows :elt r
  :keep (and (fn-fps-slot-rowp r) (not (equal r row)))
  :body r)

(def-loop fn-fps-live-names (names peers)
  :shape :map :over names :elt n
  :keep (fn-fps-pausedp n peers) :keep-order :skip-first
  :body n)

