(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-xrt-srcs-handles (srcs k)
  :shape :take :count k :over srcs :elt s
  :guard (natp k)
  :while (consp srcs)
  :body (and (natp s) s))

(def-loop fn-xrt-quiet-files (retired named fn-arena$x)
  :shape :map :over retired :elt r :stobjs fn-arena$x
  :guard (and (nat-listp retired) (true-listp named))
  :keep (and (not (member r named)) (equal (fn-arx-file-count r fn-arena$x) 0))
  :body r)

