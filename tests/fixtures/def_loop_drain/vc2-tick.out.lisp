(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-own-feed-tick (names tbl obs)
  :shape :thread :over names :st tbl :elt n
  :let ((one (fn-own-feed-tick-peer n tbl obs))) :row (cdr one) :next (car one)
  :make (cons tbl dl-rows) :st-of (car dl-r) :rows-of (cdr dl-r) :rev fn-ag-rev-onto)

(local
 (defthm fn-own-feed-tick-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto a acc) b)
          (fn-ag-rev-onto acc (append a b)))))

