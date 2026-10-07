(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-nntp-group-high (group articles)
  :shape :foldr :over articles :elt a
  :combine (let ((number (fn-nntp-article-number group a)))
                (if (and (posp number) (< acc number)) number acc))
  :init 0
  :rev fn-ag-rev-onto
  :loop-guard (natp acc))

