(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

; (:ok PROJECTIONS) in the written order, or the first address's refusal.
(def-loop fn-ncfg-listener-plan (elements)
  :shape :foldr :over elements :elt e
  :combine (let ((r (fn-ncfg-listener-element (fn-ncfg-trim e))))
                (if (equal (fn-ncfg-first r) :refused)
                    r
                    (if (equal (fn-ncfg-first acc) :refused)
                        acc
                        (if (fn-ncfg-memberp (fn-ncfg-second r) (fn-ncfg-second acc))
                            (list :refused :listener-duplicate)
                            (list :ok (cons (fn-ncfg-second r) (fn-ncfg-second acc)))))))
  :init (list :ok nil)
  :rev fn-ag-rev-onto)

