; Existing relation/model events extracted verbatim for a narrow proof boundary.
(in-package "ACL2")
(include-book "nov-row-capture")
(include-book "served-column-relation")

(defthm fn-nrf-facts-handle
  (implies (fn-nrf-facts seq fn-cat)
           (natp (fn-record-payload (fn-cat-at seq fn-cat))))
  :rule-classes :forward-chaining)

(defthm fn-nrf-facts-are-row-bytes-facts
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-nrf-facts seq fn-cat))
           (equal (fn-nrf-facts seq fn-cat)
                  (fn-held-facts-of
                   (fn-nntp-payload-bytes
                    (fn-record-payload (fn-cat-at seq fn-cat)) fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-scol-rows-okp-nth (rows fn-cat)))
           :in-theory (e/d (fn-nrf-facts fn-scol-okp fn-scol-row-okp
                            fn-cat-at-is-nth fn-cat-count-is-len)
                           (fn-held-facts-of fn-scol-rows-okp
                            fn-scol-rows-okp-nth fn-nntp-payload-bytes)))))
