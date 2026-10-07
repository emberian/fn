(include-book "peer-feed-invariants")
(include-book "def-loop")

(def-loop fn-own-feed-targets (tbl origin groups path)
  :shape :map :over tbl :elt e
  :keep (fn-own-feed-offerablep (fn-own-feed-entry-record e) origin groups path)
  :body (fn-own-feed-entry-name e))

(defthm fn-own-feed-targets-true-listp
  (true-listp (fn-own-feed-targets tbl origin groups path)))
