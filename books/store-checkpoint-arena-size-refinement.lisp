; Actual called finish projection; include full arena only for the boundary.
(in-package "ACL2")
(include-book "store-checkpoint-arena-load")
(include-book "store-checkpoint-arena-size-load")
(local (in-theory (disable (tau-system))))
(defthm fn-sckas-finish-result-is-existing-by-definition
 (equal (mv-nth 0 (fn-sckas-finish rest s i b fn-octets))
        (fn-scka-finish rest s i b fn-octets))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-sctsr-load-result-is-existing-by-definition
                         (plan rest)))
          :in-theory (e/d (fn-sckas-finish fn-scka-finish)
                          (fn-sctsr-load fn-sct-load fn-sshr-share
                           fn-sct-tables-f fn-sco-at)))))
