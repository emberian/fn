; The configuration fold invalidates adoption evidence on peer mutation.
(in-package "ACL2")
(include-book "config")

(local
 (defthm fn-par-keyed-receipt-free
   (implies (fn-par-receipt-freep rows)
            (fn-par-receipt-freep (fn-cfg-rows-with-key rows key)))
   :hints (("Goal" :induct (fn-cfg-rows-with-key rows key)
            :in-theory (enable fn-cfg-rows-with-key fn-par-receipt-freep)))))

(local
 (defthm fn-par-with-key-of-append
   (equal (fn-cfg-rows-with-key (append a b) key)
          (append (fn-cfg-rows-with-key a key) (fn-cfg-rows-with-key b key)))
   :hints (("Goal" :induct (append a b)
            :in-theory (enable fn-cfg-rows-with-key)))))

(local
 (defthm fn-par-with-key-of-without-key
   (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows key) key) nil)
   :hints (("Goal" :induct (fn-cfg-rows-without-key rows key)
            :in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-without-key)))))

(local
 (defthm fn-par-receipt-free-append
   (implies (and (fn-par-receipt-freep a) (fn-par-receipt-freep b))
            (fn-par-receipt-freep (append a b)))))

(defthm fn-par-generic-peer-mutation-invalidates-adoption
  (implies (member-equal (fn-cfg-delta-kind delta)
                        '(:set-peer :remove-peer :add-peer-rows :remove-peer-rows :set-peers))
           (fn-par-receipt-freep
            (fn-cfg-rows-with-key
             (fn-cfg-peers (fn-cfg-apply-delta value generation stamp delta))
             (fn-cfg-delta-a delta))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cfg-apply-delta)
                (fn-cfg-rows-with-key fn-cfg-rows-without-key
                 fn-par-without-receipts fn-par-receipt-freep)))))
