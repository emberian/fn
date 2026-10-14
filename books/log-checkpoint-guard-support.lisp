; Stable byte-list facts used when a predecessor keeps the predicate opaque.
(in-package "ACL2")
(include-book "cbor")
(defthm fn-lc-cbor-octet-list-head
 (implies (and (fn-cbor-octet-listp xs) (consp xs))
          (unsigned-byte-p 8 (car xs)))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
(defthm fn-lc-cbor-octet-list-tail
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs)))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
