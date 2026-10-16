; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-corr-after-log-append")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lblot-octets-append
 (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
 (fn-cbor-octet-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append fn-cbor-octet-listp)))))

(defthm fn-lb-log-model-nat-octets-are-octets
 (fn-cbor-octet-listp (fn-lb-log-model-nat-octets n))
 :hints (("Goal" :induct (fn-lb-log-model-nat-octets n)
 :in-theory (enable fn-lb-log-model-nat-octets fn-cbor-octet-listp fn-cbor-octetp))))

(local (defthm fn-lblot-string-octets-aux
 (fn-cbor-octet-listp (fn-record-string-octets-aux chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
 :in-theory (enable fn-record-string-octets-aux fn-cbor-octet-listp fn-cbor-octetp)))))

(local (defthm fn-lblot-string-octets
 (fn-cbor-octet-listp (fn-record-string-octets text))
 :hints (("Goal" :in-theory (set-difference-theories
 (union-theories (theory 'ground-zero)
 '(fn-record-string-octets fn-lblot-string-octets-aux fn-cbor-octet-listp))
 '((tau-system)))))))

(defthm fn-lb-log-model-text-octets-are-octets
 (fn-cbor-octet-listp (fn-lb-log-model-text-octets text))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-text-octets fn-lblot-octets-append fn-lblot-string-octets
 fn-lb-log-model-nat-octets-are-octets)))))

(defthm fn-lb-log-model-value-octets-are-octets
 (fn-cbor-octet-listp (fn-lb-log-model-value-octets value))
 :hints (("Goal" :induct (fn-lb-log-model-value-octets value)
 :in-theory (enable fn-lb-log-model-value-octets fn-cbor-octet-listp fn-cbor-octetp))))

(defthm fn-lb-log-model-home-frame-is-octets
 (implies (fn-cat-rowp row) (fn-cbor-octet-listp (fn-lb-log-model-home-frame row)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-home-frame fn-lblot-octets-append
 fn-lb-log-model-nat-octets-are-octets fn-lb-log-model-value-octets-are-octets)))))

(defthm fn-lb-log-model-pre-is-octets
 (fn-cbor-octet-listp (fn-lb-log-model-pre row payload))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-pre fn-lblot-octets-append fn-lb-log-model-nat-octets-are-octets
 fn-cbor-octet-listp fn-cbor-octetp)))))

(local (defthm fn-lblot-wire-is-octets
 (implies (fn-cbor-octet-listp payload) (fn-cbor-octet-listp (fn-lb-log-model-wire payload startp)))
 :hints (("Goal" :induct (fn-lb-log-model-wire payload startp)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-wire fn-cbor-octet-listp fn-cbor-octetp fn-lblot-octets-append))))))

(defthm fn-lb-log-model-next-range-is-octets
 (implies (fn-cbor-octet-listp payload) (fn-cbor-octet-listp (fn-lb-log-model-next-range payload)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-next-range fn-la-payload-wire fn-la-tombstone-raw fn-lblot-wire-is-octets)))))

(defthm fn-lb-log-model-next-prefix-is-octets
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload))
 (fn-cbor-octet-listp (fn-lb-log-model-next-prefix row payload)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-next-prefix fn-lblot-octets-append fn-lb-log-model-pre-is-octets
 fn-lb-log-model-next-range-is-octets fn-lb-log-model-home-frame-is-octets)))))
