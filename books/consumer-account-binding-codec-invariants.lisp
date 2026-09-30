; Boundary proofs for durable binding preparation, not authority adoption.
(in-package "ACL2")
(include-book "consumer-account-binding-codec")

(local (defthm fn-cab-empty-proper-tail (implies (and (true-listp x) (equal (len x) 0)) (equal x nil)) :rule-classes nil :hints (("Goal" :induct (len x)))))
(local (defthm fn-cab-proper5-reconstruct (implies (and (true-listp x) (equal (len x) 5)) (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x)) :rule-classes nil :hints (("Goal" :use ((:instance fn-cab-empty-proper-tail (x (cdr (cdr (cdr (cdr (cdr x)))))))) :in-theory (enable len true-listp nth)))))

(defthm fn-cab-event-charge-is-exact-encoding
 (equal (fn-cab-event-charge event) (len (fn-cab-encode event)))
 :hints (("Goal" :in-theory
 (e/d (fn-cab-event-charge fn-cab-encode fn-cab-eventp fn-cab-operationp
 fn-cac-fields-charge fn-cac-field-width fn-cac-fields-encode fn-cac-field-encode
 fn-cac-fieldp fn-cac-fields-validp fn-cac-u64p fn-cp-nth)
 (fn-cbor-u64-bytes fn-cp-idp fn-cab-decisionp)))))
(defthm fn-cab-encode-bound
 (<= (len (fn-cab-encode event)) (fn-cab-octet-ceiling))
 :rule-classes :linear
 :hints (("Goal"
 :use (fn-cab-event-charge-is-exact-encoding
       (:instance fn-cac-valid-fields-fit-derived-ceiling
        (values (cdr (fn-cp-nth 4 event))) (kinds *fn-cab-field-kinds*)))
 :in-theory (e/d (fn-cab-octet-ceiling fn-cab-eventp fn-cab-operationp fn-cab-event-charge)
 (fn-cab-encode fn-cac-fields-charge fn-cac-fields-validp fn-cab-decisionp
 fn-cac-fields-charge-is-encoded-length fn-cab-event-charge-is-exact-encoding)))))
(defthm fn-cab-encode-octets
 (fn-cbor-octet-listp (fn-cab-encode event))
 :hints (("Goal" :in-theory
 (e/d (fn-cab-encode fn-cab-eventp fn-cab-operationp fn-cac-fields-validp
 fn-cac-fieldp fn-cac-u64p fn-cp-nth fn-cbor-octet-listp-append
 fn-cbor-octet-listp-implies-true-listp)
 (fn-cac-fields-encode fn-cbor-octet-listp binary-append fn-cp-idp fn-cab-decisionp)))))
(local (defthm fn-cab-event-reconstruct
 (implies (fn-cab-eventp event)
 (equal (list :consumer-authority (fn-cp-nth 1 event) (fn-cp-nth 2 event)
               (fn-cp-nth 3 event) (fn-cp-nth 4 event)) event))
 :hints (("Goal"
 :use ((:instance fn-cab-proper5-reconstruct (x event)))
 :in-theory (e/d (fn-cab-eventp fn-cp-nth)
 (fn-cab-operationp fn-cac-u64p fn-cbor-at-mostp))))))

(local (defthm fn-cab-at-most-is-length-bound
 (implies (natp bound)
 (equal (fn-cbor-at-mostp xs bound) (<= (len xs) bound)))
 :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
 :in-theory (enable fn-cbor-at-mostp)))))

(local (defthm fn-cab-encode-coordinates-read
 (implies (fn-cab-eventp event)
 (equal (fn-cac-read-fields (nthcdr 6 (fn-cab-encode event)) '(:u64 :u64 :u64))
 (list :ok (list (fn-cp-nth 1 event) (fn-cp-nth 2 event) (fn-cp-nth 3 event))
 (fn-cac-fields-encode (cdr (fn-cp-nth 4 event)) *fn-cab-field-kinds*))))
 :hints (("Goal" :in-theory
 (e/d (fn-cab-encode fn-cab-eventp fn-cac-fields-validp fn-cac-fieldp fn-cp-nth nthcdr)
 (fn-cac-read-fields fn-cac-fields-encode fn-cab-operationp fn-cac-u64p))))))

(local (defthm fn-cab-encode-header
 (implies (fn-cab-eventp event)
 (equal (take 6 (fn-cab-encode event)) '(102 110 99 101 3 7)))
 :hints (("Goal" :in-theory (e/d (fn-cab-encode take)
 (fn-cab-eventp fn-cac-fields-encode))))))
(defthm fn-cab-decode-encode
 (implies (fn-cab-eventp event)
 (equal (fn-cab-decode-exact (fn-cab-encode event)) (list :ok event)))
 :hints (("Goal" :do-not-induct t
 :use (fn-cab-encode-bound fn-cab-encode-octets fn-cab-event-reconstruct)
 :in-theory (e/d (fn-cab-decode-exact fn-cab-eventp fn-cab-operationp
 fn-cp-nth fn-cab-octet-ceiling fn-cab-at-most-is-length-bound)
 (fn-cab-event-reconstruct fn-cab-encode fn-cac-read-fields fn-cac-fields-encode
 fn-cac-fields-validp fn-cac-u64p fn-cab-decisionp fn-cbor-at-mostp fn-cbor-octet-listp
 take nthcdr fn-cab-encode-octets)))))
