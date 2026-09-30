; Representation boundary for the typed physical C account-adoption commit.
; Decoding preserves bytes/fields; it does not establish publication authority.
(in-package "ACL2")
(include-book "consumer-account-config-marker")

(local (defthm fn-cacm-item-values-roundtrip
 (implies (fn-cac-fields-validp values kinds)
 (equal (fn-cacm-read-items (fn-cacm-items values kinds) kinds)
        (list :ok values)))
 :hints (("Goal" :induct (fn-cacm-items values kinds)
 :in-theory (e/d (fn-cacm-items fn-cacm-read-items fn-cac-fields-validp fn-cp-nth)
 (fn-cac-fieldp))))))

(local (defthm fn-cacm-empty-proper-tail (implies (and (true-listp x) (equal (len x) 0)) (equal x nil)) :rule-classes nil :hints (("Goal" :induct (len x)))))
(local (defthm fn-cacm-proper5-reconstruct (implies (and (true-listp x) (equal (len x) 5)) (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x)) :rule-classes nil :hints (("Goal" :use ((:instance fn-cacm-empty-proper-tail (x (cdr (cdr (cdr (cdr (cdr x)))))))) :in-theory (enable len true-listp nth)))))
(local (defthm fn-cacm-proper8-reconstruct (implies (and (true-listp x) (equal (len x) 8)) (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x)) x)) :rule-classes nil :hints (("Goal" :use ((:instance fn-cacm-empty-proper-tail (x (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))) :in-theory (enable len true-listp nth)))))

(local (defthm fn-cacm-record-fields-roundtrip
 (implies (fn-cacm-recordp r) (equal (fn-cacm-of-values (fn-cacm-values r)) r))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cacm-proper5-reconstruct (x r))
       (:instance fn-cacm-proper8-reconstruct (x (fn-cfg-record-change r)))
       (:instance fn-cacm-proper5-reconstruct (x (fn-cfg-record-stamp r))))
 :in-theory (e/d (fn-cacm-recordp fn-cacm-markerp fn-cacm-of-values fn-cacm-values
 fn-cacm-marker fn-cfg-record-make fn-cfg-record-shapep fn-cfg-record-sequence
 fn-cfg-record-txid fn-cfg-record-generation fn-cfg-record-change fn-cfg-record-stamp
 fn-cfg-ag-car fn-cfg-ag-cdr fn-cfg-stampp fn-clock-observationp
 fn-clock-observation-shapep fn-clock-observation fn-clock-monotonic fn-clock-wall
 fn-clock-wall-error fn-clock-has-wall fn-cp-nth)
 (fn-cac-u64p fn-cp-idp fn-cac-fieldp fn-cbor-at-mostp fn-clock-timep len true-listp))))))

(local (defthm fn-cacm-record-values-valid
 (implies (fn-cacm-recordp r)
          (fn-cac-fields-validp (fn-cacm-values r) *fn-cacm-kinds*))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-cacm-recordp fn-cacm-markerp fn-cacm-values
 fn-cac-fields-validp fn-cac-fieldp fn-cac-u64p fn-cfg-stampp
 fn-clock-observationp fn-clock-observation-shapep fn-clock-timep
 fn-clock-monotonic fn-clock-wall fn-clock-wall-error fn-clock-has-wall)
 (fn-cp-idp fn-cp-nth fn-cbor-at-mostp))))))

(local (defthm fn-cacm-bytes-prechecked-roundtrip
 (implies (and (fn-cbor-octet-listp xs)
               (<= (len xs) *fn-cbor-max-bytes*)
               (fn-cbor-octet-listp rest)
               (<= (len (append (fn-cbor-encode (cons :bytes xs)) rest))
                   *fn-cbor-max-input*))
  (equal (fn-cbor-decode-prechecked-wide
           (append (fn-cbor-encode (cons :bytes xs)) rest) *fn-cbor-max-bytes*)
         (fn-cbor-ok (cons :bytes xs) rest)))
 :hints (("Goal" :do-not-induct t
 :use (fn-record-cbor-stream-bytes-round-trip
       (:instance fn-cbor-decode-prechecked-wide-extends-narrow
        (octets (append (fn-cbor-encode (cons :bytes xs)) rest))
        (budget *fn-cbor-max-bytes*)))
 :in-theory (e/d (fn-cbor-decode fn-cbor-decode-bounded fn-cbor-result-okp
 fn-cbor-ok fn-record-at-most-is-length-bound)
 (fn-record-cbor-stream-bytes-round-trip fn-cbor-decode-prechecked-wide-extends-narrow
 fn-cbor-decode-prechecked-wide fn-cbor-decode-prechecked fn-cbor-encode
 fn-cbor-at-mostp fn-cbor-octet-listp))))))


(local (defthm fn-cacm-config-item-roundtrip
 (implies (and (fn-cfg-itemp item) (fn-cbor-octet-listp rest)
               (<= (len (append (fn-cfg-item-encode item) rest)) *fn-cbor-max-input*))
 (equal (fn-cfg-item-decode (append (fn-cfg-item-encode item) rest))
        (fn-cbor-ok item rest)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cfg-item-encode-octets (x item))
       (:instance fn-cbor-octet-listp-append (xs (fn-cfg-item-encode item)) (ys rest)))
 :in-theory (e/d (fn-cfg-itemp fn-cfg-uitemp fn-cfg-titemp fn-record-uint64p
 fn-cfg-item-decode fn-cfg-item-encode fn-record-at-most-is-length-bound
 fn-cbor-octet-listp-append fn-record-cbor-encode-octets fn-cbor-encode-uint-wide-octets)
 (fn-cbor-encode fn-cbor-encode-uint-wide fn-cbor-decode-prechecked-wide
 fn-cbor-octet-listp fn-cbor-at-mostp))))))

(local (defthm fn-cacm-config-cons-octets
 (fn-cbor-octet-listp (append (fn-cfg-item-encode item) (fn-cfg-item-octets items)))
 :hints (("Goal" :use ((:instance fn-cfg-item-encode-octets (x item))
 (:instance fn-cfg-item-octets-are-octets)
 (:instance fn-cbor-octet-listp-append (xs (fn-cfg-item-encode item)) (ys (fn-cfg-item-octets items))))
 :in-theory (disable fn-cfg-item-encode fn-cfg-item-octets fn-cbor-octet-listp)))))

(local (defthm fn-cacm-config-stream-roundtrip
 (implies (and (fn-cfg-item-listp items)
               (<= (len (fn-cfg-item-octets items)) *fn-cbor-max-input*))
  (equal (fn-cfg-parse-items (len items) (fn-cfg-item-octets items))
         (fn-record-parse-ok items nil)))
 :hints (("Goal" :induct (fn-cfg-item-octets items)
 :in-theory (e/d (fn-cfg-item-listp fn-cfg-item-octets fn-cfg-parse-items
 fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest fn-cbor-ok
 fn-record-parse-okp fn-record-parse-value fn-record-parse-rest fn-record-parse-ok
 fn-cfg-item-octets-are-octets fn-cfg-item-encode-octets fn-cbor-octet-listp-append)
 (fn-cfg-item-encode fn-cfg-item-decode fn-cfg-itemp fn-cbor-octet-listp))))))

(local (defthm fn-cacm-field-itemp
 (implies (and (member-eq kind '(:flag :u64 :id :bytes32)) (fn-cac-fieldp value kind))
  (fn-cfg-itemp (cons (if (member-eq kind '(:id :bytes32)) :bytes :uint) value)))
 :hints (("Goal" :in-theory (e/d (fn-cac-fieldp fn-cac-u64p fn-cp-idp
 fn-cfg-itemp fn-cfg-uitemp fn-cfg-titemp fn-record-uint64p
 fn-record-at-most-is-length-bound) (fn-cbor-at-mostp fn-cbor-octet-listp))))))

(local (defthm fn-cacm-field-item-bound
 (implies (and (member-eq kind '(:flag :u64 :id :bytes32)) (fn-cac-fieldp value kind))
  (<= (len (fn-cfg-item-encode
             (cons (if (member-eq kind '(:id :bytes32)) :bytes :uint) value)))
      (fn-cacm-item-ceiling kind)))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-cac-fieldp fn-cac-u64p fn-cp-idp fn-cacm-item-ceiling
 fn-cfg-item-encode fn-cbor-encode fn-cbor-encode-bounded
 fn-cbor-valuep-bounded fn-cbor-encode-uint-wide fn-cbor-encode-argument
 fn-record-at-most-is-length-bound fn-cbor-u16-bytes fn-cbor-u32-bytes)
 (fn-cbor-u64-bytes fn-cbor-octet-listp fn-cbor-at-mostp floor mod
 fn-cbor-encode-uint-wide-is-narrow))))))

(local (defthm fn-cacm-items-valid
 (implies (and (subsetp-equal kinds '(:flag :u64 :id :bytes32))
               (fn-cac-fields-validp values kinds))
          (fn-cfg-item-listp (fn-cacm-items values kinds)))
 :hints (("Goal" :induct (fn-cacm-items values kinds)
 :in-theory (e/d (fn-cacm-items fn-cac-fields-validp fn-cfg-item-listp fn-cp-nth fn-cac-fieldp fn-cac-u64p fn-cp-idp
 fn-cfg-itemp fn-cfg-uitemp fn-cfg-titemp fn-record-uint64p fn-record-at-most-is-length-bound)
 (fn-cbor-octet-listp fn-cbor-at-mostp))))))
(local (defthm fn-cacm-items-length
 (equal (len (fn-cacm-items values kinds)) (len kinds))
 :hints (("Goal" :induct (fn-cacm-items values kinds)
 :in-theory (enable fn-cacm-items)))))

(local (defthm fn-cacm-flag-item-bound
 (implies (fn-cac-fieldp value :flag)
 (<= (len (fn-cfg-item-encode (cons :uint value))) 1))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-cacm-field-item-bound (kind :flag)))
 :in-theory (disable fn-cac-fieldp fn-cfg-item-encode))))))
(local (defthm fn-cacm-u64-item-bound
 (implies (fn-cac-fieldp value :u64)
 (<= (len (fn-cfg-item-encode (cons :uint value))) 9))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-cacm-field-item-bound (kind :u64)))
 :in-theory (disable fn-cac-fieldp fn-cfg-item-encode))))))
(local (defthm fn-cacm-id-item-bound
 (implies (fn-cac-fieldp value :id)
 (<= (len (fn-cfg-item-encode (cons :bytes value))) 66))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-cacm-field-item-bound (kind :id)))
 :in-theory (disable fn-cac-fieldp fn-cfg-item-encode))))))
(local (defthm fn-cacm-bytes32-item-bound
 (implies (fn-cac-fieldp value :bytes32)
 (<= (len (fn-cfg-item-encode (cons :bytes value))) 34))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-cacm-field-item-bound (kind :bytes32)))
 :in-theory (disable fn-cac-fieldp fn-cfg-item-encode))))))
(local (defthm fn-cacm-items-octet-bound
 (implies (and (subsetp-equal kinds '(:flag :u64 :id :bytes32))
               (fn-cac-fields-validp values kinds))
  (<= (len (fn-cfg-item-octets (fn-cacm-items values kinds)))
      (fn-cacm-items-ceiling kinds)))
 :hints (("Goal" :induct (fn-cacm-items values kinds)
 :in-theory (e/d (fn-cacm-items fn-cac-fields-validp fn-cacm-items-ceiling
 fn-cfg-item-octets fn-cp-nth)
 (fn-cac-fieldp fn-cacm-item-ceiling fn-cfg-item-encode))))))

(defthm fn-cacm-encode-octets
 (fn-cbor-octet-listp (fn-cacm-encode r))
 :hints (("Goal" :in-theory (e/d (fn-cacm-encode fn-cbor-octet-listp-append
 fn-cfg-item-octets-are-octets) (fn-cfg-item-octets fn-cacm-recordp fn-cacm-items fn-cacm-values)))))
(defthm fn-cacm-encode-bound
 (<= (len (fn-cacm-encode r)) (fn-cacm-octet-ceiling))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-cacm-items-octet-bound
 (values (fn-cacm-values r)) (kinds *fn-cacm-kinds*)))
 :in-theory (e/d (fn-cacm-encode fn-cacm-octet-ceiling)
 (fn-cacm-recordp fn-cacm-values fn-cacm-items fn-cfg-item-octets fn-cac-fields-validp)))))
(local (defthm fn-cacm-payload-parse
 (implies (fn-cacm-recordp r)
 (equal (fn-cfg-parse-items 15 (fn-cfg-item-octets (fn-cacm-items (fn-cacm-values r) *fn-cacm-kinds*)))
 (fn-record-parse-ok (fn-cacm-items (fn-cacm-values r) *fn-cacm-kinds*) nil)))
 :hints (("Goal" :use ((:instance fn-cacm-config-stream-roundtrip
 (items (fn-cacm-items (fn-cacm-values r) *fn-cacm-kinds*)))
 (:instance fn-cacm-items-octet-bound (values (fn-cacm-values r)) (kinds *fn-cacm-kinds*)))
 :in-theory (disable fn-cacm-recordp fn-cacm-values fn-cacm-items
 fn-cfg-item-octets fn-cac-fields-validp fn-cfg-parse-items fn-cfg-item-listp)))))

(local (defthm fn-cacm-values-variant (equal (car (fn-cacm-values r)) 1) :hints (("Goal" :in-theory (enable fn-cacm-values)))))
(defthm fn-cacm-decode-encode
 (implies (fn-cacm-recordp r)
          (equal (fn-cacm-decode-exact (fn-cacm-encode r)) (list :ok r)))
 :hints (("Goal" :do-not-induct t
 :use (fn-cacm-encode-bound fn-cacm-encode-octets)
 :in-theory (e/d (fn-cacm-decode-exact fn-cacm-encode fn-cacm-octet-ceiling
 fn-cbor-octet-listp fn-cfg-item-octets-are-octets
 fn-record-at-most-is-length-bound fn-record-parse-ok fn-record-parse-okp
 fn-record-parse-value fn-record-parse-rest fn-cp-nth take nthcdr)
 (fn-cacm-recordp fn-cacm-values fn-cacm-items fn-cacm-read-items fn-cacm-of-values
 fn-cfg-item-octets fn-cfg-parse-items fn-cac-fields-validp fn-cacm-encode-octets
 fn-cbor-at-mostp)))))
