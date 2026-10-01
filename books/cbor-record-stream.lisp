; Unchanged CBOR stream support, without record identity ancestry.
(in-package "ACL2")
(include-book "cbor-record-scalar")
(include-book "cbor-invariants")
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

(defthm fn-record-at-most-is-length-bound
  (implies (natp bound)
           (equal (fn-cbor-at-mostp xs bound)
                  (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound))))

(defthm fn-record-length-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-record-cbor-encode-octets
  (fn-cbor-octet-listp (fn-cbor-encode value))
  :hints (("Goal" :in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes))))

(defthm fn-record-cbor-uint-encoding-bound
  (<= (len (fn-cbor-encode (cons :uint n))) 5)
  :rule-classes :linear)

(defthm fn-record-take-prefix
  (implies (true-listp xs)
           (equal (take (len xs) (append xs rest)) xs))
  :hints (("Goal" :induct (len xs))))

(defthm fn-record-nthcdr-prefix
  (implies (true-listp xs)
           (equal (nthcdr (len xs) (append xs rest)) rest))
  :hints (("Goal" :induct (len xs))))

(defthm fn-record-u32-prefix-fields
  (and (consp (append (fn-cbor-u32-bytes n) xs))
       (consp (cdr (append (fn-cbor-u32-bytes n) xs)))
       (consp (cddr (append (fn-cbor-u32-bytes n) xs)))
       (consp (cdddr (append (fn-cbor-u32-bytes n) xs)))
       (equal (cddddr (append (fn-cbor-u32-bytes n) xs)) xs)
       (equal (fn-cbor-u32-from (append (fn-cbor-u32-bytes n) xs))
              (fn-cbor-u32-from (fn-cbor-u32-bytes n))))
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm fn-record-cbor-stream-uint-round-trip
  (implies (and (fn-record-uint32p n)
                (fn-cbor-octet-listp rest)
                (<= (len (append (fn-cbor-encode (cons :uint n)) rest))
                    *fn-cbor-max-input*))
           (equal (fn-cbor-decode (append (fn-cbor-encode (cons :uint n)) rest))
                  (fn-cbor-ok (cons :uint n) rest)))
  :hints (("Goal" :cases ((< n 24) (< n 256) (< n 65536))
           :in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes
                               fn-cbor-u16-from fn-cbor-u32-from
                               fn-cbor-at-mostp))))

(defthm fn-record-append-associative
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-record-cbor-stream-bytes-round-trip
  (implies (and (fn-cbor-octet-listp xs)
                (<= (len xs) *fn-cbor-max-bytes*)
                (fn-cbor-octet-listp rest)
                (<= (len (append (fn-cbor-encode (cons :bytes xs)) rest))
                    *fn-cbor-max-input*))
           (equal (fn-cbor-decode (append (fn-cbor-encode (cons :bytes xs)) rest))
                  (fn-cbor-ok (cons :bytes xs) rest)))
  :hints (("Goal" :cases ((< (len xs) 24) (< (len xs) 256))
           :use (fn-record-take-prefix fn-record-nthcdr-prefix)
           :in-theory (disable fn-cbor-u16-bytes fn-cbor-u16-from
                               fn-cbor-at-mostp take nthcdr))))
