; General schema-0 record codec properties; no persistent format or disk claim.
(in-package "ACL2")
(include-book "records")
(include-book "cbor-invariants")

(defthm fn-record-chars-octets-chars
  (implies (character-listp chars)
           (equal (fn-record-octets-chars (fn-record-string-octets-aux chars))
                  chars)))

(defthm fn-record-string-round-trip
  (implies (fn-record-octet-stringp text)
           (equal (fn-record-octets-string (fn-record-string-octets text)) text)))

(defthm fn-record-ascii-implies-octets
  (implies (fn-record-ascii-octet-listp xs)
           (fn-cbor-octet-listp xs)))

(defthm fn-record-ascii-string-implies-octet-string
  (implies (fn-record-ascii-stringp text)
           (fn-record-octet-stringp text)))

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

(defthm fn-record-cbor-byte-encoding-bound
  (<= (len (fn-cbor-encode (cons :bytes xs))) (+ 3 (len xs)))
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

(defthm fn-record-read-uint-encoded
  (implies (and (fn-record-uint32p n)
                (fn-cbor-octet-listp rest)
                (<= (+ (len (fn-cbor-encode (cons :uint n))) (len rest))
                    *fn-cbor-max-input*))
           (equal (fn-record-read-uint
                   (append (fn-cbor-encode (cons :uint n)) rest))
                  (fn-record-parse-ok n rest)))
  :hints (("Goal" :in-theory (disable fn-cbor-decode fn-cbor-encode))))

(defthm fn-record-read-bytes-encoded
  (implies (and (fn-cbor-octet-listp xs)
                (<= (len xs) *fn-cbor-max-bytes*)
                (fn-cbor-octet-listp rest)
                (<= (+ (len (fn-cbor-encode (cons :bytes xs))) (len rest))
                    *fn-cbor-max-input*))
           (equal (fn-record-read-bytes
                   (append (fn-cbor-encode (cons :bytes xs)) rest))
                  (fn-record-parse-ok xs rest)))
  :hints (("Goal" :in-theory (disable fn-cbor-decode fn-cbor-encode))))

(defthm fn-record-encoded-groups-are-octets
  (fn-cbor-octet-listp (fn-record-encode-groups groups))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-record-group-encoding-bound
  (implies (fn-record-group-listp groups)
           (<= (len (fn-record-encode-groups groups)) (* 131 (len groups))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-record-encode-groups groups)
           :in-theory (disable fn-cbor-encode))))

(defthm fn-record-groups-prefix-round-trip
  (implies (and (fn-record-groupsp groups)
                (fn-cbor-octet-listp rest)
                (<= (+ (len (fn-record-encode-groups groups)) (len rest))
                    *fn-cbor-max-input*))
           (equal (fn-record-parse-groups
                   (len groups) (append (fn-record-encode-groups groups) rest))
                  (fn-record-parse-ok groups rest)))
  :hints (("Goal" :induct (fn-record-encode-groups groups)
           :in-theory (disable fn-cbor-encode fn-record-read-bytes
                               fn-record-octets-string fn-record-string-octets
                               fn-record-string-octets-aux floor mod))))

(defthm fn-record-reconstruct
  (implies (and (true-listp record) (equal (len record) 10))
           (equal (fn-record-make
                   (fn-record-sequence record) (fn-record-txid record)
                   (fn-record-generation record) (fn-record-msgid record)
                   (fn-record-payload record) (fn-record-groups record)
                   (fn-record-obligation-id record) (fn-record-content-subject record)
                   (fn-record-release-evidence record) (fn-record-charge record))
                  record)))

(defthm fn-record-read-magic-prefix
  (implies (and (fn-cbor-octet-listp rest)
                (<= (+ 5 (len rest)) *fn-cbor-max-input*))
           (equal (fn-record-read-bytes (list* 68 102 110 45 114 rest))
                  (fn-record-parse-ok *fn-record-magic* rest)))
  :hints (("Goal"
           :use ((:instance fn-record-read-bytes-encoded
                  (xs *fn-record-magic*)))
           :in-theory (disable fn-record-read-bytes))))

(defthm fn-record-read-version-prefix
  (implies (and (fn-cbor-octet-listp rest)
                (<= (+ 1 (len rest)) *fn-cbor-max-input*))
           (equal (fn-record-read-uint (cons 0 rest))
                  (fn-record-parse-ok 0 rest)))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-encoded (n 0)))
           :in-theory (disable fn-record-read-uint))))

(defthm fn-record-read-last-uint
  (implies (fn-record-uint32p n)
           (equal (fn-record-read-uint (fn-cbor-encode (cons :uint n)))
                  (fn-record-parse-ok n nil)))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-encoded (rest nil)))
           :in-theory (disable fn-record-read-uint fn-cbor-encode))))

(defthm fn-record-round-trip
  (implies (fn-record-p record)
           (equal (fn-record-decode-exact (fn-record-encode record))
                  (list :ok record)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-cbor-encode fn-cbor-decode
                               fn-record-read-uint fn-record-read-bytes
                               fn-record-parse-groups fn-record-encode-groups
                               fn-record-octets-string fn-record-string-octets
                               fn-record-string-octets-aux
                               fn-record-make fn-record-sequence fn-record-txid
                               fn-record-generation fn-record-msgid fn-record-payload
                               fn-record-groups fn-record-obligation-id
                               fn-record-content-subject fn-record-release-evidence
                               fn-record-charge floor mod))))
