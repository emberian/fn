; fn: the record recognizer over its strings, and the codec's encoder over it.
;
; fn-record-p (books/records-shape.lisp, fn-defrecord) tests a record's four
; text fields through the octet-list domain: fn-record-octet-stringp and
; fn-record-ascii-stringp convert the string to its list of char-codes
; (fn-record-string-octets: a coerce and one cons per character) and walk
; the list, and fn-record-msgidp and fn-record-metadata-bytes-p convert it a
; second time for the length bound.  fn-rcon-record-p reads the strings in
; place: an ACL2 character has a code in 0..255, so the octet-domain test is
; stringp; the length bound is `length'; the ASCII test walks the string by
; index with `char'.  fn-rcon-record-p-is-record-p: the two recognizers are
; the same function, on every input, with no hypothesis.
;
; The codec behind the seam (books/records-seam.lisp constrains
; fn-record-encode; books/records-attach.lisp attaches the implementation)
; tested its argument with fn-record-p before encoding.  fn-rcon-record-encode-impl
; is fn-record-encode-impl (books/records.lisp) with that test replaced,
; every byte-string item through the same bounded item encoder
; (fn-record-item-encode, at the record width *fn-record-max-octets*);
; fn-rcon-record-encode-impl-is-record-encode-impl equates them on every
; input, with no hypothesis, and books/records-attach-concrete.lisp attaches
; the twin in the host images, so every ground fn-record-encode the host
; evaluates (the staged record at
; write, host/owner-host.lisp fn-owner-pending-octets through
; fn-rcon-store-event-encode; the consumer poll, fn-owner-consumer-local-poll)
; recognises the record without the octet lists.  The encoded record is
; still an octet list: that is the codec's output, the next boundary.
;
; This book holds only what the codec's attachment needs (records and
; records-shape), so the attachment book does not include the store; the store
; twins are in books/records-concrete.lisp, which includes this book.

(in-package "ACL2")
(include-book "records")

; -----------------------------------------------------------------------------
; The string domain, read in place.

; Every character of TEXT at index I or beyond has a code at most 127.
(defun fn-rcon-ascii-from (text i)
  (declare (xargs :guard (and (stringp text) (natp i) (<= i (length text)))
                  :measure (nfix (- (length text) (nfix i)))))
  (if (and (stringp text) (natp i) (< i (length text)))
      (and (<= (char-code (char text i)) 127)
           (fn-rcon-ascii-from text (1+ i)))
    t))

(defun fn-rcon-msgidp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (< 0 (length text))
       (<= (length text) *fn-record-max-msgid*)
       (fn-rcon-ascii-from text 0)))

(defun fn-rcon-metadata-bytes-p (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (< 0 (length text))
       (<= (length text) *fn-record-max-metadata*)))

; fn-record-p's conjuncts in its order, with the three string tests
; replaced.  The payload and the group names are tested as before.
(defun fn-rcon-record-p (x)
  (declare (xargs :guard t))
  (and (fn-record-shapep x)
       (fn-record-uint64p (fn-record-sequence x))
       (fn-record-uint64p (fn-record-txid x))
       (fn-record-uint64p (fn-record-generation x))
       (fn-rcon-msgidp (fn-record-msgid x))
       (fn-record-payloadp (fn-record-payload x))
       (fn-record-groups-validp (fn-record-groups x))
       (fn-rcon-metadata-bytes-p (fn-record-obligation-id x))
       (fn-rcon-metadata-bytes-p (fn-record-content-subject x))
       (fn-rcon-metadata-bytes-p (fn-record-release-evidence x))
       (fn-record-uint64p (fn-record-charge x))
       (fn-record-stampp (fn-record-stamp x))))

; -----------------------------------------------------------------------------
; The correspondence, field by field.

(local (defthm fn-rcon-string-octets-aux-is-octets
  (fn-cbor-octet-listp (fn-record-string-octets-aux chars))))

(local (defthm fn-rcon-string-octets-aux-len
  (equal (len (fn-record-string-octets-aux chars)) (len chars))))

(local (defthm fn-rcon-string-octets-aux-consp
  (equal (consp (fn-record-string-octets-aux chars)) (consp chars))))

(local (defthm fn-rcon-positive-len-is-consp
  (equal (< 0 (len x)) (consp x))))

; KEYSTONE (the octet domain).  A string's characters are octets.
(defthm fn-rcon-octet-stringp-is-stringp
  (equal (fn-record-octet-stringp text) (stringp text))
  :hints (("Goal" :in-theory (enable fn-record-octet-stringp))))

(defthm fn-rcon-metadata-bytes-p-is-metadata-bytes-p
  (equal (fn-rcon-metadata-bytes-p text) (fn-record-metadata-bytes-p text))
  :hints (("Goal" :in-theory (enable fn-record-metadata-bytes-p
                                     fn-record-nonempty-at-mostp))))

(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-rcon-shift-less
  (implies (and (integerp i) (integerp n))
           (equal (< (+ -1 i) n) (< i (+ 1 n))))
  :hints (("Goal" :cases ((< i (+ 1 n)))))))

(local (defthm fn-rcon-consp-of-nthcdr
  (implies (natp i)
           (equal (consp (nthcdr i l)) (< i (len l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))

(local (defthm fn-rcon-nthcdr-past-true-list
  (implies (and (true-listp l) (natp i) (<= (len l) i))
           (equal (nthcdr i l) nil))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))

(local (defthm fn-rcon-car-of-nthcdr
  (equal (car (nthcdr i l)) (nth i l))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr nth)))))

(local (defthm fn-rcon-cdr-of-nthcdr
  (equal (cdr (nthcdr i l)) (nthcdr i (cdr l)))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))

(local (defthm fn-rcon-nthcdr-of-1+
  (implies (natp i)
           (equal (nthcdr (+ 1 i) l) (nthcdr i (cdr l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))

(local (defthm fn-rcon-character-listp-true-listp
  (implies (character-listp l) (true-listp l))))

(local (defthm fn-rcon-coerce-true-listp
  (true-listp (coerce text 'list))))

; The index walk is the list walk from index I: char I is nth I of the
; character list, and the rest of the walk is the rest of the list.
(local (defthm fn-rcon-ascii-from-is-ascii-octet-listp-of-nthcdr
  (implies (and (stringp text) (natp i))
           (equal (fn-rcon-ascii-from text i)
                  (fn-record-ascii-octet-listp
                   (fn-record-string-octets-aux (nthcdr i (coerce text 'list))))))
  :hints (("Goal" :induct (fn-rcon-ascii-from text i)
           :in-theory (e/d (fn-rcon-ascii-from) (nth fn-rcon-shift-less))
           :expand ((fn-record-string-octets-aux (nthcdr i (coerce text 'list)))
                    (fn-record-ascii-octet-listp
                     (fn-record-string-octets-aux
                      (nthcdr i (coerce text 'list)))))))))

(defthm fn-rcon-msgidp-is-msgidp
  (equal (fn-rcon-msgidp text) (fn-record-msgidp text))
  :hints (("Goal" :in-theory (enable fn-record-msgidp fn-record-ascii-stringp
                                     fn-record-nonempty-at-mostp))))

; KEYSTONE (the recognizer).  The concrete recognizer is fn-record-p, on
; every input.  Both are guard-verified with guard t, so the host's compiled
; code computes this one.
(defthm fn-rcon-record-p-is-record-p
  (equal (fn-rcon-record-p x) (fn-record-p x))
  :hints (("Goal" :in-theory (e/d (fn-record-p) (fn-record-shapep)))))

(in-theory (disable fn-rcon-ascii-from fn-rcon-msgidp fn-rcon-metadata-bytes-p
                    fn-rcon-record-p))

; -----------------------------------------------------------------------------
; The encoder behind the seam, with the concrete recognizer.

; As in books/records.lisp: admitting a fourteen-way nested APPEND with
; TRUE-LISTP-APPEND's type rule beside BINARY-APPEND's costs seconds of type
; reasoning for "no constraints"; withdrawn for the admission only.
(local (in-theory (disable (:type-prescription true-listp-append))))
(defun fn-rcon-record-encode-impl (record)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-rcon-record-p record))
      nil
    (let ((octets
           (append
            (fn-record-item-encode (cons :bytes *fn-record-magic*))
            (fn-record-uint-encode (fn-record-schema-octet record))
            (fn-record-uint-encode (fn-record-sequence record))
            (fn-record-uint-encode (fn-record-txid record))
            (fn-record-uint-encode (fn-record-generation record))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-msgid record))))
            (fn-record-item-encode (cons :bytes (fn-record-payload record)))
            (fn-record-uint-encode (len (fn-record-groups record)))
            (fn-record-encode-groups (fn-record-groups record))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-obligation-id record))))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-content-subject record))))
            (fn-record-item-encode (cons :bytes
                                  (fn-record-string-octets
                                   (fn-record-release-evidence record))))
            (fn-record-uint-encode (fn-record-charge record))
            (if (equal (fn-record-stamp record) :legacy)
                nil
              (fn-record-uint-encode (fn-record-stamp record))))))
      (if (fn-cbor-at-mostp octets *fn-record-max-octets*) octets nil))))
(local (in-theory (enable (:type-prescription true-listp-append))))

; KEYSTONE (the encoder).  The twin is the implementation, on every input.
(defthm fn-rcon-record-encode-impl-is-record-encode-impl
  (equal (fn-rcon-record-encode-impl record) (fn-record-encode-impl record))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-record-encode-impl fn-record-encode-impl
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))

; Its guard obligations are the implementation's once the recognizer is
; rewritten to fn-record-p.
(verify-guards fn-rcon-record-encode-impl
  :hints (("Goal" :use ((:guard-theorem fn-record-encode-impl))
           :in-theory (disable fn-record-encode-impl))))

(in-theory (disable fn-rcon-record-encode-impl))
