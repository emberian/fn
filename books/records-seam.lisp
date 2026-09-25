; fn: the record codec seam.
;
; Every book above the record codec calls `fn-record-encode' and
; `fn-record-decode-exact', and every proof above the codec reasons about them
; through the six constraints of the `encapsulate' below and nothing else.
; They are constrained functions: no book can open them, so a goal that only
; dispatches on a record kind cannot carry the codec, which is the growth
; that stopped proofs returning on 2026-09-21 (review 2026-09-22, F3; plan
; 2026-09-22 §4.1, step T1).
;
; The local witnesses are the real definitions, `fn-record-encode-impl' and
; `fn-record-decode-exact-impl' (books/records.lisp), so the constraints are
; satisfiable by the implementation itself, proved once in
; books/records-canonicality.lisp.  books/records-attach.lisp attaches the
; same two definitions with `defattach', which re-proves every constraint of
; them and adds no axiom; the image and the test books that evaluate ground
; vectors include it, so evaluation is what it was.  A book above the seam
; includes this book and never books/records.lisp.
;
; WHAT THE CONSTRAINTS SAY, and nothing more:
;   fn-record-encode-domain                  a non-record encodes to nil
;   fn-record-round-trip                     decode (encode r) = (:ok r) for a record r
;   fn-record-accepted-input-is-canonical    an accepted input is the encoding of what it decodes to
;   fn-record-accepted-input-bounds          an accepted input is a nonempty octet list of at most
;                                            *fn-record-max-octets* octets
;   fn-record-accepted-input-magic           an accepted input begins with the five magic octets
;                                            (*fn-record-magic-octets*, records-shape)
;   fn-record-accepted-schema-is-the-stamp-kind
;                                            an accepted input's sixth octet is the schema octet
;                                            its record needs (`fn-record-schema-octet',
;                                            records-shape: 0 at schema 0)
;   fn-record-encode-length-bound            a record encodes to at most
;                                            `fn-record-encoded-octets-ceiling' of its payload
;                                            length and group count (records-shape)
; Every other exported theorem in this book is derived from those seven
; below the `encapsulate'.  The header is two constraints, not one six-octet
; constraint, so that the acceptance stamp (specs/acceptance-stamp.md §2.1)
; widens the grammar behind the seam -- schema 1, whose version octet is 1
; -- by changing `fn-record-schema-octet' and the implementation, and no
; statement above the seam moves.
;
; WHAT THEY DO NOT SAY: any particular octet of an encoding past the header,
; the error a rejected input receives, or anything about an input no record
; encodes to beyond "rejected".  A book that needs one of those is either
; reasoning about the codec (it belongs below the seam) or has found a
; property the seam should export, which is a change to this book and to
; records-canonicality together.

(in-package "ACL2")
(include-book "records-shape")

(encapsulate
  (((fn-record-encode *) => * :formals (record) :guard t)
   ((fn-record-decode-exact *) => * :formals (octets) :guard t))

  (local (include-book "records-canonicality"))

  (local (defun fn-record-encode (record)
           (declare (xargs :guard t))
           (fn-record-encode-impl record)))

  (local (defun fn-record-decode-exact (octets)
           (declare (xargs :guard t))
           (fn-record-decode-exact-impl octets)))

  (defthm fn-record-encode-domain
    (implies (not (fn-record-p record))
             (equal (fn-record-encode record) nil))
    :hints (("Goal" :use fn-record-impl-encode-domain)))

  (defthm fn-record-round-trip
    (implies (fn-record-p record)
             (equal (fn-record-decode-exact (fn-record-encode record))
                    (list :ok record)))
    :hints (("Goal" :use fn-record-impl-round-trip
             :in-theory (disable fn-record-impl-round-trip))))

  (defthm fn-record-accepted-input-is-canonical
    (implies (fn-record-result-okp (fn-record-decode-exact octets))
             (equal (fn-record-encode
                     (fn-record-result-record (fn-record-decode-exact octets)))
                    octets))
    :hints (("Goal" :use fn-record-impl-accepted-input-is-canonical
             :in-theory (disable fn-record-impl-accepted-input-is-canonical))))

  (defthm fn-record-accepted-input-bounds
    (implies (fn-record-result-okp (fn-record-decode-exact octets))
             (and (fn-cbor-octet-listp octets)
                  (consp octets)
                  (<= (len octets) *fn-record-max-octets*)))
    :hints (("Goal" :use fn-record-impl-accepted-input-bounds))
    :rule-classes nil)

(defthm fn-record-accepted-input-magic
    (implies (fn-record-result-okp (fn-record-decode-exact octets))
             (equal (take 5 octets) *fn-record-magic-octets*))
    :hints (("Goal" :use fn-record-impl-accepted-input-magic))
    :rule-classes nil)

  (defthm fn-record-encode-length-bound
    (<= (len (fn-record-encode record))
        (fn-record-encoded-octets-ceiling
         (len (fn-record-payload record))
         (len (fn-record-groups record))))
    :hints (("Goal" :use fn-record-impl-encode-length-bound))
    :rule-classes :linear)

  (defthm fn-record-accepted-schema-is-the-stamp-kind
    (implies (fn-record-result-okp (fn-record-decode-exact octets))
             (equal (nth 5 octets)
                    (fn-record-schema-octet
                     (fn-record-result-record
                      (fn-record-decode-exact octets)))))
    :hints (("Goal" :use fn-record-impl-accepted-schema-is-the-stamp-kind))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; Derived facts.  Each is a consequence of the six constraints alone.

; The result shapes of the round trip, in the accessor vocabulary a caller
; uses (`fn-record-result-okp', `fn-record-result-record').
(defthm fn-record-round-trip-succeeds
  (implies (fn-record-p record)
           (and (fn-record-result-okp
                 (fn-record-decode-exact (fn-record-encode record)))
                (equal (fn-record-result-record
                        (fn-record-decode-exact (fn-record-encode record)))
                       record)))
  :hints (("Goal" :in-theory (enable fn-record-result-okp
                                     fn-record-result-record))))

; Kind dispatch on a decoded record: what an accepted input decodes to is a
; record.  Canonicality makes the input its encoding; the encoder refuses a
; non-record with nil; an accepted input is nonempty.
(defthm fn-record-decode-exact-yields-a-record
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (fn-record-p
            (fn-record-result-record (fn-record-decode-exact octets))))
  :hints (("Goal"
           :use (fn-record-accepted-input-is-canonical
                 fn-record-accepted-input-bounds
                 (:instance fn-record-encode-domain
                            (record (fn-record-result-record
                                     (fn-record-decode-exact octets)))))
           :in-theory (disable fn-record-accepted-input-is-canonical
                               fn-record-encode-domain))))

(defthm fn-record-accepted-input-is-an-octet-list
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (and (fn-cbor-octet-listp octets)
                (true-listp octets)
                (consp octets)))
  :hints (("Goal" :use fn-record-accepted-input-bounds))
  :rule-classes :forward-chaining)

(defthm fn-record-accepted-input-length
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (<= (len octets) *fn-record-max-octets*))
  :hints (("Goal" :use fn-record-accepted-input-bounds))
  :rule-classes :linear)

; The encoder's output, from the round trip: a record's encoding is accepted,
; so it has every property of an accepted input.
(defthm fn-record-encode-of-a-record-is-accepted
  (implies (fn-record-p record)
           (fn-record-result-okp (fn-record-decode-exact
                                  (fn-record-encode record))))
  :hints (("Goal" :use fn-record-round-trip-succeeds
           :in-theory (disable fn-record-round-trip-succeeds
                               fn-record-round-trip))))

(defthm fn-record-encode-shape
  (implies (fn-record-p record)
           (and (fn-cbor-octet-listp (fn-record-encode record))
                (true-listp (fn-record-encode record))
                (consp (fn-record-encode record))))
  :hints (("Goal"
           :use ((:instance fn-record-accepted-input-bounds
                            (octets (fn-record-encode record)))
                 fn-record-encode-of-a-record-is-accepted)
           :in-theory (disable fn-record-encode-of-a-record-is-accepted
                               fn-record-round-trip))))

(defthm fn-record-encode-length
  (implies (fn-record-p record)
           (<= (len (fn-record-encode record)) *fn-record-max-octets*))
  :hints (("Goal"
           :use ((:instance fn-record-accepted-input-bounds
                            (octets (fn-record-encode record)))
                 fn-record-encode-of-a-record-is-accepted)
           :in-theory (disable fn-record-encode-of-a-record-is-accepted
                               fn-record-round-trip)))
  :rule-classes :linear)

; Whatever the argument, the encoding is an octet list (nil for a
; non-record), which is the guard fact a caller that appends it needs.
(defthm fn-record-encode-is-an-octet-list
  (and (fn-cbor-octet-listp (fn-record-encode record))
       (true-listp (fn-record-encode record)))
  :hints (("Goal" :cases ((fn-record-p record)))))

; The magic, on the encoder's side: every record's encoding begins with it.
(defthm fn-record-encode-magic
  (implies (fn-record-p record)
           (equal (take 5 (fn-record-encode record))
                  *fn-record-magic-octets*))
  :hints (("Goal"
           :use ((:instance fn-record-accepted-input-magic
                            (octets (fn-record-encode record)))
                 fn-record-encode-of-a-record-is-accepted)
           :in-theory (disable fn-record-encode-of-a-record-is-accepted
                               fn-record-round-trip)))
  :rule-classes nil)

; The schema octet, on the encoder's side: a record's encoding carries the
; schema octet the record needs.
(defthm fn-record-encode-schema-octet
  (implies (fn-record-p record)
           (equal (nth 5 (fn-record-encode record))
                  (fn-record-schema-octet record)))
  :hints (("Goal"
           :use ((:instance fn-record-accepted-schema-is-the-stamp-kind
                            (octets (fn-record-encode record)))
                 fn-record-encode-of-a-record-is-accepted
                 fn-record-round-trip-succeeds)
           :in-theory (disable fn-record-encode-of-a-record-is-accepted
                               fn-record-round-trip-succeeds
                               fn-record-round-trip)))
  :rule-classes nil)

; The dispatch a decoder for another kind uses: an input that does not begin
; with the magic is not accepted.  Every Store event kind other than the
; record (`fn-e', books/store-events.lisp) differs from `fn-r' in the fifth
; octet.
(defthm fn-record-decode-exact-refuses-another-magic
  (implies (not (equal (take 5 octets) *fn-record-magic-octets*))
           (not (fn-record-result-okp (fn-record-decode-exact octets))))
  :hints (("Goal" :use fn-record-accepted-input-magic))
  :rule-classes nil)

; Two records with the same encoding are the same record.
(defthm fn-record-encode-is-injective
  (implies (and (fn-record-p a) (fn-record-p b)
                (equal (fn-record-encode a) (fn-record-encode b)))
           (equal a b))
  :hints (("Goal"
           :use ((:instance fn-record-round-trip (record a))
                 (:instance fn-record-round-trip (record b)))
           :in-theory (disable fn-record-round-trip)))
  :rule-classes nil)
