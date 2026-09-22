; fn: the record codec seam.
;
; Every book above the record codec calls `fn-record-encode' and
; `fn-record-decode-exact', and every proof above the codec reasons about them
; through the five constraints of the `encapsulate' below and nothing else.
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
;   fn-record-accepted-input-header          an accepted input begins with the six header octets
; Every other exported theorem in this book is derived from those five
; below the `encapsulate'.
;
; WHAT THEY DO NOT SAY: any particular octet of an encoding past the header,
; the error a rejected input receives, or anything about an input no record
; encodes to beyond "rejected".  A book that needs one of those is either
; reasoning about the codec (it belongs below the seam) or has found a
; property the seam should export, which is a change to this book and to
; records-canonicality together.

(in-package "ACL2")
(include-book "records-shape")

(defconst *fn-record-header-octets* '(68 102 110 45 114 0))

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

  (defthm fn-record-accepted-input-header
    (implies (fn-record-result-okp (fn-record-decode-exact octets))
             (equal (take 6 octets) *fn-record-header-octets*))
    :hints (("Goal" :use fn-record-impl-accepted-input-header))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; Derived facts.  Each is a consequence of the five constraints alone.

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

; The header, on the encoder's side: every record's encoding begins with it.
(defthm fn-record-encode-header
  (implies (fn-record-p record)
           (equal (take 6 (fn-record-encode record))
                  *fn-record-header-octets*))
  :hints (("Goal"
           :use ((:instance fn-record-accepted-input-header
                            (octets (fn-record-encode record)))
                 fn-record-encode-of-a-record-is-accepted)
           :in-theory (disable fn-record-encode-of-a-record-is-accepted
                               fn-record-round-trip)))
  :rule-classes nil)

; The dispatch a decoder for another kind uses: an input that does not begin
; with the header is not accepted.
(defthm fn-record-decode-exact-refuses-another-header
  (implies (not (equal (take 6 octets) *fn-record-header-octets*))
           (not (fn-record-result-okp (fn-record-decode-exact octets))))
  :hints (("Goal" :use fn-record-accepted-input-header))
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
