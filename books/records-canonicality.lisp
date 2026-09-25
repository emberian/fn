; Reverse canonicality for the experimental local schema-0 transaction record.
;
; This lifts the primitive CBOR accepted-input canonicality theorem through the
; record parser.  It concerns only a successful exact parse of schema 0; it
; does not make a persistence, guard-verification, or physical-storage claim.
(in-package "ACL2")
(include-book "records-invariants")

; The reverse direction is about the codec's definitions, so they are opened
; locally here.  Records and both results stay opaque: the record lemmas from
; `records' close the goals about them.
(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-cbor-invariants-vocabulary
                          fn-record-codec-vocabulary
                          fn-record-guard-vocabulary
                          fn-record-record-vocabulary
                          fn-record-invariants-vocabulary)))

;; The item decoder reconstructs exactly what it consumed (the bounded
;; analogue of cbor-invariants' `fn-cbor-decode-reencode-prefix').
(defthm fn-record-cbor-bytes-bounded-reencode-prefix
  (implies (and (fn-cbor-octet-listp tail)
                (natp additional) (< additional 32)
                (natp max-bytes)
                (fn-cbor-result-okp
                 (fn-cbor-decode-bytes-bounded additional tail max-bytes)))
           (equal (append (fn-cbor-encode-bounded
                           (fn-cbor-result-value
                            (fn-cbor-decode-bytes-bounded additional tail
                                                          max-bytes))
                           max-bytes)
                          (fn-cbor-result-rest
                           (fn-cbor-decode-bytes-bounded additional tail
                                                         max-bytes)))
                  (cons (+ 64 additional) tail)))
  :hints (("Goal" :in-theory (disable fn-cbor-u16-bytes fn-cbor-u16-from
                                      fn-cbor-u32-bytes fn-cbor-u32-from
                                      take nthcdr))))

(defthm fn-record-cbor-encode-bounded-of-uint-value
  (implies (and (consp value) (equal (car value) :uint))
           (equal (fn-cbor-encode-bounded value max-bytes)
                  (fn-cbor-encode value)))
  :hints (("Goal" :in-theory (enable fn-cbor-encode-bounded fn-cbor-encode
                                     fn-cbor-valuep fn-cbor-valuep-bounded))))

(defthm fn-record-item-decode-reencode-prefix
  (implies (fn-cbor-result-okp (fn-record-item-decode octets))
           (equal (append (fn-record-item-encode
                           (fn-cbor-result-value
                            (fn-record-item-decode octets)))
                          (fn-cbor-result-rest
                           (fn-record-item-decode octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-cbor-unsigned-reencode-prefix
                  (additional (car octets)) (tail (cdr octets)))
                 (:instance fn-record-cbor-decode-unsigned-success-domain
                  (additional (car octets)) (tail (cdr octets)))
                 (:instance fn-record-cbor-bytes-bounded-reencode-prefix
                  (additional (- (car octets) 64)) (tail (cdr octets))
                  (max-bytes *fn-record-max-octets*)))
           :in-theory (e/d (fn-record-item-decode fn-record-item-encode
                            fn-cbor-decode-prechecked)
                           (fn-cbor-unsigned-reencode-prefix
                            fn-record-cbor-bytes-bounded-reencode-prefix
                            fn-cbor-decode-unsigned
                            fn-cbor-decode-bytes-bounded
                            fn-cbor-encode-bounded fn-cbor-encode)))))

(local (defthm fn-record-cons-uint-of-cdr
  (implies (and (consp v) (equal (car v) :uint))
           (equal (cons :uint (cdr v)) v))))

(local (defthm fn-record-cons-bytes-of-cdr
  (implies (and (consp v) (equal (car v) :bytes))
           (equal (cons :bytes (cdr v)) v))))

(defthm fn-record-read-uint-reencode-prefix
  (implies (fn-record-parse-okp (fn-record-read-uint octets))
           (equal (append (fn-cbor-encode
                           (cons :uint
                                 (fn-record-parse-value
                                  (fn-record-read-uint octets))))
                          (fn-record-parse-rest
                           (fn-record-read-uint octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-record-item-decode-reencode-prefix)
                 (:instance fn-record-item-encode-of-uint
                  (n (cdr (fn-cbor-result-value
                           (fn-record-item-decode octets))))))
           :in-theory (e/d (fn-record-read-uint
                            fn-record-parse-okp
                            fn-record-parse-value
                            fn-record-parse-rest)
                           (fn-record-item-decode-reencode-prefix
                            fn-record-item-encode-of-uint
                            fn-record-item-decode fn-record-item-encode
                            fn-cbor-encode)))))

(defthm fn-record-read-bytes-reencode-prefix
  (implies (fn-record-parse-okp (fn-record-read-bytes octets))
           (equal (append (fn-record-item-encode
                           (cons :bytes
                                 (fn-record-parse-value
                                  (fn-record-read-bytes octets))))
                          (fn-record-parse-rest
                           (fn-record-read-bytes octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-record-item-decode-reencode-prefix))
           :in-theory (e/d (fn-record-read-bytes
                            fn-record-parse-okp
                            fn-record-parse-value
                            fn-record-parse-rest)
                           (fn-record-item-decode-reencode-prefix
                            fn-record-item-decode fn-record-item-encode)))))

(defthm fn-record-octets-chars-are-characters
  (implies (fn-cbor-octet-listp octets)
           (character-listp (fn-record-octets-chars octets)))
  :hints (("Goal"
           :induct (fn-record-octets-chars octets)
           :in-theory (enable fn-cbor-octet-listp
                              fn-record-octets-chars))))

(defthm fn-record-string-octets-aux-of-octets-chars
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-record-string-octets-aux
                   (fn-record-octets-chars octets))
                  octets))
  :hints (("Goal"
           :induct (fn-record-octets-chars octets)
           :in-theory (enable fn-cbor-octet-listp
                              fn-cbor-octetp
                              fn-record-octets-chars
                              fn-record-string-octets-aux))))

(defthm fn-record-string-octets-of-octets-string
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-record-string-octets (fn-record-octets-string octets))
                  octets))
  :hints (("Goal"
           :use ((:instance coerce-inverse-1
                  (x (fn-record-octets-chars octets)))
                 (:instance fn-record-octets-chars-are-characters
                  (octets octets))
                 (:instance fn-record-string-octets-aux-of-octets-chars
                  (octets octets)))
           :in-theory (enable fn-record-octets-string
                              fn-record-string-octets))))

(defthm fn-record-read-bytes-value-are-octets
  (implies (fn-record-parse-okp (fn-record-read-bytes octets))
           (fn-cbor-octet-listp
            (fn-record-parse-value (fn-record-read-bytes octets))))
  :hints (("Goal"
           :use fn-record-item-decode-success-domain
           :in-theory (e/d (fn-record-read-bytes
                            fn-record-parse-okp
                            fn-record-parse-value
                            fn-cbor-valuep-bounded)
                           (fn-record-item-decode-success-domain
                            fn-record-item-decode)))))

(defthm fn-record-read-uint-value-is-natural
  (implies (fn-record-parse-okp (fn-record-read-uint octets))
           (natp (fn-record-parse-value (fn-record-read-uint octets))))
  :hints (("Goal"
           :use fn-record-item-decode-success-domain
           :in-theory (e/d (fn-record-read-uint
                            fn-record-parse-okp
                            fn-record-parse-value
                            fn-cbor-valuep-bounded)
                           (fn-record-item-decode-success-domain
                            fn-record-item-decode)))))

; The final charge has no following field.  State that exact-rest consequence
; directly so the tail composition does not have to turn a propositional NIL
; fact into an append rewrite while all parser accessors are disabled.
(defthm fn-record-read-uint-reencode-exact
  (implies (and (fn-record-parse-okp (fn-record-read-uint octets))
                (null (fn-record-parse-rest
                       (fn-record-read-uint octets))))
           (equal (fn-cbor-encode
                   (cons :uint
                         (fn-record-parse-value
                          (fn-record-read-uint octets))))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-reencode-prefix))
           :in-theory (disable fn-record-read-uint
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-cbor-encode))))

; The group reader is an induction over `fn-record-read-bytes'; each step
; needs only that reader's own facts (`fn-record-read-bytes-reencode-prefix',
; `-value-are-octets' above, `fn-record-string-octets-of-octets-string') and
; the parser-result constructors, so the reader, the CBOR codec and the
; result accessors stay closed.  Opened (the book-wide codec enable), each
; step ran the whole CBOR decoder: 974 285 steps and 40 s, and 755 086 steps
; and 21 s for the length theorem below.
(defthm fn-record-parse-groups-reencode-prefix
  (implies (fn-record-parse-okp (fn-record-parse-groups count octets))
           (equal (append
                   (fn-record-encode-groups
                    (fn-record-parse-value
                     (fn-record-parse-groups count octets)))
                   (fn-record-parse-rest
                    (fn-record-parse-groups count octets)))
                  octets))
  :hints (("Goal"
           :induct (fn-record-parse-groups count octets)
           :in-theory (e/d (fn-record-parse-groups fn-record-encode-groups
                            fn-record-parse-okp-of-ok fn-record-parse-value-of-ok
                            fn-record-parse-rest-of-ok fn-record-parse-error-is-failure)
                           (fn-record-read-bytes fn-cbor-encode
                            fn-record-octets-string fn-record-string-octets
                            fn-record-group-namep fn-record-parse-okp
                            fn-record-parse-value fn-record-parse-rest
                            fn-record-parse-ok fn-record-parse-error))
           :do-not '(generalize fertilize))))

(defthm fn-record-parse-groups-value-length
  (implies (fn-record-parse-okp (fn-record-parse-groups count octets))
           (equal (len (fn-record-parse-value
                        (fn-record-parse-groups count octets)))
                  (nfix count)))
  :hints (("Goal"
           :induct (fn-record-parse-groups count octets)
           :in-theory (e/d (fn-record-parse-groups
                            fn-record-parse-okp-of-ok fn-record-parse-value-of-ok
                            fn-record-parse-rest-of-ok fn-record-parse-error-is-failure)
                           (fn-record-read-bytes fn-record-octets-string
                            fn-record-group-namep fn-record-parse-okp
                            fn-record-parse-value fn-record-parse-rest
                            fn-record-parse-ok fn-record-parse-error)))))

; Preserve parser-result abstractions during sequential composition.  Expanding
; CADR/CADDR before the typed read lemmas can match loses their useful vocabulary.
(defthm fn-record-parse-ok-is-success
  (fn-record-parse-okp (fn-record-parse-ok value rest)))

(defthm fn-record-parse-ok-has-value
  (equal (fn-record-parse-value (fn-record-parse-ok value rest)) value))

(defthm fn-record-parse-ok-has-rest
  (equal (fn-record-parse-rest (fn-record-parse-ok value rest)) rest))

; This is the non-parsing part of the lift: once each sequential field has
; reconstructed its source prefix, their append equations compose into the
; complete record encoding.  Keeping it separate prevents the tail theorem
; from unfolding the CBOR decoder while proving an append identity.
(defthm fn-record-component-prefixes-compose
  (implies
   (and (fn-record-p
         (fn-record-make sequence txid generation msgid payload groups
                         obligation-id content-subject release-evidence charge stamp))
        (equal schema (if (equal stamp :legacy) 0 1))
        (equal count (len groups))
        (equal (append (fn-cbor-encode (cons :uint count)) after-count) octets)
        (equal (append (fn-record-encode-groups groups) after-groups) after-count)
        (equal (append
                (fn-record-item-encode
                 (cons :bytes (fn-record-string-octets obligation-id)))
                after-id)
               after-groups)
        (equal (append
                (fn-record-item-encode
                 (cons :bytes (fn-record-string-octets content-subject)))
                after-subject)
               after-id)
        (equal (append
                (fn-record-item-encode
                 (cons :bytes (fn-record-string-octets release-evidence)))
                after-evidence)
               after-subject)
        (equal (append (fn-cbor-encode (cons :uint charge))
                       (if (equal stamp :legacy) nil
                         (fn-cbor-encode (cons :uint stamp))))
               after-evidence)
        (fn-cbor-at-mostp
         (append
          (fn-record-item-encode (cons :bytes *fn-record-magic*))
          (fn-cbor-encode (cons :uint schema))
          (fn-cbor-encode (cons :uint sequence))
          (fn-cbor-encode (cons :uint txid))
          (fn-cbor-encode (cons :uint generation))
          (fn-record-item-encode (cons :bytes (fn-record-string-octets msgid)))
          (fn-record-item-encode (cons :bytes payload))
          octets)
         *fn-record-max-octets*))
   (equal
    (fn-record-encode-impl
     (fn-record-make sequence txid generation msgid payload groups
                     obligation-id content-subject release-evidence charge stamp))
    (append
     (fn-record-item-encode (cons :bytes *fn-record-magic*))
     (fn-cbor-encode (cons :uint schema))
     (fn-cbor-encode (cons :uint sequence))
     (fn-cbor-encode (cons :uint txid))
     (fn-cbor-encode (cons :uint generation))
     (fn-record-item-encode (cons :bytes (fn-record-string-octets msgid)))
     (fn-record-item-encode (cons :bytes payload))
     octets)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-record-encode-impl
                 fn-record-make
                 fn-record-sequence
                 fn-record-txid
                 fn-record-generation
                 fn-record-msgid
                 fn-record-payload
                 fn-record-groups
                 fn-record-obligation-id
                 fn-record-content-subject
                 fn-record-release-evidence
                 fn-record-charge fn-record-stamp
                 fn-record-schema-octet)
                (fn-cbor-encode
                 fn-cbor-at-mostp
                 fn-record-encode-groups
                 fn-record-string-octets
                 fn-record-p
                 ; Both sides are right-nested appends of eight encodings;
                 ; with this rule on, type-set backchained through every
                 ; level's `true-listp' hypothesis (3 979 steps, 3.3 s).
                 (:type-prescription true-listp-append))))))

; A small append-only bridge for the five fields parsed before decode-tail.
; Keeping this algebra separate prevents the header proof from opening CBOR.
(defthm fn-record-five-prefixes-compose
  (implies (and (equal (append p1 after1) input)
                (equal (append p2 after2) after1)
                (equal (append p3 after3) after2)
                (equal (append p4 after4) after3)
                (equal (append p5 tail) after4))
           (equal (append p1 p2 p3 p4 p5 tail) input)))

(defthm fn-record-two-prefixes-compose
  (implies (and (equal (append p1 after1) input)
                (equal (append p2 tail) after1))
           (equal (append p1 p2 tail) input)))

; Abbreviations for the schema selected by the exact decoder's second read.
; They expand to that reader, keeping the proof statements on its real call.
(defmacro fn-record-header-schema (octets)
  `(fn-record-parse-value
    (fn-record-read-uint
     (fn-record-parse-rest (fn-record-read-bytes ,octets)))))

(defmacro fn-record-header-tail (octets)
  `(fn-record-parse-rest
    (fn-record-read-uint
     (fn-record-parse-rest (fn-record-read-bytes ,octets)))))

; The optional schema-1 stamp begins just after the charge.  This syntactic
; abbreviation keeps the primitive inverse instantiated at that exact suffix.
(defmacro fn-record-tail-after-evidence (octets)
  `(fn-record-parse-rest
    (fn-record-read-bytes
     (fn-record-parse-rest
      (fn-record-read-bytes
       (fn-record-parse-rest
        (fn-record-read-bytes
         (fn-record-parse-rest
          (fn-record-parse-groups
           (fn-record-parse-value (fn-record-read-uint ,octets))
           (fn-record-parse-rest (fn-record-read-uint ,octets)))))))))))

(defmacro fn-record-tail-after-charge (octets)
  `(fn-record-parse-rest
    (fn-record-read-uint (fn-record-tail-after-evidence ,octets))))

; Success of the sequential header decoder gives the success hypotheses needed
; by each primitive inverse.  Isolating this control-flow fact keeps ACL2 from
; opening the CBOR decoder while relieving those hypotheses later.
(defthm fn-record-decode-after-header-successes
  (implies
   (fn-record-parse-okp (fn-record-decode-after-header schema octets))
   (and
    (fn-record-parse-okp (fn-record-read-uint octets))
    (fn-record-parse-okp
     (fn-record-read-uint
      (fn-record-parse-rest (fn-record-read-uint octets))))
    (fn-record-parse-okp
     (fn-record-read-uint
      (fn-record-parse-rest
       (fn-record-read-uint
        (fn-record-parse-rest (fn-record-read-uint octets))))))
    (fn-record-parse-okp
     (fn-record-read-bytes
      (fn-record-parse-rest
       (fn-record-read-uint
        (fn-record-parse-rest
         (fn-record-read-uint
          (fn-record-parse-rest (fn-record-read-uint octets))))))))
    (fn-record-parse-okp
     (fn-record-read-bytes
      (fn-record-parse-rest
       (fn-record-read-bytes
        (fn-record-parse-rest
         (fn-record-read-uint
          (fn-record-parse-rest
           (fn-record-read-uint
            (fn-record-parse-rest (fn-record-read-uint octets))))))))))
    (fn-record-parse-okp
     (fn-record-decode-tail
      schema
      (fn-record-parse-value (fn-record-read-uint octets))
      (fn-record-parse-value
       (fn-record-read-uint
        (fn-record-parse-rest (fn-record-read-uint octets))))
      (fn-record-parse-value
       (fn-record-read-uint
        (fn-record-parse-rest
         (fn-record-read-uint
          (fn-record-parse-rest (fn-record-read-uint octets))))))
      (fn-record-octets-string
       (fn-record-parse-value
        (fn-record-read-bytes
         (fn-record-parse-rest
          (fn-record-read-uint
           (fn-record-parse-rest
            (fn-record-read-uint
             (fn-record-parse-rest (fn-record-read-uint octets)))))))))
      (fn-record-parse-value
       (fn-record-read-bytes
        (fn-record-parse-rest
         (fn-record-read-bytes
          (fn-record-parse-rest
           (fn-record-read-uint
            (fn-record-parse-rest
             (fn-record-read-uint
              (fn-record-parse-rest (fn-record-read-uint octets))))))))))
      (fn-record-parse-rest
       (fn-record-read-bytes
        (fn-record-parse-rest
         (fn-record-read-bytes
          (fn-record-parse-rest
           (fn-record-read-uint
            (fn-record-parse-rest
             (fn-record-read-uint
              (fn-record-parse-rest
               (fn-record-read-uint octets))))))))))))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-record-decode-after-header
              fn-record-parse-error-is-failure
              (:executable-counterpart not))))))

(defthm fn-record-decode-tail-reencode
  (implies (and (member-equal schema '(0 1))
            (fn-record-parse-okp
             (fn-record-decode-tail schema sequence txid generation msgid payload octets))
            (fn-cbor-at-mostp
             (append
              (fn-record-item-encode (cons :bytes *fn-record-magic*))
              (fn-cbor-encode (cons :uint schema))
              (fn-cbor-encode (cons :uint sequence))
              (fn-cbor-encode (cons :uint txid))
              (fn-cbor-encode (cons :uint generation))
              (fn-record-item-encode (cons :bytes (fn-record-string-octets msgid)))
              (fn-record-item-encode (cons :bytes payload))
              octets)
             *fn-record-max-octets*))
           (equal
            (fn-record-encode-impl
             (fn-record-parse-value
              (fn-record-decode-tail schema sequence txid generation msgid payload octets)))
            (append
             (fn-record-item-encode (cons :bytes *fn-record-magic*))
             (fn-cbor-encode (cons :uint schema))
             (fn-cbor-encode (cons :uint sequence))
             (fn-cbor-encode (cons :uint txid))
             (fn-cbor-encode (cons :uint generation))
             (fn-record-item-encode (cons :bytes (fn-record-string-octets msgid)))
             (fn-record-item-encode (cons :bytes payload))
             octets)))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-value-is-natural
                            (octets octets))
                 (:instance fn-record-read-uint-value-is-natural
                            (octets (fn-record-tail-after-charge octets)))
                 (:instance fn-record-read-uint-reencode-prefix
                            (octets (fn-record-tail-after-charge octets)))
                 (:instance fn-record-component-prefixes-compose
             (count (fn-record-parse-value (fn-record-read-uint octets)))
             (groups (fn-record-parse-value (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))
             (obligation-id (fn-record-octets-string (fn-record-parse-value (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets))))))))
             (content-subject (fn-record-octets-string (fn-record-parse-value (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets))))))))))
             (release-evidence (fn-record-octets-string (fn-record-parse-value (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets))))))))))))
             (charge (fn-record-parse-value (fn-record-read-uint (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))))))))
             (stamp
              (fn-record-stamp
               (fn-record-parse-value
                (fn-record-decode-tail schema sequence txid generation
                                       msgid payload octets))))
             (after-count (fn-record-parse-rest (fn-record-read-uint octets)))
             (after-groups (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))
             (after-id (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))
             (after-subject (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))))
             (after-evidence (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))))))
             ))
           :in-theory
           (e/d (fn-record-decode-tail fn-record-stamp fn-record-make)
                (fn-record-parse-okp
                 fn-record-parse-ok
                 fn-record-parse-value
                 fn-record-parse-rest
                 fn-record-component-prefixes-compose
                 fn-record-read-uint
                 fn-record-read-bytes
                 fn-record-parse-groups
                 fn-record-encode-groups
                 fn-cbor-encode
                 fn-record-encode-impl
                 fn-record-p
                 fn-record-octets-string
                 fn-record-string-octets
                 ; As in the composition lemma above: both sides are nested
                 ; appends, and this rule made type-set walk them (12 s).
                 (:type-prescription true-listp-append))))))

(defthm fn-record-decode-after-header-reencode
  (implies (and (member-equal schema '(0 1))
            (fn-record-parse-okp (fn-record-decode-after-header schema octets))
            (fn-cbor-at-mostp
             (append
              (fn-record-item-encode (cons :bytes *fn-record-magic*))
              (fn-cbor-encode (cons :uint schema))
              octets)
             *fn-record-max-octets*))
           (equal
             (fn-record-encode-impl
             (fn-record-parse-value (fn-record-decode-after-header schema octets)))
            (append
             (fn-record-item-encode (cons :bytes *fn-record-magic*))
             (fn-cbor-encode (cons :uint schema))
             octets)))
  :hints (("Goal"
           :use
           ((:instance fn-record-decode-after-header-successes)
            (:instance fn-record-read-uint-reencode-prefix
             (octets octets))
            (:instance fn-record-read-uint-reencode-prefix
             (octets
              (fn-record-parse-rest (fn-record-read-uint octets))))
            (:instance fn-record-read-uint-reencode-prefix
             (octets
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest (fn-record-read-uint octets))))))
            (:instance fn-record-read-bytes-reencode-prefix
             (octets
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint octets))))))))
            (:instance fn-record-read-bytes-reencode-prefix
             (octets
              (fn-record-parse-rest
               (fn-record-read-bytes
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint
                    (fn-record-parse-rest
                     (fn-record-read-uint octets))))))))))
            (:instance fn-record-read-bytes-value-are-octets
             (octets
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint octets))))))))
            (:instance fn-record-string-octets-of-octets-string
             (octets
              (fn-record-parse-value
               (fn-record-read-bytes
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint
                    (fn-record-parse-rest
                     (fn-record-read-uint octets))))))))))
            (:instance fn-record-five-prefixes-compose
             (p1
              (fn-cbor-encode
               (cons :uint
                     (fn-record-parse-value
                      (fn-record-read-uint octets)))))
             (after1
              (fn-record-parse-rest (fn-record-read-uint octets)))
             (p2
              (fn-cbor-encode
               (cons :uint
                     (fn-record-parse-value
                      (fn-record-read-uint
                       (fn-record-parse-rest
                        (fn-record-read-uint octets)))))))
             (after2
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest (fn-record-read-uint octets)))))
             (p3
              (fn-cbor-encode
               (cons :uint
                     (fn-record-parse-value
                      (fn-record-read-uint
                       (fn-record-parse-rest
                        (fn-record-read-uint
                         (fn-record-parse-rest
                          (fn-record-read-uint octets)))))))))
             (after3
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint octets)))))))
             (p4
              (fn-record-item-encode
               (cons :bytes
                     (fn-record-parse-value
                      (fn-record-read-bytes
                       (fn-record-parse-rest
                        (fn-record-read-uint
                         (fn-record-parse-rest
                          (fn-record-read-uint
                           (fn-record-parse-rest
                            (fn-record-read-uint octets)))))))))))
             (after4
              (fn-record-parse-rest
               (fn-record-read-bytes
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint
                    (fn-record-parse-rest
                     (fn-record-read-uint octets)))))))))
             (p5
              (fn-record-item-encode
               (cons :bytes
                     (fn-record-parse-value
                      (fn-record-read-bytes
                       (fn-record-parse-rest
                        (fn-record-read-bytes
                         (fn-record-parse-rest
                          (fn-record-read-uint
                           (fn-record-parse-rest
                            (fn-record-read-uint
                             (fn-record-parse-rest
                              (fn-record-read-uint octets)))))))))))))
             (tail
              (fn-record-parse-rest
               (fn-record-read-bytes
                (fn-record-parse-rest
                 (fn-record-read-bytes
                  (fn-record-parse-rest
                   (fn-record-read-uint
                    (fn-record-parse-rest
                     (fn-record-read-uint
                      (fn-record-parse-rest
                       (fn-record-read-uint octets)))))))))))
             (input octets))
            (:instance fn-record-decode-tail-reencode
             (schema schema)
             (sequence
              (fn-record-parse-value (fn-record-read-uint octets)))
             (txid
              (fn-record-parse-value
               (fn-record-read-uint
                (fn-record-parse-rest (fn-record-read-uint octets)))))
             (generation
              (fn-record-parse-value
               (fn-record-read-uint
                (fn-record-parse-rest
                 (fn-record-read-uint
                  (fn-record-parse-rest
                   (fn-record-read-uint octets)))))))
             (msgid
              (fn-record-octets-string
               (fn-record-parse-value
                (fn-record-read-bytes
                 (fn-record-parse-rest
                  (fn-record-read-uint
                   (fn-record-parse-rest
                    (fn-record-read-uint
                     (fn-record-parse-rest
                      (fn-record-read-uint octets))))))))))
             (payload
              (fn-record-parse-value
               (fn-record-read-bytes
                (fn-record-parse-rest
                 (fn-record-read-bytes
                  (fn-record-parse-rest
                   (fn-record-read-uint
                    (fn-record-parse-rest
                     (fn-record-read-uint
                      (fn-record-parse-rest
                       (fn-record-read-uint octets)))))))))))
             (octets
              (fn-record-parse-rest
               (fn-record-read-bytes
                (fn-record-parse-rest
                 (fn-record-read-bytes
                  (fn-record-parse-rest
                   (fn-record-read-uint
                    (fn-record-parse-rest
                     (fn-record-read-uint
                      (fn-record-parse-rest
                       (fn-record-read-uint octets)))))))))))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-record-decode-after-header
              fn-record-parse-error-is-failure
              fn-record-decode-after-header-successes
              fn-record-parse-ok-is-success
              fn-record-parse-ok-has-value
              fn-record-parse-ok-has-rest
              fn-record-append-associative
              fn-record-length-append
              fn-record-at-most-is-length-bound
              (:executable-counterpart equal)
              (:executable-counterpart not)
              (:executable-counterpart consp)
              (:executable-counterpart car)
              (:executable-counterpart cdr))))))

(defthm fn-record-result-okp-is-parse-okp
  (equal (fn-record-result-okp result)
         (fn-record-parse-okp result))
  :hints (("Goal"
           :in-theory (enable fn-record-result-okp
                              fn-record-parse-okp))))

(defthm fn-record-final-ok-is-success
  (fn-record-result-okp (fn-record-result-ok record))
  :hints (("Goal"
           :in-theory (enable fn-record-result-okp fn-record-result-ok))))

(defthm fn-record-final-ok-has-record
  (equal (fn-record-result-record (fn-record-result-ok record)) record)
  :hints (("Goal"
           :in-theory (enable fn-record-result-record
                              fn-record-result-ok))))

; The exact decoder's successful control-flow facts, without opening either
; primitive CBOR read.  These facts are the complete adapter from its two
; header reads to the already-proved after-header inverse.
(defthm fn-record-decode-exact-successes
  (implies
   (fn-record-result-okp (fn-record-decode-exact-impl octets))
   (and
    (fn-cbor-at-mostp octets *fn-record-max-octets*)
    (fn-record-parse-okp (fn-record-read-bytes octets))
    (equal (fn-record-parse-value (fn-record-read-bytes octets))
           *fn-record-magic*)
    (fn-record-parse-okp
     (fn-record-read-uint
      (fn-record-parse-rest (fn-record-read-bytes octets))))
    (member-equal (fn-record-header-schema octets) '(0 1))
    (fn-record-parse-okp
     (fn-record-decode-after-header
      (fn-record-header-schema octets)
      (fn-record-header-tail octets)))
    (equal
     (fn-record-result-record (fn-record-decode-exact-impl octets))
     (fn-record-parse-value
      (fn-record-decode-after-header
       (fn-record-header-schema octets)
       (fn-record-header-tail octets))))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:d fn-record-decode-exact-impl)
              fn-record-result-okp-is-parse-okp
              fn-record-parse-error-is-failure
              fn-record-final-ok-is-success
              fn-record-final-ok-has-record
              fn-record-parse-ok-has-value
              (:executable-counterpart equal)
              (:executable-counterpart not))))))

; Every accepted exact schema-0 record is already its deterministic encoding.
; The hypothesis is only parser success: the decoder itself establishes the
; byte domain, input cap, schema checks, field domains, group uniqueness, and
; absence of trailing octets.
(defthm fn-record-impl-accepted-input-is-canonical
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (equal (fn-record-encode-impl
                   (fn-record-result-record (fn-record-decode-exact-impl octets)))
                  octets))
  :hints (("Goal"
           :use
           ((:instance fn-record-decode-exact-successes)
            (:instance fn-record-read-bytes-reencode-prefix
             (octets octets))
            (:instance fn-record-read-uint-reencode-prefix
             (octets
              (fn-record-parse-rest (fn-record-read-bytes octets))))
            (:instance fn-record-two-prefixes-compose
             (p1
              (fn-record-item-encode
               (cons :bytes
                     (fn-record-parse-value
                      (fn-record-read-bytes octets)))))
             (after1
              (fn-record-parse-rest (fn-record-read-bytes octets)))
             (p2
              (fn-cbor-encode
               (cons :uint
                     (fn-record-parse-value
                      (fn-record-read-uint
                       (fn-record-parse-rest
                        (fn-record-read-bytes octets)))))))
             (tail
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest (fn-record-read-bytes octets)))))
             (input octets))
            (:instance fn-record-decode-after-header-reencode
             (schema (fn-record-header-schema octets))
             (octets
              (fn-record-header-tail octets))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-record-decode-exact-successes
              fn-record-append-associative
              (:executable-counterpart equal))))))

; -----------------------------------------------------------------------------
; Export theory.  `fn-record-accepted-input-is-canonical' is the keystone.
; Everything else is parser-adapter vocabulary, including the two accessor
; equalities (`fn-record-result-okp-is-parse-okp' and the prefix compositions)
; that must not reach an includer as rewrite rules.

(deftheory fn-record-canonicality-vocabulary
  '(    fn-record-read-uint-reencode-prefix
    fn-record-read-bytes-reencode-prefix
    fn-record-octets-chars-are-characters
    fn-record-string-octets-aux-of-octets-chars
    fn-record-string-octets-of-octets-string
    fn-record-read-bytes-value-are-octets
    fn-record-read-uint-value-is-natural
    fn-record-read-uint-reencode-exact
    fn-record-parse-groups-reencode-prefix
    fn-record-parse-groups-value-length fn-record-parse-ok-is-success
    fn-record-parse-ok-has-value fn-record-parse-ok-has-rest
    fn-record-component-prefixes-compose fn-record-five-prefixes-compose
    fn-record-two-prefixes-compose fn-record-decode-after-header-successes
    fn-record-decode-tail-reencode fn-record-decode-after-header-reencode
    fn-record-result-okp-is-parse-okp fn-record-final-ok-is-success
    fn-record-final-ok-has-record fn-record-decode-exact-successes))

(in-theory (disable fn-record-read-uint-reencode-prefix
             fn-record-read-bytes-reencode-prefix
             fn-record-octets-chars-are-characters
             fn-record-string-octets-aux-of-octets-chars
             fn-record-string-octets-of-octets-string
             fn-record-read-bytes-value-are-octets
             fn-record-read-uint-value-is-natural
             fn-record-read-uint-reencode-exact
             fn-record-parse-groups-reencode-prefix
             fn-record-parse-groups-value-length
             fn-record-parse-ok-is-success fn-record-parse-ok-has-value
             fn-record-parse-ok-has-rest
             fn-record-component-prefixes-compose
             fn-record-five-prefixes-compose
             fn-record-two-prefixes-compose
             fn-record-decode-after-header-successes
             fn-record-decode-tail-reencode
             fn-record-decode-after-header-reencode
             fn-record-result-okp-is-parse-okp
             fn-record-final-ok-is-success fn-record-final-ok-has-record
             fn-record-decode-exact-successes))

; -----------------------------------------------------------------------------
; The implementation's side of the seam (plan 2026-09-22 §4.1, step T1).
;
; `books/records-seam.lisp' constrains `fn-record-encode' and
; `fn-record-decode-exact' by six properties; these are the same six of
; `fn-record-encode-impl' and `fn-record-decode-exact-impl'.  Two are the
; keystones above (`fn-record-impl-round-trip' in records-invariants,
; `fn-record-impl-accepted-input-is-canonical' here); the other four are
; below (the magic and the schema octet derived from the six-octet header
; fact, which stays here, below the seam).  The seam's local witness and `books/records-attach.lisp''s
; `defattach' both discharge their obligations by citing these six, so the
; codec's proofs are done once, here.  All are `:rule-classes nil': the
; implementation has no caller above the seam to rewrite for.

; The encoder refuses a value that is not a record.
(defthm fn-record-impl-encode-domain
  (implies (not (fn-record-p record))
           (equal (fn-record-encode-impl record) nil))
  :hints (("Goal" :in-theory (enable fn-record-encode-impl)))
  :rule-classes nil)

; An accepted input is a nonempty octet list within the record bound: the
; decoder checks the bound before it traverses the input and the octet
; domain before it reads an item, and an empty input has no magic item.
(defthm fn-record-impl-accepted-input-bounds
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (and (fn-cbor-octet-listp octets)
                (consp octets)
                (<= (len octets) *fn-record-max-octets*)))
  :hints (("Goal"
           :use (fn-record-decode-exact-successes)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:d fn-record-decode-exact-impl)
              fn-record-result-okp-is-parse-okp
              fn-record-parse-error-is-failure
              fn-record-at-most-is-length-bound
              (:e fn-record-read-bytes) (:e fn-record-parse-okp) (:e natp)
              (:e fn-cbor-octet-listp) (:d fn-cbor-octet-listp)))))
  :rule-classes nil)

; The worst-case length of an encoded record, in its payload length and group
; count (design 2026-09-25-bounds §2.1: the relation a profile's record bound
; must satisfy for its article bound).  Every field is at its ceiling except
; those two, which are the record's own.
; No hypothesis: a non-record encodes to nil.
(defthm fn-record-impl-encode-length-bound
  (<= (len (fn-record-encode-impl record))
      (fn-record-encoded-octets-ceiling
       (len (fn-record-payload record))
       (len (fn-record-groups record))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-record-p record))
           :in-theory (e/d (fn-record-encode-impl
                            fn-record-encoded-octets-ceiling)
                           (fn-cbor-encode fn-record-item-encode
                            fn-record-item-encode-is-cbor-encode
                            fn-record-encode-groups
                            fn-record-string-octets fn-record-string-octets-aux
                            fn-cbor-at-mostp
                            (:type-prescription true-listp-append))))))

; Kind dispatch: every accepted input begins with the five magic octets and
; the decoded schema (0 or 1).  A decoder for another event kind whose inputs
; never begin with this magic cannot accept a record.
(defthm fn-record-impl-accepted-input-header
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (equal (take 6 octets)
                  (append *fn-record-magic-octets*
                          (list (fn-record-header-schema octets)))))
  :hints (("Goal"
           :use (fn-record-decode-exact-successes
                 (:instance fn-record-read-bytes-reencode-prefix
                            (octets octets))
                 (:instance fn-record-read-uint-reencode-prefix
                            (octets (fn-record-parse-rest
                                     (fn-record-read-bytes octets)))))
           :in-theory (disable fn-record-decode-exact-successes
                               fn-record-read-bytes-reencode-prefix
                               fn-record-read-uint-reencode-prefix
                               fn-record-decode-exact-impl
                               fn-record-read-bytes fn-record-read-uint
                               fn-record-decode-after-header)))
  :rule-classes nil)

; The header split the way the seam states it (plan 2026-09-22 §4.1;
; specs/acceptance-stamp.md §2.1): the five magic octets, and the schema
; octet as the one the decoded record needs.  At schema 0 both follow from
; the six-octet fact above; the acceptance stamp changes the second one's
; proof and neither statement.
(defthm fn-record-impl-accepted-input-magic
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (equal (take 5 octets) *fn-record-magic-octets*))
  :hints (("Goal"
           :use (fn-record-impl-accepted-input-header
                 fn-record-impl-accepted-input-bounds)
           :in-theory (disable fn-record-decode-exact-impl)
           :expand ((take 5 octets) (take 4 (cdr octets))
                    (take 3 (cddr octets)) (take 2 (cdddr octets))
                    (take 1 (cddddr octets))
                    (take 6 octets) (take 5 (cdr octets))
                    (take 4 (cddr octets)) (take 3 (cdddr octets))
                    (take 2 (cddddr octets)) (take 1 (cdr (cddddr octets))))))
  :rule-classes nil)

; Only the first six bytes of an emitted encoding are needed for the seam's
; schema obligation.  The remaining record fields and codecs stay closed.
(defthm fn-record-encode-impl-schema-byte
  (implies (consp (fn-record-encode-impl record))
           (equal (nth 5 (fn-record-encode-impl record))
                  (fn-record-schema-octet record)))
  :hints (("Goal"
           :cases ((equal (fn-record-stamp record) :legacy))
           :in-theory (e/d (fn-record-encode-impl fn-record-schema-octet)
                           (fn-record-p fn-cbor-encode fn-record-encode-groups
                            fn-record-string-octets fn-cbor-at-mostp
                            ; The opened encoding is a right-nested append of
                            ; fourteen fields; type-set backchains through each
                            ; level's true-listp hypothesis (26 s, 14 808 steps).
                            (:type-prescription true-listp-append))))))

(defthm fn-record-impl-accepted-schema-is-the-stamp-kind
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (equal (nth 5 octets)
                  (fn-record-schema-octet
                   (fn-record-result-record
                    (fn-record-decode-exact-impl octets)))))
  :hints (("Goal"
           :use (fn-record-impl-accepted-input-is-canonical
                 fn-record-impl-accepted-input-bounds
                 (:instance fn-record-encode-impl-schema-byte
                  (record (fn-record-result-record
                           (fn-record-decode-exact-impl octets)))))
           :in-theory (disable fn-record-decode-exact-impl
                               fn-record-encode-impl
                               fn-record-impl-accepted-input-is-canonical
                               fn-record-encode-impl-schema-byte)))
  :rule-classes nil)

; The bounded-encoder rule rewrites toward `fn-cbor-encode', whose definition
; is `fn-cbor-encode-bounded' at the generic width: with the definition
; enabled (as provenance-codec's item-length lemmas enable it) the two loop.
; Its uses are above; a later book that needs it names it in a hint.
(in-theory (disable fn-record-cbor-encode-bounded-of-uint-value))
