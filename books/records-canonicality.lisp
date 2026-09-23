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
           :use ((:instance fn-cbor-decode-reencode-prefix
                  (octets octets)))
           :in-theory (enable fn-record-read-uint
                              fn-record-parse-okp
                              fn-record-parse-value
                              fn-record-parse-rest))))

(defthm fn-record-read-bytes-reencode-prefix
  (implies (fn-record-parse-okp (fn-record-read-bytes octets))
           (equal (append (fn-cbor-encode
                           (cons :bytes
                                 (fn-record-parse-value
                                  (fn-record-read-bytes octets))))
                          (fn-record-parse-rest
                           (fn-record-read-bytes octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-cbor-decode-reencode-prefix
                  (octets octets)))
           :in-theory (enable fn-record-read-bytes
                              fn-record-parse-okp
                              fn-record-parse-value
                              fn-record-parse-rest))))

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
           :in-theory (enable fn-record-read-bytes
                              fn-record-parse-okp
                              fn-record-parse-value))))

(defthm fn-record-read-uint-value-is-natural
  (implies (fn-record-parse-okp (fn-record-read-uint octets))
           (natp (fn-record-parse-value (fn-record-read-uint octets))))
  :hints (("Goal"
           :in-theory (enable fn-record-read-uint
                              fn-record-parse-okp
                              fn-record-parse-value))))

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
                         obligation-id content-subject release-evidence charge))
        (equal count (len groups))
        (equal (append (fn-cbor-encode (cons :uint count)) after-count) octets)
        (equal (append (fn-record-encode-groups groups) after-groups) after-count)
        (equal (append
                (fn-cbor-encode
                 (cons :bytes (fn-record-string-octets obligation-id)))
                after-id)
               after-groups)
        (equal (append
                (fn-cbor-encode
                 (cons :bytes (fn-record-string-octets content-subject)))
                after-subject)
               after-id)
        (equal (append
                (fn-cbor-encode
                 (cons :bytes (fn-record-string-octets release-evidence)))
                after-evidence)
               after-subject)
        (equal (append (fn-cbor-encode (cons :uint charge)) nil) after-evidence)
        (fn-cbor-at-mostp
         (append
          (fn-cbor-encode (cons :bytes *fn-record-magic*))
          (fn-cbor-encode (cons :uint *fn-record-schema-version*))
          (fn-cbor-encode (cons :uint sequence))
          (fn-cbor-encode (cons :uint txid))
          (fn-cbor-encode (cons :uint generation))
          (fn-cbor-encode (cons :bytes (fn-record-string-octets msgid)))
          (fn-cbor-encode (cons :bytes payload))
          octets)
         *fn-record-max-octets*))
   (equal
    (fn-record-encode-impl
     (fn-record-make sequence txid generation msgid payload groups
                     obligation-id content-subject release-evidence charge))
    (append
     (fn-cbor-encode (cons :bytes *fn-record-magic*))
     (fn-cbor-encode (cons :uint *fn-record-schema-version*))
     (fn-cbor-encode (cons :uint sequence))
     (fn-cbor-encode (cons :uint txid))
     (fn-cbor-encode (cons :uint generation))
     (fn-cbor-encode (cons :bytes (fn-record-string-octets msgid)))
     (fn-cbor-encode (cons :bytes payload))
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
                 fn-record-charge)
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

; Success of the sequential header decoder gives the success hypotheses needed
; by each primitive inverse.  Isolating this control-flow fact keeps ACL2 from
; opening the CBOR decoder while relieving those hypotheses later.
(defthm fn-record-decode-after-header-successes
  (implies
   (fn-record-parse-okp (fn-record-decode-after-header octets))
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
  (implies (and
            (fn-record-parse-okp
             (fn-record-decode-tail sequence txid generation msgid payload octets))
            (fn-cbor-at-mostp
             (append
              (fn-cbor-encode (cons :bytes *fn-record-magic*))
              (fn-cbor-encode (cons :uint *fn-record-schema-version*))
              (fn-cbor-encode (cons :uint sequence))
              (fn-cbor-encode (cons :uint txid))
              (fn-cbor-encode (cons :uint generation))
              (fn-cbor-encode (cons :bytes (fn-record-string-octets msgid)))
              (fn-cbor-encode (cons :bytes payload))
              octets)
             *fn-record-max-octets*))
           (equal
            (fn-record-encode-impl
             (fn-record-parse-value
              (fn-record-decode-tail sequence txid generation msgid payload octets)))
            (append
             (fn-cbor-encode (cons :bytes *fn-record-magic*))
             (fn-cbor-encode (cons :uint *fn-record-schema-version*))
             (fn-cbor-encode (cons :uint sequence))
             (fn-cbor-encode (cons :uint txid))
             (fn-cbor-encode (cons :uint generation))
             (fn-cbor-encode (cons :bytes (fn-record-string-octets msgid)))
             (fn-cbor-encode (cons :bytes payload))
             octets)))
  :hints (("Goal"
           :use ((:instance fn-record-read-uint-value-is-natural
                            (octets octets))
                 (:instance fn-record-component-prefixes-compose
             (count (fn-record-parse-value (fn-record-read-uint octets)))
             (groups (fn-record-parse-value (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))
             (obligation-id (fn-record-octets-string (fn-record-parse-value (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets))))))))
             (content-subject (fn-record-octets-string (fn-record-parse-value (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets))))))))))
             (release-evidence (fn-record-octets-string (fn-record-parse-value (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets))))))))))))
             (charge (fn-record-parse-value (fn-record-read-uint (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))))))))
             (after-count (fn-record-parse-rest (fn-record-read-uint octets)))
             (after-groups (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))
             (after-id (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))
             (after-subject (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))))
             (after-evidence (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-read-bytes (fn-record-parse-rest (fn-record-parse-groups (fn-record-parse-value (fn-record-read-uint octets)) (fn-record-parse-rest (fn-record-read-uint octets)))))))))))
             ))
           :in-theory
           (e/d (fn-record-decode-tail)
                (fn-record-parse-okp
                 fn-record-parse-ok
                 fn-record-parse-value
                 fn-record-parse-rest
                 fn-record-make
                 fn-record-component-prefixes-compose
                 fn-record-read-uint
                 fn-record-read-bytes
                 fn-record-parse-groups
                 fn-record-encode-groups
                 fn-cbor-encode
                 fn-record-encode-impl
                 fn-record-p
                 fn-record-octets-string
                 fn-record-string-octets)))))

(defthm fn-record-decode-after-header-reencode
  (implies (and
            (fn-record-parse-okp (fn-record-decode-after-header octets))
            (fn-cbor-at-mostp
             (append
              (fn-cbor-encode (cons :bytes *fn-record-magic*))
              (fn-cbor-encode (cons :uint *fn-record-schema-version*))
              octets)
             *fn-record-max-octets*))
           (equal
            (fn-record-encode-impl
             (fn-record-parse-value (fn-record-decode-after-header octets)))
            (append
             (fn-cbor-encode (cons :bytes *fn-record-magic*))
             (fn-cbor-encode (cons :uint *fn-record-schema-version*))
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
              (fn-cbor-encode
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
              (fn-cbor-encode
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
    (equal
     (fn-record-parse-value
      (fn-record-read-uint
       (fn-record-parse-rest (fn-record-read-bytes octets))))
     *fn-record-schema-version*)
    (fn-record-parse-okp
     (fn-record-decode-after-header
      (fn-record-parse-rest
       (fn-record-read-uint
        (fn-record-parse-rest (fn-record-read-bytes octets))))))
    (equal
     (fn-record-result-record (fn-record-decode-exact-impl octets))
     (fn-record-parse-value
      (fn-record-decode-after-header
       (fn-record-parse-rest
        (fn-record-read-uint
         (fn-record-parse-rest (fn-record-read-bytes octets)))))))))
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
              (fn-cbor-encode
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
             (octets
              (fn-record-parse-rest
               (fn-record-read-uint
                (fn-record-parse-rest (fn-record-read-bytes octets)))))))
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

; Kind dispatch: every accepted input begins with the six header octets, the
; byte string "fn-r" (CBOR h'44666e2d72') and schema 0 (CBOR 0).  A decoder
; for another event kind whose inputs never begin so cannot accept a record.
(defthm fn-record-impl-accepted-input-header
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (equal (take 6 octets) '(68 102 110 45 114 0)))
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

(defthm fn-record-impl-accepted-schema-is-the-stamp-kind
  (implies (fn-record-result-okp (fn-record-decode-exact-impl octets))
           (equal (nth 5 octets)
                  (fn-record-schema-octet
                   (fn-record-result-record
                    (fn-record-decode-exact-impl octets)))))
  :hints (("Goal"
           :use (fn-record-impl-accepted-input-header)
           :in-theory (e/d (fn-record-schema-octet)
                           (fn-record-decode-exact-impl))
           :expand ((take 6 octets) (take 5 (cdr octets))
                    (take 4 (cddr octets)) (take 3 (cdddr octets))
                    (take 2 (cddddr octets)) (take 1 (cdr (cddddr octets))))))
  :rule-classes nil)
