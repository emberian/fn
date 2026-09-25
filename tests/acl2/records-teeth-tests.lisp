; Teeth for the record codec keystones, including schema 1.
;
; Both directions of the record codec are keystones with one hypothesis each,
; stated twice: once of the seam's constrained `fn-record-encode' and
; `fn-record-decode-exact' (books/records-seam.lisp, the functions every book
; above the codec and the host call), and once of the implementation the
; image attaches to them (`fn-record-impl-round-trip' in records-invariants,
; `fn-record-impl-accepted-input-is-canonical' in records-canonicality).
; Both hypotheses are recognizers, so each negative case is a malformed value:
; a record that is not a record, and octets the decoder refuses.  The ground
; assertions evaluate through the attachment (books/records-attach.lisp); the
; `must-fail' cases are proof attempts, where no attachment is used, so the
; seam's cases fail from the constraints alone.

(in-package "ACL2")
(include-book "../../books/records-canonicality")
(include-book "../../books/records-attach")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; Every field distinct and none empty: a record whose Message-ID, obligation
; identity, content subject and release evidence are four different strings,
; a multi-octet payload, and more than one group.  A witness with equal fields
; would satisfy a codec that transposed two of them.

(defconst *rec-teeth-record*
  (fn-record-make 1 2 3 "<a@example.invalid>" '(72 105 13 10)
                  '("fn.letters" "fn.test") "archive-a" "content-a"
                  "release-a" 4 841000000))

(assert-event (fn-record-p *rec-teeth-record*))
(assert-event
 (not (equal (fn-record-msgid *rec-teeth-record*)
             (fn-record-content-subject *rec-teeth-record*))))
(assert-event
 (not (equal (fn-record-obligation-id *rec-teeth-record*)
             (fn-record-release-evidence *rec-teeth-record*))))
(assert-event (equal (len (fn-record-groups *rec-teeth-record*)) 2))

(defconst *rec-teeth-octets* (fn-record-encode-impl *rec-teeth-record*))

; Both directions close at the witness.
(assert-event (equal (fn-record-decode-exact *rec-teeth-octets*)
                     (list :ok *rec-teeth-record*)))
(assert-event (fn-record-result-okp (fn-record-decode-exact *rec-teeth-octets*)))
(assert-event (equal (fn-record-encode
                      (fn-record-result-record
                       (fn-record-decode-exact *rec-teeth-octets*)))
                     *rec-teeth-octets*))

; A non-shortest CBOR magic length is refused before record parsing, so there
; is exactly one octet string per record.
(assert-event (equal (fn-record-decode-exact '(88 4 102 110 45 114 0))
                     '(:error :noncanonical)))

; -----------------------------------------------------------------------------
; Teeth for `fn-record-round-trip'
;   (implies (fn-record-p record)
;            (equal (fn-record-decode-exact (fn-record-encode record))
;                   (list :ok record)))

; The only hypothesis is a recognizer, so the case is a malformed value.
(defconst *rec-teeth-not-a-record* '(:not-a-record))
(assert-event (not (fn-record-p *rec-teeth-not-a-record*)))

(local
 (must-fail
  (defthm rec-teeth-round-trip-without-record-p
    (equal (fn-record-decode-exact (fn-record-encode *rec-teeth-not-a-record*))
           (list :ok *rec-teeth-not-a-record*)))))

; A second malformed value that has the right shape and a bad field: a payload
; octet out of range.  Shape validity alone is not the hypothesis.
(defconst *rec-teeth-bad-payload*
  (fn-record-make 1 2 3 "<a@example.invalid>" '(256)
                  '("fn.letters") "archive-a" "content-a" "release-a" 4 841000000))
(assert-event (not (fn-record-p *rec-teeth-bad-payload*)))

(local
 (must-fail
  (defthm rec-teeth-round-trip-without-octet-payload
    (equal (fn-record-decode-exact (fn-record-encode *rec-teeth-bad-payload*))
           (list :ok *rec-teeth-bad-payload*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-record-accepted-input-is-canonical'
;   (implies (fn-record-result-okp (fn-record-decode-exact octets))
;            (equal (fn-record-encode
;                    (fn-record-result-record (fn-record-decode-exact octets)))
;                   octets))

; The hypothesis dropped: octets the decoder refuses.  Re-encoding what the
; refused decode "returned" is not the input.
(defconst *rec-teeth-refused* '(88 4 102 110 45 114 0))
(assert-event (not (fn-record-result-okp (fn-record-decode-exact *rec-teeth-refused*))))

(local
 (must-fail
  (defthm rec-teeth-canonical-without-accepted-decode
    (equal (fn-record-encode
            (fn-record-result-record (fn-record-decode-exact *rec-teeth-refused*)))
           *rec-teeth-refused*))))

; -----------------------------------------------------------------------------
; The same three cases of the implementation's keystones.

(local
 (must-fail
  (defthm rec-teeth-impl-round-trip-without-record-p
    (equal (fn-record-decode-exact-impl
            (fn-record-encode-impl *rec-teeth-not-a-record*))
           (list :ok *rec-teeth-not-a-record*)))))

(local
 (must-fail
  (defthm rec-teeth-impl-round-trip-without-octet-payload
    (equal (fn-record-decode-exact-impl
            (fn-record-encode-impl *rec-teeth-bad-payload*))
           (list :ok *rec-teeth-bad-payload*)))))

(local
 (must-fail
  (defthm rec-teeth-impl-canonical-without-accepted-decode
    (equal (fn-record-encode-impl
            (fn-record-result-record
             (fn-record-decode-exact-impl *rec-teeth-refused*)))
           *rec-teeth-refused*))))

; The attachment is the implementation: the seam's functions evaluate to the
; implementation's values on the witness and on the refused input.
(assert-event (equal (fn-record-encode *rec-teeth-record*)
                     (fn-record-encode-impl *rec-teeth-record*)))
(assert-event (equal (fn-record-decode-exact *rec-teeth-refused*)
                     (fn-record-decode-exact-impl *rec-teeth-refused*)))

; -----------------------------------------------------------------------------
; Teeth for `fn-record-accepted-input-magic'
;   (implies (fn-record-result-okp (fn-record-decode-exact octets))
;            (equal (take 5 octets) *fn-record-magic-octets*))
; and `fn-record-accepted-schema-is-the-stamp-kind'
;   (implies (fn-record-result-okp (fn-record-decode-exact octets))
;            (equal (nth 5 octets)
;                   (fn-record-schema-octet
;                    (fn-record-result-record (fn-record-decode-exact octets)))))

; The witness: an accepted encoding carries the magic and the schema octet
; its record needs (1 at schema 1, 0 at schema 0).
(assert-event (equal (take 5 *rec-teeth-octets*) *fn-record-magic-octets*))
(assert-event (equal (nth 5 *rec-teeth-octets*)
                     (fn-record-schema-octet
                      (fn-record-result-record
                       (fn-record-decode-exact *rec-teeth-octets*)))))
(assert-event (equal (nth 5 *rec-teeth-octets*) 1))
(defconst *rec-teeth-legacy-record*
  (fn-record-with-stamp *rec-teeth-record* :legacy))
(defconst *rec-teeth-legacy-octets*
  (fn-record-encode-impl *rec-teeth-legacy-record*))
(assert-event (equal (nth 5 *rec-teeth-legacy-octets*) 0))
(assert-event (equal (fn-record-decode-exact *rec-teeth-legacy-octets*)
                     (list :ok *rec-teeth-legacy-record*)))
(assert-event
 (equal (fn-record-encode
         (fn-record-result-record
          (fn-record-decode-exact *rec-teeth-legacy-octets*)))
        *rec-teeth-legacy-octets*))

; The hypothesis dropped, for the magic: a Store event of another kind
; (`fn-e', books/store-events.lisp), refused by the record decoder.
(defconst *rec-teeth-event-octets* '(68 102 110 45 101 0))
(assert-event (not (fn-record-result-okp
                    (fn-record-decode-exact *rec-teeth-event-octets*))))

(local
 (must-fail
  (defthm rec-teeth-magic-without-accepted-decode
    (equal (take 5 *rec-teeth-event-octets*) *fn-record-magic-octets*))))

; The hypothesis dropped, for the schema octet: the right magic followed by
; a version octet no grammar has (refused as `:unknown-version').
(defconst *rec-teeth-unknown-version* '(68 102 110 45 114 3))
(assert-event (equal (fn-record-decode-exact *rec-teeth-unknown-version*)
                     '(:error :unknown-version)))

(local
 (must-fail
  (defthm rec-teeth-schema-without-accepted-decode
    (equal (nth 5 *rec-teeth-unknown-version*)
           (fn-record-schema-octet
            (fn-record-result-record
             (fn-record-decode-exact *rec-teeth-unknown-version*)))))))

; The magic case is ground and needs no decoder.  The schema case of the
; implementation, where the conclusion is decided by evaluation and is
; false: the refused input's sixth octet is 2 where the dummy record
; needs 0.
(local
 (must-fail
  (defthm rec-teeth-impl-schema-without-accepted-decode
    (equal (nth 5 *rec-teeth-unknown-version*)
           (fn-record-schema-octet
            (fn-record-result-record
             (fn-record-decode-exact-impl *rec-teeth-unknown-version*))))
    :hints (("Goal" :in-theory (enable fn-record-schema-octet))))))
(assert-event (not (equal (nth 5 *rec-teeth-unknown-version*)
                          (fn-record-schema-octet
                           (fn-record-result-record
                            (fn-record-decode-exact-impl
                             *rec-teeth-unknown-version*))))))
(assert-event (not (equal (take 5 *rec-teeth-event-octets*)
                          *fn-record-magic-octets*)))
