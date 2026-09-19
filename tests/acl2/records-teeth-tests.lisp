; Teeth for the schema-0 record codec keystones.
;
; Both directions of the record codec are keystones with one hypothesis each
; (books/records-invariants.lisp:174, books/records-canonicality.lisp:661).
; Both hypotheses are recognizers, so each negative case is a malformed value:
; a record that is not a record, and octets the decoder refuses.

(in-package "ACL2")
(include-book "../../books/records-canonicality")
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
                  "release-a" 4))

(assert-event (fn-record-p *rec-teeth-record*))
(assert-event
 (not (equal (fn-record-msgid *rec-teeth-record*)
             (fn-record-content-subject *rec-teeth-record*))))
(assert-event
 (not (equal (fn-record-obligation-id *rec-teeth-record*)
             (fn-record-release-evidence *rec-teeth-record*))))
(assert-event (equal (len (fn-record-groups *rec-teeth-record*)) 2))

(defconst *rec-teeth-octets* (fn-record-encode *rec-teeth-record*))

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
                  '("fn.letters") "archive-a" "content-a" "release-a" 4))
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
