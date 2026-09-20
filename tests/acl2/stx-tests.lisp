; Witnesses and teeth for the FN-Statement carrier and the verdict.
;
; The seam's functions are constrained, so nothing executes until a realiser
; is attached; this book inherits crypto-seam-tests' toy attachment (a
; polynomial mix digest and a sign-by-public-key scheme, neither
; cryptographic -- A-CRYPTO).  Every verdict below is therefore a statement
; about the CODEC and the composition, never about unforgeability.
;
; Order: guard-world audit, digest-independent golden vectors, malformed-input
; regressions, the round-trip scenario, then teeth -- one concrete violating
; value per hypothesis (docs/proof-style.md section 5).

(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/stx-invariants")

; -----------------------------------------------------------------------------
; Golden base64 vectors, RFC 4648 section 10.  These depend on no digest, no
; signature and no statement: the carrier's bottom layer is pinned to the RFC
; test vectors byte for byte, both ways.

(assert-event (equal (fn-stx-b64-encode nil) nil))
(assert-event (equal (fn-stx-b64-encode '(102)) '(90 103 61 61)))
(assert-event (equal (fn-stx-b64-encode '(102 111)) '(90 109 56 61)))
(assert-event (equal (fn-stx-b64-encode '(102 111 111)) '(90 109 57 118)))
(assert-event (equal (fn-stx-b64-encode '(102 111 111 98))
                     '(90 109 57 118 89 103 61 61)))
(assert-event (equal (fn-stx-b64-encode '(102 111 111 98 97))
                     '(90 109 57 118 89 109 69 61)))
(assert-event (equal (fn-stx-b64-encode '(102 111 111 98 97 114))
                     '(90 109 57 118 89 109 70 121)))

(assert-event (and (fn-stx-okp (fn-stx-b64-decode-exact '(90 109 57 118 89 109 70 121)))
                   (equal (fn-stx-val (fn-stx-b64-decode-exact
                                       '(90 109 57 118 89 109 70 121)))
                          '(102 111 111 98 97 114))))
(assert-event (and (fn-stx-okp (fn-stx-b64-decode-exact '(90 103 61 61)))
                   (equal (fn-stx-val (fn-stx-b64-decode-exact '(90 103 61 61)))
                          '(102))))

; Teeth for canonicality at the base64 layer.  Each is a concrete value that
; a permissive decoder would accept and this one refuses.
(assert-event (equal (fn-stx-why (fn-stx-b64-decode-exact '(90 104 61 61)))
                     :b64-padding-bits))      ; "Zh==": the 4 padding bits are not zero
(assert-event (equal (fn-stx-why (fn-stx-b64-decode-exact '(90 109 57 45)))
                     :b64-alphabet))          ; "Zm9-": not in the RFC 4648 section 4 alphabet
(assert-event (equal (fn-stx-why (fn-stx-b64-decode-exact '(90 109 57)))
                     :b64-quantum))           ; "Zm9": a truncated quantum
(assert-event (equal (fn-stx-why (fn-stx-b64-decode-exact '(90 109 61 118)))
                     :b64-alphabet))          ; "Zm=v": padding inside the quantum

; -----------------------------------------------------------------------------
; A signed statement, attached to an article, verified through the seam.

(defun fn-stx-test-line (str)
  (declare (xargs :guard t))
  (append (fn-record-string-octets (if (stringp str) str "")) '(13 10)))

; A defconst may not call an attached function (see :DOC ignored-attachment),
; and the toy realiser reaches every value below through fn-digest and
; fn-sig-public-key.  The three constants that call one directly are built by
; make-event, whose expansion is recorded in the certificate; everything
; downstream of them is a pure function of a literal and stays a defconst.
(defconst *stx-sk* (make-list 32 :initial-element 7))
(make-event (list 'defconst '*stx-pk* (list 'quote (fn-sig-public-key *stx-sk*))))
(defconst *stx-token* '(1 2 3))
(make-event (list 'defconst '*stx-creator*
                  (list 'quote (fn-prin-id *stx-pk* *stx-token*))))
(defconst *stx-keyring* (list (cons *stx-creator* *stx-pk*)))

(assert-event (fn-prin-keyringp *stx-keyring*))

(defconst *stx-authored*
  (append (fn-stx-test-line "From: agent-a@example.invalid")
          (append (fn-stx-test-line "Newsgroups: fn.test")
                  (append (fn-stx-test-line "Subject: hello")
                          (append (fn-stx-test-line "Message-ID: <a1@example.invalid>")
                                  (append '(13 10)
                                          (fn-record-string-octets "body line")))))))

(defconst *stx-tampered-authored*
  (append (fn-stx-test-line "From: agent-a@example.invalid")
          (append (fn-stx-test-line "Newsgroups: fn.test")
                  (append (fn-stx-test-line "Subject: hello")
                          (append (fn-stx-test-line "Message-ID: <a1@example.invalid>")
                                  (append '(13 10)
                                          (fn-record-string-octets "body lone")))))))

(make-event (list 'defconst '*stx-statement*
                  (list 'quote (fn-stmt-sign *stx-sk* *stx-creator* 1 1 nil
                                             :article *stx-authored*))))

(assert-event (fn-stmt-p *stx-statement*))
(assert-event (fn-prin-verifiedp *stx-statement* *stx-keyring*))

(make-event (list 'defconst '*stx-field* (list 'quote (fn-stx-header-value *stx-statement*))))

(defun fn-stx-test-received (field authored)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "FN-Statement: ")
          (append (if (true-listp field) field nil)
                  (append '(13 10) (if (true-listp authored) authored nil)))))

(defun fn-stx-test-article (octets)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse octets)))
    (if (and (true-listp parsed) (fn-article-result-okp parsed))
        (fn-article-result-article parsed)
      nil)))

(make-event (list 'defconst '*stx-article* (list 'quote (fn-stx-test-article (fn-stx-test-received *stx-field* *stx-authored*)))))

(assert-event (fn-article-syntax-p *stx-article*))

; The receiver's projection of the received bytes is exactly the bytes the
; author signed: the carrier subtracted itself.
(assert-event (equal (fn-stx-authored-source *stx-article*) *stx-authored*))

; The field survives the article parser byte-identical.
(assert-event (equal (fn-stx-strip-wsp
                      (fn-article-field-unfolded-value (fn-stx-field *stx-article*)))
                     *stx-field*))

; S1-1 on this witness: the field decodes to exactly this statement's header
; and signature, and the accepted value is its own canonical form.
(assert-event (and (fn-stx-okp (fn-stx-parse-header
                                (fn-article-field-unfolded-value
                                 (fn-stx-field *stx-article*))))
                   (equal (fn-stx-val (fn-stx-parse-header *stx-field*))
                          (fn-stmt-header *stx-statement*))
                   (equal (fn-stx-val2 (fn-stx-parse-header *stx-field*))
                          (fn-stmt-signature *stx-statement*))))
(assert-event (equal (fn-stx-header-value-parts
                      (fn-stx-val (fn-stx-parse-header *stx-field*))
                      (fn-stx-val2 (fn-stx-parse-header *stx-field*)))
                     *stx-field*))

; The verdict, and its rendering.
(assert-event (equal (fn-stx-verdict-token (fn-stx-verdict *stx-article* *stx-keyring* 7))
                     :verified))
(assert-event (equal (fn-stx-verdict-detail (fn-stx-verdict *stx-article* *stx-keyring* 7))
                     *stx-creator*))
(assert-event (equal (fn-stx-verdict-generation
                      (fn-stx-verdict *stx-article* *stx-keyring* 7))
                     7))
(assert-event (equal (fn-stx-verified-item (fn-stx-verdict *stx-article* *stx-keyring* 7))
                     (append (fn-record-string-octets "verified ")
                             (append (fn-stx-hex-octets *stx-creator*)
                                     (fn-record-string-octets " keyring 7")))))

; A folded field (RFC 5536 section 2.2) still verifies: folding is legal and
; the parser strips the continuation WSP before decoding.
(make-event (list 'defconst '*stx-folded-field* (list 'quote (append (take 40 *stx-field*)
          (append '(13 10 32) (nthcdr 40 *stx-field*))))))
(make-event (list 'defconst '*stx-folded-article* (list 'quote (fn-stx-test-article (fn-stx-test-received *stx-folded-field* *stx-authored*)))))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict *stx-folded-article* *stx-keyring* 7))
                     :verified))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per hypothesis and per verdict outcome.

; A modified payload never verifies: the ref is recomputed from the
; receiver's own projection, so a rewritten body is :ref-mismatch and not a
; forged :verified.
(make-event (list 'defconst '*stx-tampered-article* (list 'quote (fn-stx-test-article (fn-stx-test-received *stx-field* *stx-tampered-authored*)))))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict *stx-tampered-article* *stx-keyring* 7))
                     :unverified))
(assert-event (equal (fn-stx-verdict-detail
                      (fn-stx-verdict *stx-tampered-article* *stx-keyring* 7))
                     :ref-mismatch))

; An unknown creator never verifies, whatever the seam says about NIL keys.
(assert-event (equal (fn-stx-verdict-token (fn-stx-verdict *stx-article* nil 7))
                     :unverified))
(assert-event (equal (fn-stx-verdict-detail (fn-stx-verdict *stx-article* nil 7))
                     :signature))

; A malformed field loses authority and nothing else.
(make-event (list 'defconst '*stx-malformed-article* (list 'quote (fn-stx-test-article
   (fn-stx-test-received (fn-record-string-octets "!!!!") *stx-authored*)))))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict *stx-malformed-article* *stx-keyring* 7))
                     :unverified))
(assert-event (equal (fn-stx-verdict-detail
                      (fn-stx-verdict *stx-malformed-article* *stx-keyring* 7))
                     :malformed))

; No field at all is :absent, and :absent is rendered differently from every
; :unverified outcome (D13: three outcomes stay distinct all the way out).
(make-event (list 'defconst '*stx-bare-article* (list 'quote (fn-stx-test-article *stx-authored*))))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict *stx-bare-article* *stx-keyring* 7))
                     :absent))
(assert-event (equal (fn-stx-verified-item
                      (fn-stx-verdict *stx-bare-article* *stx-keyring* 7))
                     (fn-record-string-octets "absent no-field")))
(assert-event (not (equal (fn-stx-verified-item
                           (fn-stx-verdict *stx-bare-article* *stx-keyring* 7))
                          (fn-stx-verified-item
                           (fn-stx-verdict *stx-malformed-article* *stx-keyring* 7)))))
(assert-event (not (equal (fn-stx-verified-item
                           (fn-stx-verdict *stx-article* *stx-keyring* 7))
                          (fn-stx-verified-item
                           (fn-stx-verdict *stx-article* nil 7)))))

; Teeth for S1-1's hypotheses.
;
; fn-stx-field-round-trip needs (fn-stmt-p s): a non-statement has no field
; value and its "round trip" fails.
(assert-event (not (fn-stx-okp (fn-stx-parse-header (fn-stx-header-value '(1 2 3))))))

; fn-stx-field-accepted-input-is-canonical needs the value to be ACCEPTED.
; "Zh==" is refused, and the conclusion fails for it.
(assert-event (not (fn-stx-okp (fn-stx-parse-header '(90 104 61 61)))))
(assert-event (not (equal (fn-stx-header-value-parts
                           (fn-stx-val (fn-stx-parse-header '(90 104 61 61)))
                           (fn-stx-val2 (fn-stx-parse-header '(90 104 61 61))))
                          (fn-stx-strip-wsp '(90 104 61 61)))))

; The 8192-octet field bound, checked before any item is parsed.
(assert-event (equal (fn-stx-why (fn-stx-parse-header
                                  (make-list 8193 :initial-element 65)))
                     :field-too-long))

; A payload item present in the detached encoding is refused: the FULL
; fn-stmt- encoding, base64ed, is not a field value.
(assert-event (not (fn-stx-okp (fn-stx-parse-header
                                (fn-stx-b64-encode (fn-stmt-encode *stx-statement*))))))

; The 25-item budget, checked before each item is parsed.
(assert-event (equal (fn-stx-why
                      (fn-stx-parse-header
                       (fn-stx-b64-encode
                        (fn-stmt-encode-items
                         (make-list 26 :initial-element (cons :uint 1))))))
                     :too-many-items))

; The peer is not an argument: fn-stx-verdict's formals are (article keyring
; generation), so no function of a peer, a session or a route can appear in
; its support.  There is no value to exhibit for this one -- it is a property
; of the definition's signature, checked by reading it, and it is what makes
; every verdict theorem above hold at every hop.
