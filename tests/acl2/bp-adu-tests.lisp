; Golden and malformed vectors for the experimental BP ADU wrapper.
(in-package "ACL2")
(include-book "../../books/bp-adu")

(defconst *bpa-request*
  (fn-bpa-make-request "w" "s" "a" "b" "p" "i" "c" "t" '(88 13 10)))
(defconst *bpa-request-octets*
  '(73 70 78 45 66 80 45 65 68 85 0 0 9
    65 119 65 115 65 97 65 98 65 112 65 105 65 99 65 116 67 88 13 10))

(assert-event (fn-bpa-requestp *bpa-request*))
(assert-event (equal (fn-bpa-encode *bpa-request*) *bpa-request-octets*))
(assert-event (equal (fn-bpa-decode-exact *bpa-request-octets*)
                     (list :ok *bpa-request*)))
(assert-event (equal (fn-bpa-request-article
                      (fn-bpa-result-message
                       (fn-bpa-decode-exact *bpa-request-octets*)))
                     '(88 13 10)))

(defconst *bpa-receipt*
  (fn-bpa-make-receipt "r" "w" "s" "i" "e" "p" "n" "c" "t"))
(defconst *bpa-receipt-octets*
  '(73 70 78 45 66 80 45 65 68 85 0 1 9
    65 114 65 119 65 115 65 105 65 101 65 112 65 110 65 99 65 116))

(assert-event (fn-bpa-receiptp *bpa-receipt*))
(assert-event (equal (fn-bpa-encode *bpa-receipt*) *bpa-receipt-octets*))
(assert-event (equal (fn-bpa-decode-exact *bpa-receipt-octets*)
                     (list :ok *bpa-receipt*)))

; Non-shortest magic length, wrong magic/version/kind/count, truncation and
; trailing bytes all fail closed.
(assert-event
 (equal (fn-bpa-decode-exact
         '(88 9 70 78 45 66 80 45 65 68 85 0 0 9))
        '(:error :noncanonical)))
(assert-event
 (equal (fn-bpa-decode-exact
         '(73 70 78 45 66 80 45 65 68 84 0 0 9))
        '(:error :magic)))
(assert-event
 (equal (fn-bpa-decode-exact
         '(73 70 78 45 66 80 45 65 68 85 1 0 9))
        '(:error :unknown-version)))
(assert-event
 (equal (fn-bpa-decode-exact
         '(73 70 78 45 66 80 45 65 68 85 0 2 9))
        '(:error :unknown-kind)))
(assert-event
 (equal (fn-bpa-decode-exact
         '(73 70 78 45 66 80 45 65 68 85 0 0 8))
        '(:error :field-count)))
(assert-event
 (equal (fn-bpa-decode-exact
         '(73 70 78 45 66 80 45 65 68 85 0 0 9 65))
        '(:error :truncated)))
(assert-event
 (equal (fn-bpa-decode-exact (append *bpa-request-octets* '(0)))
        '(:error :trailing)))

; Empty or oversized portable metadata and oversized articles never encode.
(assert-event
 (equal (fn-bpa-encode
         (fn-bpa-make-request "" "s" "a" "b" "p" "i" "c" "t" nil))
        nil))

(defun fn-bpa-test-repeat (n value)
  (if (zp n) nil (cons value (fn-bpa-test-repeat (1- n) value))))

(assert-event
 (equal (fn-bpa-encode
         (fn-bpa-make-request
          (coerce (fn-bpa-test-repeat 257 #\x) 'string)
          "s" "a" "b" "p" "i" "c" "t" nil))
        nil))
; PRF-134 (the codec half of P5): the article's width is the ADU codec's,
; *fn-bpa-max-article* (2^24 - 2106), not 32,768.  A 70,000-octet article --
; past the pre-P5 ADU record of 65,538 octets, which refused it -- encodes
; with the u32 byte-string head and round-trips; the node's bound is its
; profile's ADU octets (books/bp-node-profile-admission).
(defconst *bpa-wide-request*
  (fn-bpa-make-request "w" "s" "a" "b" "p" "i" "c" "t"
                       (make-list 70000 :initial-element 65)))
(assert-event (fn-bpa-requestp *bpa-wide-request*))
(assert-event (< 65538 (len (fn-bpa-encode *bpa-wide-request*))))
(assert-event (equal (fn-bpa-decode-exact (fn-bpa-encode *bpa-wide-request*))
                     (list :ok *bpa-wide-request*)))
; An article at exactly the old bound keeps the bytes the generic CBOR entry
; wrote (a three-octet head), so ADUs written before P5 are unchanged.
(assert-event
 (equal (fn-bpa-encode
         (fn-bpa-make-request "w" "s" "a" "b" "p" "i" "c" "t"
                              (make-list 32768 :initial-element 65)))
        (append (fn-cbor-encode (cons :bytes *fn-bpa-magic*))
                (fn-cbor-encode (cons :uint *fn-bpa-version*))
                (fn-cbor-encode (cons :uint *fn-bpa-request-kind*))
                (fn-cbor-encode (cons :uint *fn-bpa-field-count*))
                (fn-cbor-encode (cons :bytes (list 119)))
                (fn-cbor-encode (cons :bytes (list 115)))
                (fn-cbor-encode (cons :bytes (list 97)))
                (fn-cbor-encode (cons :bytes (list 98)))
                (fn-cbor-encode (cons :bytes (list 112)))
                (fn-cbor-encode (cons :bytes (list 105)))
                (fn-cbor-encode (cons :bytes (list 99)))
                (fn-cbor-encode (cons :bytes (list 116)))
                (fn-cbor-encode (cons :bytes (make-list 32768 :initial-element 65))))))

; The portable wrapper contains no local Store transaction, generation, BPA
; identifier, or NNTP article-number field; exact article bytes remain one
; opaque bounded byte string.
(assert-event (equal (len *bpa-request*) 10))
(assert-event (equal (len *bpa-receipt*) 10))


; These decoder entries used to remain :ideal despite codec certification.
; The public guard-T decoder and its typed internal callees are now verified.
(assert-event (equal (symbol-class 'fn-bpa-read-fields (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpa-decode-fields (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpa-decode-after-magic (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpa-decode-candidate (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpa-decode-exact (w state)) :common-lisp-compliant))
