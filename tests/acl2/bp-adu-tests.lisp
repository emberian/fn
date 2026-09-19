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
(assert-event
 (equal (fn-bpa-encode
         (fn-bpa-make-request
          "w" "s" "a" "b" "p" "i" "c" "t"
          (fn-bpa-test-repeat 32769 65)))
        nil))

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
