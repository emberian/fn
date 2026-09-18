; RFC 3977 section 4 wildmat parser/matcher assertion vectors.
(in-package "ACL2")
(include-book "../../books/wildmat")

(defun fn-wildmat-test-repeat (n byte)
  (if (zp n)
      nil
    (cons byte (fn-wildmat-test-repeat (1- n) byte))))

; Exact ASCII alternatives and RFC 3977 section 4.4's UTF-8 pound example.
(assert-event (equal (fn-wildmat-match '(97 98 99) '(97 98 99)) '(:ok t)))
(assert-event (equal (fn-wildmat-match '(97 98 99 44 100 101 102) '(100 101 102))
                     '(:ok t)))
(assert-event (equal (fn-wildmat-match '(194 163) '(194 163)) '(:ok t)))
(assert-event (equal (fn-wildmat-match '(194 163) '(194 164)) '(:ok nil)))

; The rightmost matching constituent controls inclusion, exactly as section
; 4.2 demonstrates for a*,!*b,*c*.
(defconst *fn-wildmat-rfc-example* '(97 42 44 33 42 98 44 42 99 42))
(assert-event (equal (fn-wildmat-match *fn-wildmat-rfc-example* '(97 97 97))
                     '(:ok t)))
(assert-event (equal (fn-wildmat-match *fn-wildmat-rfc-example* '(97 98 98))
                     '(:ok nil)))
(assert-event (equal (fn-wildmat-match *fn-wildmat-rfc-example* '(99 99 98))
                     '(:ok t)))
(assert-event (equal (fn-wildmat-match *fn-wildmat-rfc-example* '(120 120 120))
                     '(:ok nil)))
(assert-event (equal (fn-wildmat-match '(97 42 44 33 42 98 44 99 42) '(99 97 98))
                     '(:ok t)))

; Anchoring permits a star to consume zero characters but does not search for
; unanchored substrings.  The empty string is also a legal target for `*`.
(assert-event (equal (fn-wildmat-match '(97 42 98) '(97 98)) '(:ok t)))
(assert-event (equal (fn-wildmat-match '(97 42 98) '(120 97 98)) '(:ok nil)))
(assert-event (equal (fn-wildmat-match '(42) nil) '(:ok t)))

; `?` is one Unicode character, not one octet.  U+00A3 is encoded by two
; octets, yet it satisfies one question mark and leaves the following `a` at
; the second character position.
(assert-event (equal (fn-wildmat-match '(63 97 42) '(194 163 97 122))
                     '(:ok t)))
(assert-event (equal (fn-wildmat-match '(63) '(194 163)) '(:ok t)))
(assert-event (equal (fn-wildmat-match '(63) '(194 163 97)) '(:ok nil)))

; The generic matcher preserves a BOM as an ordinary non-ASCII exact code
; point.  Command-line BOM prohibition is intentionally not folded into this
; reusable matching layer.
(assert-event (equal (fn-wildmat-match '(239 187 191) '(239 187 191)) '(:ok t)))

; Empty patterns, doubled/trailing commas, leading negation, and every reserved
; punctuation are syntax errors.  `*` and `?` remain legal wildcard items.
(assert-event (equal (fn-wildmat-parse nil) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(97 44 44 98)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(97 44)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(33 97)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(91)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(92)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(93)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse '(42)) '(:ok ((:positive (42))))))

; The preflight cap is checked before octet traversal.  Exactly 497 octets are
; accepted, while 498 is rejected as a local profile limit for both source and
; target.  The adversarial star pattern is bounded and exercises the DP path.
(defconst *fn-wildmat-497-as* (fn-wildmat-test-repeat 497 97))
(defconst *fn-wildmat-498-as* (fn-wildmat-test-repeat 498 97))
(assert-event (fn-wildmat-result-okp (fn-wildmat-parse *fn-wildmat-497-as*)))
(assert-event (equal (fn-wildmat-parse *fn-wildmat-498-as*) '(:error :limit)))
(assert-event (equal (fn-wildmat-match '(42) *fn-wildmat-498-as*) '(:error :limit)))
(assert-event (equal
               (fn-wildmat-match
                '(42 97 42 97 42 97 42 97 42 97 42 97 42 97 42 97 42 97 42 97 42)
                '(97 97 97 97 97 97 97 97 97 97 97 97 97 97 97 97 97 97 97 97))
               '(:ok t)))

; Reject invalid leading bytes, truncation, overlong encodings, surrogates, and
; values above U+10FFFF.  The RFC explicitly calls out C0.A0 as an overlong
; form in section 12.5.
(assert-event (equal (fn-wildmat-parse '(128)) '(:error :malformed-utf8)))
(assert-event (equal (fn-wildmat-parse '(194)) '(:error :malformed-utf8)))
(assert-event (equal (fn-wildmat-parse '(192 160)) '(:error :malformed-utf8)))
(assert-event (equal (fn-wildmat-parse '(237 160 128)) '(:error :malformed-utf8)))
(assert-event (equal (fn-wildmat-parse '(244 144 128 128)) '(:error :malformed-utf8)))
(assert-event (equal (fn-wildmat-match '(42) '(194 32)) '(:error :malformed-utf8)))
