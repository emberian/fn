; RFC 3977 section 4 wildmat parser/matcher assertion vectors.
(in-package "ACL2")
(include-book "../../books/wildmat")

; Internal next-step success must also exclude non-octet leading values.  The
; public decoder already rejects these during its bounded octet preflight.
(assert-event
 (and (not (fn-wildmat-result-okp (fn-wildmat-utf8-next '(-1))))
      (not (fn-wildmat-result-okp (fn-wildmat-utf8-next '(1/2))))
      (not (fn-wildmat-result-okp (fn-wildmat-utf8-next '(389/2 128))))
      (not (fn-wildmat-result-okp (fn-wildmat-utf8-next '(word))))))

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

; -----------------------------------------------------------------------------
; The header-value profile (decision D19)
;
; Every value below was read out of `fn-wildmat-parse-text' and
; `fn-wildmat-match-parsed' before it was written here.  RFC 2980 §2.9's join
; puts an SP in every multi-token XPAT pattern; RFC 3977 §4.1's grammar
; excludes SP because "these characters cannot occur in newsgroup names, which
; is the only current use of wildmats"; §4.3 permits the wider profile.

; `*T *t*', the joined two-token pattern of the XPAT measurement in
; planning/evidence/inn-xpat-2026-09-20.md.  The newsgroup-name entry refuses
; it and the header entry parses it as ONE pattern carrying a literal SP.
(defconst *fn-wildmat-joined* '(42 84 32 42 116 42))
(assert-event (equal (fn-wildmat-parse *fn-wildmat-joined*) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse-text *fn-wildmat-joined*)
                     '(:ok ((:positive (42 84 32 42 116 42))))))

; ... and it matches exactly where INN 2.7.4's uwildmat_simple matches: not
; "Test", which has no SP, and yes "T st", which does.  Those are the same two
; answers the foreign client gave for the same pattern.
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value
                       (fn-wildmat-parse-text *fn-wildmat-joined*))
                      '(84 101 115 116))
                     '(:ok nil)))
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value
                       (fn-wildmat-parse-text *fn-wildmat-joined*))
                      '(84 32 115 116))
                     '(:ok t)))

; A phrase pattern against a phrase value: "*Hello *world*" over
; "Hello there world".  This is XPAT's ordinary use and it was unreachable.
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value
                       (fn-wildmat-parse-text
                        '(42 72 101 108 108 111 32 42 119 111 114 108 100 42)))
                      '(72 101 108 108 111 32 116 104 101 114 101 32 119 111
                        114 108 100))
                     '(:ok t)))

; The three other code points the profile adds, and no more.  `[PATCH]' is an
; ordinary Subject tag; §4.1 reserves the brackets and the backslash, so the
; newsgroup-name entry still refuses them.
(assert-event (equal (fn-wildmat-parse-text '(91 80 65 84 67 72 93))
                     '(:ok ((:positive (91 80 65 84 67 72 93))))))
(assert-event (equal (fn-wildmat-parse '(91 80 65 84 67 72 93))
                     '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse-text '(92)) '(:ok ((:positive (92))))))
(assert-event (equal (fn-wildmat-parse '(92)) '(:error :syntax)))

; The four metacharacters are metacharacters in BOTH profiles, and a control
; octet and DEL are literals in neither.  A `!' is still only the post-comma
; negation marker and is still not an item anywhere.
(assert-event (equal (fn-wildmat-parse-text '(33 97)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse-text '(9)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse-text '(127)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse-text '(97 44 33 98))
                     '(:ok ((:positive (97)) (:negative (98))))))
(assert-event (not (fn-wildmat-text-exactp 33)))
(assert-event (not (fn-wildmat-text-exactp 42)))
(assert-event (not (fn-wildmat-text-exactp 44)))
(assert-event (not (fn-wildmat-text-exactp 63)))

; DIVERGENCE from INN, recorded and deliberately unchanged by D19: `,' is
; wildmat alternation in fn and a literal in INN's uwildmat_simple.  §2.9's
; "At least one pattern in wildmat must be specified" is on fn's side.  44 is
; an exact item in neither profile, so the header profile does not move it.
(assert-event (equal (fn-wildmat-parse-text '(42 84 44 42 116 42))
                     '(:ok ((:positive (42 84)) (:positive (42 116 42))))))
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value
                       (fn-wildmat-parse-text '(42 84 44 42 116 42)))
                      '(84 101 115 116))
                     '(:ok t)))

; The remaining row of the INN 2.7.4 measurement: `* *' joined from two bare
; stars.  INN answers false for "Test", and so does fn, for the same reason --
; the target carries no SP.  With those, fn and INN agree on five of the six
; rows of planning/evidence/inn-xpat-2026-09-20.md and differ only on the
; comma, where RFC 2980 is on fn's side.
(assert-event (equal (fn-wildmat-parse-text '(42 32 42))
                     '(:ok ((:positive (42 32 42))))))
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value (fn-wildmat-parse-text '(42 32 42)))
                      '(84 101 115 116))
                     '(:ok nil)))
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value (fn-wildmat-parse-text '(42 32 42)))
                      '(84 32 115 116))
                     '(:ok t)))
(assert-event (equal (fn-wildmat-match-parsed
                      (fn-wildmat-result-value (fn-wildmat-parse-text '(42 84 42)))
                      '(84 101 115 116))
                     '(:ok t)))

; The newsgroup-name path is where it was: a group wildmat still matches a
; group name, and SP alone is still not a wildmat there.
(assert-event (equal (fn-wildmat-match '(102 110 46 42)
                                       '(102 110 46 108 101 116 116 101 114
                                         115))
                     '(:ok t)))
(assert-event (equal (fn-wildmat-parse '(32)) '(:error :syntax)))
(assert-event (equal (fn-wildmat-parse-text '(32)) '(:ok ((:positive (32))))))
