; fn: teeth for books/octet-text.lisp.
;
; What this book is evidence FOR.  Every keystone of octet-text gets a
; ground positive witness asserting its complete antecedent and conclusion,
; and for each hypothesis a witness on which every retained hypothesis
; holds, the omitted one fails, and the conclusion fails.  The RFC 4648
; section 10 test vectors pin the encoders to the standard, not to
; themselves.  The in-place twins are run on a live local buffer, the way
; the host runs them, and compared with their list models.

(in-package "ACL2")
(include-book "../../books/octet-text")
(include-book "must-fail-checked")

(defun ott-oct-chars (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs) (cons (char-code (car cs)) (ott-oct-chars (cdr cs))) nil))

(defun ott (s)
  (declare (xargs :guard (stringp s)))
  (ott-oct-chars (coerce s 'list)))


;; The decoders return (mv err value); a test form reads them as a list.
(defun ott-hexd (xs) (declare (xargs :guard t)) (mv-list 2 (fn-ot-hex-decode xs)))
(defun ott-b64d (xs) (declare (xargs :guard t)) (mv-list 2 (fn-ot-b64-decode xs)))
(defun ott-split (xs limit) (declare (xargs :guard (natp limit))) (mv-list 2 (fn-ot-split-wsp xs limit)))

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(defun ott-compliant (names wrld)
  (declare (xargs :mode :program))
  (or (atom names)
      (and (eq (symbol-class (car names) wrld) :common-lisp-compliant)
           (ott-compliant (cdr names) wrld))))

(assert-event
 (ott-compliant
  '(fn-ot-digitp fn-ot-upperp fn-ot-lowerp fn-ot-alphap fn-ot-wspp
    fn-ot-hex-value fn-ot-radixp fn-ot-digit-value fn-ot-hex-digit
    fn-ot-hex-digit-upper fn-ot-maxp fn-ot-nat-parse-aux fn-ot-nat-parse
    fn-ot-decimal-parse fn-ot-hexnat-parse fn-ot-digitsp fn-ot-nat-digits
    fn-ot-nat-octets fn-ot-decimal-octets fn-ot-hexnat-octets fn-ot-octet-fix
    fn-ot-hex-encode fn-ot-hex-decode fn-ot-b64-sextet fn-ot-b64-value
    fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last
    fn-ot-b64-c2-last fn-ot-b64-encode fn-ot-b64-quantum
    fn-ot-b64-quantum-octets fn-ot-b64-decode fn-ot-downcase-octet
    fn-ot-upcase-octet fn-ot-downcase fn-ot-upcase fn-ot-ci-equal
    fn-ot-drop-wsp fn-ot-token fn-ot-after-token fn-ot-split-wsp
    fn-ot-strip-wsp fn-ot-concat fn-ot-no-wspp fn-ot-tokensp fn-ot-spanp
    fn-ot-nat-parse-aux-at fn-ot-nat-parse-at fn-ot-decimal-parse-at
    fn-ot-hexnat-parse-at fn-ot-hex-decode-at fn-ot-b64-decode-at
    fn-ot-downcase-at fn-ot-ci-equal-at fn-ot-drop-wsp-at fn-ot-token-end-at
    fn-ot-split-wsp-at fn-ot-append-nat fn-ot-append-decimal fn-ot-append-hex
    fn-ot-append-b64)
  (w state)))

; -----------------------------------------------------------------------------
; RFC 4648 section 10 test vectors (BASE64 and BASE16).

(defconst *ott-vectors*
  '(("" "" "")
    ("f" "Zg==" "66")
    ("fo" "Zm8=" "666f")
    ("foo" "Zm9v" "666f6f")
    ("foob" "Zm9vYg==" "666f6f62")
    ("fooba" "Zm9vYmE=" "666f6f6261")
    ("foobar" "Zm9vYmFy" "666f6f626172")))

(defun ott-vectors-ok (vs)
  (declare (xargs :mode :program))
  (or (atom vs)
      (let ((plain (ott (first (car vs))))
            (b64 (ott (second (car vs))))
            (b16 (ott (third (car vs)))))
        (and (equal (fn-ot-b64-encode plain) b64)
             (equal (ott-b64d b64) (list nil plain))
             (equal (fn-ot-hex-encode plain) b16)
             (equal (ott-hexd b16) (list nil plain))
             (equal (ott-hexd (fn-ot-upcase b16)) (list nil plain))
             (ott-vectors-ok (cdr vs))))))

(assert-event (ott-vectors-ok *ott-vectors*))

; -----------------------------------------------------------------------------
; fn-ot-nat-parse-of-nat-octets:
;   (natp n) (fn-ot-radixp r) (or (null max) (and (natp max) (<= n max)))
;   => (fn-ot-nat-parse (fn-ot-nat-octets n r) r max) = n

(assert-event                           ; positive, bounded and unbounded
 (and (natp 18446744073709551615) (fn-ot-radixp 10) (natp 18446744073709551615)
      (equal (fn-ot-decimal-octets 18446744073709551615) (ott "18446744073709551615"))
      (equal (fn-ot-nat-parse (fn-ot-nat-octets 18446744073709551615 10) 10
                              18446744073709551615)
             18446744073709551615)
      (equal (fn-ot-nat-parse (fn-ot-nat-octets 0 10) 10 nil) 0)
      (equal (fn-ot-hexnat-octets 48879) (ott "beef"))
      (equal (fn-ot-nat-parse (fn-ot-nat-octets 48879 16) 16 nil) 48879)
      (equal (fn-ot-nat-parse (fn-ot-nat-octets 5 2) 2 nil) 5)))

(assert-event                           ; the bound omitted: n > max
 (and (natp 1000) (fn-ot-radixp 10)
      (not (or (null 999) (and (natp 999) (<= 1000 999))))
      (not (equal (fn-ot-nat-parse (fn-ot-nat-octets 1000 10) 10 999) 1000))))

;; The theorem's term outside its guard, evaluated in the logic.
(defun ott-nat-round-trip (n r max)
  (declare (xargs :verify-guards nil))
  (fn-ot-nat-parse (fn-ot-nat-octets n r) r max))

(assert-event                           ; the radix omitted: 17 prints "0"
 (and (natp 20) (not (fn-ot-radixp 17)) (null nil)
      (not (equal (with-guard-checking :none (ott-nat-round-trip 20 17 nil)) 20))))

(assert-event                           ; natp omitted: -3 is not printed
 (and (not (natp -3)) (fn-ot-radixp 10) (null nil)
      (not (equal (fn-ot-nat-parse (fn-ot-nat-octets -3 10) 10 nil) -3))))

; fn-ot-nat-parse-bounded: (natp max), accepted => <= max.
(assert-event
 (and (natp 65535) (fn-ot-decimal-parse (ott "65535") 65535)
      (<= (fn-ot-decimal-parse (ott "65535") 65535) 65535)
      ; the refusal one past it
      (null (fn-ot-decimal-parse (ott "65536") 65535))
      ; leading zeros accepted, value unchanged
      (equal (fn-ot-decimal-parse (ott "0042") nil) 42)
      ; not digits, empty, a sign: refused
      (null (fn-ot-decimal-parse (ott "4x2") nil))
      (null (fn-ot-decimal-parse nil nil))
      (null (fn-ot-decimal-parse (ott "-1") nil))
      (null (fn-ot-decimal-parse (ott "a") nil))
      (equal (fn-ot-hexnat-parse (ott "BeEf") nil) 48879)))

(assert-event                           ; (natp max) omitted: nil bounds nothing
 (and (not (natp nil))
      (fn-ot-decimal-parse (ott "70000") nil)
      (not (<= (fn-ot-decimal-parse (ott "70000") nil) 65535))))

; -----------------------------------------------------------------------------
; fn-ot-hex-decode-of-encode: (fn-cbor-octet-listp xs) => decode (encode xs) = (mv nil xs)

(assert-event
 (and (fn-cbor-octet-listp '(0 15 16 255))
      (equal (fn-ot-hex-encode '(0 15 16 255)) (ott "000f10ff"))
      (equal (ott-hexd (fn-ot-hex-encode '(0 15 16 255))) (list nil '(0 15 16 255)))))

(assert-event                           ; octet-listp omitted
 (and (not (fn-cbor-octet-listp '(256)))
      (not (equal (ott-hexd (fn-ot-hex-encode '(256))) (list nil '(256))))))

; The refusals, named.
(assert-event
 (and (equal (ott-hexd (ott "abc")) (list :hex-odd nil))
      (equal (ott-hexd (ott "ag")) (list :hex-digit nil))
      (equal (ott-hexd (ott "a g0")) (list :hex-digit nil))))

;; fn-ot-hex-decode-length: accepted => len = 2 * decoded.
(assert-event
 (and (not (mv-nth 0 (ott-hexd (ott "0a0b"))))
      (equal (len (ott "0a0b")) (* 2 (len (mv-nth 1 (ott-hexd (ott "0a0b"))))))))

(assert-event                           ; accepted omitted: odd length
 (and (mv-nth 0 (ott-hexd (ott "0a0")))
      (not (equal (len (ott "0a0")) (* 2 (len (mv-nth 1 (ott-hexd (ott "0a0")))))))))

; -----------------------------------------------------------------------------
; fn-ot-b64-decode-of-encode: (fn-cbor-octet-listp xs) => decode (encode xs) = (mv nil xs)

(defconst *ott-bytes* '(0 1 2 3 127 128 200 254 255 63 62 61 97))

(assert-event
 (and (fn-cbor-octet-listp *ott-bytes*)
      (equal (ott-b64d (fn-ot-b64-encode *ott-bytes*)) (list nil *ott-bytes*))
      (equal (ott-b64d (fn-ot-b64-encode (cdr *ott-bytes*))) (list nil (cdr *ott-bytes*)))
      (equal (ott-b64d (fn-ot-b64-encode (cddr *ott-bytes*))) (list nil (cddr *ott-bytes*)))))

(assert-event                           ; octet-listp omitted
 (and (not (fn-cbor-octet-listp '(300 1)))
      (not (equal (ott-b64d (fn-ot-b64-encode '(300 1))) (list nil '(300 1))))))

; fn-ot-b64-accepted-is-canonical: accepted, true-list => encode (decode xs) = xs.
(assert-event
 (and (not (mv-nth 0 (ott-b64d (ott "Zm9vYg=="))))
      (true-listp (ott "Zm9vYg=="))
      (equal (fn-ot-b64-encode (mv-nth 1 (ott-b64d (ott "Zm9vYg==")))) (ott "Zm9vYg=="))))

(assert-event                           ; accepted omitted: nonzero padding bits
 (and (equal (mv-nth 0 (ott-b64d (ott "Zm9vYh=="))) :b64-padding-bits)
      (true-listp (ott "Zm9vYh=="))
      (not (equal (fn-ot-b64-encode (mv-nth 1 (ott-b64d (ott "Zm9vYh=="))))
                  (ott "Zm9vYh==")))))

(assert-event                           ; true-listp omitted
 (and (not (mv-nth 0 (ott-b64d (list* 90 103 61 61 7))))
      (not (true-listp (list* 90 103 61 61 7)))
      (not (equal (fn-ot-b64-encode (mv-nth 1 (ott-b64d (list* 90 103 61 61 7))))
                  (list* 90 103 61 61 7)))))

; The refusals, named (RFC 4648 sections 3.3 and 3.5).
(assert-event
 (and (equal (ott-b64d (ott "Zm9")) (list :b64-quantum nil))         ; short
      (equal (ott-b64d (ott "Zm9vY")) (list :b64-quantum nil))
      (equal (ott-b64d (ott "Zm!v")) (list :b64-alphabet nil))       ; alphabet
      (equal (ott-b64d (ott "Zm9 ")) (list :b64-alphabet nil))       ; no WSP
      (equal (ott-b64d (ott "Zg==Zm9v")) (list :b64-alphabet nil))   ; early pad
      (equal (ott-b64d (ott "Z=9v")) (list :b64-alphabet nil))       ; pad mid-group
      (equal (ott-b64d (ott "Zh==")) (list :b64-padding-bits nil))   ; bits
      (equal (ott-b64d (ott "Zm9=")) (list :b64-padding-bits nil))))

; fn-ot-b64-refuses-outside-alphabet: (member c xs), c not in the alphabet,
; c not the pad => refused.
(assert-event
 (and (member-equal 33 (ott "Zm9vYmE!")) (not (fn-ot-b64-value 33)) (not (equal 33 61))
      (mv-nth 0 (ott-b64d (ott "Zm9vYmE!")))))
(assert-event                           ; member omitted
 (and (not (member-equal 33 (ott "Zm9v"))) (not (fn-ot-b64-value 33)) (not (equal 33 61))
      (not (mv-nth 0 (ott-b64d (ott "Zm9v"))))))
(assert-event                           ; "not in the alphabet" omitted
 (and (member-equal 90 (ott "Zm9v")) (fn-ot-b64-value 90) (not (equal 90 61))
      (not (mv-nth 0 (ott-b64d (ott "Zm9v"))))))
(assert-event                           ; "not the pad" omitted
 (and (member-equal 61 (ott "Zm8=")) (not (fn-ot-b64-value 61)) (equal 61 61)
      (not (mv-nth 0 (ott-b64d (ott "Zm8="))))))

; -----------------------------------------------------------------------------
; fn-ot-ci-equal-is-downcase-equal (no hypotheses).
(assert-event
 (and (fn-ot-ci-equal (ott "Content-Length") (ott "content-LENGTH"))
      (equal (fn-ot-downcase (ott "Content-Length")) (fn-ot-downcase (ott "content-LENGTH")))
      ; only A-Z fold: "@" (64) and "`" (96) differ by 32 and stay distinct
      (not (fn-ot-ci-equal (ott "@") (ott "`")))
      (not (fn-ot-ci-equal (ott "[") (ott "{")))
      (not (fn-ot-ci-equal (ott "ab") (ott "abc")))
      (equal (fn-ot-upcase (ott "group fn.Test")) (ott "GROUP FN.TEST"))))

; -----------------------------------------------------------------------------
; fn-ot-split-wsp-loses-nothing: accepted => tokens, concat = strip, <= limit.
(assert-event
 (let ((r (ott-split (ott "  GROUP	 fn.test ") 2)))
   (and (not (mv-nth 0 r))
        (equal (mv-nth 1 r) (list (ott "GROUP") (ott "fn.test")))
        (fn-ot-tokensp (mv-nth 1 r))
        (equal (fn-ot-concat (mv-nth 1 r)) (fn-ot-strip-wsp (ott "  GROUP	 fn.test ")))
        (<= (len (mv-nth 1 r)) 2))))

(assert-event                           ; accepted omitted: one past the limit
 (let ((r (ott-split (ott "LIST ACTIVE fn.*") 2)))
   (and (equal (mv-nth 0 r) :too-many-tokens)
        (not (equal (fn-ot-concat (mv-nth 1 r)) (fn-ot-strip-wsp (ott "LIST ACTIVE fn.*")))))))

(assert-event                           ; empty and all-WSP inputs: no tokens
 (and (equal (ott-split nil 0) (list nil nil))
      (equal (ott-split (ott " 	 ") 0) (list nil nil))))

; The limit is load-bearing: without the refusal the split would truncate.
(must-fail-checked
 (defthm ott-false-split-never-refuses
   (not (mv-nth 0 (ott-split xs limit)))))

; -----------------------------------------------------------------------------
; The twins on a live buffer, against their list models on the same slice.

(defconst *ott-buffer*
  (ott "XX 1234567 00ff10 Zm9vYmFy Content-Length  GROUP  fn.test YY"))

(defun ott-run (fn-octets)
  (declare (xargs :stobjs fn-octets :mode :program))
  (let ((fn-octets (fn-octets-from-list *ott-buffer* fn-octets)))
    (mv (list (fn-ot-decimal-parse-at 3 10 nil fn-octets)
              (fn-ot-decimal-parse-at 3 10 1234566 fn-octets)
              (fn-ot-hexnat-parse-at 11 17 nil fn-octets)
              (mv-list 2 (fn-ot-hex-decode-at 11 17 fn-octets))
              (mv-list 2 (fn-ot-hex-decode-at 11 16 fn-octets))
              (mv-list 2 (fn-ot-b64-decode-at 18 26 fn-octets))
              (mv-list 2 (fn-ot-b64-decode-at 18 25 fn-octets))
              (fn-ot-ci-equal-at 27 41 (ott "CONTENT-LENGTH") fn-octets)
              (fn-ot-downcase-at 27 34 fn-octets)
              (mv-list 2 (fn-ot-split-wsp-at 41 57 2 fn-octets))
              (mv-list 2 (fn-ot-split-wsp-at 41 57 1 fn-octets))
              (fn-ot-drop-wsp-at 41 57 fn-octets)
              (fn-ot-token-end-at 43 57 fn-octets))
        fn-octets)))

(defun ott-run-value ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (ott-run fn-octets) v)))

(defun ott-slice (i n) (declare (xargs :mode :program)) (take (- n i) (nthcdr i *ott-buffer*)))

(assert-event
 (equal (ott-run-value)
        (list 1234567 nil 65296 (list nil '(0 255 16)) (list :hex-odd nil)
              (list nil (ott "foobar")) (list :b64-quantum nil) t (ott "content")
              (list nil (list (ott "GROUP") (ott "fn.test")))
              (list :too-many-tokens nil)
              43 48)))

(assert-event
 (equal (ott-run-value)
        (list (fn-ot-decimal-parse (ott-slice 3 10) nil)
              (fn-ot-decimal-parse (ott-slice 3 10) 1234566)
              (fn-ot-hexnat-parse (ott-slice 11 17) nil)
              (ott-hexd (ott-slice 11 17))
              (ott-hexd (ott-slice 11 16))
              (ott-b64d (ott-slice 18 26))
              (ott-b64d (ott-slice 18 25))
              (fn-ot-ci-equal (ott-slice 27 41) (ott "CONTENT-LENGTH"))
              (fn-ot-downcase (ott-slice 27 34))
              (ott-split (ott-slice 41 57) 2)
              (ott-split (ott-slice 41 57) 1)
              (+ 41 (- (len (ott-slice 41 57)) (len (fn-ot-drop-wsp (ott-slice 41 57)))))
              (+ 43 (len (fn-ot-token (ott-slice 43 57)))))))

; The encoders' buffer twins append exactly the list model's octets.
(defun ott-append-run (fn-octets)
  (declare (xargs :stobjs fn-octets :mode :program))
  (let* ((fn-octets (fn-octets-from-list (ott "n=") fn-octets))
         (fn-octets (fn-ot-append-decimal 3977 fn-octets))
         (fn-octets (fn-octets-append-list (ott " ") fn-octets))
         (fn-octets (fn-ot-append-hex '(222 173) fn-octets))
         (fn-octets (fn-octets-append-list (ott " ") fn-octets))
         (fn-octets (fn-ot-append-b64 (ott "fo") fn-octets)))
    (mv (fn-octets-list fn-octets) fn-octets)))

(defun ott-append-run-value ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (ott-append-run fn-octets) v)))

(assert-event (equal (ott-append-run-value) (ott "n=3977 dead Zm8=")))
