; fn: octet text -- the small textual codecs every wire book re-derived.
;
; Decimal and hexadecimal naturals, hex octet strings, base64 (RFC 4648
; section 4), ASCII case folding and case-insensitive equality, and
; whitespace token splitting, each as
;
;   a list model     over octet lists (the logical model of every codec, D27);
;   an in-place twin `...-at' that reads st[i..n) of the octet buffer
;                    (books/octets-stobj.lisp, or any abstract stobj declared
;                    `:congruent-to fn-octets') without consing the input;
;   the boundary     `...-at-is-...': the twin equals the list model on
;                    (take (- n i) (nthcdr i st)), the buffer's logical slice;
;
; and every executable function guard-verified.  Encoders take a list (their
; input already is one) and have an `fn-ot-append-...' twin that writes the
; encoding into the buffer in one `fn-octets-append-list' call (PKT-315).
;
; Keystones:
;   fn-ot-nat-parse-of-nat-octets    parse (print n) = n, any radix 2..16,
;                                    under the bound MAX
;   fn-ot-nat-parse-bounded          an accepted natural is <= MAX
;   fn-ot-hex-decode-of-encode       hex decode (encode xs) = xs
;   fn-ot-b64-decode-of-encode       base64 decode (encode xs) = xs
;   fn-ot-b64-accepted-is-canonical  an accepted base64 text is the encoding
;                                    of what it decodes to: padding bits zero,
;                                    the pad only in the last quantum
;   fn-ot-b64-refuses-outside-alphabet  and the refusal kinds, named
;   fn-ot-ci-equal-is-downcase-equal case-insensitive equality is equality
;                                    of the ASCII case folds
;   fn-ot-split-wsp-loses-nothing    the tokens are the input's non-WSP
;                                    octets, in order, and at most LIMIT of
;                                    them; more is the refusal
;                                    :too-many-tokens, never a truncation
;
; Bounds (D27).  No function here caps the data: a parse takes the caller's
; MAX (the operator profile's admission limit; nil when the length already
; bounds it), a split takes the caller's LIMIT and refuses past it.  Work is
; linear in the slice read.  Leading zeros are accepted by the natural
; parsers (RFC 9110 Content-Length, RFC 3977 numbers); the printers never
; emit them.
;
; The base64 alphabet functions are books/stx-carrier.lisp's (the same
; ranges, the same inverse laws); that book keeps its own copies for now,
; see the lane notes.

(in-package "ACL2")
(include-book "octets-stobj")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; Octet classes (RFC 5234 appendix B.1).

(defun fn-ot-digitp (o)
  (declare (xargs :guard t))
  (and (integerp o) (<= 48 o) (<= o 57)))

(defun fn-ot-upperp (o)
  (declare (xargs :guard t))
  (and (integerp o) (<= 65 o) (<= o 90)))

(defun fn-ot-lowerp (o)
  (declare (xargs :guard t))
  (and (integerp o) (<= 97 o) (<= o 122)))

(defun fn-ot-alphap (o)
  (declare (xargs :guard t))
  (or (fn-ot-upperp o) (fn-ot-lowerp o)))

; WSP: SP or HTAB.
(defun fn-ot-wspp (o)
  (declare (xargs :guard t))
  (or (equal o 32) (equal o 9)))

; -----------------------------------------------------------------------------
; Digits.  A digit's value is its hexadecimal value (either case); in radix
; R only values below R are digits.  The printers emit lower case.

(defun fn-ot-hex-value (o)
  (declare (xargs :guard t))
  (cond ((fn-ot-digitp o) (- o 48))
        ((and (integerp o) (<= 65 o) (<= o 70)) (- o 55))
        ((and (integerp o) (<= 97 o) (<= o 102)) (- o 87))
        (t nil)))

(defthm fn-ot-hex-value-type
  (or (null (fn-ot-hex-value o))
      (and (natp (fn-ot-hex-value o)) (< (fn-ot-hex-value o) 16)))
  :rule-classes ((:type-prescription :corollary
                  (or (null (fn-ot-hex-value o)) (natp (fn-ot-hex-value o))))
                 (:linear :corollary
                  (implies (fn-ot-hex-value o) (< (fn-ot-hex-value o) 16)))))

(defun fn-ot-radixp (r)
  (declare (xargs :guard t))
  (and (integerp r) (<= 2 r) (<= r 16)))

(defun fn-ot-digit-value (o radix)
  (declare (xargs :guard t))
  (let ((v (fn-ot-hex-value o)))
    (and v (integerp radix) (< v radix) v)))

(defthm fn-ot-digit-value-type
  (or (null (fn-ot-digit-value o r))
      (natp (fn-ot-digit-value o r)))
  :rule-classes :type-prescription)

(defthm fn-ot-digit-value-bound
  (implies (fn-ot-digit-value o r)
           (< (fn-ot-digit-value o r) r))
  :rule-classes :linear)

(defun fn-ot-hex-digit (d)
  ; The lower-case digit of 0 <= d < 16 (anything else prints as 0).
  (declare (xargs :guard t))
  (if (and (natp d) (< d 16)) (if (< d 10) (+ 48 d) (+ 87 d)) 48))

(defun fn-ot-hex-digit-upper (d)
  ; The upper-case digit, for RFC 3986 section 2.1 percent-encoding.
  (declare (xargs :guard t))
  (if (and (natp d) (< d 16)) (if (< d 10) (+ 48 d) (+ 55 d)) 48))

(defthm fn-ot-hex-digit-is-octet
  (and (fn-cbor-octetp (fn-ot-hex-digit d))
       (fn-cbor-octetp (fn-ot-hex-digit-upper d))))

(defthm fn-ot-hex-value-of-hex-digit
  (implies (and (natp d) (< d 16))
           (and (equal (fn-ot-hex-value (fn-ot-hex-digit d)) d)
                (equal (fn-ot-hex-value (fn-ot-hex-digit-upper d)) d))))

(defthm fn-ot-digit-value-of-hex-digit
  (implies (and (natp d) (< d r) (fn-ot-radixp r))
           (equal (fn-ot-digit-value (fn-ot-hex-digit d) r) d)))

;; The digit 0 as the constant it evaluates to.
(defthm fn-ot-digit-value-of-zero-digit
  (implies (fn-ot-radixp r)
           (equal (fn-ot-digit-value 48 r) 0)))

(in-theory (disable fn-ot-hex-value fn-ot-digit-value fn-ot-hex-digit
                    fn-ot-hex-digit-upper))

; -----------------------------------------------------------------------------
; Naturals in radix 2..16: parse (1*DIGIT, value <= MAX, MAX nil = unbounded)
; and print (no leading zeros).  The parse refuses with nil.

(defun fn-ot-maxp (max)
  (declare (xargs :guard t))
  (or (null max) (natp max)))

(defun fn-ot-nat-parse-aux (xs radix max acc)
  (declare (xargs :guard (and (fn-ot-radixp radix) (fn-ot-maxp max) (natp acc))))
  (if (consp xs)
      (let ((v (fn-ot-digit-value (car xs) radix)))
        (and v
             (let ((acc2 (+ (* (nfix radix) (nfix acc)) v)))
               (and (or (null max) (<= acc2 (nfix max)))
                    (fn-ot-nat-parse-aux (cdr xs) radix max acc2)))))
    (nfix acc)))

(defun fn-ot-nat-parse (xs radix max)
  (declare (xargs :guard (and (fn-ot-radixp radix) (fn-ot-maxp max))))
  (and (consp xs) (fn-ot-nat-parse-aux xs radix max 0)))

(defun fn-ot-decimal-parse (xs max)
  (declare (xargs :guard (fn-ot-maxp max)))
  (fn-ot-nat-parse xs 10 max))

(defun fn-ot-hexnat-parse (xs max)
  (declare (xargs :guard (fn-ot-maxp max)))
  (fn-ot-nat-parse xs 16 max))

(defthm fn-ot-nat-parse-aux-type
  (or (null (fn-ot-nat-parse-aux xs r max acc))
      (natp (fn-ot-nat-parse-aux xs r max acc)))
  :rule-classes :type-prescription)

(defthm fn-ot-nat-parse-type
  (or (null (fn-ot-nat-parse xs r max))
      (natp (fn-ot-nat-parse xs r max)))
  :rule-classes :type-prescription)

(defthm fn-ot-nat-parse-aux-bounded
  (implies (and (natp max) (<= (nfix acc) max)
                (fn-ot-nat-parse-aux xs r max acc))
           (<= (fn-ot-nat-parse-aux xs r max acc) max))
  :rule-classes nil)

; Keystone: an accepted natural is within the caller's bound.
(defthm fn-ot-nat-parse-bounded
  (implies (and (natp max) (fn-ot-nat-parse xs r max))
           (<= (fn-ot-nat-parse xs r max) max))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-ot-nat-parse-aux-bounded (acc 0))))))

; Every octet of an accepted text is a digit of the radix.
(defun fn-ot-digitsp (xs r)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-ot-digit-value (car xs) r) (fn-ot-digitsp (cdr xs) r) t)
    t))

(defthm fn-ot-nat-parse-aux-digits
  (implies (fn-ot-nat-parse-aux xs r max acc)
           (fn-ot-digitsp xs r)))

(defthm fn-ot-nat-parse-accepts-only-digits
  (implies (fn-ot-nat-parse xs r max)
           (and (consp xs) (fn-ot-digitsp xs r))))

; The printer, tail-recursive from the least significant digit.
(defun fn-ot-nat-digits (n radix acc)
  (declare (xargs :guard (and (natp n) (fn-ot-radixp radix))
                  :measure (nfix n)))
  (if (or (zp n) (not (fn-ot-radixp radix)) (< n radix))
      (cons (fn-ot-hex-digit (nfix n)) acc)
    (fn-ot-nat-digits (floor n radix) radix
                      (cons (fn-ot-hex-digit (mod n radix)) acc))))

(defun fn-ot-nat-octets (n radix)
  (declare (xargs :guard (fn-ot-radixp radix)))
  (fn-ot-nat-digits (nfix n) radix nil))

(defun fn-ot-decimal-octets (n)
  (declare (xargs :guard t))
  (fn-ot-nat-octets n 10))

(defun fn-ot-hexnat-octets (n)
  (declare (xargs :guard t))
  (fn-ot-nat-octets n 16))

(local
 (defthm fn-ot-nat-digits-append
   (equal (fn-ot-nat-digits n r (append a b))
          (append (fn-ot-nat-digits n r a) b))))

(defthm fn-ot-nat-digits-acc
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (fn-ot-nat-digits n r acc)
                  (append (fn-ot-nat-digits n r nil) acc)))
  :hints (("Goal" :use ((:instance fn-ot-nat-digits-append (a nil) (b acc)))
           :in-theory (disable fn-ot-nat-digits-append))))

(defthm fn-ot-octet-listp-of-nat-digits
  (implies (fn-cbor-octet-listp acc)
           (fn-cbor-octet-listp (fn-ot-nat-digits n r acc))))

(defthm fn-ot-consp-of-nat-digits
  (consp (fn-ot-nat-digits n r acc))
  :rule-classes :type-prescription)

(defthm fn-ot-nat-parse-aux-of-append
  (equal (fn-ot-nat-parse-aux (append a b) r max acc)
         (let ((x (fn-ot-nat-parse-aux a r max acc)))
           (and x (fn-ot-nat-parse-aux b r max x)))))

(local
 (defthm fn-ot-floor-below
   (implies (and (natp n) (fn-ot-radixp r))
            (<= (floor n r) n))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(defthm fn-ot-nat-parse-aux-of-nat-digits
  (implies (and (natp n) (fn-ot-radixp r)
                (or (null max) (and (natp max) (<= n max))))
           (equal (fn-ot-nat-parse-aux (fn-ot-nat-digits n r nil) r max 0) n))
  :hints (("Goal" :induct (fn-ot-nat-digits n r nil))))

; Keystone: parse inverts print, in every radix, under the bound.
(defthm fn-ot-nat-parse-of-nat-octets
  (implies (and (natp n) (fn-ot-radixp r)
                (or (null max) (and (natp max) (<= n max))))
           (equal (fn-ot-nat-parse (fn-ot-nat-octets n r) r max) n)))

(in-theory (disable fn-ot-nat-digits))

; -----------------------------------------------------------------------------
; Hex octet strings: two lower-case digits per octet; decode accepts either
; case.  (mv err octets): err nil, :hex-odd (a lone final digit) or
; :hex-digit (an octet that is not a hex digit).

(defun fn-ot-octet-fix (o)
  (declare (xargs :guard t))
  (if (fn-cbor-octetp o) o 0))

(defun fn-ot-hex-encode (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (let ((o (fn-ot-octet-fix (car xs))))
        (list* (fn-ot-hex-digit (floor o 16)) (fn-ot-hex-digit (mod o 16))
               (fn-ot-hex-encode (cdr xs))))
    nil))

(defthm fn-ot-octet-listp-of-hex-encode
  (fn-cbor-octet-listp (fn-ot-hex-encode xs)))

(defthm fn-ot-len-of-hex-encode
  (equal (len (fn-ot-hex-encode xs)) (* 2 (len xs))))

(defun fn-ot-hex-decode (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) (mv nil nil))
        ((atom (cdr xs)) (mv :hex-odd nil))
        (t (let ((h (fn-ot-hex-value (car xs)))
                 (l (fn-ot-hex-value (cadr xs))))
             (if (and h l)
                 (mv-let (err rest) (fn-ot-hex-decode (cddr xs))
                   (if err
                       (mv err nil)
                     (mv nil (cons (+ (* 16 h) l) rest))))
               (mv :hex-digit nil))))))

(defthm fn-ot-hex-decode-error-kinds
  (member (mv-nth 0 (fn-ot-hex-decode xs)) '(nil :hex-odd :hex-digit)))

(defthm fn-ot-octet-listp-of-hex-decode
  (fn-cbor-octet-listp (mv-nth 1 (fn-ot-hex-decode xs))))

; An accepted text is exactly two digits per octet: an odd length is refused.
(defthm fn-ot-hex-decode-length
  (implies (not (mv-nth 0 (fn-ot-hex-decode xs)))
           (equal (len xs) (* 2 (len (mv-nth 1 (fn-ot-hex-decode xs)))))))

(local
 (defthm fn-ot-hex-split
   (implies (fn-cbor-octetp o)
            (equal (+ (* 16 (floor o 16)) (mod o 16)) o))))

(local
 (defthm fn-ot-hex-floor-bound
   (implies (fn-cbor-octetp o)
            (and (natp (floor o 16)) (< (floor o 16) 16)
                 (natp (mod o 16)) (< (mod o 16) 16)))))

; Keystone: hex decode inverts hex encode.
(defthm fn-ot-hex-decode-of-encode
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-ot-hex-decode (fn-ot-hex-encode xs))
                  (mv nil xs))))

; -----------------------------------------------------------------------------
; Base64, RFC 4648 section 4, with padding, canonical (padding bits zero).
; Alphabet by range, so the inverse laws are linear arithmetic (the
; books/stx-carrier.lisp construction).  (mv err octets): err nil,
; :b64-quantum (a final group of fewer than four), :b64-alphabet (an octet
; outside the alphabet, or a pad before the last quantum or before a
; non-pad), :b64-padding-bits (nonzero bits under the pad: RFC 4648 section
; 3.5's canonical encoding).

(defconst *fn-ot-b64-pad* 61)

(defun fn-ot-b64-sextet (n)
  (declare (xargs :guard t))
  (let ((k (nfix n)))
    (cond ((< k 26) (+ 65 k))                ; A-Z
          ((< k 52) (+ 71 k))                ; a-z
          ((< k 62) (- k 4))                 ; 0-9
          ((equal k 62) 43)                  ; +
          (t 47))))                          ; /

(defun fn-ot-b64-value (c)
  (declare (xargs :guard t))
  (cond ((and (integerp c) (<= 65 c) (<= c 90)) (- c 65))
        ((and (integerp c) (<= 97 c) (<= c 122)) (- c 71))
        ((and (integerp c) (<= 48 c) (<= c 57)) (+ c 4))
        ((equal c 43) 62)
        ((equal c 47) 63)
        (t nil)))

(defthm fn-ot-b64-sextet-is-octet
  (fn-cbor-octetp (fn-ot-b64-sextet n)))

(defthm fn-ot-b64-value-type
  (or (null (fn-ot-b64-value c))
      (and (natp (fn-ot-b64-value c)) (< (fn-ot-b64-value c) 64)))
  :rule-classes ((:type-prescription :corollary
                  (or (null (fn-ot-b64-value c)) (natp (fn-ot-b64-value c))))
                 (:linear :corollary
                  (implies (fn-ot-b64-value c) (< (fn-ot-b64-value c) 64)))))

(defthm fn-ot-b64-value-of-sextet
  (implies (and (natp n) (< n 64))
           (equal (fn-ot-b64-value (fn-ot-b64-sextet n)) n)))

(defthm fn-ot-b64-sextet-of-value
  (implies (fn-ot-b64-value c)
           (equal (fn-ot-b64-sextet (fn-ot-b64-value c)) c)))

(defthm fn-ot-b64-value-of-pad
  (equal (fn-ot-b64-value *fn-ot-b64-pad*) nil))

(defthm fn-ot-b64-sextet-is-not-pad
  (not (equal (fn-ot-b64-sextet n) *fn-ot-b64-pad*)))

(defthm fn-ot-b64-value-of-any-sextet
  (natp (fn-ot-b64-value (fn-ot-b64-sextet n)))
  :rule-classes :type-prescription)

(in-theory (disable fn-ot-b64-sextet fn-ot-b64-value))

(local (in-theory (disable floor mod)))

(local (defthm fn-ot-mod-facts
         (implies (natp x)
                  (and (natp (mod x 4)) (< (mod x 4) 4)
                       (natp (mod x 16)) (< (mod x 16) 16)
                       (natp (mod x 64)) (< (mod x 64) 64)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-floor-facts
         (implies (and (natp x) (<= x 255))
                  (and (natp (floor x 4)) (< (floor x 4) 64)
                       (natp (floor x 16)) (< (floor x 16) 16)
                       (natp (floor x 64)) (< (floor x 64) 4)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-floor-of-sextet
         (implies (and (natp v) (< v 64))
                  (and (natp (floor v 4)) (< (floor v 4) 16)
                       (natp (floor v 16)) (< (floor v 16) 4)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-split-4
         (implies (and (natp m) (natp f) (< f 4))
                  (and (equal (floor (+ (* 4 m) f) 4) m)
                       (equal (mod (+ (* 4 m) f) 4) f)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-split-16
         (implies (and (natp m) (natp f) (< f 16))
                  (and (equal (floor (+ (* 16 m) f) 16) m)
                       (equal (mod (+ (* 16 m) f) 16) f)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-split-64
         (implies (and (natp m) (natp f) (< f 64))
                  (and (equal (floor (+ (* 64 m) f) 64) m)
                       (equal (mod (+ (* 64 m) f) 64) f)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-elim
         (implies (natp a)
                  (and (equal (+ (* 4 (floor a 4)) (mod a 4)) a)
                       (equal (+ (* 16 (floor a 16)) (mod a 16)) a)
                       (equal (+ (* 64 (floor a 64)) (mod a 64)) a)))
         :hints (("Goal" :nonlinearp t))))
(local (defthm fn-ot-mod-of-times
         (implies (natp m)
                  (and (equal (mod (* 16 m) 16) 0)
                       (equal (mod (* 4 m) 4) 0)))
         :hints (("Goal" :nonlinearp t))))

(local (defthm fn-ot-mod-zero-is-multiple
         (implies (and (natp v) (equal (mod v 4) 0)) (equal (* 4 (floor v 4)) v))
         :hints (("Goal" :use ((:instance fn-ot-elim (a v)))
                  :in-theory (disable fn-ot-elim)))))
(local (defthm fn-ot-mod-zero-is-multiple-16
         (implies (and (natp v) (equal (mod v 16) 0)) (equal (* 16 (floor v 16)) v))
         :hints (("Goal" :use ((:instance fn-ot-elim (a v)))
                  :in-theory (disable fn-ot-elim)))))

(local (defthm fn-ot-floor-of-times
         (implies (natp m)
                  (and (equal (floor (* 16 m) 16) m)
                       (equal (floor (* 4 m) 4) m)))
         :hints (("Goal" :nonlinearp t))))

;; Linear forms of the bounds, and every sextet's value is defined.
(local (defthm fn-ot-floor-mod-bounds
         (implies (natp x)
                  (and (< (mod x 4) 4) (< (mod x 16) 16) (< (mod x 64) 64)))
         :rule-classes :linear))
(local (defthm fn-ot-floor-octet-bounds
         (implies (and (natp x) (<= x 255))
                  (and (< (floor x 4) 64) (< (floor x 16) 16) (< (floor x 64) 4)))
         :rule-classes :linear))
(local (defthm fn-ot-floor-sextet-bounds
         (implies (and (natp v) (< v 64))
                  (and (< (floor v 4) 16) (< (floor v 16) 4)))
         :rule-classes :linear))


;; The four sextet octets of a group, and of the two short groups.
(defun fn-ot-b64-c0 (a)
  (declare (xargs :guard t))
  (fn-ot-b64-sextet (floor (fn-ot-octet-fix a) 4)))
(defun fn-ot-b64-c1 (a b)
  (declare (xargs :guard t))
  (fn-ot-b64-sextet (+ (* 16 (mod (fn-ot-octet-fix a) 4))
                       (floor (fn-ot-octet-fix b) 16))))
(defun fn-ot-b64-c2 (b c)
  (declare (xargs :guard t))
  (fn-ot-b64-sextet (+ (* 4 (mod (fn-ot-octet-fix b) 16))
                       (floor (fn-ot-octet-fix c) 64))))
(defun fn-ot-b64-c3 (c)
  (declare (xargs :guard t))
  (fn-ot-b64-sextet (mod (fn-ot-octet-fix c) 64)))
(defun fn-ot-b64-c1-last (a)
  (declare (xargs :guard t))
  (fn-ot-b64-sextet (* 16 (mod (fn-ot-octet-fix a) 4))))
(defun fn-ot-b64-c2-last (b)
  (declare (xargs :guard t))
  (fn-ot-b64-sextet (* 4 (mod (fn-ot-octet-fix b) 16))))

(defun fn-ot-b64-encode (xs)
  (declare (xargs :guard t :measure (len xs)))
  (cond ((atom xs) nil)
        ((atom (cdr xs))
         (list (fn-ot-b64-c0 (car xs)) (fn-ot-b64-c1-last (car xs))
               *fn-ot-b64-pad* *fn-ot-b64-pad*))
        ((atom (cddr xs))
         (list (fn-ot-b64-c0 (car xs)) (fn-ot-b64-c1 (car xs) (cadr xs))
               (fn-ot-b64-c2-last (cadr xs)) *fn-ot-b64-pad*))
        (t (list* (fn-ot-b64-c0 (car xs)) (fn-ot-b64-c1 (car xs) (cadr xs))
                  (fn-ot-b64-c2 (cadr xs) (caddr xs)) (fn-ot-b64-c3 (caddr xs))
                  (fn-ot-b64-encode (cdddr xs))))))

(in-theory (disable fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3
                    fn-ot-b64-c1-last fn-ot-b64-c2-last))

;; The encoder's arithmetic, as the quantum reads it back.  Each lemma is
;; proved in a theory holding only the concrete floor/mod facts above:
;; arithmetic-5's general rules cost ten times what they contribute here.
(local
 (defmacro fn-ot-arith-theory (&rest names)
   `(union-theories '(fn-ot-split-4 fn-ot-split-16 fn-ot-split-64 fn-ot-elim
                      fn-ot-floor-facts fn-ot-mod-facts fn-ot-mod-of-times
                      fn-ot-floor-of-sextet fn-ot-mod-zero-is-multiple
                      fn-ot-mod-zero-is-multiple-16 fn-ot-floor-of-times (:type-prescription floor) (:type-prescription mod) fn-cbor-octetp natp
                      fn-ot-octet-fix fn-ot-b64-value-of-sextet
                      fn-ot-b64-sextet-of-value fn-ot-b64-value-type
                      fn-ot-b64-sextet-is-not-pad fn-ot-b64-value-of-any-sextet
                      ,@names)
                    (theory 'minimal-theory))))

(local
 (defthm fn-ot-b64-value-of-cs
   (implies (and (fn-cbor-octetp a) (fn-cbor-octetp b) (fn-cbor-octetp c))
            (and (equal (fn-ot-b64-value (fn-ot-b64-c0 a)) (floor a 4))
                 (equal (fn-ot-b64-value (fn-ot-b64-c1 a b))
                        (+ (* 16 (mod a 4)) (floor b 16)))
                 (equal (fn-ot-b64-value (fn-ot-b64-c2 b c))
                        (+ (* 4 (mod b 16)) (floor c 64)))
                 (equal (fn-ot-b64-value (fn-ot-b64-c3 c)) (mod c 64))
                 (equal (fn-ot-b64-value (fn-ot-b64-c1-last a)) (* 16 (mod a 4)))
                 (equal (fn-ot-b64-value (fn-ot-b64-c2-last b)) (* 4 (mod b 16)))))
   :hints (("Goal" :in-theory (e/d (fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3
                                    fn-ot-b64-c1-last fn-ot-b64-c2-last)
                                   (floor mod))))))

(local
 (defthm fn-ot-b64-cs-are-not-pad
   (and (not (equal (fn-ot-b64-c0 a) 61)) (not (equal (fn-ot-b64-c1 a b) 61))
        (not (equal (fn-ot-b64-c2 b c) 61)) (not (equal (fn-ot-b64-c3 c) 61))
        (not (equal (fn-ot-b64-c1-last a) 61)) (not (equal (fn-ot-b64-c2-last b) 61)))
   :hints (("Goal" :in-theory (enable fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3
                                      fn-ot-b64-c1-last fn-ot-b64-c2-last)))))

(local
 (defthm fn-ot-b64-cs-have-values
   (and (fn-ot-b64-value (fn-ot-b64-c0 a)) (fn-ot-b64-value (fn-ot-b64-c1 a b))
        (fn-ot-b64-value (fn-ot-b64-c2 b c)) (fn-ot-b64-value (fn-ot-b64-c3 c))
        (fn-ot-b64-value (fn-ot-b64-c1-last a)) (fn-ot-b64-value (fn-ot-b64-c2-last b)))
   :hints (("Goal" :in-theory (enable fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3
                                      fn-ot-b64-c1-last fn-ot-b64-c2-last)))))

(local
 (defthm fn-ot-j0
   (implies (and (fn-cbor-octetp a) (fn-cbor-octetp b))
            (equal (+ (* 4 (floor a 4)) (floor (+ (* 16 (mod a 4)) (floor b 16)) 16)) a))
   :hints (("Goal" :in-theory (fn-ot-arith-theory)))))
(local
 (defthm fn-ot-j1
   (implies (and (fn-cbor-octetp b) (fn-cbor-octetp c) (natp m) (< m 4))
            (equal (+ (* 16 (mod (+ (* 16 m) (floor b 16)) 16))
                      (floor (+ (* 4 (mod b 16)) (floor c 64)) 4))
                   b))
   :hints (("Goal" :in-theory (fn-ot-arith-theory)))))
(local
 (defthm fn-ot-j2
   (implies (and (fn-cbor-octetp c) (natp m) (< m 16))
            (equal (+ (* 64 (mod (+ (* 4 m) (floor c 64)) 4)) (mod c 64)) c))
   :hints (("Goal" :in-theory (fn-ot-arith-theory)))))
(local
 (defthm fn-ot-j0-short
   (implies (fn-cbor-octetp a)
            (and (equal (+ (* 4 (floor a 4)) (mod a 4)) a)
                 (equal (mod (* 16 (mod a 4)) 16) 0)))
   :hints (("Goal" :in-theory (fn-ot-arith-theory)
))))
(local
 (defthm fn-ot-j1-short
   (implies (and (fn-cbor-octetp b) (natp m) (< m 4))
            (and (equal (+ (* 16 (mod (+ (* 16 m) (floor b 16)) 16)) (mod b 16))
                        b)
                 (equal (mod (* 4 (mod b 16)) 4) 0)))
   :hints (("Goal" :in-theory (fn-ot-arith-theory)
))))
(local
 (defthm fn-ot-mod-a-4-bounds
   (implies (fn-cbor-octetp a)
            (and (natp (mod a 4)) (< (mod a 4) 4) (natp (mod a 16)) (< (mod a 16) 16)))
   :hints (("Goal" :in-theory (fn-ot-arith-theory)))))


(defthm fn-ot-octet-listp-of-b64-encode
  (fn-cbor-octet-listp (fn-ot-b64-encode xs))
  :hints (("Goal" :in-theory (enable fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3
                                     fn-ot-b64-c1-last fn-ot-b64-c2-last))))

; One quantum: four octets C0..C3, LAST when nothing follows them.
; (mv err k o0 o1 o2): K octets decoded (1..3).
(defun fn-ot-b64-quantum (c0 c1 c2 c3 last)
  (declare (xargs :guard t))
  (let ((v0 (fn-ot-b64-value c0))
        (v1 (fn-ot-b64-value c1)))
    (if (or (null v0) (null v1))
        (mv :b64-alphabet 0 0 0 0)
      (if (and last (equal c2 *fn-ot-b64-pad*) (equal c3 *fn-ot-b64-pad*))
          (if (not (equal (mod v1 16) 0))
              (mv :b64-padding-bits 0 0 0 0)
            (mv nil 1 (+ (* 4 v0) (floor v1 16)) 0 0))
        (let ((v2 (fn-ot-b64-value c2)))
          (if (null v2)
              (mv :b64-alphabet 0 0 0 0)
            (if (and last (equal c3 *fn-ot-b64-pad*))
                (if (not (equal (mod v2 4) 0))
                    (mv :b64-padding-bits 0 0 0 0)
                  (mv nil 2 (+ (* 4 v0) (floor v1 16))
                      (+ (* 16 (mod v1 16)) (floor v2 4)) 0))
              (let ((v3 (fn-ot-b64-value c3)))
                (if (null v3)
                    (mv :b64-alphabet 0 0 0 0)
                  (mv nil 3 (+ (* 4 v0) (floor v1 16))
                      (+ (* 16 (mod v1 16)) (floor v2 4))
                      (+ (* 64 (mod v2 4)) v3)))))))))))

(defun fn-ot-b64-quantum-octets (k o0 o1 o2 rest)
  (declare (xargs :guard t))
  (cond ((equal k 1) (list o0))
        ((equal k 2) (list o0 o1))
        (t (list* o0 o1 o2 rest))))

(in-theory (disable fn-ot-b64-quantum))

(defthm fn-ot-b64-quantum-octets-range
  (and (integerp (mv-nth 2 (fn-ot-b64-quantum c0 c1 c2 c3 last)))
       (<= 0 (mv-nth 2 (fn-ot-b64-quantum c0 c1 c2 c3 last)))
       (< (mv-nth 2 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 256)
       (integerp (mv-nth 3 (fn-ot-b64-quantum c0 c1 c2 c3 last)))
       (<= 0 (mv-nth 3 (fn-ot-b64-quantum c0 c1 c2 c3 last)))
       (< (mv-nth 3 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 256)
       (integerp (mv-nth 4 (fn-ot-b64-quantum c0 c1 c2 c3 last)))
       (<= 0 (mv-nth 4 (fn-ot-b64-quantum c0 c1 c2 c3 last)))
       (< (mv-nth 4 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 256))
  :rule-classes
  (:rewrite
   (:linear :corollary
    (and (< (mv-nth 2 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 256)
         (< (mv-nth 3 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 256)
         (< (mv-nth 4 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 256))))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum))))

;; The quantum's laws.  The encoder's groups decode to their octets
;; (a full group whatever LAST says: no sextet is the pad) ...
(defthm fn-ot-b64-quantum-of-three
  (implies (and (fn-cbor-octetp a) (fn-cbor-octetp b) (fn-cbor-octetp c))
           (equal (fn-ot-b64-quantum
                   (fn-ot-b64-c0 a) (fn-ot-b64-c1 a b)
                   (fn-ot-b64-c2 b c) (fn-ot-b64-c3 c)
                   last)
                  (mv nil 3 a b c)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (fn-ot-arith-theory fn-ot-b64-quantum fn-ot-b64-value-of-cs
                                                  fn-ot-b64-cs-are-not-pad
                                                  fn-ot-b64-cs-have-values
                                                  fn-ot-j0 fn-ot-j1 fn-ot-j2 fn-ot-j0-short
                                                  fn-ot-j1-short fn-ot-mod-a-4-bounds)
                              '(fn-cbor-octetp)))))

(defthm fn-ot-b64-quantum-of-two
  (implies (and (fn-cbor-octetp a) (fn-cbor-octetp b))
           (equal (fn-ot-b64-quantum
                   (fn-ot-b64-c0 a) (fn-ot-b64-c1 a b)
                   (fn-ot-b64-c2-last b)
                   *fn-ot-b64-pad*
                   t)
                  (mv nil 2 a b 0)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (fn-ot-arith-theory fn-ot-b64-quantum fn-ot-b64-value-of-cs
                                                  fn-ot-b64-cs-are-not-pad
                                                  fn-ot-b64-cs-have-values
                                                  fn-ot-j0 fn-ot-j1 fn-ot-j2 fn-ot-j0-short
                                                  fn-ot-j1-short fn-ot-mod-a-4-bounds)
                              '(fn-cbor-octetp)))))

(defthm fn-ot-b64-quantum-of-one
  (implies (fn-cbor-octetp a)
           (equal (fn-ot-b64-quantum
                   (fn-ot-b64-c0 a) (fn-ot-b64-c1-last a)
                   *fn-ot-b64-pad* *fn-ot-b64-pad*
                   t)
                  (mv nil 1 a 0 0)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (fn-ot-arith-theory fn-ot-b64-quantum fn-ot-b64-value-of-cs
                                                  fn-ot-b64-cs-are-not-pad
                                                  fn-ot-b64-cs-have-values
                                                  fn-ot-j0 fn-ot-j1 fn-ot-j2 fn-ot-j0-short
                                                  fn-ot-j1-short fn-ot-mod-a-4-bounds)
                              '(fn-cbor-octetp)))))

;; ... and an accepted group is the encoding of what it decodes to, with a
;; short group only when it is the last.
;; ... and an accepted group is the encoding of what it decodes to, with a
;; short group only when it is the last.
(defthm fn-ot-b64-quantum-accepted-count
  (implies (not (car (fn-ot-b64-quantum c0 c1 c2 c3 last)))
           (member (mv-nth 1 (fn-ot-b64-quantum c0 c1 c2 c3 last)) '(1 2 3)))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last fn-ot-b64-c2-last))))

(defthm fn-ot-b64-quantum-accepted-3
  (implies (and (not (car (fn-ot-b64-quantum c0 c1 c2 c3 last)))
                (equal (mv-nth 1 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 3))
           (equal (fn-ot-b64-encode
                   (fn-ot-b64-quantum-octets 3 (mv-nth 2 (fn-ot-b64-quantum c0 c1 c2 c3 last)) (mv-nth 3 (fn-ot-b64-quantum c0 c1 c2 c3 last))
                                             (mv-nth 4 (fn-ot-b64-quantum c0 c1 c2 c3 last)) nil))
                  (list c0 c1 c2 c3)))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last fn-ot-b64-c2-last))))

(defthm fn-ot-b64-quantum-accepted-short
  (implies (and (not (car (fn-ot-b64-quantum c0 c1 c2 c3 last)))
                (not (equal (mv-nth 1 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 3)))
           (equal (fn-ot-b64-encode
                   (fn-ot-b64-quantum-octets (mv-nth 1 (fn-ot-b64-quantum c0 c1 c2 c3 last)) (mv-nth 2 (fn-ot-b64-quantum c0 c1 c2 c3 last))
                                             (mv-nth 3 (fn-ot-b64-quantum c0 c1 c2 c3 last)) (mv-nth 4 (fn-ot-b64-quantum c0 c1 c2 c3 last)) nil))
                  (list c0 c1 c2 c3)))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last fn-ot-b64-c2-last))))

(defthm fn-ot-b64-quantum-short-only-last
  (implies (and (not last)
                (not (car (fn-ot-b64-quantum c0 c1 c2 c3 last))))
           (equal (mv-nth 1 (fn-ot-b64-quantum c0 c1 c2 c3 last)) 3))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum))))

(defthm fn-ot-b64-quantum-error-kinds
  (implies (car (fn-ot-b64-quantum c0 c1 c2 c3 last))
           (or (equal (car (fn-ot-b64-quantum c0 c1 c2 c3 last)) :b64-alphabet)
               (equal (car (fn-ot-b64-quantum c0 c1 c2 c3 last)) :b64-padding-bits)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum))))

(defthm fn-ot-b64-quantum-refuses-outside-alphabet
  (implies (or (and (not (fn-ot-b64-value c0)))
               (and (not (fn-ot-b64-value c1)))
               (and (not (fn-ot-b64-value c2)) (not (equal c2 *fn-ot-b64-pad*)))
               (and (not (fn-ot-b64-value c3)) (not (equal c3 *fn-ot-b64-pad*))))
           (car (fn-ot-b64-quantum c0 c1 c2 c3 last)))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum))))

(defthm fn-ot-b64-quantum-refuses-early-pad
  (implies (and (not last)
                (or (equal c2 *fn-ot-b64-pad*) (equal c3 *fn-ot-b64-pad*)))
           (car (fn-ot-b64-quantum c0 c1 c2 c3 last)))
  :hints (("Goal" :in-theory (enable fn-ot-b64-quantum))))

(defthm fn-ot-b64-encode-of-three-and-rest
  (implies (syntaxp (not (equal rest ''nil)))
  (equal (fn-ot-b64-encode (list* a b c rest))
         (append (fn-ot-b64-encode (list a b c)) (fn-ot-b64-encode rest)))))

(defthm fn-ot-b64-encode-of-quantum-octets-3
  (implies (syntaxp (not (equal rest ''nil)))
           (equal (fn-ot-b64-encode (fn-ot-b64-quantum-octets 3 a b c rest))
                  (append (fn-ot-b64-encode (fn-ot-b64-quantum-octets 3 a b c nil))
                          (fn-ot-b64-encode rest))))
  :hints (("Goal" :in-theory (disable fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3))))

(defun fn-ot-b64-decode (xs)
  (declare (xargs :guard t :measure (len xs)))
  (cond ((atom xs) (mv nil nil))
        ((or (atom (cdr xs)) (atom (cddr xs)) (atom (cdddr xs)))
         (mv :b64-quantum nil))
        (t (let ((last (atom (cddddr xs))))
             (mv-let (err k o0 o1 o2)
               (fn-ot-b64-quantum (car xs) (cadr xs) (caddr xs) (cadddr xs) last)
               (cond (err (mv err nil))
                     ((not (equal k 3)) (mv nil (fn-ot-b64-quantum-octets k o0 o1 o2 nil)))
                     (t (mv-let (err2 rest) (fn-ot-b64-decode (cddddr xs))
                          (if err2
                              (mv err2 nil)
                            (mv nil (fn-ot-b64-quantum-octets 3 o0 o1 o2 rest)))))))))))

(defthm fn-ot-b64-decode-error-kinds
  (member (mv-nth 0 (fn-ot-b64-decode xs))
          '(nil :b64-quantum :b64-alphabet :b64-padding-bits)))

(defthm fn-ot-octet-listp-of-b64-decode
  (fn-cbor-octet-listp (mv-nth 1 (fn-ot-b64-decode xs))))

; Keystone: base64 decode inverts base64 encode.
(defthm fn-ot-b64-decode-of-encode
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-ot-b64-decode (fn-ot-b64-encode xs))
                  (mv nil xs)))
  :hints (("Goal" :induct (fn-ot-b64-encode xs)
           :in-theory (disable fn-ot-b64-encode-of-three-and-rest))))

; Keystone: an accepted text is canonical -- the encoding of what it decodes
; to.  So its length is a multiple of four, every octet is in the alphabet
; but the trailing pads, and the bits under a pad are zero.
(defthm fn-ot-b64-accepted-is-canonical
  (implies (and (not (mv-nth 0 (fn-ot-b64-decode xs))) (true-listp xs))
           (equal (fn-ot-b64-encode (mv-nth 1 (fn-ot-b64-decode xs))) xs))
  :hints (("Goal" :induct (fn-ot-b64-decode xs)
           :in-theory (disable fn-ot-b64-quantum-octets
                               fn-ot-b64-encode-of-three-and-rest))))

; The alphabet refusal, named: an octet that is neither in the alphabet nor
; the pad is refused wherever it stands.
(defthm fn-ot-b64-refuses-outside-alphabet
  (implies (and (member-equal c xs)
                (not (fn-ot-b64-value c))
                (not (equal c *fn-ot-b64-pad*)))
           (mv-nth 0 (fn-ot-b64-decode xs)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ot-b64-decode xs))))

(local (in-theory (enable floor mod)))

; -----------------------------------------------------------------------------
; ASCII case (RFC 5234: A-Z and a-z only; no other octet moves).

(defun fn-ot-downcase-octet (o)
  (declare (xargs :guard t))
  (if (fn-ot-upperp o) (+ o 32) o))

(defun fn-ot-upcase-octet (o)
  (declare (xargs :guard t))
  (if (fn-ot-lowerp o) (- o 32) o))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-ot-downcase-loop (xs acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp xs)
      (fn-ot-downcase-loop (cdr xs) (cons (fn-ot-downcase-octet (car xs)) acc))
    (revappend acc nil)))

(defun fn-ot-downcase (xs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (cons (fn-ot-downcase-octet (car xs)) (fn-ot-downcase (cdr xs)))
         nil)
       :exec (fn-ot-downcase-loop xs nil)))

(local
 (defthm fn-ot-downcase-loop-is-revappend
   (equal (fn-ot-downcase-loop xs acc)
          (revappend acc (fn-ot-downcase xs)))
   :hints (("Goal" :induct (fn-ot-downcase-loop xs acc)
                   :in-theory (union-theories '(fn-ot-downcase-loop fn-ot-downcase revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-ot-downcase-loop)

(verify-guards fn-ot-downcase
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-ot-downcase)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-ot-downcase-loop-is-revappend (acc nil))))))


(defun fn-ot-upcase (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-ot-upcase-octet (car xs)) (fn-ot-upcase (cdr xs)))
    nil))

(defthm fn-ot-octet-listp-of-downcase
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-ot-downcase xs))))

(defthm fn-ot-octet-listp-of-upcase
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-ot-upcase xs))))

(defthm fn-ot-len-of-downcase
  (equal (len (fn-ot-downcase xs)) (len xs)))

(defun fn-ot-ci-equal (xs ys)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (consp ys)
           (equal (fn-ot-downcase-octet (car xs)) (fn-ot-downcase-octet (car ys)))
           (fn-ot-ci-equal (cdr xs) (cdr ys)))
    (atom ys)))

; Keystone: case-insensitive equality is equality of the case folds.
(defthm fn-ot-ci-equal-is-downcase-equal
  (equal (fn-ot-ci-equal xs ys)
         (equal (fn-ot-downcase xs) (fn-ot-downcase ys))))

; -----------------------------------------------------------------------------
; Whitespace tokens: maximal runs of non-WSP octets, at most LIMIT of them.
; (mv err tokens): err nil or :too-many-tokens.

(defun fn-ot-drop-wsp (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-ot-wspp (car xs)))
      (fn-ot-drop-wsp (cdr xs))
    xs))

(defun fn-ot-token (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (fn-ot-wspp (car xs))))
      (cons (car xs) (fn-ot-token (cdr xs)))
    nil))

(defun fn-ot-after-token (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (fn-ot-wspp (car xs))))
      (fn-ot-after-token (cdr xs))
    xs))

(defthm fn-ot-len-of-drop-wsp
  (<= (len (fn-ot-drop-wsp xs)) (len xs))
  :rule-classes :linear)

(defthm fn-ot-len-of-after-token
  (implies (and (consp xs) (not (fn-ot-wspp (car xs))))
           (< (len (fn-ot-after-token xs)) (len xs)))
  :rule-classes :linear)

(defthm fn-ot-drop-wsp-head
  (implies (consp (fn-ot-drop-wsp xs))
           (not (fn-ot-wspp (car (fn-ot-drop-wsp xs))))))

(defun fn-ot-split-wsp (xs limit)
  (declare (xargs :guard (natp limit) :measure (len xs)))
  (let ((ys (fn-ot-drop-wsp xs)))
    (cond ((atom ys) (mv nil nil))
          ((zp limit) (mv :too-many-tokens nil))
          (t (mv-let (err toks) (fn-ot-split-wsp (fn-ot-after-token ys) (1- limit))
               (if err
                   (mv err nil)
                 (mv nil (cons (fn-ot-token ys) toks))))))))

; Every octet of XS but the WSP, in order.
(defun fn-ot-strip-wsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-ot-wspp (car xs))
          (fn-ot-strip-wsp (cdr xs))
        (cons (car xs) (fn-ot-strip-wsp (cdr xs))))
    nil))

;; The tokens, concatenated.
(defun fn-ot-concat (toks)
  (declare (xargs :guard t))
  (if (consp toks)
      (fn-oct-cat (car toks) (fn-ot-concat (cdr toks)))
    nil))

; A token: a nonempty true list of non-WSP octets.
(defun fn-ot-no-wspp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (fn-ot-wspp (car xs))) (fn-ot-no-wspp (cdr xs)))
    (null xs)))

(defun fn-ot-tokensp (toks)
  (declare (xargs :guard t))
  (if (consp toks)
      (and (consp (car toks)) (fn-ot-no-wspp (car toks))
           (fn-ot-tokensp (cdr toks)))
    (null toks)))

(defthm fn-ot-strip-wsp-of-drop-wsp
  (equal (fn-ot-strip-wsp (fn-ot-drop-wsp xs)) (fn-ot-strip-wsp xs)))

(defthm fn-ot-strip-wsp-splits-at-token
  (equal (append (fn-ot-token xs) (fn-ot-strip-wsp (fn-ot-after-token xs)))
         (fn-ot-strip-wsp xs)))

(defthm fn-ot-token-is-no-wsp
  (fn-ot-no-wspp (fn-ot-token xs)))

(defthm fn-ot-consp-token
  (implies (and (consp xs) (not (fn-ot-wspp (car xs))))
           (consp (fn-ot-token xs))))

(defthm fn-ot-strip-wsp-of-atom-drop
  (implies (not (consp (fn-ot-drop-wsp xs)))
           (equal (fn-ot-strip-wsp xs) nil))
  :hints (("Goal" :use fn-ot-strip-wsp-of-drop-wsp
           :in-theory (disable fn-ot-strip-wsp-of-drop-wsp))))

; Keystone: an accepted split loses nothing and invents nothing -- its
; tokens are nonempty WSP-free runs whose concatenation is the input with
; its WSP removed -- and there are at most LIMIT of them.  An input with
; more is refused (:too-many-tokens), never truncated.
(defthm fn-ot-split-wsp-loses-nothing
  (implies (not (mv-nth 0 (fn-ot-split-wsp xs limit)))
           (and (fn-ot-tokensp (mv-nth 1 (fn-ot-split-wsp xs limit)))
                (equal (fn-ot-concat (mv-nth 1 (fn-ot-split-wsp xs limit)))
                       (fn-ot-strip-wsp xs))
                (<= (len (mv-nth 1 (fn-ot-split-wsp xs limit))) (nfix limit))))
  :hints (("Goal" :induct (fn-ot-split-wsp xs limit))))

(defthm fn-ot-split-wsp-error-kinds
  (member (mv-nth 0 (fn-ot-split-wsp xs limit)) '(nil :too-many-tokens)))

; -----------------------------------------------------------------------------
; In-place twins over the octet buffer.  Each reads st[i..n) with
; `fn-octets-get' and conses nothing of the input; its boundary theorem
; says it equals the list model on the slice (fn-oct-slice-list i n st),
; which books/octets-stobj.lisp equates to (take (- n i) (nthcdr i st)).
; A caller holding a stobj declared `:congruent-to fn-octets' passes it for
; FN-OCTETS.

(local
 (defthm fn-ot-slice-opens
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n fn-octets)
                   (cons (nth i fn-octets) (fn-oct-slice-list (1+ i) n fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-ot-slice-empty
   (implies (not (and (natp i) (natp n) (< i n)))
            (equal (fn-oct-slice-list i n fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(defun fn-ot-spanp (i n len)
  (declare (xargs :guard t))
  (and (natp i) (natp n) (<= i n) (natp len) (<= n len)))

;; Naturals.
(defun fn-ot-nat-parse-aux-at (i n radix max acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ot-spanp i n (fn-octets-len fn-octets))
                              (fn-ot-radixp radix) (fn-ot-maxp max) (natp acc))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (nfix acc)
    (let ((v (fn-ot-digit-value (fn-octets-get i fn-octets) radix)))
      (and v
           (let ((acc2 (+ (* (nfix radix) (nfix acc)) v)))
             (and (or (null max) (<= acc2 (nfix max)))
                  (fn-ot-nat-parse-aux-at (1+ i) n radix max acc2 fn-octets)))))))

(defun fn-ot-nat-parse-at (i n radix max fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ot-spanp i n (fn-octets-len fn-octets))
                              (fn-ot-radixp radix) (fn-ot-maxp max))))
  (and (natp i) (natp n) (< i n)
       (fn-ot-nat-parse-aux-at i n radix max 0 fn-octets)))

(defun fn-ot-decimal-parse-at (i n max fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ot-spanp i n (fn-octets-len fn-octets))
                              (fn-ot-maxp max))))
  (fn-ot-nat-parse-at i n 10 max fn-octets))

(defun fn-ot-hexnat-parse-at (i n max fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ot-spanp i n (fn-octets-len fn-octets))
                              (fn-ot-maxp max))))
  (fn-ot-nat-parse-at i n 16 max fn-octets))

(defthm fn-ot-nat-parse-aux-at-is-slice
  (equal (fn-ot-nat-parse-aux-at i n r max acc fn-octets)
         (fn-ot-nat-parse-aux (fn-oct-slice-list i n fn-octets) r max acc)))

(defthm fn-ot-nat-parse-at-is-slice
  (equal (fn-ot-nat-parse-at i n r max fn-octets)
         (fn-ot-nat-parse (fn-oct-slice-list i n fn-octets) r max)))

;; Hex octet strings.
(defun fn-ot-hex-decode-at (i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (fn-ot-spanp i n (fn-octets-len fn-octets))
                  :measure (nfix (- n i))))
  (cond ((or (not (natp i)) (not (natp n)) (<= n i)) (mv nil nil))
        ((<= n (1+ i)) (mv :hex-odd nil))
        (t (let ((h (fn-ot-hex-value (fn-octets-get i fn-octets)))
                 (l (fn-ot-hex-value (fn-octets-get (1+ i) fn-octets))))
             (if (and h l)
                 (mv-let (err rest) (fn-ot-hex-decode-at (+ 2 i) n fn-octets)
                   (if err
                       (mv err nil)
                     (mv nil (cons (+ (* 16 h) l) rest))))
               (mv :hex-digit nil))))))

(defthm fn-ot-hex-decode-at-is-slice
  (equal (fn-ot-hex-decode-at i n fn-octets)
         (fn-ot-hex-decode (fn-oct-slice-list i n fn-octets)))
  :hints (("Goal" :induct (fn-ot-hex-decode-at i n fn-octets))))

;; Base64.
(defun fn-ot-b64-decode-at (i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (fn-ot-spanp i n (fn-octets-len fn-octets))
                  :measure (nfix (- n i))))
  (cond ((or (not (natp i)) (not (natp n)) (<= n i)) (mv nil nil))
        ((< n (+ 4 i)) (mv :b64-quantum nil))
        (t (mv-let (err k o0 o1 o2)
             (fn-ot-b64-quantum (fn-octets-get i fn-octets)
                                (fn-octets-get (+ 1 i) fn-octets)
                                (fn-octets-get (+ 2 i) fn-octets)
                                (fn-octets-get (+ 3 i) fn-octets)
                                (<= n (+ 4 i)))
             (cond (err (mv err nil))
                   ((not (equal k 3)) (mv nil (fn-ot-b64-quantum-octets k o0 o1 o2 nil)))
                   (t (mv-let (err2 rest) (fn-ot-b64-decode-at (+ 4 i) n fn-octets)
                        (if err2
                            (mv err2 nil)
                          (mv nil (fn-ot-b64-quantum-octets 3 o0 o1 o2 rest))))))))))

(local
 (defthm fn-ot-slice-opens-4
   (implies (and (natp i) (natp n) (<= (+ 4 i) n))
            (equal (fn-oct-slice-list i n fn-octets)
                   (list* (nth i fn-octets) (nth (+ 1 i) fn-octets)
                          (nth (+ 2 i) fn-octets) (nth (+ 3 i) fn-octets)
                          (fn-oct-slice-list (+ 4 i) n fn-octets))))))

(local
 (defthm fn-ot-b64-decode-of-short-slice
   (implies (and (natp i) (natp n) (< i n) (< n (+ 4 i)))
            (equal (fn-ot-b64-decode (fn-oct-slice-list i n fn-octets))
                   (mv :b64-quantum nil)))
   :hints (("Goal" :cases ((equal n (+ 1 i)) (equal n (+ 2 i)) (equal n (+ 3 i)))))))

(local
 (defthm fn-ot-consp-slice
   (implies (and (natp i) (natp n))
            (equal (consp (fn-oct-slice-list i n fn-octets)) (< i n)))
   :hints (("Goal" :cases ((< i n))))))

(defthm fn-ot-b64-decode-at-is-slice
  (equal (fn-ot-b64-decode-at i n fn-octets)
         (fn-ot-b64-decode (fn-oct-slice-list i n fn-octets)))
  :hints (("Goal" :induct (fn-ot-b64-decode-at i n fn-octets)
           :in-theory (disable fn-ot-slice-opens))))

;; Case.
(defun fn-ot-downcase-at (i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (fn-ot-spanp i n (fn-octets-len fn-octets))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (fn-ot-downcase-octet (fn-octets-get i fn-octets))
          (fn-ot-downcase-at (1+ i) n fn-octets))))

(defthm fn-ot-downcase-at-is-slice
  (equal (fn-ot-downcase-at i n fn-octets)
         (fn-ot-downcase (fn-oct-slice-list i n fn-octets)))
  :hints (("Goal" :induct (fn-ot-downcase-at i n fn-octets))))

(defun fn-ot-ci-equal-at (i n xs fn-octets)
  ; Whether st[i..n) equals XS up to ASCII case, read in place.
  (declare (xargs :stobjs fn-octets
                  :guard (fn-ot-spanp i n (fn-octets-len fn-octets))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (atom xs)
    (and (consp xs)
         (equal (fn-ot-downcase-octet (fn-octets-get i fn-octets))
                (fn-ot-downcase-octet (car xs)))
         (fn-ot-ci-equal-at (1+ i) n (cdr xs) fn-octets))))

(defthm fn-ot-ci-equal-at-is-slice
  (equal (fn-ot-ci-equal-at i n xs fn-octets)
         (fn-ot-ci-equal (fn-oct-slice-list i n fn-octets) xs))
  :hints (("Goal" :induct (fn-ot-ci-equal-at i n xs fn-octets) :in-theory (disable fn-ot-ci-equal-is-downcase-equal))))

;; Tokens: indices, then the split.
(defun fn-ot-drop-wsp-at (i n fn-octets)
  ; The first index at or after I holding no WSP, or N.
  (declare (xargs :stobjs fn-octets
                  :guard (fn-ot-spanp i n (fn-octets-len fn-octets))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (if (and (natp i) (natp n)) n (nfix i))
    (if (fn-ot-wspp (fn-octets-get i fn-octets))
        (fn-ot-drop-wsp-at (1+ i) n fn-octets)
      i)))

(defun fn-ot-token-end-at (i n fn-octets)
  ; The first index at or after I holding WSP, or N.
  (declare (xargs :stobjs fn-octets
                  :guard (fn-ot-spanp i n (fn-octets-len fn-octets))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (if (and (natp i) (natp n)) n (nfix i))
    (if (fn-ot-wspp (fn-octets-get i fn-octets))
        i
      (fn-ot-token-end-at (1+ i) n fn-octets))))

(defthm fn-ot-drop-wsp-at-natp
  (natp (fn-ot-drop-wsp-at i n fn-octets))
  :rule-classes :type-prescription)

(defthm fn-ot-drop-wsp-at-bounds
  (implies (and (natp i) (natp n) (<= i n))
           (and (<= i (fn-ot-drop-wsp-at i n fn-octets))
                (<= (fn-ot-drop-wsp-at i n fn-octets) n)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ot-drop-wsp-at i n fn-octets))))

(defthm fn-ot-token-end-at-natp
  (natp (fn-ot-token-end-at i n fn-octets))
  :rule-classes :type-prescription)

(defthm fn-ot-token-end-at-bounds
  (implies (and (natp i) (natp n) (<= i n))
           (and (<= i (fn-ot-token-end-at i n fn-octets))
                (<= (fn-ot-token-end-at i n fn-octets) n)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ot-token-end-at i n fn-octets))))

(defthm fn-ot-drop-wsp-at-stops-on-non-wsp
  (implies (and (natp i) (natp n) (< (fn-ot-drop-wsp-at i n fn-octets) n))
           (not (fn-ot-wspp (nth (fn-ot-drop-wsp-at i n fn-octets) fn-octets))))
  :hints (("Goal" :induct (fn-ot-drop-wsp-at i n fn-octets))))

(defthm fn-ot-token-end-at-advances
  (implies (and (natp i) (natp n) (< i n)
                (not (fn-ot-wspp (nth i fn-octets))))
           (< i (fn-ot-token-end-at i n fn-octets)))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-ot-token-end-at i n fn-octets)))))

(defthm fn-ot-slice-at-drop-wsp
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-ot-drop-wsp (fn-oct-slice-list i n fn-octets))
                  (fn-oct-slice-list (fn-ot-drop-wsp-at i n fn-octets) n fn-octets)))
  :hints (("Goal" :induct (fn-ot-drop-wsp-at i n fn-octets))))

(defthm fn-ot-slice-to-token-end
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-ot-token (fn-oct-slice-list i n fn-octets))
                  (fn-oct-slice-list i (fn-ot-token-end-at i n fn-octets) fn-octets)))
  :hints (("Goal" :induct (fn-ot-token-end-at i n fn-octets))))

(defthm fn-ot-slice-from-token-end
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-ot-after-token (fn-oct-slice-list i n fn-octets))
                  (fn-oct-slice-list (fn-ot-token-end-at i n fn-octets) n fn-octets)))
  :hints (("Goal" :induct (fn-ot-token-end-at i n fn-octets))))

(defun fn-ot-split-wsp-at (i n limit fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-ot-spanp i n (fn-octets-len fn-octets)) (natp limit))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (< n i))
      (mv nil nil)
    (let ((j (fn-ot-drop-wsp-at i n fn-octets)))
      (cond ((<= n j) (mv nil nil))
            ((zp limit) (mv :too-many-tokens nil))
            (t (let ((e (fn-ot-token-end-at j n fn-octets)))
                 (mv-let (err toks) (fn-ot-split-wsp-at e n (1- limit) fn-octets)
                   (if err
                       (mv err nil)
                     (mv nil (cons (fn-oct-slice-list j e fn-octets) toks))))))))))

(defthm fn-ot-split-wsp-at-is-slice
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-ot-split-wsp-at i n limit fn-octets)
                  (fn-ot-split-wsp (fn-oct-slice-list i n fn-octets) limit)))
  :hints (("Goal" :induct (fn-ot-split-wsp-at i n limit fn-octets)
           :in-theory (disable fn-ot-slice-opens fn-ot-drop-wsp fn-ot-token
                               fn-ot-after-token))))


; -----------------------------------------------------------------------------
; The boundary theorems in the list vocabulary: each twin is its list model
; on (take (- n i) (nthcdr i st)).

(defmacro fn-ot-slice (i n st) `(take (- ,n ,i) (nthcdr ,i ,st)))

(defthm fn-ot-nat-parse-at-is-nat-parse
  (implies (and (fn-ot-spanp i n (len fn-octets)) (true-listp fn-octets))
           (equal (fn-ot-nat-parse-at i n r max fn-octets)
                  (fn-ot-nat-parse (fn-ot-slice i n fn-octets) r max))))

(defthm fn-ot-hex-decode-at-is-hex-decode
  (implies (and (fn-ot-spanp i n (len fn-octets)) (true-listp fn-octets))
           (equal (fn-ot-hex-decode-at i n fn-octets)
                  (fn-ot-hex-decode (fn-ot-slice i n fn-octets)))))

(defthm fn-ot-b64-decode-at-is-b64-decode
  (implies (and (fn-ot-spanp i n (len fn-octets)) (true-listp fn-octets))
           (equal (fn-ot-b64-decode-at i n fn-octets)
                  (fn-ot-b64-decode (fn-ot-slice i n fn-octets)))))

(defthm fn-ot-downcase-at-is-downcase
  (implies (and (fn-ot-spanp i n (len fn-octets)) (true-listp fn-octets))
           (equal (fn-ot-downcase-at i n fn-octets)
                  (fn-ot-downcase (fn-ot-slice i n fn-octets)))))

(defthm fn-ot-ci-equal-at-is-ci-equal
  (implies (and (fn-ot-spanp i n (len fn-octets)) (true-listp fn-octets))
           (equal (fn-ot-ci-equal-at i n xs fn-octets)
                  (fn-ot-ci-equal (fn-ot-slice i n fn-octets) xs)))
  :hints (("Goal" :in-theory (disable fn-ot-ci-equal-is-downcase-equal))))

(defthm fn-ot-split-wsp-at-is-split-wsp
  (implies (and (fn-ot-spanp i n (len fn-octets)) (true-listp fn-octets))
           (equal (fn-ot-split-wsp-at i n limit fn-octets)
                  (fn-ot-split-wsp (fn-ot-slice i n fn-octets) limit))))

(in-theory (disable fn-ot-nat-parse-at-is-slice fn-ot-hex-decode-at-is-slice
                    fn-ot-b64-decode-at-is-slice fn-ot-downcase-at-is-slice
                    fn-ot-ci-equal-at-is-slice fn-ot-split-wsp-at-is-slice))

; -----------------------------------------------------------------------------
; Encoders into the buffer: one `fn-octets-append-list' call each.

(defun fn-ot-append-nat (n radix fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-ot-radixp radix)))
  (fn-octets-append-list (fn-ot-nat-octets n radix) fn-octets))

(defun fn-ot-append-decimal (n fn-octets)
  (declare (xargs :stobjs fn-octets))
  (fn-octets-append-list (fn-ot-decimal-octets n) fn-octets))

(defun fn-ot-append-hex (xs fn-octets)
  (declare (xargs :stobjs fn-octets))
  (fn-octets-append-list (fn-ot-hex-encode xs) fn-octets))

(defun fn-ot-append-b64 (xs fn-octets)
  (declare (xargs :stobjs fn-octets))
  (fn-octets-append-list (fn-ot-b64-encode xs) fn-octets))

(defthm fn-ot-append-encoders-are-append
  (and (equal (fn-ot-append-nat n r fn-octets)
              (append fn-octets (fn-ot-nat-octets n r)))
       (equal (fn-ot-append-decimal n fn-octets)
              (append fn-octets (fn-ot-decimal-octets n)))
       (equal (fn-ot-append-hex xs fn-octets)
              (append fn-octets (fn-ot-hex-encode xs)))
       (equal (fn-ot-append-b64 xs fn-octets)
              (append fn-octets (fn-ot-b64-encode xs)))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-ot-hex-decode)
                    (:definition fn-ot-nat-digits)
                    (:rewrite fn-ot-hex-decode-length)))
