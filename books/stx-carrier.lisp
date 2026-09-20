; fn: the FN-Statement carrier -- the detached statement encoding, its base64
; field value, and where the signed payload lives in the article.
;
; specs/substrate-transport.md section 1.2 chose a header field, not an
; article in a reserved group: RFC 5537 section 3.6 requires a relaying agent
; to alter nothing but Path and Xref, so an unknown field crosses an INN
; byte-identical while a separate article crosses only where someone
; configured its group.
;
; Three layers, each a projection of a layer books/statement.lisp already
; owns.  Nothing here re-decides what a statement is.
;
;   detached   fn-stmt-items minus the payload item: the header items and the
;              signature.  fn-stx-detached-encode is fn-stmt-encode-items over
;              that list, so the canonical octets are the fn-stmt- octets and
;              the wire adds nothing below them
;              (fn-stx-detached-encode-is-fn-stmt-encode-without-the-payload).
;   base64     RFC 4648 section 4, with padding.  Canonical: the padding bits
;              must be zero, so exactly one character string decodes to any
;              octet list (fn-stx-b64-accepted-input-is-canonical).
;   field      the unfolded field value, whitespace removed, base64-decoded,
;              then decoded as detached items, under the 8192-octet field
;              bound and a 25-item budget checked before any item is parsed.
;
; Whitespace and canonicality.  RFC 5536 section 2.2 folding is legal and a
; 6kB field will be folded, and books/article.lisp's unfolded value retains
; the continuation WSP.  So the field parser strips WSP, and the canonical
; form is the stripped value: every accepted value has exactly ONE canonical
; form (fn-stx-field-accepted-input-is-canonical), which is what stops a
; middle box offering a second value that decodes to the same statement.
; A non-alphabet octet, a wrong quantum, wrong padding or a non-zero padding
; bit is refused; nothing here refuses the ARTICLE (specs/substrate-transport.md
; "never refuse bytes, refuse authority").
;
; Where the payload is (section 1.3): for kind :article it is the authored
; source -- the received octets with every field the injecting agent adds
; removed -- and for the other kinds it is the article body, base64.  The
; :article projection is a function of the received octets alone, so a reader
; at hop three computes the bytes the author signed at hop zero without
; knowing the route.  w4/post owns the injector's side of that subtraction;
; when it lands the two must be equated by a named theorem (open item, see
; planning/lanes/HANDOFF-w7-substrate-s1.md).

(in-package "ACL2")
(include-book "statement-invariants")
(include-book "article")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Bounds (local policy, specs/substrate-transport.md section 1.2).  Checked in
; this order, before any item is parsed: the field length, base64 acceptance,
; the detached octet cap, the item budget, then the items.

(defconst *fn-stx-max-field-octets* 8192)
(defconst *fn-stx-max-detached-octets* 6144)
(defconst *fn-stx-max-detached-items* 25)   ; *fn-stmt-max-items* less the payload

; -----------------------------------------------------------------------------
; The result record.  (:ok v) / (:ok v w) / (:error why).  Accessors are total
; so every consumer has guard T, and the definitions are withdrawn at the end:
; nothing below this book opens the record.

(defun fn-stx-ok (vals)
  (declare (xargs :guard t))
  (cons :ok vals))
(defun fn-stx-error (why)
  (declare (xargs :guard t))
  (list :error why))
(defun fn-stx-okp (r)
  (declare (xargs :guard t))
  (and (consp r) (equal (car r) :ok)))
(defun fn-stx-val (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r))) (car (cdr r)) nil))
(defun fn-stx-val2 (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r)) (consp (cdr (cdr r)))) (car (cdr (cdr r))) nil))
(defun fn-stx-why (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r))) (car (cdr r)) nil))

(defthm fn-stx-okp-of-fn-stx-ok
  (fn-stx-okp (fn-stx-ok vals)))
(defthm fn-stx-okp-of-fn-stx-error
  (not (fn-stx-okp (fn-stx-error why))))
(defthm fn-stx-val-of-fn-stx-ok
  (equal (fn-stx-val (fn-stx-ok (cons v rest))) v))
(defthm fn-stx-val2-of-fn-stx-ok
  (equal (fn-stx-val2 (fn-stx-ok (list* v w rest))) w))
(defthm fn-stx-why-of-fn-stx-error
  (equal (fn-stx-why (fn-stx-error why)) why))

(in-theory (disable (:d fn-stx-ok) (:d fn-stx-error) (:d fn-stx-okp)
                    (:d fn-stx-val) (:d fn-stx-val2) (:d fn-stx-why)))

; -----------------------------------------------------------------------------
; Base64, RFC 4648 section 4.  Alphabet by range rather than by table, so the
; two inverse laws below are linear arithmetic.

(defconst *fn-stx-b64-pad* 61)

(defun fn-stx-b64-sextet (n)
  (declare (xargs :guard t))
  (let ((k (nfix n)))
    (cond ((< k 26) (+ 65 k))                ; A-Z
          ((< k 52) (+ 71 k))                ; a-z   97 + (k - 26)
          ((< k 62) (- k 4))                 ; 0-9   48 + (k - 52)
          ((equal k 62) 43)                  ; +
          (t 47))))                          ; /

(defun fn-stx-b64-value (c)
  (declare (xargs :guard t))
  (cond ((and (integerp c) (<= 65 c) (<= c 90)) (- c 65))
        ((and (integerp c) (<= 97 c) (<= c 122)) (- c 71))
        ((and (integerp c) (<= 48 c) (<= c 57)) (+ c 4))
        ((equal c 43) 62)
        ((equal c 47) 63)
        (t nil)))

(defthm fn-stx-b64-sextet-is-vchar
  (and (integerp (fn-stx-b64-sextet n))
       (<= 33 (fn-stx-b64-sextet n))
       (<= (fn-stx-b64-sextet n) 126)))

(defthm fn-stx-b64-sextet-is-octet
  (fn-cbor-octetp (fn-stx-b64-sextet n)))

(defthm fn-stx-b64-value-is-natural
  (implies (fn-stx-b64-value c)
           (and (natp (fn-stx-b64-value c))
                (integerp (fn-stx-b64-value c)))))

(defthm fn-stx-b64-value-is-nonnegative
  (implies (fn-stx-b64-value c)
           (<= 0 (fn-stx-b64-value c)))
  :rule-classes (:rewrite :linear))

(defthm fn-stx-b64-value-is-below-64
  (implies (fn-stx-b64-value c)
           (< (fn-stx-b64-value c) 64))
  :rule-classes (:rewrite :linear))

(defthm fn-stx-b64-value-of-sextet
  (implies (and (natp n) (< n 64))
           (equal (fn-stx-b64-value (fn-stx-b64-sextet n)) n)))

(defthm fn-stx-b64-sextet-of-value
  (implies (fn-stx-b64-value c)
           (equal (fn-stx-b64-sextet (fn-stx-b64-value c)) c)))

(defthm fn-stx-b64-value-of-pad
  (equal (fn-stx-b64-value *fn-stx-b64-pad*) nil))

; The pad octet is not in the alphabet, so an encoded quantum is never
; mistaken for a padded one.
(defthm fn-stx-b64-sextet-is-not-pad
  (not (equal (fn-stx-b64-sextet n) *fn-stx-b64-pad*)))

; Nor is it WSP, so RFC 5536 folding is the only whitespace a field value can
; carry and stripping it is information preserving.
(defthm fn-stx-b64-sextet-is-not-wsp
  (and (not (equal (fn-stx-b64-sextet n) 32))
       (not (equal (fn-stx-b64-sextet n) 9)))
  :hints (("Goal" :use fn-stx-b64-sextet-is-vchar
           :in-theory (disable fn-stx-b64-sextet-is-vchar))))

(in-theory (disable (:d fn-stx-b64-sextet) (:d fn-stx-b64-value)))

; Splitting an octet into (floor . mod) is the only arithmetic the codec needs.
; Concrete moduli with `floor`/`mod` closed and `:nonlinearp`, on the pattern
; of `fn-bpc-split-floor` in books/bp-primary-cbor.lisp; nothing below sees a
; symbolic modulus.

(local (defthm fn-stx-mod-is-natural
         (implies (natp x)
                  (and (natp (mod x 4)) (natp (mod x 16)) (natp (mod x 64))
                       (integerp (mod x 4)) (integerp (mod x 16))
                       (integerp (mod x 64))))
         :hints (("Goal" :in-theory (disable mod)))))
(local (defthm fn-stx-mod-is-nonnegative
         (implies (natp x)
                  (and (<= 0 (mod x 4)) (<= 0 (mod x 16)) (<= 0 (mod x 64))))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable mod)))))
(local (defthm fn-stx-mod-bound-4
         (implies (natp x) (< (mod x 4) 4))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable mod)))))
(local (defthm fn-stx-mod-bound-16
         (implies (natp x) (< (mod x 16) 16))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable mod)))))
(local (defthm fn-stx-mod-bound-64
         (implies (natp x) (< (mod x 64) 64))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable mod)))))
(local (defthm fn-stx-floor-is-natural
         (implies (natp x)
                  (and (natp (floor x 4)) (natp (floor x 16)) (natp (floor x 64))
                       (integerp (floor x 4)) (integerp (floor x 16))
                       (integerp (floor x 64))))
         :hints (("Goal" :in-theory (disable floor)))))
(local (defthm fn-stx-floor-is-nonnegative
         (implies (natp x)
                  (and (<= 0 (floor x 4)) (<= 0 (floor x 16)) (<= 0 (floor x 64))))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable floor)))))
(local (defthm fn-stx-floor-bound-4
         (implies (and (natp x) (<= x 255)) (< (floor x 4) 64))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable floor)))))
(local (defthm fn-stx-floor-bound-16
         (implies (and (natp x) (<= x 255)) (< (floor x 16) 16))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable floor)))))
(local (defthm fn-stx-floor-bound-64
         (implies (and (natp x) (<= x 255)) (< (floor x 64) 4))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable floor)))))
(local (defthm fn-stx-split-floor-4
         (implies (and (natp m) (natp f) (< f 4))
                  (equal (floor (+ (* 4 m) f) 4) m))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-split-mod-4
         (implies (and (natp m) (natp f) (< f 4))
                  (equal (mod (+ (* 4 m) f) 4) f))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-split-floor-16
         (implies (and (natp m) (natp f) (< f 16))
                  (equal (floor (+ (* 16 m) f) 16) m))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-split-mod-16
         (implies (and (natp m) (natp f) (< f 16))
                  (equal (mod (+ (* 16 m) f) 16) f))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-split-floor-64
         (implies (and (natp m) (natp f) (< f 64))
                  (equal (floor (+ (* 64 m) f) 64) m))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-split-mod-64
         (implies (and (natp m) (natp f) (< f 64))
                  (equal (mod (+ (* 64 m) f) 64) f))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-elim-4
         (implies (natp a) (equal (+ (* 4 (floor a 4)) (mod a 4)) a))))
(local (defthm fn-stx-elim-16
         (implies (natp a) (equal (+ (* 16 (floor a 16)) (mod a 16)) a))))
(local (defthm fn-stx-elim-64
         (implies (natp a) (equal (+ (* 64 (floor a 64)) (mod a 64)) a))))
(local (defthm fn-stx-mod-of-16-times
         (implies (natp m) (equal (mod (* 16 m) 16) 0))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-mod-of-4-times
         (implies (natp m) (equal (mod (* 4 m) 4) 0))
         :hints (("Goal" :in-theory (disable floor mod) :nonlinearp t))))
(local (defthm fn-stx-floor-16-of-sextet
         (implies (and (natp v) (< v 64)) (< (floor v 16) 4))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable floor)))))
(local (defthm fn-stx-floor-4-of-sextet
         (implies (and (natp v) (< v 64)) (< (floor v 4) 16))
         :rule-classes (:rewrite :linear)
         :hints (("Goal" :in-theory (disable floor)))))

; From here down `floor` and `mod` stay closed: every fact the codec needs
; about them is one of the rules above, and opening them puts rational
; arithmetic into the codec's case tree (books/bp-primary-cbor.lisp measured
; the same thing on base-256 digits).
(local (in-theory (disable floor mod)))

(defun fn-stx-b64-encode (octets)
  (declare (xargs :guard t
                  :measure (acl2-count octets)
                  :verify-guards nil))
  (if (atom octets)
      nil
    (let ((a (nfix (car octets))))
      (if (atom (cdr octets))
          (list (fn-stx-b64-sextet (floor a 4))
                (fn-stx-b64-sextet (* 16 (mod a 4)))
                *fn-stx-b64-pad* *fn-stx-b64-pad*)
        (let ((b (nfix (car (cdr octets)))))
          (if (atom (cdr (cdr octets)))
              (list (fn-stx-b64-sextet (floor a 4))
                    (fn-stx-b64-sextet (+ (* 16 (mod a 4)) (floor b 16)))
                    (fn-stx-b64-sextet (* 4 (mod b 16)))
                    *fn-stx-b64-pad*)
            (let ((c (nfix (car (cdr (cdr octets))))))
              (cons (fn-stx-b64-sextet (floor a 4))
                    (cons (fn-stx-b64-sextet (+ (* 16 (mod a 4)) (floor b 16)))
                          (cons (fn-stx-b64-sextet (+ (* 4 (mod b 16)) (floor c 64)))
                                (cons (fn-stx-b64-sextet (mod c 64))
                                      (fn-stx-b64-encode (cdr (cdr (cdr octets)))))))))))))))

(verify-guards fn-stx-b64-encode)

(defun fn-stx-b64-decode-exact (chars)
  (declare (xargs :guard t :measure (acl2-count chars)))
  (if (atom chars)
      (if (null chars) (fn-stx-ok (list nil)) (fn-stx-error :b64-improper))
    (if (not (and (consp (cdr chars))
                  (consp (cdr (cdr chars)))
                  (consp (cdr (cdr (cdr chars))))))
        (fn-stx-error :b64-quantum)
      (let ((c2 (car (cdr (cdr chars))))
            (c3 (car (cdr (cdr (cdr chars)))))
            (rest (cdr (cdr (cdr (cdr chars)))))
            (v0 (fn-stx-b64-value (car chars)))
            (v1 (fn-stx-b64-value (car (cdr chars)))))
        (if (or (null v0) (null v1))
            (fn-stx-error :b64-alphabet)
          (if (and (equal c2 *fn-stx-b64-pad*)
                   (equal c3 *fn-stx-b64-pad*)
                   (null rest))
              (if (not (equal (mod v1 16) 0))
                  (fn-stx-error :b64-padding-bits)
                (fn-stx-ok (list (list (+ (* 4 v0) (floor v1 16))))))
            (let ((v2 (fn-stx-b64-value c2)))
              (if (null v2)
                  (fn-stx-error :b64-alphabet)
                (if (and (equal c3 *fn-stx-b64-pad*) (null rest))
                    (if (not (equal (mod v2 4) 0))
                        (fn-stx-error :b64-padding-bits)
                      (fn-stx-ok (list (list (+ (* 4 v0) (floor v1 16))
                                             (+ (* 16 (mod v1 16)) (floor v2 4))))))
                  (let ((v3 (fn-stx-b64-value c3)))
                    (if (null v3)
                        (fn-stx-error :b64-alphabet)
                      (let ((tail (fn-stx-b64-decode-exact rest)))
                        (if (not (fn-stx-okp tail))
                            tail
                          (fn-stx-ok
                           (list (cons (+ (* 4 v0) (floor v1 16))
                                       (cons (+ (* 16 (mod v1 16)) (floor v2 4))
                                             (cons (+ (* 64 (mod v2 4)) v3)
                                                   (fn-stx-val tail)))))))))))))))))))

(defthm fn-stx-b64-encode-is-octet-list
  (fn-cbor-octet-listp (fn-stx-b64-encode octets))
  :hints (("Goal" :induct (fn-stx-b64-encode octets))))

(defthm fn-stx-b64-encode-is-header-bytes
  (fn-article-header-bytes-p (fn-stx-b64-encode octets))
  :hints (("Goal" :induct (fn-stx-b64-encode octets)
           :in-theory (enable fn-article-header-bytep fn-article-vcharp))))

; 3 * len(b64) <= 8 + 4 * len(octets): the 4/3 expansion, stated without
; division so the field bound is a linear-arithmetic consequence.
(defthm fn-stx-b64-encode-length
  (<= (* 3 (len (fn-stx-b64-encode octets)))
      (+ 8 (* 4 (len octets))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-stx-b64-encode octets))))

(defthm fn-stx-b64-decode-is-octet-list
  (implies (fn-stx-okp (fn-stx-b64-decode-exact chars))
           (fn-cbor-octet-listp (fn-stx-val (fn-stx-b64-decode-exact chars))))
  :hints (("Goal" :induct (fn-stx-b64-decode-exact chars))))

(defthm fn-stx-b64-round-trip
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-stx-b64-decode-exact (fn-stx-b64-encode octets))
                  (fn-stx-ok (list octets))))
  :hints (("Goal" :induct (fn-stx-b64-encode octets))))

(defthm fn-stx-b64-accepted-input-is-canonical
  (implies (fn-stx-okp (fn-stx-b64-decode-exact chars))
           (equal (fn-stx-b64-encode (fn-stx-val (fn-stx-b64-decode-exact chars)))
                  chars))
  :hints (("Goal" :induct (fn-stx-b64-decode-exact chars))))

; -----------------------------------------------------------------------------
; The detached encoding: fn-stmt-items with the payload item removed.

(defun fn-stx-detached-items (header signature)
  (declare (xargs :guard (fn-stmt-headerp header)))
  (append (fn-stmt-header-items header)
          (list (cons :bytes signature))))

(local (defthm fn-stx-bytes-item-is-a-cbor-value
         (implies (fn-sig-signature-p signature)
                  (fn-cbor-valuep (cons :bytes signature)))
         :hints (("Goal" :in-theory (enable (:d fn-sig-signature-p)
                                            fn-cbor-valuep)))))

(defun fn-stx-detached-encode-parts (header signature)
  (declare (xargs :guard t))
  (if (and (fn-stmt-headerp header) (fn-sig-signature-p signature))
      (fn-stmt-encode-items (fn-stx-detached-items header signature))
    nil))

(defun fn-stx-detached-encode (s)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable (:d fn-stmt-p))))))
  (if (fn-stmt-p s)
      (fn-stx-detached-encode-parts (fn-stmt-header s) (fn-stmt-signature s))
    nil))

; Reattachment: the payload comes from the article, never from the field.
; NIL when the header's ref does not bind the payload the receiver projected.
(defun fn-stx-reattach (header signature payload)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable (:d fn-stmt-p))))))
  (let ((s (fn-stmt-make header payload signature)))
    (if (fn-stmt-p s) s nil)))

(defun fn-stx-detached-of-items (items)
  (declare (xargs :guard t))
  (let ((parsed (fn-stmt-header-of-items items)))
    (if (not (fn-stmt-okp parsed))
        (fn-stx-error (fn-stmt-value parsed))
      (let ((i1 (fn-stmt-rest parsed)))
        (if (not (and (consp i1)
                      (consp (car i1))
                      (fn-stmt-bytes-item-p (car i1))
                      (fn-sig-signature-p (cdr (car i1)))))
            (fn-stx-error :signature)
          (if (not (null (cdr i1)))
              (fn-stx-error :trailing)
            (fn-stx-ok (list (fn-stmt-value parsed) (cdr (car i1))))))))))

(defun fn-stx-detached-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stx-max-detached-octets*))
      (fn-stx-error :limit)
    (let ((items (fn-stmt-decode-items *fn-stx-max-detached-items* octets)))
      (if (not (fn-stmt-okp items))
          (fn-stx-error (fn-stmt-value items))
        (fn-stx-detached-of-items (fn-stmt-value items))))))

; -----------------------------------------------------------------------------
; The field value: whitespace-stripped base64 of the detached encoding.

(defun fn-stx-strip-wsp (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (if (or (equal (car octets) 32) (equal (car octets) 9))
          (fn-stx-strip-wsp (cdr octets))
        (cons (car octets) (fn-stx-strip-wsp (cdr octets))))
    nil))

(defun fn-stx-header-value-parts (header signature)
  (declare (xargs :guard t))
  (fn-stx-b64-encode (fn-stx-detached-encode-parts header signature)))

(defun fn-stx-header-value (s)
  (declare (xargs :guard t))
  (fn-stx-b64-encode (fn-stx-detached-encode s)))

(defun fn-stx-parse-header (value)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp value *fn-stx-max-field-octets*))
      (fn-stx-error :field-too-long)
    (let ((b (fn-stx-b64-decode-exact (fn-stx-strip-wsp value))))
      (if (not (fn-stx-okp b))
          b
        (fn-stx-detached-decode-exact (fn-stx-val b))))))

(defthm fn-stx-header-value-is-header-bytes
  (and (fn-cbor-octet-listp (fn-stx-header-value s))
       (fn-article-header-bytes-p (fn-stx-header-value s))))

(defthm fn-stx-strip-wsp-is-octet-list
  (implies (fn-cbor-octet-listp octets)
           (fn-cbor-octet-listp (fn-stx-strip-wsp octets))))

(defthm fn-stx-strip-wsp-of-b64-encode
  (equal (fn-stx-strip-wsp (fn-stx-b64-encode octets))
         (fn-stx-b64-encode octets))
  :hints (("Goal" :induct (fn-stx-b64-encode octets)
           :in-theory (e/d ((:d fn-stx-strip-wsp)) (floor mod)))))

(defthm fn-stx-strip-wsp-length
  (<= (len (fn-stx-strip-wsp octets)) (len octets))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; Where the payload is, by kind (section 1.3).

(defconst *fn-stx-statement-name*
  '(102 110 45 115 116 97 116 101 109 101 110 116))            ; fn-statement
(defconst *fn-stx-policy-name*
  '(102 110 45 112 111 108 105 99 121))                        ; fn-policy
(defconst *fn-stx-path-name* '(112 97 116 104))                ; path
(defconst *fn-stx-xref-name* '(120 114 101 102))               ; xref
(defconst *fn-stx-injection-date-name*
  '(105 110 106 101 99 116 105 111 110 45 100 97 116 101))     ; injection-date
(defconst *fn-stx-injection-info-name*
  '(105 110 106 101 99 116 105 111 110 45 105 110 102 111))    ; injection-info

; The fields the injecting agent adds, and the carrier itself.  A statement
; cannot sign the field that carries it, so fn-statement is subtracted here
; and fn-stx-payload-ignores-the-carrier-field (books/stx-invariants.lisp) is
; why attaching the field after signing is sound.
(defun fn-stx-injected-namep (name)
  (declare (xargs :guard t))
  (or (equal name *fn-stx-path-name*)
      (equal name *fn-stx-xref-name*)
      (equal name *fn-stx-injection-date-name*)
      (equal name *fn-stx-injection-info-name*)
      (equal name *fn-stx-statement-name*)
      (equal name *fn-stx-policy-name*)))

(defun fn-stx-field-octets (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (append (if (true-listp (car lines)) (car lines) nil)
              (append '(13 10) (fn-stx-field-octets (cdr lines))))
    nil))

(defun fn-stx-authored-header (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (or (not (true-listp (car fields)))
              (fn-stx-injected-namep (fn-article-field-name (car fields))))
          (fn-stx-authored-header (cdr fields))
        (append (fn-stx-field-octets (fn-article-field-raw-lines (car fields)))
                (fn-stx-authored-header (cdr fields))))
    nil))

; D01 authored source: the received octets with every injected field removed.
; A function of the received octets alone -- no peer, no route, no clock.
(defun fn-stx-authored-source (article)
  (declare (xargs :guard t))
  (if (not (true-listp article))
      nil
    (append (fn-stx-authored-header (fn-article-fields article))
            (append '(13 10)
                    (if (true-listp (fn-article-body article))
                        (fn-article-body article)
                      nil)))))

; Kinds other than :article carry their payload as the article body, base64.
; The body is accepted only in its canonical unwrapped spelling; the wrapping
; question (RFC 4648 section 4 CRLF every 76 characters) is the caller's, and
; fn-stx-strip-wsp removes only WSP, never CRLF.
(defun fn-stx-body-payload (body)
  (declare (xargs :guard t))
  (fn-stx-b64-decode-exact (fn-stx-strip-wsp body)))

(defun fn-stx-payload-for (article header)
  (declare (xargs :guard t))
  (if (and (true-listp header)
           (equal (fn-stmt-header-kind header) :article))
      (fn-stx-authored-source article)
    (let ((r (fn-stx-body-payload
              (if (and (true-listp article)
                       (true-listp (fn-article-body article)))
                  (fn-article-body article)
                nil))))
      (if (fn-stx-okp r) (fn-stx-val r) nil))))

(defthm fn-stx-authored-source-is-octet-list
  (implies (fn-article-syntax-p article)
           (fn-cbor-octet-listp (fn-stx-authored-source article)))
  :hints (("Goal" :in-theory (enable fn-article-syntax-p))))

(defthm fn-stx-payload-for-is-octet-list
  (implies (fn-article-syntax-p article)
           (fn-cbor-octet-listp (fn-stx-payload-for article header)))
  :hints (("Goal" :in-theory (enable fn-article-syntax-p))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  The record accessors, the
; base64 primitives, the codecs and the projections are withdrawn; the record
; lemmas, the shape facts and the round-trip and canonicality keystones stay.

(in-theory (disable (:d fn-stx-b64-encode) (:d fn-stx-b64-decode-exact)
                    (:d fn-stx-strip-wsp)
                    (:d fn-stx-detached-items) (:d fn-stx-detached-encode-parts)
                    (:d fn-stx-detached-encode) (:d fn-stx-reattach)
                    (:d fn-stx-detached-of-items) (:d fn-stx-detached-decode-exact)
                    (:d fn-stx-header-value-parts) (:d fn-stx-header-value)
                    (:d fn-stx-parse-header)
                    (:d fn-stx-injected-namep) (:d fn-stx-field-octets)
                    (:d fn-stx-authored-header) (:d fn-stx-authored-source)
                    (:d fn-stx-body-payload) (:d fn-stx-payload-for)))
