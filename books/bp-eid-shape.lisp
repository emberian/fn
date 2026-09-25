; fn: the text shape of an enrolled Bundle Protocol endpoint ID.
;
; `bp-boundary add' (books/native-admin.lisp) refuses an EID word that is
; not `fn-bp-eid-shapep'.  A small book of its own so that the grammar and
; its proofs do not add to native-admin's certification time.

(in-package "ACL2")
(include-book "config")

; The text shape of a BP endpoint ID an operator may enroll: the boundary's
; own EID, and every `carries' and `releases-for' EID of `bp-boundary add'.
;
; RFC requirement, RFC 9171 s4.2.5.1.1 and s4.2.5.1.2 (ABNF per RFC 5234):
;   dtn-uri       = "dtn:" ("none" / dtn-hier-part)
;   dtn-hier-part = "//" node-name "/" demux
;   node-name     = reg-name        ; RFC 3986 s3.2.2:
;                   *( unreserved / pct-encoded / sub-delims )
;   demux         = *VCHAR          ; %x21-7E
;   ipn-uri       = "ipn:" 1*DIGIT "." 1*DIGIT
; Local policy, stronger than the RFC and stated as such:
;   - "dtn:none" is refused: the null endpoint has no members, so it names no
;     neighbour, no carried source and no release issuer;
;   - node-name is non-empty (as `fn-bpp-dtn-sspp' requires of a wire SSP);
;   - the scheme is lower case and each ipn number is canonical decimal (no
;     leading zero) at most 2^64-1, the form `fn-bpaj-eid-text' renders a
;     wire EID in, so an enrolled EID is compared with a received one as the
;     same text;
;   - the whole EID is a configuration label (`fn-cfg-labelp': ASCII, at most
;     *fn-cfg-max-label* = 256 octets), far inside the wire's 1024-octet text
;     bound.
; Every character of such an EID is a VCHAR, so it holds no SP, HTAB, CR or
; LF: `fn-bp-eid-shapep-is-vchar' below, from the grammar.
(defun fn-bp-eid-vcharp (c)
  (declare (xargs :guard t))
  (and (characterp c) (<= 33 (char-code c)) (<= (char-code c) 126)))

(defun fn-bp-eid-vchar-listp (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (and (fn-bp-eid-vcharp (car cs)) (fn-bp-eid-vchar-listp (cdr cs)))
    t))

(defun fn-bp-eid-hexdigp (c)
  (declare (xargs :guard t))
  (and (member c (coerce "0123456789ABCDEFabcdef" 'list)) t))

(defun fn-bp-eid-reg-name-charp (c)
  ; unreserved / sub-delims (RFC 3986 s2.3, s2.2); `%' is handled by the walker.
  (declare (xargs :guard t))
  (and (member c (coerce "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~!$&'()*+,;=" 'list)) t))

; A dtn node-name then "/" then the demux: walk the reg-name characters to
; the first "/", which reg-name cannot hold, and take the rest as the demux.
(defun fn-bp-eid-dtn-walk (cs)
  (declare (xargs :guard t))
  (cond ((atom cs) nil)
        ((equal (car cs) #\/) (fn-bp-eid-vchar-listp (cdr cs)))
        ((equal (car cs) #\%)
         (and (consp (cdr cs)) (fn-bp-eid-hexdigp (cadr cs))
              (consp (cddr cs)) (fn-bp-eid-hexdigp (caddr cs))
              (fn-bp-eid-dtn-walk (cdddr cs))))
        (t (and (fn-bp-eid-reg-name-charp (car cs))
                (fn-bp-eid-dtn-walk (cdr cs))))))

(defun fn-bp-eid-dtn-sspp (cs)
  (declare (xargs :guard t))
  (and (consp cs) (equal (car cs) #\/)
       (consp (cdr cs)) (equal (cadr cs) #\/)
       (consp (cddr cs)) (not (equal (caddr cs) #\/))
       (fn-bp-eid-dtn-walk (cddr cs))))

(defun fn-bp-eid-digitsp (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (and (member (car cs) (coerce "0123456789" 'list))
           (fn-bp-eid-digitsp (cdr cs)))
    t))

; One ipn number: 1*DIGIT, canonical, at most 2^64-1 (RFC 9171 s4.2.5.1.2
; encodes it as a CBOR unsigned integer).
(defun fn-bp-eid-decimal-value (cs value)
  ; The value of a digit list read left to right; only called on digits.
  (declare (xargs :guard t))
  (if (consp cs)
      (fn-bp-eid-decimal-value
       (cdr cs)
       (+ (* 10 (nfix value))
          (if (characterp (car cs)) (nfix (- (char-code (car cs)) 48)) 0)))
    (nfix value)))

(defun fn-bp-eid-nbrp (cs)
  (declare (xargs :guard t))
  (and (consp cs)
       (fn-bp-eid-digitsp cs)
       (not (and (equal (car cs) #\0) (consp (cdr cs))))
       (<= (fn-bp-eid-decimal-value cs 0) 18446744073709551615)))

(defun fn-bp-eid-before-dot (cs)
  (declare (xargs :guard t))
  (if (or (atom cs) (equal (car cs) #\.)) nil
    (cons (car cs) (fn-bp-eid-before-dot (cdr cs)))))

(defun fn-bp-eid-ipn-sspp (cs)
  (declare (xargs :guard t))
  (let ((dot (member-equal #\. (if (true-listp cs) cs nil))))
    (and (consp dot)
         (fn-bp-eid-nbrp (fn-bp-eid-before-dot cs))
         (fn-bp-eid-nbrp (cdr dot)))))

(defun fn-bp-eid-shapep (x)
  "X is an EID `bp-boundary add' may enroll: RFC 9171 s4.2.5.1 dtn (not
dtn:none) or ipn text, canonical, a configuration label."
  (declare (xargs :guard t))
  (and (stringp x)
       (fn-cfg-labelp x)
       (let ((cs (coerce x 'list)))
         (and (consp cs) (consp (cdr cs)) (consp (cddr cs)) (consp (cdddr cs))
              (equal (cadddr cs) #\:)
              (cond ((and (equal (car cs) #\d) (equal (cadr cs) #\t)
                          (equal (caddr cs) #\n))
                     (fn-bp-eid-dtn-sspp (cddddr cs)))
                    ((and (equal (car cs) #\i) (equal (cadr cs) #\p)
                          (equal (caddr cs) #\n))
                     (fn-bp-eid-ipn-sspp (cddddr cs)))
                    (t nil))))))

(encapsulate ()
(local (defthm fn-bp-eid-vchar-listp-of-before-dot
  (implies (and (fn-bp-eid-vchar-listp (fn-bp-eid-before-dot cs))
                (fn-bp-eid-vchar-listp (cdr (member-equal #\. cs))))
           (fn-bp-eid-vchar-listp cs))
  :hints (("Goal" :induct (fn-bp-eid-before-dot cs)
                  :in-theory (disable fn-bp-eid-vcharp)))))
(local (defthm fn-bp-eid-digitsp-is-vchar
  (implies (fn-bp-eid-digitsp cs) (fn-bp-eid-vchar-listp cs))))
(local (defthm fn-bp-eid-nbrp-is-vchar
  (implies (fn-bp-eid-nbrp cs) (fn-bp-eid-vchar-listp cs))))
(local (defthm fn-bp-eid-hexdigp-is-vchar
  (implies (fn-bp-eid-hexdigp c) (fn-bp-eid-vcharp c))))
(local (defthm fn-bp-eid-reg-name-charp-is-vchar
  (implies (fn-bp-eid-reg-name-charp c) (fn-bp-eid-vcharp c))))
(local (defthm fn-bp-eid-dtn-walk-is-vchar
  (implies (fn-bp-eid-dtn-walk cs) (fn-bp-eid-vchar-listp cs))
  :hints (("Goal" :in-theory (disable fn-bp-eid-hexdigp fn-bp-eid-reg-name-charp
                                      fn-bp-eid-vcharp)))))
; KEYSTONE (shape).  From the grammar, not by a conjunct: every character of
; an accepted EID is a VCHAR, so none is SP (32), HTAB (9), CR (13) or LF (10).
(defthm fn-bp-eid-shapep-is-vchar
  (implies (fn-bp-eid-shapep x)
           (fn-bp-eid-vchar-listp (coerce x 'list)))
  :hints (("Goal" :in-theory (disable fn-cfg-labelp fn-bp-eid-dtn-walk
                                      fn-bp-eid-nbrp)))))

; The octets an accepted EID renders as, each a VCHAR.
(defun fn-bp-eid-vchar-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (fn-bp-eid-vchar-octetsp (cdr xs)))
    t))

(encapsulate ()
(local (defthm shapep-is-a-nonempty-string
  (implies (fn-bp-eid-shapep x)
           (and (stringp x) (consp (coerce x 'list))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bp-eid-dtn-sspp fn-bp-eid-ipn-sspp
                                      fn-cfg-labelp)))))
(local (defthm consp-of-string-octets-aux
  (equal (consp (fn-record-string-octets-aux cs)) (consp cs))
  :hints (("Goal" :expand ((fn-record-string-octets-aux cs))))))
(local (defthm vchar-octets-of-string-octets-aux
  (implies (fn-bp-eid-vchar-listp cs)
           (fn-bp-eid-vchar-octetsp (fn-record-string-octets-aux cs)))))
(defthm fn-bp-eid-shapep-octets-are-vchar
  (implies (fn-bp-eid-shapep x)
           (and (consp (fn-record-string-octets x))
                (fn-bp-eid-vchar-octetsp (fn-record-string-octets x))))
  :hints (("Goal" :use (fn-bp-eid-shapep-is-vchar shapep-is-a-nonempty-string)
                  :in-theory (e/d (fn-record-string-octets)
                                  (fn-bp-eid-shapep-is-vchar
                                   fn-bp-eid-shapep fn-bp-eid-vchar-listp))))))

; Closed from here on: a proof about a plan that admits an EID reasons from
; the lemmas above, never by opening the grammar.
(in-theory (disable fn-bp-eid-shapep))

(defun fn-bp-eid-shape-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bp-eid-shapep (car xs)) (fn-bp-eid-shape-listp (cdr xs)))
    t))

