; fn: the node's own web face -- RFC 2047 encoded-words in the headers it
; shows (lane web-native-2, PRF-353, WEB-005; 2026-09-28).
;
; A Subject or From such as `=?UTF-8?B?R3LDvMOfZQ==?=' is shown as the text
; it encodes.  `fn-w47-decode' is the list model; books/web-render.lisp's
; (:w S . E) segment applies it to a span of fn-web-in and escapes the
; result like any other text, so the page's escaping keystone
; (fn-wr-emit-writes-vocabulary-or-escaped) covers decoded text unchanged:
; an encoded `<' is shown as `&lt;'.
;
; What is decoded (RFC 2047, cited by section):
;   encoded-word = "=?" charset "?" encoding "?" encoded-text "?="    (2)
;     at most 75 octets (2); charset, encoding and encoded-text contain
;     no SP, CTL or "?" (2); a charset may carry an RFC 2231 section 5
;     "*language" suffix, which is dropped
;   encoding B: base64 (4.1; books/octet-text.lisp fn-ot-b64-decode,
;     refusing a non-canonical text); Q: "_" is SP, "=" two hex digits
;     is that octet (4.2); a "=" without them refuses the word
;   charsets UTF-8, US-ASCII (every octet below 128) and ISO-8859-1
;     (each octet mapped to its UTF-8 sequence), case-insensitively
;   linear white space between two encoded-words is dropped (6.2)
; Anything else -- another charset, a malformed word, a word longer than
; 75 octets -- is shown as it is.  LOCAL POLICY: a field longer than
; *fn-w47-max* octets is shown as it is, undecoded (the emitter copies the
; span into a list to decode it; D27 bounds that copy, never the field).
; The decoded octets are not checked as UTF-8: the page is served as UTF-8
; and the browser shows a replacement character for a bad sequence.
;
; Work: one pass; at each "=?" the word parse reads at most 75 octets, so
; decoding a field of N octets reads at most 76 N.
;
; KEYSTONES
;   fn-w47-decode-without-openers-is-identity  a field with no "=?" is
;                                              shown exactly as it is
;   fn-w47-decode-octets                       the decoded field is octets

(in-package "ACL2")
(include-book "octet-text")

(defconst *fn-w47-max* 4096)
(defconst *fn-w47-word-max* 75)

(defconst *fn-w47-utf-8* '(117 116 102 45 56))                        ; utf-8
(defconst *fn-w47-us-ascii* '(117 115 45 97 115 99 105 105))          ; us-ascii
(defconst *fn-w47-latin-1* '(105 115 111 45 56 56 53 57 45 49))      ; iso-8859-1

(defun fn-w47-rev (xs acc)
  (declare (xargs :guard t))
  (if (consp xs) (fn-w47-rev (cdr xs) (cons (car xs) acc)) acc))

; An octet of charset, encoding or encoded-text: VCHAR except "?".
(defun fn-w47-textp (o)
  (declare (xargs :guard t))
  (and (integerp o) (< 32 o) (< o 127) (not (equal o 63))))

; (mv FOUND TOKEN REST): the octets before the first "?" among the next N,
; and what follows that "?"; FOUND nil when there is none or a non-text
; octet comes first.
(defun fn-w47-field (xs n acc)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (cond ((or (zp n) (atom xs)) (mv nil nil xs))
        ((equal (car xs) 63) (mv t (fn-w47-rev acc nil) (cdr xs)))
        ((not (fn-w47-textp (car xs))) (mv nil nil xs))
        (t (fn-w47-field (cdr xs) (1- n) (cons (car xs) acc)))))

(defthm fn-w47-field-rest-shorter
  (and (<= (len (mv-nth 2 (fn-w47-field xs n acc))) (len xs))
       (implies (mv-nth 0 (fn-w47-field xs n acc))
                (< (len (mv-nth 2 (fn-w47-field xs n acc))) (len xs))))
  :rule-classes :linear)

(defthm fn-w47-true-listp-rev
  (implies (true-listp acc) (true-listp (fn-w47-rev xs acc))))

(defun fn-w47-before-star (xs)
  ; RFC 2231 section 5: charset "*" language.
  (declare (xargs :guard t))
  (if (and (consp xs) (not (equal (car xs) 42)))
      (cons (car xs) (fn-w47-before-star (cdr xs)))
    nil))

(defun fn-w47-charset (cs)
  (declare (xargs :guard t))
  (let ((name (fn-ot-downcase (fn-w47-before-star cs))))
    (cond ((equal name *fn-w47-utf-8*) :utf-8)
          ((equal name *fn-w47-us-ascii*) :us-ascii)
          ((equal name *fn-w47-latin-1*) :latin-1)
          (t nil))))

; Q (4.2): (mv OK OCTETS).
(defun fn-w47-q (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) (mv t nil))
        ((equal (car xs) 95)
         (mv-let (ok rest) (fn-w47-q (cdr xs)) (mv ok (and ok (cons 32 rest)))))
        ((equal (car xs) 61)
         (if (and (consp (cdr xs)) (consp (cddr xs))
                  (fn-ot-hex-value (cadr xs)) (fn-ot-hex-value (caddr xs)))
             (mv-let (ok rest) (fn-w47-q (cdddr xs))
               (mv ok (and ok (cons (+ (* 16 (fn-ot-hex-value (cadr xs)))
                                       (fn-ot-hex-value (caddr xs)))
                                    rest))))
           (mv nil nil)))
        ((fn-cbor-octetp (car xs))
         (mv-let (ok rest) (fn-w47-q (cdr xs)) (mv ok (and ok (cons (car xs) rest)))))
        (t (mv nil nil))))

(defun fn-w47-asciip (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs)) (<= 0 (car xs)) (< (car xs) 128) (fn-w47-asciip (cdr xs)))
    t))

(defun fn-w47-latin-1 (xs)
  ; Each octet as its UTF-8 sequence (U+0000..U+00FF).
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (if (consp xs)
      (let ((o (car xs)))
        (cond ((< o 128) (cons o (fn-w47-latin-1 (cdr xs))))
              ((< o 192) (list* 194 o (fn-w47-latin-1 (cdr xs))))          ; C2 80..BF
              (t (list* 195 (- o 64) (fn-w47-latin-1 (cdr xs))))))          ; C3 80..BF
    nil))

; The octets one word stands for: (mv OK OCTETS).
(defun fn-w47-payload (cs enc txt)
  (declare (xargs :guard t))
  (let ((charset (fn-w47-charset cs)))
    (mv-let (ok raw)
      (cond ((member enc '(66 98))
             (mv-let (err out) (fn-ot-b64-decode txt) (mv (not err) out)))
            ((member enc '(81 113)) (fn-w47-q txt))
            (t (mv nil nil)))
      (cond ((not (and ok charset (fn-cbor-octet-listp raw))) (mv nil nil))
            ((equal charset :latin-1) (mv t (fn-w47-latin-1 raw)))
            ((equal charset :us-ascii) (if (fn-w47-asciip raw) (mv t raw) (mv nil nil)))
            (t (mv t raw))))))

; One encoded-word opening XS: (mv OK OCTETS REST).
(defun fn-w47-word (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (equal (car xs) 61) (consp (cdr xs)) (equal (cadr xs) 63))
      (mv-let (ok1 cs r1) (fn-w47-field (cddr xs) *fn-w47-word-max* nil)
        (mv-let (ok2 enc r2) (fn-w47-field r1 *fn-w47-word-max* nil)
          (mv-let (ok3 txt r3) (fn-w47-field r2 *fn-w47-word-max* nil)
            (if (and ok1 ok2 ok3 (consp cs) (consp enc) (atom (cdr enc)) (consp txt)
                     (consp r3) (equal (car r3) 61)
                     (<= (+ 7 (len cs) (len txt)) *fn-w47-word-max*))
                (mv-let (ok out) (fn-w47-payload cs (car enc) txt)
                  (if ok (mv t out (cdr r3)) (mv nil nil xs)))
              (mv nil nil xs)))))
    (mv nil nil xs)))

(defthm fn-w47-len-cdr
  (implies (consp x) (< (len (cdr x)) (len x)))
  :rule-classes :linear)

(defthm fn-w47-word-rest-shorter
  (implies (mv-nth 0 (fn-w47-word xs))
           (< (len (mv-nth 2 (fn-w47-word xs))) (len xs)))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-w47-word) (fn-w47-payload fn-w47-field)))))

(defthm fn-w47-payload-true-listp
  (true-listp (mv-nth 1 (fn-w47-payload cs enc txt))))

(defthm fn-w47-word-out-true-listp
  (true-listp (mv-nth 1 (fn-w47-word xs)))
  :hints (("Goal" :in-theory (disable fn-w47-payload))))

(defun fn-w47-lwspp (o)
  (declare (xargs :guard t))
  (and (member o '(32 9 13 10)) t))

; (mv RUN REST): the linear white space opening XS.
(defun fn-w47-lws (xs acc)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-w47-lwspp (car xs)))
      (fn-w47-lws (cdr xs) (cons (car xs) acc))
    (mv (fn-w47-rev acc nil) xs)))

(defthm fn-w47-lws-rest-shorter
  (and (<= (len (mv-nth 1 (fn-w47-lws xs acc))) (len xs))
       (implies (and (consp xs) (fn-w47-lwspp (car xs)))
                (< (len (mv-nth 1 (fn-w47-lws xs acc))) (len xs))))
  :rule-classes :linear)

(defthm fn-w47-lws-run-true-listp
  (true-listp (car (fn-w47-lws xs acc))))

(defun fn-w47-wordp (xs)
  (declare (xargs :guard t))
  (mv-let (ok out rest) (fn-w47-word xs)
    (declare (ignore out rest))
    ok))

(in-theory (disable fn-w47-word fn-w47-lwspp))

; PREV: the octets just before XS ended an encoded-word.
(defun fn-w47-decode-aux (xs prev)
  (declare (xargs :guard t :measure (len xs)
                  :guard-hints (("Goal" :in-theory (disable fn-w47-lws)))))
  (if (atom xs)
      nil
    (mv-let (ok out rest) (fn-w47-word xs)
      (if ok
          (append out (fn-w47-decode-aux rest t))
        (if (and prev (fn-w47-lwspp (car xs)))
            (mv-let (run rest2) (fn-w47-lws xs nil)
              (if (fn-w47-wordp rest2)
                  (fn-w47-decode-aux rest2 t)                      ; 6.2: dropped
                (append run (fn-w47-decode-aux rest2 nil))))
          (cons (car xs) (fn-w47-decode-aux (cdr xs) nil)))))))

; THE HOST-REACHED MODEL: books/web-render.lisp's (:w S . E) piece.
(defun fn-w47-decode (xs)
  (declare (xargs :guard t))
  (if (and (true-listp xs) (<= (len xs) *fn-w47-max*))
      (fn-w47-decode-aux xs nil)
    xs))

; -----------------------------------------------------------------------------
; The decoded field is octets.

(defthm fn-w47-octets-of-rev
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp (fn-w47-rev xs acc))))

(defthm fn-w47-field-token-octets
  (implies (fn-cbor-octet-listp acc)
           (fn-cbor-octet-listp (mv-nth 1 (fn-w47-field xs n acc)))))

(defthm fn-w47-field-rest-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (mv-nth 2 (fn-w47-field xs n acc)))))

(defthm fn-w47-octets-of-latin-1
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-w47-latin-1 xs))))

(defthm fn-w47-payload-octets
  (fn-cbor-octet-listp (mv-nth 1 (fn-w47-payload cs enc txt))))

(defthm fn-w47-octets-of-cdr
  (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (cdr xs))))

(defthm fn-w47-word-octets
  (and (fn-cbor-octet-listp (mv-nth 1 (fn-w47-word xs)))
       (implies (fn-cbor-octet-listp xs)
                (fn-cbor-octet-listp (mv-nth 2 (fn-w47-word xs)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-w47-word) (fn-w47-payload fn-w47-field)))))

(defthm fn-w47-lws-octets
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octet-listp acc))
           (and (fn-cbor-octet-listp (car (fn-w47-lws xs acc)))
                (fn-cbor-octet-listp (mv-nth 1 (fn-w47-lws xs acc))))))

(defthm fn-w47-octets-append
  (implies (fn-cbor-octet-listp a)
           (equal (fn-cbor-octet-listp (append a b)) (fn-cbor-octet-listp b))))

(defthm fn-w47-decode-aux-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-w47-decode-aux xs prev))))

(defthm fn-w47-decode-octets
  ; KEYSTONE (PRF-353): what the page shows for an octet field is octets.
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-w47-decode xs))))

; -----------------------------------------------------------------------------
; A field with no encoded-word opener is shown as it is.

(defun fn-w47-no-openersp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (and (equal (car xs) 61) (consp (cdr xs)) (equal (cadr xs) 63)))
           (fn-w47-no-openersp (cdr xs)))
    t))

(defthm fn-w47-word-needs-an-opener
  (implies (fn-w47-no-openersp xs)
           (not (car (fn-w47-word xs))))
  :hints (("Goal" :in-theory (enable fn-w47-word))))

(defthm fn-w47-lws-rest-true-listp
  (implies (true-listp xs) (true-listp (mv-nth 1 (fn-w47-lws xs acc)))))

(defthm fn-w47-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-w47-rev-of-append
  (equal (fn-w47-rev xs (append a b)) (append (fn-w47-rev xs a) b)))

(defthm fn-w47-rev-append
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (fn-w47-rev xs acc) (append (fn-w47-rev xs nil) acc)))
  :hints (("Goal" :use ((:instance fn-w47-rev-of-append (a nil) (b acc)))
           :in-theory (disable fn-w47-rev-of-append))))

(defthm fn-w47-lws-splits
  (equal (append (car (fn-w47-lws xs acc)) (mv-nth 1 (fn-w47-lws xs acc)))
         (append (fn-w47-rev acc nil) xs))
  :hints (("Goal" :induct (fn-w47-lws xs acc))))

(defthm fn-w47-no-openersp-of-lws-rest
  (implies (fn-w47-no-openersp xs)
           (fn-w47-no-openersp (mv-nth 1 (fn-w47-lws xs acc)))))

(defthm fn-w47-decode-aux-without-openers
  (implies (and (true-listp xs) (fn-w47-no-openersp xs))
           (equal (fn-w47-decode-aux xs prev) xs))
  :hints (("Goal" :induct (fn-w47-decode-aux xs prev))))

(defthm fn-w47-decode-without-openers-is-identity
  ; KEYSTONE (PRF-353): a field with no "=?" is shown exactly as it is.
  (implies (fn-w47-no-openersp xs)
           (equal (fn-w47-decode xs) xs)))

(defthm fn-w47-decode-of-long
  ; A field past the bound is shown as it is.
  (implies (< *fn-w47-max* (len xs))
           (equal (fn-w47-decode xs) xs)))

(in-theory (disable fn-w47-decode))
