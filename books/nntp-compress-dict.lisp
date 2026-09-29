; fn: the wire dictionary negotiation's decisions (NNT-055, lane compress-4;
; docs/extensions/nntp-compress-dict.md "Negotiation").  Prefix `fn-zdn-'.
;
;   the capability line           `fn-zdn-capability-line': XFN-DICT and the
;                                  full BLAKE3 digests (lower-case hex) of the
;                                  shipped dictionaries, newest first
;   the capability block          `fn-zdn-capability-lines': the line joins
;                                  the block of a connection that may ask
;   the request                   `fn-zdn-request': XFN-ZARTICLE <message-id>
;                                  <b3-hex> ..., the digests the peer holds
;   the reply's form              `fn-zdn-choose': over the store's answer
;                                  (DICT C N), stored when the peer holds
;                                  DICT's digest, else :decoded (ARTICLE's)
;   the stored body               `fn-zdn-body-lines': C escaped (yEnc's
;                                  four critical octets) and cut into lines
;                                  (lane compress-5; served by
;                                  books/nntp-zarticle.lisp)
;
; KEYSTONES: `fn-zdn-choose-stored-only-shared' (a stored answer names the
; digest the shipped table records for the answer's dictionary, that digest
; is one the peer listed, and it names the same octets back) and
; `fn-zdn-choose-complete' (an answer whose dictionary the peer holds is
; always stored: the peer is never sent decoded octets it could have had as
; stored); `fn-zdn-body-round-trip' (join and unescape give C back).  `fn-zdn-request-shape': a parsed request names a message-id and
; one 32-octet digest for each token after it.

(in-package "ACL2")
(include-book "nntp-syntax") ; below books/nntp.lisp, which includes this book's includer
(include-book "payload-lz-dicts")

; -----------------------------------------------------------------------------
; Hex.

(defun fn-zdn-hex-digit (d)
  (declare (xargs :guard t))
  (let ((d (nfix d)))
    (if (< d 10) (+ 48 d) (+ 87 (min d 15)))))

(defun fn-zdn-hex (octets)
  ; Lower-case hex, two digits an octet.
  (declare (xargs :guard t))
  (if (consp octets)
      (let ((o (nfix (car octets))))
        (list* (fn-zdn-hex-digit (floor (min o 255) 16))
               (fn-zdn-hex-digit (mod (min o 255) 16))
               (fn-zdn-hex (cdr octets))))
    nil))

(defun fn-zdn-hex-value (c)
  ; A lower-case hex digit's value, or nil.
  (declare (xargs :guard t))
  (cond ((not (integerp c)) nil)
        ((and (<= 48 c) (<= c 57)) (- c 48))
        ((and (<= 97 c) (<= c 102)) (- c 87))
        (t nil)))

(defun fn-zdn-unhex (token)
  ; The octets a lower-case hex token names, or :bad.
  (declare (xargs :guard t))
  (cond ((atom token) (if (null token) nil :bad))
        ((atom (cdr token)) :bad)
        (t (let ((hi (fn-zdn-hex-value (car token)))
                 (lo (fn-zdn-hex-value (cadr token)))
                 (rest (fn-zdn-unhex (cddr token))))
             (if (and hi lo (not (equal rest :bad)))
                 (cons (+ (* 16 hi) lo) rest)
               :bad)))))

; -----------------------------------------------------------------------------
; The advertisement.

(defun fn-zdn-digests-of (entries)
  ; The shipped entries' digests, oldest first.
  (declare (xargs :guard t))
  (if (consp entries)
      (cons (if (and (consp (car entries)) (consp (cdar entries))) (cadar entries) nil)
            (fn-zdn-digests-of (cdr entries)))
    nil))

(defun fn-zdn-digests ()
  ; Newest first, as the capability lists them.
  (declare (xargs :guard t))
  (reverse (fn-zdn-digests-of (fn-lzd-shipped))))

(defun fn-zdn-hex-words (digests)
  (declare (xargs :guard t))
  (if (consp digests)
      (append (list 32) (fn-zdn-hex (car digests)) (fn-zdn-hex-words (cdr digests)))
    nil))

(defun fn-zdn-capability-line ()
  (declare (xargs :guard t))
  (append (fn-nntp-string-octets "XFN-DICT") (fn-zdn-hex-words (fn-zdn-digests))))

(defun fn-zdn-capability-lines (lines mayp)
  ; LINES with the XFN-DICT line when this connection may ask for stored
  ; payloads (the COMPRESS policy's: an authenticated connection or a
  ; configured peer, fn-auth-compress-mayp).
  (declare (xargs :guard t))
  (if mayp (append (true-list-fix lines) (list (fn-zdn-capability-line))) lines))

; -----------------------------------------------------------------------------
; The request: XFN-ZARTICLE <message-id> <b3-hex> [<b3-hex> ...].

(defun fn-zdn-digest-tokens (tokens)
  ; The 32-octet digests TOKENS name, or :bad.
  (declare (xargs :guard t))
  (if (consp tokens)
      (let ((d (fn-zdn-unhex (car tokens)))
            (rest (fn-zdn-digest-tokens (cdr tokens))))
        (if (and (not (equal d :bad)) (equal (len d) 32) (not (equal rest :bad)))
            (cons d rest)
          :bad))
    (if (null tokens) nil :bad)))

(defun fn-zdn-request (args)
  ; (:ask MESSAGE-ID DIGESTS) or :syntax.
  (declare (xargs :guard t))
  (if (and (consp args) (consp (cdr args))
           (fn-nntp-message-id-tokenp (car args)))
      (let ((ds (fn-zdn-digest-tokens (cdr args))))
        (if (equal ds :bad) :syntax (list :ask (car args) ds)))
    :syntax))

;; -----------------------------------------------------------------------------
; The reply's form.  STORED is what the store holds for the article's payload
; when it is held compressed, (DICT C N): C a DEFLATE stream that decodes
; against the dictionary octets DICT to the N payload octets
; (books/assumptions-stored.lisp A-ARENA-STORED says so of the served read),
; or nil.  The digest named for DICT is the shipped table's: the entry whose
; octets ARE DICT (BLAKE3 over them was checked when the table's book was
; certified), so a peer that listed it holds the same octets.

(defun fn-zdn-digest-of-dict-in (dict entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (let ((e (car entries)))
        (if (and (consp e) (consp (cdr e)) (consp (cddr e)) (equal (caddr e) dict))
            (cadr e)
          (fn-zdn-digest-of-dict-in dict (cdr entries))))
    nil))

(defun fn-zdn-digest-of-dict (dict)
  ; The full digest the shipped table records for the dictionary octets
  ; DICT, or nil (the empty dictionary, and any octets not shipped).
  (declare (xargs :guard t))
  (fn-zdn-digest-of-dict-in dict (fn-lzd-shipped)))

(defun fn-zdn-dict-of-digest-in (digest entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (let ((e (car entries)))
        (if (and (consp e) (consp (cdr e)) (consp (cddr e)) (equal (cadr e) digest))
            (caddr e)
          (fn-zdn-dict-of-digest-in digest (cdr entries))))
    nil))

(defun fn-zdn-dict-of-digest (digest)
  ; The dictionary octets a peer holding DIGEST decodes with.
  (declare (xargs :guard t))
  (fn-zdn-dict-of-digest-in digest (fn-lzd-shipped)))

(defthm fn-zdn-dict-of-digest-of-dict
  ; A digest named for DICT names DICT back (the table's digests are
  ; distinct: fn-lzd-entries-okp, checked at certification).
  (implies (fn-zdn-digest-of-dict dict)
           (equal (fn-zdn-dict-of-digest (fn-zdn-digest-of-dict dict)) dict))
  :hints (("Goal" :in-theory (enable fn-lzd-shipped))))

(defun fn-zdn-choose (stored digests)
  ; (:stored DIGEST) when the peer listed the digest of STORED's dictionary,
  ; else :decoded.
  (declare (xargs :guard (true-listp digests)))
  (let ((d (and (consp stored) (fn-zdn-digest-of-dict (car stored)))))
    (if (and d (member-equal d digests)) (list :stored d) :decoded)))

(defthm fn-zdn-choose-stored-only-shared
  (let ((r (fn-zdn-choose stored digests)))
    (implies (equal (car r) :stored)
             (and (consp stored)
                  (equal (cadr r) (fn-zdn-digest-of-dict (car stored)))
                  (cadr r)
                  (member-equal (cadr r) digests)
                  (equal (fn-zdn-dict-of-digest (cadr r)) (car stored))))))

(defthm fn-zdn-choose-complete
  (implies (and (consp stored)
                (fn-zdn-digest-of-dict (car stored))
                (member-equal (fn-zdn-digest-of-dict (car stored)) digests))
           (equal (fn-zdn-choose stored digests)
                  (list :stored (fn-zdn-digest-of-dict (car stored))))))

(defthm fn-zdn-choose-answers
  (or (equal (fn-zdn-choose stored digests) :decoded)
      (equal (car (fn-zdn-choose stored digests)) :stored))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The stored reply's body.  RFC 3977 section 3.1.1: a multi-line block
; carries no NUL, CR or LF apart from its line endings, so C (binary) is
; not sent raw.  Each of NUL, LF, CR and "=" is escaped as "=" and the octet
; plus 64 (mod 256), as yEnc does on Usenet; the escaped stream holds none
; of the three, so it is cut into lines of at most *fn-zdn-line* octets
; anywhere (a line break may fall inside an escape: the receiver joins the
; lines before it unescapes).  The block is then dot-stuffed as every block
; is (fn-nntp-stuff-lines).  The reply line carries C's length, and the
; receiver checks it.  KEYSTONE fn-zdn-body-round-trip: joining the body's
; lines and unescaping gives C back, for every octet list C.

(defconst *fn-zdn-line* 128)

(defun fn-zdn-criticalp (o)
  (declare (xargs :guard t))
  (or (equal o 0) (equal o 10) (equal o 13) (equal o 61)))

(defun fn-zdn-shift (o)
  ; A critical octet plus 64: NUL 64, LF 74, CR 77, "=" 125.
  (declare (xargs :guard t))
  (case o (0 64) (10 74) (13 77) (otherwise 125)))

(defun fn-zdn-unshift (o)
  ; An escaped octet minus 64 (mod 256), as yEnc decoders read it.
  (declare (xargs :guard t))
  (case o (64 0) (74 10) (77 13) (125 61) (otherwise (mod (+ 192 (nfix o)) 256))))

(defun fn-zdn-escape (c)
  (declare (xargs :guard t))
  (if (consp c)
      (if (fn-zdn-criticalp (car c))
          (list* 61 (fn-zdn-shift (car c)) (fn-zdn-escape (cdr c)))
        (cons (car c) (fn-zdn-escape (cdr c))))
    nil))

(defun fn-zdn-unescape (e)
  (declare (xargs :guard t))
  (if (consp e)
      (if (and (equal (car e) 61) (consp (cdr e)))
          (cons (fn-zdn-unshift (cadr e)) (fn-zdn-unescape (cddr e)))
        (cons (car e) (fn-zdn-unescape (cdr e))))
    nil))

(defthm fn-zdn-unescape-escape
  (equal (fn-zdn-unescape (fn-zdn-escape c)) (true-list-fix c)))

(local (defthm fn-zdn-len-nthcdr-le
  (<= (len (nthcdr n e)) (len e))
  :rule-classes :linear))

(local (defthm fn-zdn-len-nthcdr
  (implies (and (consp e) (posp n)) (< (len (nthcdr n e)) (len e)))
  :hints (("Goal" :expand ((nthcdr n e))
           :use ((:instance fn-zdn-len-nthcdr-le (n (+ -1 n)) (e (cdr e))))))))

(defun fn-zdn-chunks (e)
  ; E cut into lines of *fn-zdn-line* octets, the last one shorter.
  (declare (xargs :guard (true-listp e) :measure (len e)))
  (if (consp e)
      (cons (take (min *fn-zdn-line* (len e)) e)
            (fn-zdn-chunks (nthcdr *fn-zdn-line* e)))
    nil))

(defun fn-zdn-join (lines)
  (declare (xargs :guard (true-list-listp lines)))
  (if (consp lines) (append (car lines) (fn-zdn-join (cdr lines))) nil))

(local (defthm fn-zdn-append-take-nthcdr
  (implies (and (true-listp e) (natp n) (<= n (len e)))
           (equal (append (take n e) (nthcdr n e)) e))))

(local (defthm fn-zdn-nthcdr-past
  (implies (and (true-listp e) (natp n) (<= (len e) n))
           (equal (nthcdr n e) nil))))

(local (defthm fn-zdn-take-len
  (implies (true-listp e) (equal (take (len e) e) e))))

(defthm fn-zdn-join-chunks
  (implies (true-listp e) (equal (fn-zdn-join (fn-zdn-chunks e)) e))
  :hints (("Goal" :in-theory (disable take nthcdr))))

(defun fn-zdn-body-lines (c)
  (declare (xargs :guard t :verify-guards nil))
  (fn-zdn-chunks (fn-zdn-escape c)))

(defthm fn-zdn-true-listp-escape (true-listp (fn-zdn-escape c)))
(verify-guards fn-zdn-body-lines)

(defthm fn-zdn-body-round-trip
  (equal (fn-zdn-unescape (fn-zdn-join (fn-zdn-body-lines c)))
         (true-list-fix c)))

(defun fn-zdn-digest-listp (ds)
  (declare (xargs :guard t))
  (if (consp ds)
      (and (true-listp (car ds)) (equal (len (car ds)) 32) (fn-zdn-digest-listp (cdr ds)))
    (null ds)))

(local (defthm fn-zdn-unhex-true-listp
  (implies (not (equal (fn-zdn-unhex tk) :bad)) (true-listp (fn-zdn-unhex tk)))))

(local (defthm fn-zdn-digest-tokens-shape
  (implies (not (equal (fn-zdn-digest-tokens ts) :bad))
           (and (fn-zdn-digest-listp (fn-zdn-digest-tokens ts))
                (equal (len (fn-zdn-digest-tokens ts)) (len ts))))))

(local (defthm fn-zdn-len-of-consp
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear))

; A parsed request names a message-id and one or more 32-octet digests, one
; for each token after it.
(defthm fn-zdn-request-shape
  (let ((r (fn-zdn-request args)))
    (implies (not (equal r :syntax))
             (and (equal (car r) :ask)
                  (fn-nntp-message-id-tokenp (cadr r))
                  (consp (caddr r))
                  (fn-zdn-digest-listp (caddr r))
                  (equal (len (caddr r)) (len (cdr args))))))
  :hints (("Goal" :in-theory (disable fn-zdn-digest-tokens-shape)
           :use ((:instance fn-zdn-digest-tokens-shape (ts (cdr args)))))))

(in-theory (disable fn-zdn-choose fn-zdn-request fn-zdn-capability-line))

