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
;   the reply's form              `fn-zdn-choose': per stored payload, the
;                                  stored frame as it is stored when the
;                                  peer holds the frame's dictionary, else
;                                  :decoded (the article, decoded here and
;                                  sent as ARTICLE sends it: raw, or inside
;                                  the connection's COMPRESS DEFLATE layer)
;
; KEYSTONES: `fn-zdn-choose-stored-only-shared' (a stored answer names the
; digest the shipped table records for the frame's DICT-ID, that digest is
; one the peer listed, and the frame parses) and `fn-zdn-choose-complete'
; (a parsed frame whose dictionary the peer holds is always answered
; stored: the peer is never sent decoded octets it could have had as
; stored).  `fn-zdn-request-shape': a parsed request names a message-id and
; one 32-octet digest for each token after it.

(in-package "ACL2")
(include-book "nntp-compress")
(include-book "payload-lz-record")

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

; -----------------------------------------------------------------------------
; The reply's form.

(defun fn-zdn-digest-of-id-in (id entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (and (consp (car entries)) (consp (cdar entries)) (equal (caar entries) id))
          (cadar entries)
        (fn-zdn-digest-of-id-in id (cdr entries)))
    nil))

(defun fn-zdn-digest-of-id (id)
  ; The full digest the shipped table records for DICT-ID ID, or nil (ID 0,
  ; the empty dictionary, has none: a frame over it is sent decoded).
  (declare (xargs :guard t))
  (fn-zdn-digest-of-id-in id (fn-lzd-shipped)))

(defun fn-zdn-choose (z digests)
  ; Z the stored payload's octets (the payload-lz-record frame), DIGESTS the
  ; ones the peer holds: (:stored DIGEST) or :decoded.
  (declare (xargs :guard (and (true-listp z) (true-listp digests))))
  (let ((f (fn-lzr-parse z)))
    (if f
        (let ((d (fn-zdn-digest-of-id (car f))))
          (if (and d (member-equal d digests)) (list :stored d) :decoded))
      :decoded)))

(defthm fn-zdn-choose-stored-only-shared
  (let ((r (fn-zdn-choose z digests)))
    (implies (equal (car r) :stored)
             (and (fn-lzr-parse z)
                  (equal (cadr r) (fn-zdn-digest-of-id (car (fn-lzr-parse z))))
                  (cadr r)
                  (member-equal (cadr r) digests)))))

(defthm fn-zdn-choose-complete
  (implies (and (fn-lzr-parse z)
                (fn-zdn-digest-of-id (car (fn-lzr-parse z)))
                (member-equal (fn-zdn-digest-of-id (car (fn-lzr-parse z))) digests))
           (equal (fn-zdn-choose z digests)
                  (list :stored (fn-zdn-digest-of-id (car (fn-lzr-parse z)))))))

(defthm fn-zdn-choose-answers
  (or (equal (fn-zdn-choose z digests) :decoded)
      (equal (car (fn-zdn-choose z digests)) :stored))
  :rule-classes nil)

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
