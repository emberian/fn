; fn: the RFC 8315 lines the injecting node generates, where it puts them,
; and how the D25 comparison sets them aside (SEC-006, PRF-210; D25; gpt-6's
; wave-5 review section 3).
;
; On a served POST from an authenticated account the owner puts at most two
; header lines IN FRONT of the injected octets (books/cancel-lock.lisp
; `fn-cl-served-payload'):
;
;   Cancel-Lock: sha256:LOCK CRLF                     LOCK 44 Base64 characters
;   Cancel-Key: sha256:KEY [SP sha256:KEY ...] CRLF   one KEY per retained epoch
;
; They are injecting-node metadata, outside the authored source, like Path,
; Injection-Date and Injection-Info (D25).  In front of the injected block
; they are unambiguous: every injected article this node writes opens with
; its block ("Path: " in recipe v2, "Injection-" in recipe v3), which the
; poster never supplies, and the poster's source follows the block.  So a
; leading line opening "Cancel-Lock:" or "Cancel-Key:" is the node's, and a
; Cancel-Lock the poster wrote, wherever it stands in the source, is the
; poster's input and stays in the comparison subject.
;
; `fn-cll-skip' removes the node's leading lines; books/poster-bytes.lisp
; reads the agent and the source of an article through it, so a same-source
; retry is "already stored here" whatever account or key epoch posted it,
; and the node's lines never enter the comparison
; (`fn-cll-skip-of-the-generated-lines').
;
; No dependency: octet constants and list walks.
;
; Prefix `fn-cll-' (docs/prefixes.md).
(in-package "ACL2")

; "Cancel-Lock: sha256:"
(defconst *fn-cll-lock-head*
  '(67 97 110 99 101 108 45 76 111 99 107 58 32 115 104 97 50 53 54 58))
; "Cancel-Key:"
(defconst *fn-cll-key-field*
  '(67 97 110 99 101 108 45 75 101 121 58))
; " sha256:"
(defconst *fn-cll-key-word* '(32 115 104 97 50 53 54 58))
; "Cancel-Lock:"
(defconst *fn-cll-lock-field*
  '(67 97 110 99 101 108 45 76 111 99 107 58))
(defconst *fn-cll-value-length* 44)   ; Base64 of 32 octets

(defun fn-cll-append (a b)
  (declare (xargs :guard t))
  (if (consp a) (cons (car a) (fn-cll-append (cdr a) b)) b))

(defthm fn-cll-append-is-append
  (equal (fn-cll-append a b) (append a b)))

; The line HEAD VALUE CRLF.
(defun fn-cll-line (head value)
  (declare (xargs :guard t))
  (fn-cll-append head (fn-cll-append value '(13 10))))

; " sha256:K1 sha256:K2 ..." for the keys KEYS.
(defun fn-cll-key-values (keys)
  (declare (xargs :guard t))
  (if (consp keys)
      (fn-cll-append *fn-cll-key-word*
                     (fn-cll-append (car keys) (fn-cll-key-values (cdr keys))))
    nil))

; "Cancel-Key: sha256:K1 sha256:K2 ..." CRLF
(defun fn-cll-key-line (keys)
  (declare (xargs :guard t))
  (fn-cll-line *fn-cll-key-field* (fn-cll-key-values keys)))

; A Base64 character (RFC 4648 section 4 alphabet, and the pad).
(defun fn-cll-b64-charp (c)
  (declare (xargs :guard t))
  (and (integerp c)
       (or (and (<= 65 c) (<= c 90)) (and (<= 97 c) (<= c 122))
           (and (<= 48 c) (<= c 57)) (equal c 43) (equal c 47) (equal c 61))))

; A value of Base64 characters.
(defun fn-cll-valuep (v)
  (declare (xargs :guard t))
  (if (consp v)
      (and (fn-cll-b64-charp (car v)) (fn-cll-valuep (cdr v)))
    (null v)))

(defun fn-cll-values-p (vs)
  (declare (xargs :guard t))
  (if (consp vs)
      (and (fn-cll-valuep (car vs)) (fn-cll-values-p (cdr vs)))
    (null vs)))

; X opens with PREFIX; the rest, or :no.
(defun fn-cll-strip (prefix x)
  (declare (xargs :guard t))
  (if (consp prefix)
      (if (and (consp x) (equal (car x) (car prefix)))
          (fn-cll-strip (cdr prefix) (cdr x))
        :no)
    x))

; X after its first LF; nil when it has none.
(defun fn-cll-after-line (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10) (cdr x) (fn-cll-after-line (cdr x)))
    nil))

; X without a leading line opening with FIELD.
(defun fn-cll-skip-one (field x)
  (declare (xargs :guard t))
  (if (equal (fn-cll-strip field x) :no) x (fn-cll-after-line x)))

; THE D25 PROJECTION of the node's lines: X without a leading Cancel-Lock
; line, then without a leading Cancel-Key line (the order the node writes).
(defun fn-cll-skip (x)
  (declare (xargs :guard t))
  (fn-cll-skip-one *fn-cll-key-field* (fn-cll-skip-one *fn-cll-lock-field* x)))

; The lines the node writes: the lock line when LOCK is a value, then the key
; line when KEYS is not empty.
(defun fn-cll-lines (lock keys)
  (declare (xargs :guard t))
  (fn-cll-append (if lock (fn-cll-line *fn-cll-lock-head* lock) nil)
                 (if (consp keys) (fn-cll-key-line keys) nil)))

; -----------------------------------------------------------------------------
; Theorems.

(defthm fn-cll-skip-of-an-article-not-opening-with-c
  (implies (not (equal (car x) 67))
           (equal (fn-cll-skip x) x))
  :hints (("Goal" :in-theory (enable fn-cll-skip-one fn-cll-strip))))

(local
 (defthm fn-cll-b64-valuep-has-no-lf
   (implies (fn-cll-valuep v)
            (equal (fn-cll-after-line (append v x)) (fn-cll-after-line x)))))

(local
 (defthm fn-cll-key-values-have-no-lf
   (implies (fn-cll-values-p keys)
            (equal (fn-cll-after-line (append (fn-cll-key-values keys) x))
                   (fn-cll-after-line x)))))

(local
 (defthm fn-cll-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-cll-strip-of-append
   (implies (true-listp p)
            (equal (fn-cll-strip p (append p x)) x))))

; KEYSTONE (D25: the generated lines leave the comparison).  Whatever lock
; and keys the node writes, for whichever account and key epoch, the D25
; projection of the stored octets is the injected octets exactly.  Subject:
; `fn-cll-skip', which books/poster-bytes.lisp fn-pb-path-agent and
; fn-pb-subject call on both payloads the host's D25 verdict compares
; (host/owner-host.lisp fn-owner-existing-action-buffer, fn-owner-prepare-
; buffer); the lines are books/cancel-lock.lisp fn-cl-served-payload's.
(defthm fn-cll-skip-of-the-generated-lines
  (implies (and (or (null lock) (fn-cll-valuep lock))
                (fn-cll-values-p keys)
                (not (equal (car x) 67)))
           (equal (fn-cll-skip (append (fn-cll-lines lock keys) x)) x))
  :hints (("Goal" :in-theory (e/d (fn-cll-skip-one) (fn-cll-key-values)))))

(in-theory (disable fn-cll-skip))
