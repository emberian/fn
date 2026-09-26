; fn: where the owner writes the Cancel-Lock and Cancel-Key lines (SEC-006,
; PRF-210).
;
; On a served POST from an authenticated login the owner adds at most two
; header lines to the injected octets (books/cancel-lock.lisp
; `fn-cl-served-payload'):
;
;   Cancel-Lock: sha256:LOCK CRLF     LOCK 44 Base64 characters
;   Cancel-Key: sha256:KEY CRLF       KEY  44 Base64 characters
;
; the lock first, directly after the node's own Injection-Info line: the
; first header line opening "Injection-Info: " (a proto-article carrying
; Injection-Info is refused at injection, RFC 5537 section 3.5 item 2, so
; that line is the node's, in recipe v2 and v3 alike).  Nothing else moves:
; the injected block keeps its order and every octet of the poster's source
; follows unchanged (`fn-cll-insert-adds-only-the-lines').  The D25
; comparison (books/poster-bytes.lisp) reads the source after the
; Injection-Info line, so the lines are part of its subject: a retry by the
; same login under the same Message-ID carries the same lines and is the
; same article; the same source from another login under that Message-ID
; is a different one (a conflict, where before SEC-006 it was a duplicate).
;
; No dependency: octet constants and list walks.
;
; Prefix `fn-cll-' (docs/prefixes.md).
(in-package "ACL2")

; "Cancel-Lock: sha256:" and "Cancel-Key: sha256:"
(defconst *fn-cll-lock-head*
  '(67 97 110 99 101 108 45 76 111 99 107 58 32 115 104 97 50 53 54 58))
(defconst *fn-cll-key-head*
  '(67 97 110 99 101 108 45 75 101 121 58 32 115 104 97 50 53 54 58))
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

; A Base64 character (RFC 4648 section 4 alphabet, and the pad).
(defun fn-cll-b64-charp (c)
  (declare (xargs :guard t))
  (and (integerp c)
       (or (and (<= 65 c) (<= c 90)) (and (<= 97 c) (<= c 122))
           (and (<= 48 c) (<= c 57)) (equal c 43) (equal c 47) (equal c 61))))

; X opens with PREFIX; the rest, or :no.
(defun fn-cll-strip (prefix x)
  (declare (xargs :guard t))
  (if (consp prefix)
      (if (and (consp x) (equal (car x) (car prefix)))
          (fn-cll-strip (cdr prefix) (cdr x))
        :no)
    x))

; A value of Base64 characters.
(defun fn-cll-valuep (v)
  (declare (xargs :guard t))
  (if (consp v)
      (and (fn-cll-b64-charp (car v)) (fn-cll-valuep (cdr v)))
    (null v)))

;; "Injection-Info: "
(defconst *fn-cll-info-head*
  '(73 110 106 101 99 116 105 111 110 45 73 110 102 111 58 32))

; The position just after the LF that ends the line starting at X (POS its
; position), or nil when the octets end first.
(defun fn-cll-line-end (x pos)
  (declare (xargs :guard (natp pos)))
  (cond ((atom x) nil)
        ((equal (car x) 10) (+ 1 pos))
        (t (fn-cll-line-end (cdr x) (+ 1 pos)))))

; The position just after the first header line opening "Injection-Info: ",
; X at position POS; MODE is :start at a line start and :skip inside a line
; that does not open so.  An empty line (one opening with CR) ends the
; header: nil.  Cost: one walk of the header.
(defun fn-cll-info-end (x pos mode)
  (declare (xargs :guard (natp pos)))
  (cond ((atom x) nil)
        ((eq mode :skip)
         (fn-cll-info-end (cdr x) (+ 1 pos) (if (equal (car x) 10) :start :skip)))
        ((equal (car x) 13) nil)
        ((not (equal (fn-cll-strip *fn-cll-info-head* x) :no))
         (fn-cll-line-end x pos))
        (t (fn-cll-info-end (cdr x) (+ 1 pos) (if (equal (car x) 10) :start :skip)))))

(defun fn-cll-take (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (zp (nfix n)) (atom x)) nil
    (cons (car x) (fn-cll-take (1- (nfix n)) (cdr x)))))

(defun fn-cll-drop (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (zp (nfix n)) (atom x)) x
    (fn-cll-drop (1- (nfix n)) (cdr x))))

; X with LINES inserted after its Injection-Info line; X itself when it has
; none (an article this node did not inject gets no lines).
(defun fn-cll-insert (lines x)
  (declare (xargs :guard t))
  (let ((k (fn-cll-info-end x 0 :start)))
    (if k
        (fn-cll-append (fn-cll-take k x) (fn-cll-append lines (fn-cll-drop k x)))
      x)))

(defthm fn-cll-take-drop
  (equal (append (fn-cll-take n x) (fn-cll-drop n x)) x))

; KEYSTONE (SEC-006, the payload is kept).  The octets the owner stores are
; the injected octets with LINES inserted at one position K, the end of the
; Injection-Info line; taking LINES out again gives the injected octets
; exactly.  Subject: `fn-cll-insert', called by books/cancel-lock.lisp
; fn-cl-served-payload (the host's call).
(defthm fn-cll-insert-adds-only-the-lines
  (let ((k (fn-cll-info-end x 0 :start)))
    (and (equal (fn-cll-insert lines x)
                (if k
                    (append (fn-cll-take k x) lines (fn-cll-drop k x))
                  x))
         (equal (append (fn-cll-take k x) (fn-cll-drop k x)) x))))

(in-theory (disable fn-cll-insert))
