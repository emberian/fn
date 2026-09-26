; fn: the node secret and its keyed hashes (SEC-006, PRF-210; PKT-574 and
; PKT-576 share it, the coordinator's decision of 2026-09-27).
;
; One 32-octet secret per node, written by `init' into STORE/keys/
; node-secret.key (mode 0600; host/native/io.lisp fnn-node-secret-create),
; read by the owner at every start and after every recovery, refused by
; name at start when missing, of the wrong size or readable by group or
; others (host/native/owner.lisp fnn-owner-load-node-secret).  It is never
; served, never printed and never written into a configuration record
; (`show' prints those; backups and checkpoints replay them).  The owner
; carries it (books/owner.lisp fn-own-node-secret).
;
; Every use is HMAC-SHA256 (RFC 2104, FIPS 198-1) under one secret with a
; DOMAIN LABEL in front of the message:
;
;   fn-ns-mac S LABEL M = HMAC-SHA256(S, LABEL || 0x00 || M)
;
; A label is an octet string without NUL, so the first NUL of the
; HMAC input ends the label: two uses with distinct labels never MAC the
; same input, whatever their messages (fn-ns-input-separates-labels).  The
; labels:
;
;   "fn cancel-lock v1"       RFC 8315 Cancel-Key K = Base64(fn-ns-mac S L
;                             (MSGID || LOGIN)); books/cancel-lock.lisp
;   "fn posting-account v1"   RFC 5536 section 3.2.8 posting-account value
;                             (the accessor fn-ns-posting-account-mac;
;                             Injection-Info is lane usenet-headers-3's)
;
; What is proved is the separation of the INPUTS.  That distinct inputs
; give unrelated outputs is HMAC-SHA256's pseudorandomness under a key the
; adversary does not hold: an assumption about the real function, not a
; theorem, and no theorem here uses it.
;
; Prefix `fn-ns-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "sha256")
(include-book "cbor")

(defconst *fn-ns-secret-octets* 32)

(defun fn-ns-secret-width ()
  (declare (xargs :guard t))
  *fn-ns-secret-octets*)

(defun fn-ns-secretp (s)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp s) (equal (len s) *fn-ns-secret-octets*)))

(defun fn-ns-append (a b)
  (declare (xargs :guard t))
  (if (consp a) (cons (car a) (fn-ns-append (cdr a) b)) b))

(defthm fn-ns-append-is-append
  (equal (fn-ns-append a b) (append a b)))

; -----------------------------------------------------------------------------
; HMAC-SHA256, block length 64, over `fn-sha256' (RFC 4231 cases 2 and 6 in
; tests/acl2/node-secret-tests.lisp).

(defconst *fn-ns-ipad* 54)   ; 0x36
(defconst *fn-ns-opad* 92)   ; 0x5c

(defun fn-ns-octet (x)
  (declare (xargs :guard t))
  (if (and (natp x) (< x 256)) x 0))

; KEY, zero-padded to N octets, each octet XOR PAD.
(defun fn-ns-padded (key pad n)
  (declare (xargs :guard (and (natp n) (natp pad)) :measure (nfix n)))
  (if (zp n)
      nil
    (cons (logxor (fn-ns-octet (if (consp key) (car key) 0)) pad)
          (fn-ns-padded (if (consp key) (cdr key) nil) pad (1- n)))))

(defun fn-ns-hmac-sha256 (key msg)
  (declare (xargs :guard t))
  (let ((k (if (< 64 (len key)) (fn-sha256 key) key)))
    (fn-sha256 (fn-ns-append (fn-ns-padded k *fn-ns-opad* 64)
                             (fn-sha256 (fn-ns-append
                                         (fn-ns-padded k *fn-ns-ipad* 64)
                                         msg))))))

; -----------------------------------------------------------------------------
; Domain labels.

(defun fn-ns-labelp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x) (not (member-equal 0 x))))

; "fn cancel-lock v1"
(defconst *fn-ns-cancel-lock-label*
  '(102 110 32 99 97 110 99 101 108 45 108 111 99 107 32 118 49))
; "fn posting-account v1"
(defconst *fn-ns-posting-account-label*
  '(102 110 32 112 111 115 116 105 110 103 45 97 99 99 111 117 110 116 32 118 49))

(defun fn-ns-input (label msg)
  (declare (xargs :guard t))
  (fn-ns-append label (cons 0 msg)))

(defun fn-ns-mac (secret label msg)
  (declare (xargs :guard t))
  (fn-ns-hmac-sha256 secret (fn-ns-input label msg)))

; The two uses.  THE ACCESSORS: books/cancel-lock.lisp fn-cl-key calls the
; first; the posting-account hash calls the second.
(defun fn-ns-cancel-lock-mac (secret msg)
  (declare (xargs :guard t))
  (fn-ns-mac secret *fn-ns-cancel-lock-label* msg))

(defun fn-ns-posting-account-mac (secret login)
  (declare (xargs :guard t))
  (fn-ns-mac secret *fn-ns-posting-account-label* login))

; -----------------------------------------------------------------------------
; Separation.

(local
 (defun fn-ns-two-lists (l1 l2)
   (if (and (consp l1) (consp l2))
       (fn-ns-two-lists (cdr l1) (cdr l2))
     (list l1 l2))))

(local
 (defthm fn-ns-input-prefix-lemma
   (implies (and (not (member-equal 0 l1)) (not (member-equal 0 l2))
                 (true-listp l1) (true-listp l2)
                 (equal (append l1 (cons 0 m1)) (append l2 (cons 0 m2))))
            (equal l1 l2))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ns-two-lists l1 l2)))))

(local
 (defthm fn-ns-octet-list-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; KEYSTONE (the separation).  Under distinct labels the HMAC inputs differ,
; whatever the two messages: no value MACed for one use is ever the input
; of another use.
(defthm fn-ns-input-separates-labels
  (implies (and (fn-ns-labelp l1) (fn-ns-labelp l2) (not (equal l1 l2)))
           (not (equal (fn-ns-input l1 m1) (fn-ns-input l2 m2))))
  :hints (("Goal" :use ((:instance fn-ns-input-prefix-lemma))
           :in-theory (disable fn-ns-append))))

(defthm fn-ns-labels-are-labels
  (and (fn-ns-labelp *fn-ns-cancel-lock-label*)
       (fn-ns-labelp *fn-ns-posting-account-label*)
       (not (equal *fn-ns-cancel-lock-label* *fn-ns-posting-account-label*)))
  :rule-classes nil)

; The two uses of the one secret never MAC the same input.
(defthm fn-ns-cancel-lock-and-posting-account-inputs-differ
  (not (equal (fn-ns-input *fn-ns-cancel-lock-label* m1)
              (fn-ns-input *fn-ns-posting-account-label* m2)))
  :hints (("Goal" :use ((:instance fn-ns-input-separates-labels
                                   (l1 *fn-ns-cancel-lock-label*)
                                   (l2 *fn-ns-posting-account-label*)))
           :in-theory (disable fn-ns-input))
          ("Goal'" :use fn-ns-labels-are-labels)))

; Every use yields 32 octets (the lock and key lengths of RFC 8315 rest on it).
(defthm fn-ns-hmac-sha256-shape
  (and (true-listp (fn-ns-hmac-sha256 key msg))
       (equal (len (fn-ns-hmac-sha256 key msg)) 32)))

(defthm fn-ns-mac-shape
  (and (true-listp (fn-ns-mac secret label msg))
       (equal (len (fn-ns-mac secret label msg)) 32)))

(in-theory (disable fn-ns-input fn-ns-mac fn-ns-hmac-sha256))
