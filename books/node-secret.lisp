; fn: the node's one protected root and the purpose keys derived from it
; (SEC-006, PRF-210; PKT-574 and PKT-576 share it; gpt-6's wave-5 review
; section 3, binding).
;
; ONE random root per key epoch, never served, never printed, never in a
; configuration record or an export.  It lives in the store directory, the
; node's persistent private state under D34 (the release directory is
; immutable): STORE/keys/node-secret.key, mode 0600 in a 0700 directory,
; written once by the explicit verb `node-secret create' (and by `init'),
; which refuses by name when a secret exists; a start with the file missing
; or readable by group or others is refused by name and NEVER regenerates
; one (host/native/io.lisp fnn-node-secret-create, host/native/owner.lisp
; fnn-owner-load-node-secret).  A rotation keeps each older epoch's file as
; STORE/keys/node-secret-E.key, so cancellation of older articles keeps
; its key material (RFC 8315 section 4: secret, user id, Message-ID).
;
; The file (versioned; `fn-ns-file-render', `fn-ns-file-parse'):
;
;   "fn-node-secret v1" LF   18 octets, the format version
;   EPOCH                    4 octets, big-endian, 1 or more
;   N                        2 octets, big-endian, the identity's length
;   IDENTITY                 N octets, the node identity the keys are bound to
;   ROOT                     32 octets from the OS CSPRNG
;
; A ring is the node's entries (EPOCH IDENTITY ROOT), the current epoch
; first and every older retained one after it, epochs strictly decreasing.
; The owner carries the ring (books/owner.lisp fn-own-node-secret).
;
; Every use is a PURPOSE KEY derived from one entry by HKDF-SHA256 (RFC
; 5869) with the entry's node identity as the salt, the root as the input
; keying material, and a versioned info label:
;
;   PRK        = HMAC-SHA256(IDENTITY, ROOT)                (HKDF-Extract)
;   key(INFO)  = HMAC-SHA256(PRK, INFO || 0x01)             (HKDF-Expand, L = 32)
;
;   INFO "fn/cancel-lock/v1"      the RFC 8315 section 4 secret <sec>;
;                                 books/cancel-lock.lisp fn-cl-key
;   INFO "fn/posting-account/v1"  the RFC 5536 section 3.2.8 posting-account
;                                 value's key (lane usenet-headers-3's
;                                 fn-pa-mac)
;
; What is proved is the separation of the derivation INPUTS
; (`fn-ns-expand-input-separates-info'): two distinct info labels never
; expand the same HMAC input under one entry, so no value derived for one
; purpose is ever derived for another.  That distinct inputs give unrelated
; outputs is HMAC-SHA256's pseudorandomness under a key the adversary does
; not hold: an assumption about the real function, not a theorem, and no
; theorem here uses it.
;
; Prefix `fn-ns-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "sha256")
(include-book "cbor")
(local (include-book "cbor-invariants"))

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
; HKDF-SHA256 (RFC 5869) for one 32-octet output block (RFC 5869 test
; cases 1 and 3 in the teeth).

(defun fn-ns-hkdf-extract (salt ikm)
  (declare (xargs :guard t))
  (fn-ns-hmac-sha256 salt ikm))

; T(1) = HMAC(PRK, T(0) || info || 0x01) with T(0) empty.
(defun fn-ns-expand-input (info)
  (declare (xargs :guard t))
  (fn-ns-append info (list 1)))

(defun fn-ns-hkdf-expand-32 (prk info)
  (declare (xargs :guard t))
  (fn-ns-hmac-sha256 prk (fn-ns-expand-input info)))

(defun fn-ns-hkdf-sha256-32 (salt ikm info)
  (declare (xargs :guard t))
  (fn-ns-hkdf-expand-32 (fn-ns-hkdf-extract salt ikm) info))

; -----------------------------------------------------------------------------
; The info labels (versioned).

; "fn/cancel-lock/v1"
(defconst *fn-ns-cancel-lock-info*
  '(102 110 47 99 97 110 99 101 108 45 108 111 99 107 47 118 49))
; "fn/posting-account/v1"
(defconst *fn-ns-posting-account-info*
  '(102 110 47 112 111 115 116 105 110 103 45 97 99 99 111 117 110 116 47 118 49))

; -----------------------------------------------------------------------------
; An entry (EPOCH IDENTITY ROOT) and a ring of them.  The bounds are the
; file codec's widths (4 and 2 octets): every entry the ring admits is one
; the file represents (`fn-ns-file-parse-of-render').

(defconst *fn-ns-epoch-limit* 4294967296)   ; 2^32
(defconst *fn-ns-identity-limit* 65536)     ; 2^16

(defun fn-ns-entry-epoch (e) (declare (xargs :guard t)) (if (consp e) (car e) nil))
(defun fn-ns-entry-identity (e)
  (declare (xargs :guard t))
  (if (and (consp e) (consp (cdr e))) (cadr e) nil))
(defun fn-ns-entry-root (e)
  (declare (xargs :guard t))
  (if (and (consp e) (consp (cdr e)) (consp (cddr e))) (caddr e) nil))

(defun fn-ns-entryp (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 3)
       (posp (car e)) (< (car e) *fn-ns-epoch-limit*)
       (fn-cbor-octet-listp (cadr e)) (< (len (cadr e)) *fn-ns-identity-limit*)
       (fn-ns-secretp (caddr e))))

(defun fn-ns-ring-entriesp (r)
  (declare (xargs :guard t))
  (if (consp r)
      (and (fn-ns-entryp (car r))
           (or (atom (cdr r))
               (and (fn-ns-entryp (cadr r))
                    (< (car (cadr r)) (car (car r)))))
           (fn-ns-ring-entriesp (cdr r)))
    (null r)))

; The current epoch first, every retained older one after it.
(defun fn-ns-ringp (r)
  (declare (xargs :guard t))
  (and (consp r) (fn-ns-ring-entriesp r)))

(defun fn-ns-current (r)
  (declare (xargs :guard t))
  (if (consp r) (car r) nil))

; A ring of one fresh entry: what `node-secret create' and `init' publish.
(defun fn-ns-make-entry (epoch identity root)
  (declare (xargs :guard t))
  (list epoch identity root))

; The entries `node-secret create' and `node-secret rotate' write
; (host/native/io.lisp): epoch 1, or the current epoch plus one, bound to
; IDENTITY (the operator's name for the node; "local" when none is given,
; and on a rotation the current entry's unless another is given).  ROOT is
; 32 octets from the OS CSPRNG.
; "local"
(defconst *fn-ns-default-identity* '(108 111 99 97 108))

(defun fn-ns-identity-or-default (identity default)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp identity) (consp identity)) identity default))

(defun fn-ns-create-entry (identity root)
  (declare (xargs :guard t))
  (fn-ns-make-entry 1 (fn-ns-identity-or-default identity *fn-ns-default-identity*)
                    root))

(defun fn-ns-rotate-entry (current identity root)
  (declare (xargs :guard t))
  (fn-ns-make-entry (+ 1 (nfix (fn-ns-entry-epoch current)))
                    (fn-ns-identity-or-default identity
                                               (fn-ns-entry-identity current))
                    root))

; The host checks the ring it assembles (the rotated entry in front of the
; retained ones) with fn-ns-ringp at every start (host/owner-host.lisp
; fn-owner-install-node-secret): epochs strictly decreasing.

; -----------------------------------------------------------------------------
; The purpose keys.  THE ACCESSORS: books/cancel-lock.lisp fn-cl-key calls
; `fn-ns-cancel-lock-key' of the entry an article's lock was made under;
; lane usenet-headers-3 (its fn-pa-mac) calls
; `fn-ns-posting-account-key' of the ring (its current entry).

(defun fn-ns-purpose-key (entry info)
  (declare (xargs :guard t))
  (fn-ns-hkdf-sha256-32 (fn-ns-entry-identity entry) (fn-ns-entry-root entry) info))

(defun fn-ns-cancel-lock-key (entry)
  (declare (xargs :guard t))
  (fn-ns-purpose-key entry *fn-ns-cancel-lock-info*))

(defun fn-ns-posting-account-key (ring)
  (declare (xargs :guard t))
  (fn-ns-purpose-key (fn-ns-current ring) *fn-ns-posting-account-info*))

; The posting-account value's MAC over LOGIN (kept for lane
; usenet-headers-3's fn-pa-mac, whose argument is the owner's ring).
(defun fn-ns-posting-account-mac (ring login)
  (declare (xargs :guard t))
  (fn-ns-hmac-sha256 (fn-ns-posting-account-key ring) login))

; -----------------------------------------------------------------------------
; Separation.

(local
 (defun fn-ns-two (a b)
   (if (and (consp a) (consp b)) (fn-ns-two (cdr a) (cdr b)) (list a b))))

(local
 (defthm fn-ns-append-one-injective
   (implies (and (true-listp a) (true-listp b)
                 (equal (append a (list 1)) (append b (list 1))))
            (equal a b))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ns-two a b)))))

(local
 (defthm fn-ns-octet-list-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; KEYSTONE (the separation).  Under distinct info labels the HKDF-Expand
; inputs differ, so under one entry (one PRK) no purpose key is computed
; from the HMAC input of another purpose.
(defthm fn-ns-expand-input-separates-info
  (implies (and (true-listp i1) (true-listp i2) (not (equal i1 i2)))
           (not (equal (fn-ns-expand-input i1) (fn-ns-expand-input i2))))
  :hints (("Goal" :use ((:instance fn-ns-append-one-injective (a i1) (b i2))))))

(defthm fn-ns-cancel-lock-and-posting-account-inputs-differ
  (not (equal (fn-ns-expand-input *fn-ns-cancel-lock-info*)
              (fn-ns-expand-input *fn-ns-posting-account-info*)))
  :hints (("Goal" :use ((:instance fn-ns-expand-input-separates-info
                                   (i1 *fn-ns-cancel-lock-info*)
                                   (i2 *fn-ns-posting-account-info*)))
           :in-theory (disable fn-ns-expand-input))))

; Every derived value is 32 octets.
(defthm fn-ns-hmac-sha256-shape
  (and (true-listp (fn-ns-hmac-sha256 key msg))
       (equal (len (fn-ns-hmac-sha256 key msg)) 32)))

(defthm fn-ns-hmac-sha256-octets
  (fn-sha256-octet-listp (fn-ns-hmac-sha256 key msg)))

(defthm fn-ns-purpose-key-shape
  (and (true-listp (fn-ns-purpose-key entry info))
       (equal (len (fn-ns-purpose-key entry info)) 32)
       (fn-sha256-octet-listp (fn-ns-purpose-key entry info))))

(defthm fn-ns-posting-account-key-shape
  (and (true-listp (fn-ns-posting-account-key ring))
       (equal (len (fn-ns-posting-account-key ring)) 32)
       (fn-sha256-octet-listp (fn-ns-posting-account-key ring))))

(defthm fn-ns-posting-account-mac-shape
  (and (true-listp (fn-ns-posting-account-mac ring login))
       (equal (len (fn-ns-posting-account-mac ring login)) 32)
       (fn-sha256-octet-listp (fn-ns-posting-account-mac ring login))))

; -----------------------------------------------------------------------------
; The key file.

; "fn-node-secret v1" LF
(defconst *fn-ns-file-magic*
  '(102 110 45 110 111 100 101 45 115 101 99 114 101 116 32 118 49 10))

(defun fn-ns-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x) nil (if (zp n) (car x) (fn-ns-nth (1- n) (cdr x)))))

(defun fn-ns-take (n x)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom x)) nil (cons (car x) (fn-ns-take (1- n) (cdr x)))))

(defun fn-ns-drop (n x)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom x)) x (fn-ns-drop (1- n) (cdr x))))

(defun fn-ns-strip (prefix x)
  (declare (xargs :guard t))
  (if (consp prefix)
      (if (and (consp x) (equal (car x) (car prefix)))
          (fn-ns-strip (cdr prefix) (cdr x))
        :no)
    x))

(defun fn-ns-file-render (entry)
  (declare (xargs :guard (fn-ns-entryp entry)))
  (fn-ns-append *fn-ns-file-magic*
                (fn-ns-append (fn-cbor-u32-bytes (fn-ns-entry-epoch entry))
                              (fn-ns-append (fn-cbor-u16-bytes
                                             (len (fn-ns-entry-identity entry)))
                                            (fn-ns-append (fn-ns-entry-identity entry)
                                                          (fn-ns-entry-root entry))))))

(defun fn-ns-u32-from (x)
  (declare (xargs :guard t))
  (+ (* 16777216 (fn-ns-octet (fn-ns-nth 0 x)))
     (* 65536 (fn-ns-octet (fn-ns-nth 1 x)))
     (* 256 (fn-ns-octet (fn-ns-nth 2 x)))
     (fn-ns-octet (fn-ns-nth 3 x))))

(defun fn-ns-u16-from (x)
  (declare (xargs :guard t))
  (+ (* 256 (fn-ns-octet (fn-ns-nth 0 x)))
     (fn-ns-octet (fn-ns-nth 1 x))))

; The entry a key file holds, or nil (the host refuses the file by name).
(defun fn-ns-file-parse (octets)
  (declare (xargs :guard t))
  (let ((r (fn-ns-strip *fn-ns-file-magic* octets)))
    (if (and (fn-cbor-octet-listp r) (<= 6 (len r)))
        (let* ((epoch (fn-ns-u32-from r))
               (r2 (fn-ns-drop 4 r))
               (n (fn-ns-u16-from r2))
               (r3 (fn-ns-drop 2 r2))
               (entry (fn-ns-make-entry epoch (fn-ns-take n r3) (fn-ns-drop n r3))))
          (if (and (<= n (len r3)) (fn-ns-entryp entry)) entry nil))
      nil)))

(defthm fn-ns-file-parse-is-an-entry
  (implies (fn-ns-file-parse octets)
           (fn-ns-entryp (fn-ns-file-parse octets))))

(local
 (defthm fn-ns-u32-round-trip
   (implies (and (natp n) (< n 4294967296))
            (equal (fn-ns-u32-from (append (fn-cbor-u32-bytes n) rest)) n))
   :hints (("Goal" :use (fn-cbor-u32-from-u32-bytes fn-cbor-u32-bytes-are-octets)
            :in-theory (e/d (fn-cbor-u32-bytes fn-cbor-u32-from fn-cbor-octet-listp
                             fn-cbor-octetp)
                            (floor mod))))))

(local
 (defthm fn-ns-u16-round-trip
   (implies (and (natp n) (< n 65536))
            (equal (fn-ns-u16-from (append (fn-cbor-u16-bytes n) rest)) n))
   :hints (("Goal" :use (fn-cbor-u16-from-u16-bytes fn-cbor-u16-bytes-are-octets)
            :in-theory (e/d (fn-cbor-u16-bytes fn-cbor-u16-from fn-cbor-octet-listp
                             fn-cbor-octetp)
                            (floor mod))))))

(local
 (defthm fn-ns-octet-listp-of-append
   (implies (true-listp a)
            (equal (fn-cbor-octet-listp (append a b))
                   (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-ns-u32-bytes-shape
   (and (true-listp (fn-cbor-u32-bytes n)) (equal (len (fn-cbor-u32-bytes n)) 4))
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

(local
 (defthm fn-ns-u16-bytes-shape
   (and (true-listp (fn-cbor-u16-bytes n)) (equal (len (fn-cbor-u16-bytes n)) 2))
   :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes)))))

(local
 (defthm fn-ns-three-list
   (implies (and (true-listp e) (equal (len e) 3))
            (equal (list (car e) (cadr e) (caddr e)) e))))

(local
 (defthm fn-ns-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-ns-true-list-fix-of-octets
   (implies (fn-cbor-octet-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-ns-take-of-append
   (implies (equal n (len a))
            (equal (fn-ns-take n (append a b)) (true-list-fix a)))))

(local
 (defthm fn-ns-drop-of-append
   (implies (equal n (len a))
            (equal (fn-ns-drop n (append a b)) b))))

(local
 (defthm fn-ns-strip-of-append
   (implies (true-listp p)
            (equal (fn-ns-strip p (append p x)) x))))

; KEYSTONE (the file keeps the entry).  What `node-secret create' writes,
; the start reads back unchanged.
(defthm fn-ns-file-parse-of-render
  (implies (fn-ns-entryp entry)
           (equal (fn-ns-file-parse (fn-ns-file-render entry)) entry))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes-are-octets fn-cbor-u16-bytes-are-octets)
                                  (fn-cbor-u32-bytes fn-cbor-u16-bytes
                                   fn-ns-u32-from fn-ns-u16-from)))))

(in-theory (disable fn-ns-hmac-sha256 fn-ns-expand-input fn-ns-purpose-key
                    fn-ns-file-parse fn-ns-file-render))
