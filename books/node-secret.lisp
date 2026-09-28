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
; Every use is a PURPOSE KEY derived from one entry by BLAKE3's derive_key
; mode (books/blake3.lisp `fn-blake3-derive-key'; lane blake3-digest,
; 2026-09-28, replacing HKDF-SHA256 of RFC 5869: ember, "BLAKE3 wherever fn
; chooses the algorithm"), with a versioned info label as the context string
; and the root followed by the entry's node identity as the key material:
;
;   key(INFO)  = BLAKE3-derive_key(context INFO, material ROOT || IDENTITY)
;   MAC(K, M)  = BLAKE3-keyed_hash(K, M)                   (K a purpose key)
;
;   INFO "fn/cancel-lock/v2"      the RFC 8315 section 4 secret <sec>;
;                                 books/cancel-lock.lisp fn-cl-key
;   INFO "fn/posting-account/v2"  the RFC 5536 section 3.2.8 posting-account
;                                 value's key (fn-pa-mac)
;
; No foreign party reproduces either derivation: the Cancel-Lock key is
; checked by others only through SHA-256 of its Base64 form (RFC 8315
; sections 2.1, 2.2 and 3; section 4 says the MAC's hash need not be the
; scheme's), and the posting-account value is opaque by design (RFC 5536
; section 3.2.8).  So both are fn's choice, and both are BLAKE3.  The root
; is 32 octets, so ROOT || IDENTITY splits back into the two.
;
; What is proved is the separation of the derivation INPUTS
; (`fn-ns-purpose-inputs-separate-by-definition'): two distinct info labels
; are two distinct derive_key contexts, so no value derived for one purpose
; is derived from the inputs of another.  That distinct contexts give
; unrelated outputs is BLAKE3's pseudorandomness as a KDF, and that a keyed
; hash is unforgeable without its key is its PRF assumption: assumptions
; about the real function (A-CRYPTO), not theorems, and no theorem here
; uses them.
;
; Prefix `fn-ns-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "blake3")
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
; The MAC: BLAKE3's keyed_hash under a 32-octet purpose key.

(defun fn-ns-octet (x)
  (declare (xargs :guard t))
  (if (and (natp x) (< x 256)) x 0))

(defun fn-ns-mac (key msg)
  (declare (xargs :guard t))
  (fn-blake3-keyed key msg))

; -----------------------------------------------------------------------------
; The info labels (versioned).

; "fn/cancel-lock/v2" (v1 was the HKDF-SHA256 derivation, store format 9)
(defconst *fn-ns-cancel-lock-info*
  '(102 110 47 99 97 110 99 101 108 45 108 111 99 107 47 118 50))
; "fn/posting-account/v2"
(defconst *fn-ns-posting-account-info*
  '(102 110 47 112 111 115 116 105 110 103 45 97 99 99 111 117 110 116 47 118 50))

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

; The key material of an entry: its root, then its node identity.
(defun fn-ns-key-material (entry)
  (declare (xargs :guard t))
  (fn-ns-append (fn-ns-entry-root entry) (fn-ns-entry-identity entry)))

; What a purpose key is derived from: the context and the material.
(defun fn-ns-purpose-input (entry info)
  (declare (xargs :guard t))
  (cons info (fn-ns-key-material entry)))

(defun fn-ns-purpose-key (entry info)
  (declare (xargs :guard t))
  (let ((in (fn-ns-purpose-input entry info)))
    (fn-blake3-derive-key (car in) (cdr in))))

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
  (fn-ns-mac (fn-ns-posting-account-key ring) login))

; -----------------------------------------------------------------------------
; Separation.

; Under one entry, distinct info labels are distinct derive_key contexts:
; the purpose inputs differ (the context is the input's first component).
(defthm fn-ns-purpose-inputs-separate-by-definition
  (implies (not (equal i1 i2))
           (not (equal (fn-ns-purpose-input entry i1) (fn-ns-purpose-input entry i2)))))

(defthm fn-ns-cancel-lock-and-posting-account-inputs-differ
  (not (equal (fn-ns-purpose-input entry *fn-ns-cancel-lock-info*)
              (fn-ns-purpose-input entry *fn-ns-posting-account-info*)))
  :hints (("Goal" :in-theory (disable fn-ns-purpose-input))))

(local
 (defthm fn-ns-octet-list-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; Every derived value is 32 octets.
(defthm fn-ns-mac-shape
  (and (true-listp (fn-ns-mac key msg))
       (equal (len (fn-ns-mac key msg)) 32)
       (fn-b3-octet-listp (fn-ns-mac key msg))))

(defthm fn-ns-purpose-key-shape
  (and (true-listp (fn-ns-purpose-key entry info))
       (equal (len (fn-ns-purpose-key entry info)) 32)
       (fn-b3-octet-listp (fn-ns-purpose-key entry info))))

(defthm fn-ns-posting-account-key-shape
  (and (true-listp (fn-ns-posting-account-key ring))
       (equal (len (fn-ns-posting-account-key ring)) 32)
       (fn-b3-octet-listp (fn-ns-posting-account-key ring))))

(defthm fn-ns-posting-account-mac-shape
  (and (true-listp (fn-ns-posting-account-mac ring login))
       (equal (len (fn-ns-posting-account-mac ring login)) 32)
       (fn-b3-octet-listp (fn-ns-posting-account-mac ring login))))

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

(in-theory (disable fn-ns-mac fn-ns-purpose-input fn-ns-purpose-key
                    fn-ns-file-parse fn-ns-file-render))
