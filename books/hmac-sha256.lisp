; fn: HMAC-SHA-256 (RFC 2104, FIPS 198-1) and PBKDF2-HMAC-SHA-256 with one
; output block (RFC 8018 section 5.2; RFC 5802 section 2.2 calls it Hi), over
; octet lists, executable and guard verified.
;
; Why this book exists.  SCRAM-SHA-256 (RFC 5802, RFC 7677) is defined over
; HMAC-SHA-256 and Hi; the algorithm is the RFC's, not fn's choice, so the
; BLAKE3 rule for fn's own derivations (books/node-secret.lisp) does not
; apply here.  books/sha256.lisp is FIPS 180-4 SHA-256; this book is the two
; constructions above it and nothing else.
;
; Two definitions of each, one function.  `fn-hmac-sha256' is RFC 2104's
; text: H((K0 xor opad) || H((K0 xor ipad) || m)).  `fn-pbkdf2-sha256' is
; Hi = U1 xor ... xor Ui with U1 = HMAC(P, S || INT(1)) and Uj = HMAC(P,
; Uj-1).  Executed as written, one Hi iteration costs four SHA-256
; compressions and rebuilds both key blocks.  The executable body instead
; compresses each key block ONCE (the "midstate") and then runs one
; compression per HMAC half, two per iteration: the `:exec' half of an `mbe'
; whose `:logic' half is the RFC's text, so the function the host calls IS
; the RFC's definition in the logic and the guard proof is the equality
; (`fn-sha256-of-block-prefix-is-from-state', the one lemma that carries it).
;
; What is proved: every output is 32 octets; the fast evaluation equals the
; RFC text (the mbe).  Agreement with the standards is evidence, not proof:
; tests/acl2/hmac-sha256-tests.lisp checks RFC 4231's HMAC vectors and RFC
; 7914 section 11's PBKDF2-HMAC-SHA-256 vectors by evaluation.  Nothing here
; is a claim about pseudorandomness or password-guessing cost (A-CRYPTO).

(in-package "ACL2")
(include-book "sha256")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable floor mod)))

; -----------------------------------------------------------------------------
; Octets

(defconst *fn-hmac-block-octets* 64)
(defconst *fn-hmac-ipad* #x36)
(defconst *fn-hmac-opad* #x5c)

(defun fn-hmac-octets (x)
  ; Any object as an octet list (the identity on octet lists).
  (declare (xargs :guard t))
  (fn-sha256-fix-octets x))

(defun fn-hmac-xor-octet (a b)
  (declare (xargs :guard t))
  (fn-sha256-byte (logxor (fn-sha256-byte a) (fn-sha256-byte b))))

(defun fn-hmac-xor (xs ys)
  ; Pointwise xor of two octet lists, as long as the shorter.
  (declare (xargs :guard t))
  (if (and (consp xs) (consp ys))
      (cons (fn-hmac-xor-octet (car xs) (car ys))
            (fn-hmac-xor (cdr xs) (cdr ys)))
    nil))

(defthm fn-hmac-octet-listp-of-xor
  (fn-sha256-octet-listp (fn-hmac-xor xs ys)))

(defthm fn-hmac-len-of-xor
  (equal (len (fn-hmac-xor xs ys)) (min (len xs) (len ys))))

;; XOR is an involution on octets: (a xor b) xor b = a.  No bit library in
;; the certified set proves logxor associative (centaur/bitops is not built
;; for this toolchain), and the domain is 256 x 256, so it is checked
;; exhaustively: a ground evaluation of the checker below, and one induction
;; per loop to carry it to every octet pair.
(local
 (defun fn-hmac-inv-row (a b)
   (declare (xargs :guard t :measure (nfix b)))
   (if (zp (nfix b))
       (equal (fn-hmac-xor-octet (fn-hmac-xor-octet a 0) 0) a)
     (and (equal (fn-hmac-xor-octet (fn-hmac-xor-octet a b) b) a)
          (fn-hmac-inv-row a (- (nfix b) 1))))))

(local
 (defun fn-hmac-inv-all (a)
   (declare (xargs :guard t :measure (nfix a)))
   (if (zp (nfix a))
       (fn-hmac-inv-row 0 255)
     (and (fn-hmac-inv-row a 255)
          (fn-hmac-inv-all (- (nfix a) 1))))))

(local
 (defthm fn-hmac-inv-row-holds
   (implies (and (natp n) (fn-hmac-inv-row a n) (natp b) (<= b n))
            (equal (fn-hmac-xor-octet (fn-hmac-xor-octet a b) b) a))
   :hints (("Goal" :induct (fn-hmac-inv-row a n)
            :in-theory (disable fn-hmac-xor-octet)))))

(local
 (defthm fn-hmac-inv-all-holds
   (implies (and (natp n) (fn-hmac-inv-all n) (natp a) (<= a n))
            (fn-hmac-inv-row a 255))
   :hints (("Goal" :induct (fn-hmac-inv-all n)))))

(local
 (defthm fn-hmac-inv-all-255
   (fn-hmac-inv-all 255)))

(local
 (defthm fn-hmac-mod-of-octet
   (implies (and (natp y) (< y 256))
            (equal (mod y 256) y))))

(local
 (defthm fn-hmac-byte-of-byte
   (equal (fn-sha256-byte (fn-sha256-byte x)) (fn-sha256-byte x))
   :hints (("Goal" :expand ((fn-sha256-byte (fn-sha256-byte x)))
            :use ((:instance fn-hmac-mod-of-octet (y (fn-sha256-byte x))))
            :in-theory (disable fn-hmac-mod-of-octet)))))

(local
 (defthm fn-hmac-xor-octet-of-byte
   (equal (fn-hmac-xor-octet x (fn-sha256-byte b)) (fn-hmac-xor-octet x b))
   :hints (("Goal" :in-theory (enable fn-hmac-xor-octet)))))

(defthm fn-hmac-xor-octet-involution
  (implies (and (natp a) (< a 256))
           (equal (fn-hmac-xor-octet (fn-hmac-xor-octet a b) b) a))
  :hints (("Goal"
           :use ((:instance fn-hmac-inv-row-holds
                            (n 255) (b (fn-sha256-byte b)))
                 (:instance fn-hmac-inv-all-holds (n 255))
                 (:instance fn-hmac-inv-all-255))
           :in-theory (disable fn-hmac-xor-octet fn-hmac-inv-row
                               fn-hmac-inv-all fn-hmac-inv-row-holds
                               fn-hmac-inv-all-holds fn-hmac-inv-all-255))))

(defthm fn-hmac-xor-involution
  ; (xs xor ys) xor ys = xs, for an octet list no longer than YS.
  (implies (and (fn-sha256-octet-listp xs) (<= (len xs) (len ys)))
           (equal (fn-hmac-xor (fn-hmac-xor xs ys) ys) xs))
  :hints (("Goal" :induct (fn-hmac-xor xs ys)
           :in-theory (disable fn-hmac-xor-octet))))

(defun fn-hmac-xor-const (xs c)
  ; Every octet of XS xor the octet C.
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-hmac-xor-octet (car xs) c) (fn-hmac-xor-const (cdr xs) c))
    nil))

(defthm fn-hmac-octet-listp-of-xor-const
  (fn-sha256-octet-listp (fn-hmac-xor-const xs c)))

(defthm fn-hmac-len-of-xor-const
  (equal (len (fn-hmac-xor-const xs c)) (len xs)))

; -----------------------------------------------------------------------------
; HMAC-SHA-256, RFC 2104 section 2, as written

(defun fn-hmac-key-block (key)
  ; K0: a key longer than the block is hashed first; then zeros to 64 octets.
  (declare (xargs :guard t))
  (let* ((k (fn-hmac-octets key))
         (k (if (< *fn-hmac-block-octets* (len k)) (fn-sha256 k) k)))
    (fn-sha256-appx k (fn-sha256-zeros (- *fn-hmac-block-octets* (len k))))))

(defthm fn-hmac-key-block-shape
  (and (fn-sha256-octet-listp (fn-hmac-key-block key))
       (equal (len (fn-hmac-key-block key)) 64))
  :hints (("Goal" :in-theory (e/d (fn-sha256-appx) (fn-sha256-fix-octets)))))

(defun fn-hmac-sha256 (key msg)
  ; HMAC-SHA-256(KEY, MSG).  KEY and MSG are read as octets.
  (declare (xargs :guard t))
  (let ((k0 (fn-hmac-key-block key)))
    (fn-sha256
     (fn-sha256-appx (fn-hmac-xor-const k0 *fn-hmac-opad*)
                     (fn-sha256
                      (fn-sha256-appx (fn-hmac-xor-const k0 *fn-hmac-ipad*)
                                      (fn-hmac-octets msg)))))))

(defthm fn-hmac-sha256-shape
  (and (fn-sha256-octet-listp (fn-hmac-sha256 key msg))
       (true-listp (fn-hmac-sha256 key msg))
       (equal (len (fn-hmac-sha256 key msg)) 32)))

; -----------------------------------------------------------------------------
; The midstate: SHA-256 of a 64-octet block followed by a message, resumed
; from the block's compression.

(defun fn-sha256-pad-after (prefix msg)
  ; The padded tail of a message whose first PREFIX octets were already
  ; compressed: msg || 0x80 || zeros || the 64-bit length of the WHOLE message.
  (declare (xargs :guard t))
  (let ((total (+ (nfix prefix) (len msg))))
    (fn-sha256-appx
     msg
     (cons 128
           (fn-sha256-appx (fn-sha256-zeros (mod (- 55 total) 64))
                           (fn-sha256-u64-be (* 8 total)))))))

(defun fn-sha256-from-state (hs prefix msg)
  ; SHA-256 finished from the chaining value HS after PREFIX octets.
  (declare (xargs :guard t))
  (fn-sha256-words-octets
   (fn-sha256-firstn 8 (fn-sha256-blocks (fn-sha256-pad-after prefix msg) hs))))

(local
 (defthm fn-hmac-appx-is-append
   (equal (fn-sha256-appx xs ys) (append xs ys))
   :hints (("Goal" :in-theory (enable fn-sha256-appx)))))

(local
 (defthm fn-hmac-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-hmac-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-hmac-firstn-of-append-block
   (implies (and (true-listp b) (equal (len b) n))
            (equal (fn-sha256-firstn n (append b rest)) b))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn)
            :induct (fn-sha256-firstn n b)))))

(local
 (defthm fn-hmac-nthcdrx-of-append-block
   (implies (and (true-listp b) (equal (len b) n))
            (equal (fn-sha256-nthcdrx n (append b rest)) rest))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx n b)))))

(local
 (defthm fn-hmac-pad-of-block-prefix
   (implies (and (true-listp b) (equal (len b) 64))
            (equal (fn-sha256-pad (append b msg))
                   (append b (fn-sha256-pad-after 64 msg))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-sha256-pad fn-sha256-pad-after)))))

(local
 (defthm fn-hmac-blocks-of-block-prefix
   (implies (and (true-listp b) (equal (len b) 64))
            (equal (fn-sha256-blocks (append b rest) hs)
                   (fn-sha256-blocks rest (fn-sha256-compress b hs))))
   :hints (("Goal" :expand ((fn-sha256-blocks (append b rest) hs))
            :in-theory (disable fn-sha256-compress)))))

(local
 (defthm fn-hmac-octet-listp-true-listp
   (implies (fn-sha256-octet-listp x) (true-listp x))
   :hints (("Goal" :use ((:instance fn-sha256-octet-listp-implies-true-listp
                                    (xs x)))))))

(local
 (defthm fn-hmac-octet-listp-of-append
   (implies (and (fn-sha256-octet-listp a) (fn-sha256-octet-listp b))
            (fn-sha256-octet-listp (append a b)))))

; The one lemma the fast evaluation rests on.
(defthm fn-sha256-of-block-prefix-is-from-state
  (implies (and (fn-sha256-octet-listp b) (equal (len b) 64)
                (fn-sha256-octet-listp msg))
           (equal (fn-sha256 (append b msg))
                  (fn-sha256-from-state (fn-sha256-compress b *fn-sha256-h0*)
                                        64 msg)))
  :hints (("Goal" :use ((:instance fn-sha256-is-of-octets-on-octets
                                   (m (append b msg))))
           :in-theory (e/d (fn-sha256-of-octets fn-sha256-from-state)
                           (fn-sha256-pad fn-sha256-pad-after
                            fn-sha256-compress fn-sha256-blocks
                            fn-sha256-words-octets fn-sha256-firstn)))))

(in-theory (disable fn-sha256-pad-after fn-sha256-from-state))

; -----------------------------------------------------------------------------
; HMAC from the two key-block states

(defun fn-hmac-states (key)
  ; (inner-state . outer-state): each key block compressed once.
  (declare (xargs :guard t))
  (let ((k0 (fn-hmac-key-block key)))
    (cons (fn-sha256-compress (fn-hmac-xor-const k0 *fn-hmac-ipad*)
                              *fn-sha256-h0*)
          (fn-sha256-compress (fn-hmac-xor-const k0 *fn-hmac-opad*)
                              *fn-sha256-h0*))))

(defun fn-hmac-from-states (states msg)
  ; HMAC finished from `fn-hmac-states': two compressions for a message of
  ; at most 55 octets.
  (declare (xargs :guard t))
  (let ((inner (if (consp states) (car states) nil))
        (outer (if (consp states) (cdr states) nil)))
    (fn-sha256-from-state
     outer 64 (fn-sha256-from-state inner 64 (fn-hmac-octets msg)))))

(defthm fn-hmac-from-states-is-hmac
  (equal (fn-hmac-from-states (fn-hmac-states key) msg)
         (fn-hmac-sha256 key msg))
  :hints (("Goal"
           :in-theory (e/d (fn-hmac-sha256 fn-hmac-from-states fn-hmac-states
                            fn-hmac-octets)
                           (fn-sha256 fn-sha256-compress fn-hmac-key-block
                            fn-hmac-xor-const fn-sha256-fix-octets))
           :use ((:instance fn-sha256-of-block-prefix-is-from-state
                            (b (fn-hmac-xor-const (fn-hmac-key-block key)
                                                  *fn-hmac-ipad*))
                            (msg (fn-sha256-fix-octets msg)))
                 (:instance fn-sha256-of-block-prefix-is-from-state
                            (b (fn-hmac-xor-const (fn-hmac-key-block key)
                                                  *fn-hmac-opad*))
                            (msg (fn-sha256
                                  (append (fn-hmac-xor-const
                                           (fn-hmac-key-block key)
                                           *fn-hmac-ipad*)
                                          (fn-sha256-fix-octets msg)))))))))

; -----------------------------------------------------------------------------
; PBKDF2-HMAC-SHA-256, one block: RFC 5802's Hi(str, salt, i)

(defun fn-pbkdf2-int1 ()
  ; INT(1): the block index as four big-endian octets.
  (declare (xargs :guard t))
  (list 0 0 0 1))

(defun fn-pbkdf2-chain (password u n acc)
  ; N more iterations after U: acc xor U2 xor ... (RFC text).
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n))
      acc
    (let ((next (fn-hmac-sha256 password u)))
      (fn-pbkdf2-chain password next (- (nfix n) 1) (fn-hmac-xor acc next)))))

(defun fn-pbkdf2-chain-fast (states u n acc)
  ; The same chain from the key's two states.
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n))
      acc
    (let ((next (fn-hmac-from-states states u)))
      (fn-pbkdf2-chain-fast states next (- (nfix n) 1) (fn-hmac-xor acc next)))))

(defthm fn-pbkdf2-chain-fast-is-chain
  (equal (fn-pbkdf2-chain-fast (fn-hmac-states password) u n acc)
         (fn-pbkdf2-chain password u n acc))
  :hints (("Goal" :induct (fn-pbkdf2-chain password u n acc)
           :in-theory (disable fn-hmac-states fn-hmac-sha256
                               fn-hmac-from-states))))

(defun fn-pbkdf2-sha256 (password salt iterations)
  ; Hi(PASSWORD, SALT, ITERATIONS), 32 octets.  An iteration count below one
  ; is read as one (RFC 8018 requires a positive count; the callers only
  ; pass the enrolled count, which the verifier requires positive).
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-hmac-states fn-hmac-sha256
                                          fn-hmac-from-states
                                          fn-pbkdf2-chain fn-pbkdf2-chain-fast)))))
  (mbe :logic
       (let ((u1 (fn-hmac-sha256 password
                                 (fn-sha256-appx (fn-hmac-octets salt)
                                                 (fn-pbkdf2-int1)))))
         (fn-pbkdf2-chain password u1 (- (max 1 (nfix iterations)) 1) u1))
       :exec
       (let* ((states (fn-hmac-states password))
              (u1 (fn-hmac-from-states states
                                       (fn-sha256-appx (fn-hmac-octets salt)
                                                       (fn-pbkdf2-int1)))))
         (fn-pbkdf2-chain-fast states u1 (- (max 1 (nfix iterations)) 1) u1))))

(local
 (defthm fn-pbkdf2-chain-shape
   (implies (and (fn-sha256-octet-listp acc) (equal (len acc) 32))
            (and (fn-sha256-octet-listp (fn-pbkdf2-chain password u n acc))
                 (equal (len (fn-pbkdf2-chain password u n acc)) 32)))
   :hints (("Goal" :in-theory (disable fn-hmac-sha256)))))

(defthm fn-pbkdf2-sha256-shape
  (and (fn-sha256-octet-listp (fn-pbkdf2-sha256 password salt iterations))
       (true-listp (fn-pbkdf2-sha256 password salt iterations))
       (equal (len (fn-pbkdf2-sha256 password salt iterations)) 32))
  :hints (("Goal" :in-theory (disable fn-hmac-sha256 fn-pbkdf2-chain))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2)

(deftheory fn-hmac-sha256-internals
  '((:d fn-hmac-octets) (:d fn-hmac-xor-octet) (:d fn-hmac-xor)
    (:d fn-hmac-xor-const) (:d fn-hmac-key-block) (:d fn-hmac-sha256)
    (:d fn-hmac-states) (:d fn-hmac-from-states) (:d fn-pbkdf2-int1)
    (:d fn-pbkdf2-chain) (:d fn-pbkdf2-chain-fast) (:d fn-pbkdf2-sha256)))

(in-theory (disable fn-hmac-sha256-internals))
