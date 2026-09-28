; fn: BLAKE3 over octet lists, executable and guard verified: the logical
; definition of fn's digest (ember 2026-09-28: BLAKE3 wherever fn chooses the
; algorithm; SHA-256 only where an RFC puts it on the wire).
;
; What this book is.  The BLAKE3 hash function (J. O'Connor, J.-P. Aumasson,
; S. Neves, Z. Wilcox-O'Hearn, "BLAKE3: one function, fast everywhere",
; 2020-01-09; the reference implementation `reference_impl.rs' and the C
; `blake3_impl.h' vendored at third_party/blake3, version 1.8.7) as ACL2
; functions over octet lists: the compression function over 64-octet blocks
; (seven rounds of G on columns and diagonals), the chunk (up to 1024 octets,
; sixteen blocks chained, CHUNK_START on the first, CHUNK_END on the last),
; the binary tree over chunks (a left subtree of the largest power-of-two
; number of whole chunks strictly shorter than the input, section 2.1), the
; parent node, and the root: the first 32 output octets, which is BLAKE3's
; default output and the only length fn uses.  The three modes: `fn-blake3'
; (hash, the IV as the key), `fn-blake3-keyed' (keyed_hash, a 32-octet key)
; and `fn-blake3-derive-key' (derive_key: the context string hashed under
; DERIVE_KEY_CONTEXT, the result the key for the material under
; DERIVE_KEY_MATERIAL).
;
; What it does and does not establish.  It proves the SHAPE (32 octets,
; always; the chaining values are words) and admits every function with its
; guard verified.  Agreement with BLAKE3 is evidence, not proof: the official
; test vectors (the BLAKE3 repository's test_vectors/test_vectors.json, all
; 35 lengths in all three modes) are checked by evaluation in
; tests/acl2/blake3-tests.lisp, and the executable twin over the octet buffer
; (books/blake3-stobj.lisp) is proved equal to this definition.  Collision
; and preimage resistance are A-CRYPTO (specs/failures.md) and are not
; provable here: about 2^-128 per chosen pair (the birthday bound over a
; 256-bit output) is the figure to quote, not the 2^-256 second-preimage one.
;
; Representation.  Words are naturals below 2^32.  The word operations are
; declared on 32-bit words and reduce with `mod' by 2^32 (SBCL compiles each
; to fixnum arithmetic and a mask), so every guard obligation is a fact about
; `mod' and no bitvector library is needed; the compression function is a
; chain of seven functions of the sixteen state and sixteen message words
; (`fn-b3-rounds-1' .. `-7') that return multiple values, so it conses
; nothing.  The top-level functions have `:guard t' and read any object as
; octets (`fn-b3-fix-octets'), as the digest seam's `fn-digest' is
; constrained over any object; on an octet list the coercion is the identity.

(in-package "ACL2")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local (in-theory (disable floor mod truncate rem)))

; -----------------------------------------------------------------------------
; Constants (section 2.1, Table 3 and the IV of section 2.2)

(defconst *fn-b3-digest-octets* 32)
(defconst *fn-b3-block-octets* 64)
(defconst *fn-b3-chunk-octets* 1024)

(defconst *fn-b3-chunk-start* 1)
(defconst *fn-b3-chunk-end* 2)
(defconst *fn-b3-parent* 4)
(defconst *fn-b3-root* 8)
(defconst *fn-b3-keyed-hash* 16)
(defconst *fn-b3-derive-key-context* 32)
(defconst *fn-b3-derive-key-material* 64)

; The IV: SHA-256's initial hash value (FIPS 180-4 section 5.3.3), as the
; paper takes it.
(defconst *fn-b3-iv*
  '(1779033703 3144134277 1013904242 2773480762
    1359893119 2600822924 528734635 1541459225))

; -----------------------------------------------------------------------------
; Words and octets

(defun fn-b3-w32 (x)
  ; Any object as a 32-bit word.
  (declare (xargs :guard t))
  (mod (ifix x) 4294967296))

(defthm fn-b3-w32-type
  (and (integerp (fn-b3-w32 x))
       (<= 0 (fn-b3-w32 x))
       (< (fn-b3-w32 x) 4294967296))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-b3-w32 x))
                                  (<= 0 (fn-b3-w32 x))))
                 (:linear
                  :corollary (and (<= 0 (fn-b3-w32 x))
                                  (< (fn-b3-w32 x) 4294967296)))
                 (:rewrite
                  :corollary (integerp (fn-b3-w32 x)))))

(defun fn-b3-byte (x)
  ; Any object as an octet.
  (declare (xargs :guard t))
  (mod (ifix x) 256))

(defthm fn-b3-byte-type
  (and (integerp (fn-b3-byte x))
       (<= 0 (fn-b3-byte x))
       (<= (fn-b3-byte x) 255))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-b3-byte x))
                                  (<= 0 (fn-b3-byte x))))
                 (:linear
                  :corollary (and (<= 0 (fn-b3-byte x))
                                  (<= (fn-b3-byte x) 255)))
                 (:rewrite
                  :corollary (integerp (fn-b3-byte x)))))

(defthm fn-b3-w32-of-word
  (implies (and (integerp x) (<= 0 x) (< x 4294967296))
           (equal (fn-b3-w32 x) x)))

(defthm fn-b3-byte-of-octet
  (implies (and (integerp x) (<= 0 x) (< x 256))
           (equal (fn-b3-byte x) x)))

(defthm fn-b3-u32-of-w32
  (unsigned-byte-p 32 (fn-b3-w32 x)))

(in-theory (disable fn-b3-w32 fn-b3-byte))

(local
 (defthm fn-b3-u32-of-mod
   (implies (integerp z)
            (unsigned-byte-p 32 (mod z 4294967296)))
   :hints (("Goal" :use ((:instance fn-b3-u32-of-w32 (x z)))
            :in-theory (enable fn-b3-w32)))))

(defun fn-b3-word (x)
  ; Any object as a word; the identity on a word, without a division.
  (declare (xargs :guard t))
  (mbe :logic (fn-b3-w32 x)
       :exec (if (and (integerp x) (<= 0 x) (< x 4294967296)) x (fn-b3-w32 x))))

(defun fn-b3-octet (x)
  ; Any object as an octet; the identity on an octet.
  (declare (xargs :guard t))
  (mbe :logic (fn-b3-byte x)
       :exec (if (and (integerp x) (<= 0 x) (< x 256)) x (fn-b3-byte x))))

(defthm fn-b3-word-type
  (unsigned-byte-p 32 (fn-b3-word x)))

(defthm fn-b3-octet-type
  (and (integerp (fn-b3-octet x))
       (<= 0 (fn-b3-octet x))
       (<= (fn-b3-octet x) 255))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-b3-octet x))
                                  (<= 0 (fn-b3-octet x))))
                 (:linear
                  :corollary (and (<= 0 (fn-b3-octet x))
                                  (<= (fn-b3-octet x) 255)))))

(in-theory (disable fn-b3-word fn-b3-octet))

; An octet list, recognized without depending on any other fn book (this book
; sits at the bottom of the tree beside books/sha256.lisp).
(defun fn-b3-octet-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs))
           (<= 0 (car xs))
           (<= (car xs) 255)
           (fn-b3-octet-listp (cdr xs)))
    (null xs)))

; -----------------------------------------------------------------------------
; Total list primitives (as in books/sha256.lisp: `:guard t', so that no guard
; obligation reaches below a type prescription).

(defun fn-b3-nthx (n xs)
  ; Element n, or 0 past the end: the zero padding of a short block.
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (cond ((atom xs) 0)
          ((zp n) (car xs))
          (t (fn-b3-nthx (- n 1) (cdr xs))))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-b3-firstn-loop (n xs acc)
  (declare (xargs :measure (nfix n) :guard (true-listp acc) :verify-guards nil))
  (let ((n (nfix n)))
    (if (or (zp n) (atom xs))
        (revappend acc nil)
      (fn-b3-firstn-loop (- n 1) (cdr xs) (cons (car xs) acc)))))

(defun fn-b3-firstn (n xs)
  (declare (xargs :verify-guards nil :guard t :measure (nfix n)))
  (mbe :logic
       (let ((n (nfix n)))
         (if (or (zp n) (atom xs))
             nil
           (cons (car xs) (fn-b3-firstn (- n 1) (cdr xs)))))
       :exec (fn-b3-firstn-loop n xs nil)))

(local
 (defthm fn-b3-firstn-loop-is-revappend
   (equal (fn-b3-firstn-loop n xs acc)
          (revappend acc (fn-b3-firstn n xs)))
   :hints (("Goal" :induct (fn-b3-firstn-loop n xs acc)
                   :in-theory (union-theories '(fn-b3-firstn-loop fn-b3-firstn revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-b3-firstn-loop)

(verify-guards fn-b3-firstn
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-b3-firstn)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-b3-firstn-loop-is-revappend (acc nil))))))


(defun fn-b3-nthcdrx (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom xs))
        xs
      (fn-b3-nthcdrx (- n 1) (cdr xs)))))

(defthm fn-b3-len-of-nthcdrx
  (equal (len (fn-b3-nthcdrx n xs))
         (nfix (- (len xs) (nfix n)))))

(defthm fn-b3-len-of-firstn
  (equal (len (fn-b3-firstn n xs))
         (min (nfix n) (len xs))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-b3-fix-octets-walk-loop (m acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp m)
      (fn-b3-fix-octets-walk-loop (cdr m) (cons (fn-b3-octet (car m)) acc))
    (revappend acc nil)))

(defun fn-b3-fix-octets-walk (m)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp m)
           (cons (fn-b3-octet (car m)) (fn-b3-fix-octets-walk (cdr m)))
         nil)
       :exec (fn-b3-fix-octets-walk-loop m nil)))

(local
 (defthm fn-b3-fix-octets-walk-loop-is-revappend
   (equal (fn-b3-fix-octets-walk-loop m acc)
          (revappend acc (fn-b3-fix-octets-walk m)))
   :hints (("Goal" :induct (fn-b3-fix-octets-walk-loop m acc)
                   :in-theory (union-theories '(fn-b3-fix-octets-walk-loop fn-b3-fix-octets-walk revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-b3-fix-octets-walk-loop)

(verify-guards fn-b3-fix-octets-walk
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-b3-fix-octets-walk)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-b3-fix-octets-walk-loop-is-revappend (acc nil))))))


(defthm fn-b3-fix-octets-walk-of-octets
  (implies (fn-b3-octet-listp m)
           (equal (fn-b3-fix-octets-walk m) m))
  :hints (("Goal" :in-theory (enable fn-b3-octet))))

(defun fn-b3-fix-octets (m)
  ; Any object as an octet list: each element of its conses as an octet, the
  ; last tail dropped.  The identity on an octet list, which is not copied.
  (declare (xargs :guard t))
  (mbe :logic (fn-b3-fix-octets-walk m)
       :exec (if (fn-b3-octet-listp m) m (fn-b3-fix-octets-walk m))))

(defthm fn-b3-octet-listp-of-fix-octets
  (fn-b3-octet-listp (fn-b3-fix-octets m))
  :hints (("Goal" :in-theory (enable fn-b3-octet))))

(defthm fn-b3-len-of-fix-octets
  (equal (len (fn-b3-fix-octets m)) (len m)))

(defthm fn-b3-fix-octets-of-octets
  (implies (fn-b3-octet-listp m)
           (equal (fn-b3-fix-octets m) m)))

; -----------------------------------------------------------------------------
; The word operations, on declared words (section 2.2: addition modulo 2^32,
; XOR, rotation right).

(defun fn-b3-add (x y)
  (declare (type (unsigned-byte 32) x y))
  (the (unsigned-byte 32) (mod (+ (ifix x) (ifix y)) 4294967296)))

(defun fn-b3-add3 (x y z)
  (declare (type (unsigned-byte 32) x y z))
  (the (unsigned-byte 32) (mod (+ (ifix x) (ifix y) (ifix z)) 4294967296)))

(defun fn-b3-xor (x y)
  ; The reduction is the identity on two words; it is here so that the
  ; result is a word by a fact about `mod' rather than about `logxor'.
  (declare (type (unsigned-byte 32) x y))
  (the (unsigned-byte 32) (mod (logxor x y) 4294967296)))

(defun fn-b3-rotr (x n)
  (declare (type (unsigned-byte 32) x) (type (integer 1 31) n))
  (the (unsigned-byte 32)
       (mod (logior (ash x (- n)) (ash x (- 32 n))) 4294967296)))

(defthm fn-b3-word-ops-type
  (and (unsigned-byte-p 32 (fn-b3-add x y))
       (unsigned-byte-p 32 (fn-b3-add3 x y z))
       (unsigned-byte-p 32 (fn-b3-xor x y))
       (unsigned-byte-p 32 (fn-b3-rotr x n))))

(in-theory (disable fn-b3-add fn-b3-add3 fn-b3-xor fn-b3-rotr))

; From here on a word is `unsigned-byte-p 32' and stays closed: the declared
; types of the functions below are proved from the type theorems of their
; callees, never by reopening the bound.
(local (in-theory (disable unsigned-byte-p mv-nth)))

; The quarter-round G (section 2.2), with the rotation distances 16, 12, 8, 7.
(defun fn-b3-g (a b c d mx my)
  (declare (type (unsigned-byte 32) a b c d mx my))
  (let* ((a (fn-b3-add3 a b mx))
         (d (fn-b3-rotr (fn-b3-xor d a) 16))
         (c (fn-b3-add c d))
         (b (fn-b3-rotr (fn-b3-xor b c) 12))
         (a (fn-b3-add3 a b my))
         (d (fn-b3-rotr (fn-b3-xor d a) 8))
         (c (fn-b3-add c d))
         (b (fn-b3-rotr (fn-b3-xor b c) 7)))
    (mv a b c d)))

(defthm fn-b3-g-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-g a b c d mx my)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-g a b c d mx my)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-g a b c d mx my)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-g a b c d mx my))))
  :hints (("Goal" :in-theory (enable fn-b3-g))))

(in-theory (disable fn-b3-g))

(defun fn-b3-round (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; One round (the BLAKE3 paper, section 2.2): G on the four columns, then
  ; on the four diagonals, each consuming the next two message words.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v4 v8 v12) (fn-b3-g v0 v4 v8 v12 m0 m1)
   (mv-let (v1 v5 v9 v13) (fn-b3-g v1 v5 v9 v13 m2 m3)
    (mv-let (v2 v6 v10 v14) (fn-b3-g v2 v6 v10 v14 m4 m5)
     (mv-let (v3 v7 v11 v15) (fn-b3-g v3 v7 v11 v15 m6 m7)
      (mv-let (v0 v5 v10 v15) (fn-b3-g v0 v5 v10 v15 m8 m9)
       (mv-let (v1 v6 v11 v12) (fn-b3-g v1 v6 v11 v12 m10 m11)
        (mv-let (v2 v7 v8 v13) (fn-b3-g v2 v7 v8 v13 m12 m13)
         (mv-let (v3 v4 v9 v14) (fn-b3-g v3 v4 v9 v14 m14 m15)
          (mv v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))))))))))

(defthm fn-b3-round-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 8 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 9 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 10 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 11 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 12 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 13 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 14 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 15 (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                              m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-round))))

(in-theory (disable fn-b3-round))

(defun fn-b3-rounds-7 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 7, then the output chaining value: the first half of the state XOR
  ; the second (section 2.2).
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m11 m15 m5 m0 m1 m9 m8 m6 m14 m10 m2 m12 m3 m4 m7 m13)
    (mv (fn-b3-xor v0 v8)
        (fn-b3-xor v1 v9)
        (fn-b3-xor v2 v10)
        (fn-b3-xor v3 v11)
        (fn-b3-xor v4 v12)
        (fn-b3-xor v5 v13)
        (fn-b3-xor v6 v14)
        (fn-b3-xor v7 v15))))

(defthm fn-b3-rounds-7-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-7))))

(in-theory (disable fn-b3-rounds-7))

(defun fn-b3-rounds-6 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 6 and the rounds after it.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m9 m14 m11 m5 m8 m12 m15 m1 m13 m3 m0 m10 m2 m6 m4 m7)
    (fn-b3-rounds-7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))

(defthm fn-b3-rounds-6-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-6))))

(in-theory (disable fn-b3-rounds-6))

(defun fn-b3-rounds-5 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 5 and the rounds after it.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m12 m13 m9 m11 m15 m10 m14 m8 m7 m2 m5 m3 m0 m1 m6 m4)
    (fn-b3-rounds-6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))

(defthm fn-b3-rounds-5-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-5))))

(in-theory (disable fn-b3-rounds-5))

(defun fn-b3-rounds-4 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 4 and the rounds after it.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m10 m7 m12 m9 m14 m3 m13 m15 m4 m0 m11 m2 m5 m8 m1 m6)
    (fn-b3-rounds-5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))

(defthm fn-b3-rounds-4-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-4))))

(in-theory (disable fn-b3-rounds-4))

(defun fn-b3-rounds-3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 3 and the rounds after it.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m3 m4 m10 m12 m13 m2 m7 m14 m6 m5 m9 m0 m11 m15 m8 m1)
    (fn-b3-rounds-4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))

(defthm fn-b3-rounds-3-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-3))))

(in-theory (disable fn-b3-rounds-3))

(defun fn-b3-rounds-2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 2 and the rounds after it.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m2 m6 m3 m10 m7 m0 m4 m13 m1 m11 m12 m5 m9 m14 m15 m8)
    (fn-b3-rounds-3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))

(defthm fn-b3-rounds-2-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-2))))

(in-theory (disable fn-b3-rounds-2))

(defun fn-b3-rounds-1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
  ; Round 1 and the rounds after it.
  (declare (type (unsigned-byte 32) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
           (type (unsigned-byte 32) m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))
  (mv-let (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (fn-b3-round v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)
    (fn-b3-rounds-2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                     m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))

(defthm fn-b3-rounds-1-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-rounds-1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                                                  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15))))
  :hints (("Goal" :in-theory (enable fn-b3-rounds-1))))

(in-theory (disable fn-b3-rounds-1))

; -----------------------------------------------------------------------------
; The compression function over any objects: each input read as a word, the
; state initialised (section 2.2: the chaining value, IV[0..3], the counter's
; low and high words, the block length, the flags), then the seven rounds.
; The counter is a natural of any size read modulo 2^64, as the reference's
; u64; fn's counters are chunk indices.

(defun fn-b3-compress-core (c0 c1 c2 c3 c4 c5 c6 c7
                             m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
                             counter blen flags)
  (declare (xargs :guard t))
  (fn-b3-rounds-1 (fn-b3-word c0) (fn-b3-word c1) (fn-b3-word c2) (fn-b3-word c3) (fn-b3-word c4) (fn-b3-word c5) (fn-b3-word c6) (fn-b3-word c7)
                  1779033703 3144134277 1013904242 2773480762
                  (fn-b3-word counter) (fn-b3-word (floor (nfix counter) 4294967296))
                  (fn-b3-word blen) (fn-b3-word flags)
                  (fn-b3-word m0) (fn-b3-word m1) (fn-b3-word m2) (fn-b3-word m3) (fn-b3-word m4) (fn-b3-word m5) (fn-b3-word m6) (fn-b3-word m7) (fn-b3-word m8) (fn-b3-word m9) (fn-b3-word m10) (fn-b3-word m11) (fn-b3-word m12) (fn-b3-word m13) (fn-b3-word m14) (fn-b3-word m15)))

(defthm fn-b3-compress-core-type
  (and (unsigned-byte-p 32 (mv-nth 0 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 1 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 2 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 3 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 4 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 5 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 6 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags)))
       (unsigned-byte-p 32 (mv-nth 7 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 counter blen flags))))
  :hints (("Goal" :in-theory (enable fn-b3-compress-core))))

(in-theory (disable fn-b3-compress-core))

; The compression function on a chaining value of 8 words and a block of 16,
; each a list; the output chaining value as a list of 8 words.
(defun fn-b3-compress (cv words counter blen flags)
  (declare (xargs :guard t))
  (mv-let (o0 o1 o2 o3 o4 o5 o6 o7)
    (fn-b3-compress-core (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv) (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv)
                         (fn-b3-nthx 0 words) (fn-b3-nthx 1 words) (fn-b3-nthx 2 words) (fn-b3-nthx 3 words) (fn-b3-nthx 4 words) (fn-b3-nthx 5 words) (fn-b3-nthx 6 words) (fn-b3-nthx 7 words) (fn-b3-nthx 8 words) (fn-b3-nthx 9 words) (fn-b3-nthx 10 words) (fn-b3-nthx 11 words) (fn-b3-nthx 12 words) (fn-b3-nthx 13 words) (fn-b3-nthx 14 words) (fn-b3-nthx 15 words)
                         counter blen flags)
    (list o0 o1 o2 o3 o4 o5 o6 o7)))

(defun fn-b3-word-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (unsigned-byte-p 32 (car xs)) (fn-b3-word-listp (cdr xs)))
    (null xs)))

(defthm fn-b3-compress-shape
  (and (fn-b3-word-listp (fn-b3-compress cv words counter blen flags))
       (true-listp (fn-b3-compress cv words counter blen flags))
       (equal (len (fn-b3-compress cv words counter blen flags)) 8)))

(in-theory (disable fn-b3-compress))

; -----------------------------------------------------------------------------
; Octets to words and back, little-endian (section 2.2: "the message block
; ... interpreted as 16 little-endian 32-bit words"; the output is the words
; serialized little-endian).

(defun fn-b3-le-word (b0 b1 b2 b3)
  (declare (xargs :guard t))
  (+ (fn-b3-octet b0)
     (* 256 (fn-b3-octet b1))
     (* 65536 (fn-b3-octet b2))
     (* 16777216 (fn-b3-octet b3))))

(defthm fn-b3-le-word-type
  (unsigned-byte-p 32 (fn-b3-le-word b0 b1 b2 b3))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(in-theory (disable fn-b3-le-word))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-b3-words-loop (k octets acc)
  (declare (xargs :measure (nfix k) :guard (true-listp acc) :verify-guards nil))
  (if (zp (nfix k))
      (revappend acc nil)
    (fn-b3-words-loop (- (nfix k) 1)
                      (fn-b3-nthcdrx 4 octets)
                      (cons (fn-b3-le-word (fn-b3-nthx 0 octets)
                                           (fn-b3-nthx 1 octets)
                                           (fn-b3-nthx 2 octets)
                                           (fn-b3-nthx 3 octets))
                            acc))))

(defun fn-b3-words (k octets)
  ; K little-endian words from the front of OCTETS, the octets past its end
  ; read as zero: a short final block is zero-padded (section 2.1).
  (declare (xargs :verify-guards nil :guard t :measure (nfix k)))
  (mbe :logic
       (if (zp (nfix k))
           nil
         (cons (fn-b3-le-word (fn-b3-nthx 0 octets) (fn-b3-nthx 1 octets)
                              (fn-b3-nthx 2 octets) (fn-b3-nthx 3 octets))
               (fn-b3-words (- (nfix k) 1) (fn-b3-nthcdrx 4 octets))))
       :exec (fn-b3-words-loop k octets nil)))

(local
 (defthm fn-b3-words-loop-is-revappend
   (equal (fn-b3-words-loop k octets acc)
          (revappend acc (fn-b3-words k octets)))
   :hints (("Goal" :induct (fn-b3-words-loop k octets acc)
                   :in-theory (union-theories '(fn-b3-words-loop fn-b3-words revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-b3-words-loop)

(verify-guards fn-b3-words
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-b3-words)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-b3-words-loop-is-revappend (acc nil))))))


(defthm fn-b3-words-shape
  (and (fn-b3-word-listp (fn-b3-words k octets))
       (true-listp (fn-b3-words k octets))
       (equal (len (fn-b3-words k octets)) (nfix k))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-b3-words-octets-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-b3-words-octets-loop (cdr rev)
                               (let ((w (fn-b3-word (car rev))))
                                 (list* (mod w 256)
                                        (mod (floor w 256) 256)
                                        (mod (floor w 65536) 256)
                                        (mod (floor w 16777216) 256)
                                        acc)))
    acc))

(defun fn-b3-words-octets (ws)
  ; Each word's four octets, least significant first.
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp ws)
           (let ((w (fn-b3-word (car ws))))
             (list* (mod w 256)
                    (mod (floor w 256) 256)
                    (mod (floor w 65536) 256)
                    (mod (floor w 16777216) 256)
                    (fn-b3-words-octets (cdr ws))))
         nil)
       :exec (fn-b3-words-octets-loop (fn-ag-rev-onto ws nil) nil)))

(local
 (defthm fn-b3-words-octets-loop-of-rev-onto
   (equal (fn-b3-words-octets-loop (fn-ag-rev-onto ws zs) nil)
          (fn-b3-words-octets-loop zs (fn-b3-words-octets ws)))
   :hints (("Goal" :induct (fn-ag-rev-onto ws zs)
                   :in-theory (union-theories '(fn-b3-words-octets-loop fn-b3-words-octets fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-b3-words-octets-loop)

(verify-guards fn-b3-words-octets
  :hints (("Goal" :in-theory (union-theories '(fn-b3-words-octets fn-b3-words-octets-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-b3-words-octets-loop-of-rev-onto (zs nil))))))


(defthm fn-b3-words-octets-shape
  (and (fn-b3-octet-listp (fn-b3-words-octets ws))
       (equal (len (fn-b3-words-octets ws)) (* 4 (len ws)))))

; -----------------------------------------------------------------------------
; A node's output (section 2.4): the inputs of the last compression of a chunk
; or of a parent, kept so that the root can compress them again with ROOT.

(defun fn-b3-output (cv words counter blen flags)
  (declare (xargs :guard t))
  (list cv words counter blen flags))

; The chaining value of a non-root node.
(defun fn-b3-output-cv (out)
  (declare (xargs :guard t))
  (fn-b3-compress (fn-b3-nthx 0 out) (fn-b3-nthx 1 out) (fn-b3-nthx 2 out)
                  (fn-b3-nthx 3 out) (fn-b3-nthx 4 out)))

; The root's 32 output octets: the same inputs with ROOT set and the output
; block counter 0 (section 2.6; fn uses only the first 32 octets).
(defun fn-b3-output-root (out)
  (declare (xargs :guard t))
  (fn-b3-words-octets
   (fn-b3-compress (fn-b3-nthx 0 out) (fn-b3-nthx 1 out) 0
                   (fn-b3-nthx 3 out)
                   (logior (ifix (fn-b3-nthx 4 out)) *fn-b3-root*))))

(defthm fn-b3-output-cv-shape
  (and (fn-b3-word-listp (fn-b3-output-cv out))
       (true-listp (fn-b3-output-cv out))
       (equal (len (fn-b3-output-cv out)) 8)))

(defthm fn-b3-output-root-shape
  (and (fn-b3-octet-listp (fn-b3-output-root out))
       (true-listp (fn-b3-output-root out))
       (equal (len (fn-b3-output-root out)) 32))
  :hints (("Goal" :use ((:instance fn-b3-words-octets-shape
                                   (ws (fn-b3-compress (fn-b3-nthx 0 out) (fn-b3-nthx 1 out) 0
                                                       (fn-b3-nthx 3 out)
                                                       (logior (ifix (fn-b3-nthx 4 out)) *fn-b3-root*)))))
           :in-theory (disable fn-b3-words-octets-shape))))

(in-theory (disable fn-b3-output-cv fn-b3-output-root))

; A chaining value as its eight words: what the compression function reads of
; any object.
(defun fn-b3-cv8 (cv)
  (declare (xargs :guard t))
  (list (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv)
        (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv)))

; -----------------------------------------------------------------------------
; A chunk (section 2.4): its blocks chained from the chaining value CV (the
; key), each compressed with the chunk counter; CHUNK_START on the first
; block, CHUNK_END on the last, whose length is its octet count (0 for the
; empty input's one block).  The result is the last block's output.

(defun fn-b3-chunk (cv octets counter flags startp)
  (declare (xargs :guard t :measure (len octets)))
  (let ((fl (logior (ifix flags) (if startp *fn-b3-chunk-start* 0))))
    (if (< 64 (len octets))
        (fn-b3-chunk (fn-b3-compress cv (fn-b3-words 16 octets) counter 64 fl)
                     (fn-b3-nthcdrx 64 octets) counter flags nil)
      (fn-b3-output (fn-b3-cv8 cv) (fn-b3-words 16 octets) counter (len octets)
                    (logior fl *fn-b3-chunk-end*)))))

; -----------------------------------------------------------------------------
; The tree (section 2.1): above one chunk, the left subtree holds the largest
; power-of-two number of whole chunks whose octets are fewer than the input's,
; the right subtree the rest; a parent compresses its children's chaining
; values under the key with counter 0, block length 64 and PARENT.

(defun fn-b3-left-chunks (p n)
  ; From P, doubled while twice it still leaves octets to its right.
  (declare (xargs :guard (and (natp p) (natp n))
                  :measure (nfix (- (nfix n) (* 1024 (nfix p))))))
  (if (and (posp p) (natp n) (< (* 2048 p) n))
      (fn-b3-left-chunks (* 2 p) n)
    p))

(defthm fn-b3-left-chunks-posp
  (implies (posp p) (posp (fn-b3-left-chunks p n)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-b3-left-chunks-below
  (implies (and (posp p) (natp n) (< (* 1024 p) n))
           (< (* 1024 (fn-b3-left-chunks p n)) n))
  :rule-classes (:rewrite :linear))

(defun fn-b3-node (key octets counter flags)
  (declare (xargs :guard t :measure (len octets)))
  (if (< 1024 (len octets))
      (let* ((lc (fn-b3-left-chunks 1 (len octets)))
             (ll (* 1024 lc)))
        (fn-b3-output key
                      (append (fn-b3-output-cv
                               (fn-b3-node key (fn-b3-firstn ll octets) counter flags))
                              (fn-b3-output-cv
                               (fn-b3-node key (fn-b3-nthcdrx ll octets)
                                           (+ (nfix counter) lc) flags)))
                      0 64 (logior (ifix flags) *fn-b3-parent*)))
    (fn-b3-chunk key octets counter flags t)))

; -----------------------------------------------------------------------------
; The three modes (section 2.3).

(defun fn-b3-hash (key flags octets)
  ; The root output of OCTETS under the key words KEY and the mode flags.
  (declare (xargs :guard t))
  (fn-b3-output-root (fn-b3-node key octets 0 flags)))

(defun fn-blake3 (m)
  ; BLAKE3 of any object read as octets: the hash mode, the IV as the key.
  (declare (xargs :guard t))
  (fn-b3-hash *fn-b3-iv* 0 (fn-b3-fix-octets m)))

(defun fn-blake3-keyed (key m)
  ; keyed_hash: KEY is 32 octets, read as eight words.
  (declare (xargs :guard t))
  (fn-b3-hash (fn-b3-words 8 (fn-b3-fix-octets key)) *fn-b3-keyed-hash*
              (fn-b3-fix-octets m)))

(defun fn-blake3-derive-key (context material)
  ; derive_key: the context string hashed under DERIVE_KEY_CONTEXT gives the
  ; key for the material under DERIVE_KEY_MATERIAL.
  (declare (xargs :guard t))
  (fn-b3-hash (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                          (fn-b3-fix-octets context)))
              *fn-b3-derive-key-material*
              (fn-b3-fix-octets material)))

; -----------------------------------------------------------------------------
; The shape: 32 octets, always, in every mode.

(defthm fn-b3-hash-shape
  (and (fn-b3-octet-listp (fn-b3-hash key flags octets))
       (true-listp (fn-b3-hash key flags octets))
       (equal (len (fn-b3-hash key flags octets)) 32)))

(defthm fn-blake3-shape
  (and (fn-b3-octet-listp (fn-blake3 m))
       (true-listp (fn-blake3 m))
       (equal (len (fn-blake3 m)) 32)))

(defthm fn-blake3-keyed-shape
  (and (fn-b3-octet-listp (fn-blake3-keyed key m))
       (true-listp (fn-blake3-keyed key m))
       (equal (len (fn-blake3-keyed key m)) 32)))

(defthm fn-blake3-derive-key-shape
  (and (fn-b3-octet-listp (fn-blake3-derive-key context material))
       (true-listp (fn-blake3-derive-key context material))
       (equal (len (fn-blake3-derive-key context material)) 32)))

; The coercion is the identity on the octets fn digests: on an octet list,
; `fn-blake3' is the hash of exactly those octets.
(defthm fn-blake3-of-octets
  (implies (fn-b3-octet-listp m)
           (equal (fn-blake3 m) (fn-b3-hash *fn-b3-iv* 0 m))))

(in-theory (disable fn-b3-hash fn-blake3 fn-blake3-keyed fn-blake3-derive-key))
