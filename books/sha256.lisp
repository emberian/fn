; fn: SHA-256 (FIPS 180-4) over octet lists, executable and guard verified.
;
; Why this book exists.  `books/crypto-seam.lisp' introduces `fn-digest' and
; `books/frame-octets.lisp' introduces `fn-frame-digest' as CONSTRAINED
; functions: shape only, no realiser, so a term mentioning either one cannot be
; evaluated.  That made a digest unusable on the served path (board note
; OB-AUTH-DIGEST) and forced the Python host to compute identities that ACL2
; owns, which AGENTS.md's one-owner rule refuses.  This book supplies the
; realiser; `books/crypto-attach.lisp' attaches it.
;
; What this book does and does not establish.  It defines the FIPS 180-4
; SHA-256 algorithm as an executable ACL2 function and proves its SHAPE (32
; octets, always).  Agreement with the standard is evidence, not proof: the
; published test vectors are checked by evaluation in
; `tests/acl2/sha256-tests.lisp'.  Collision resistance and preimage
; resistance are NOT proved here and are not provable here; they remain
; A-CRYPTO (specs/failures.md).  Attaching this book to the seam changes
; exactly one thing about the seam's logical content: nothing.  `defattach'
; adds no axioms; it makes the constrained function executable and obliges the
; attachment to satisfy every stated constraint.
;
; Representation.  Words are naturals below 2^32, carried through
; `fn-sha256-w32', which is `mod'-by-2^32 of an `ifix'.  Every bitwise step is
; `logand' / `logior' / `logxor' / `lognot' / `ash' wrapped in `fn-sha256-w32',
; so each intermediate is provably a natural below 2^32 from ONE type lemma
; and the guard obligations of the bit operations are discharged by type
; reasoning alone.  That is why this book needs no bitvector library: the only
; facts it uses about `logxor' and `ash' are their built-in type
; prescriptions.
;
; Totality.  Every function is total; the top-level `fn-sha256' has `:guard t'
; and coerces its argument with `fn-sha256-fix-octets', because the seam's
; `fn-digest' is constrained over ANY object.  `crypto-attach' proves the
; coercion is the identity on octet lists, so on every preimage fn actually
; digests, `fn-sha256' is SHA-256 of those octets and nothing else.

(in-package "ACL2")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local (in-theory (disable floor mod truncate rem)))

; -----------------------------------------------------------------------------
; Words and octets

(defconst *fn-sha256-w32-modulus* 4294967296)
(defconst *fn-sha256-digest-octets* 32)
(defconst *fn-sha256-block-octets* 64)

(defun fn-sha256-w32 (x)
  ; Any object as a 32-bit word.
  (declare (xargs :guard t))
  (mod (ifix x) 4294967296))

(defthm fn-sha256-w32-type
  (and (integerp (fn-sha256-w32 x))
       (<= 0 (fn-sha256-w32 x))
       (< (fn-sha256-w32 x) 4294967296))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-sha256-w32 x))
                                  (<= 0 (fn-sha256-w32 x))))
                 (:linear
                  :corollary (and (<= 0 (fn-sha256-w32 x))
                                  (< (fn-sha256-w32 x) 4294967296)))
                 (:rewrite
                  :corollary (integerp (fn-sha256-w32 x)))))

(defun fn-sha256-byte (x)
  ; Any object as an octet.
  (declare (xargs :guard t))
  (mod (ifix x) 256))

(defthm fn-sha256-byte-type
  (and (integerp (fn-sha256-byte x))
       (<= 0 (fn-sha256-byte x))
       (<= (fn-sha256-byte x) 255))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-sha256-byte x))
                                  (<= 0 (fn-sha256-byte x))))
                 (:linear
                  :corollary (and (<= 0 (fn-sha256-byte x))
                                  (<= (fn-sha256-byte x) 255)))
                 (:rewrite
                  :corollary (integerp (fn-sha256-byte x)))))

(in-theory (disable fn-sha256-w32 fn-sha256-byte))

; An octet list, recognized without depending on any other fn book: this book
; sits at the bottom of the tree so that the attachment book can include it
; beside the two seams without dragging a codec in.
(defun fn-sha256-octet-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs))
           (<= 0 (car xs))
           (<= (car xs) 255)
           (fn-sha256-octet-listp (cdr xs)))
    (null xs)))

; -----------------------------------------------------------------------------
; Total list primitives.  `nth', `take' and `append' all carry guards that
; would have to be re-established at every call site; these four are `:guard t'
; and total, which keeps every guard obligation below a type-prescription.

(defun fn-sha256-nthx (n xs)
  ; Element n, or 0 past the end.  Never reached past the end below.
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (cond ((atom xs) 0)
          ((zp n) (car xs))
          (t (fn-sha256-nthx (- n 1) (cdr xs))))))

(defun fn-sha256-firstn (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom xs))
        nil
      (cons (car xs) (fn-sha256-firstn (- n 1) (cdr xs))))))

(defun fn-sha256-nthcdrx (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom xs))
        xs
      (fn-sha256-nthcdrx (- n 1) (cdr xs)))))

(defun fn-sha256-appx (xs ys)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (car xs) (fn-sha256-appx (cdr xs) ys))
    ys))

(defun fn-sha256-revx (xs acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-sha256-revx (cdr xs) (cons (car xs) acc))
    acc))

(defthm fn-sha256-len-of-nthcdrx-decreases
  (implies (and (consp xs) (not (zp n)))
           (< (len (fn-sha256-nthcdrx n xs)) (len xs)))
  :rule-classes :linear)

(defthm fn-sha256-octet-listp-of-appx
  (implies (and (fn-sha256-octet-listp xs)
                (fn-sha256-octet-listp ys))
           (fn-sha256-octet-listp (fn-sha256-appx xs ys))))

(defthm fn-sha256-octet-listp-of-revx
  (implies (and (fn-sha256-octet-listp xs)
                (fn-sha256-octet-listp acc))
           (fn-sha256-octet-listp (fn-sha256-revx xs acc))))

(defthm fn-sha256-true-listp-of-appx
  (implies (true-listp ys)
           (true-listp (fn-sha256-appx xs ys))))

(defthm fn-sha256-len-of-appx
  (equal (len (fn-sha256-appx xs ys))
         (+ (len xs) (len ys))))

; -----------------------------------------------------------------------------
; FIPS 180-4 section 4.1.2: the six logical functions.

(defun fn-sha256-rotr32 (n x)
  ; Circular right shift by n in 0..31 (section 3.2).
  (declare (xargs :guard t))
  (let ((x (fn-sha256-w32 x))
        (n (mod (nfix n) 32)))
    (fn-sha256-w32 (logior (ash x (- n)) (ash x (- 32 n))))))

(defun fn-sha256-shr32 (n x)
  (declare (xargs :guard t))
  (fn-sha256-w32 (ash (fn-sha256-w32 x) (- (nfix n)))))

(defun fn-sha256-ch (x y z)
  (declare (xargs :guard t))
  (fn-sha256-w32
   (logxor (logand (fn-sha256-w32 x) (fn-sha256-w32 y))
           (logand (lognot (fn-sha256-w32 x)) (fn-sha256-w32 z)))))

(defun fn-sha256-maj (x y z)
  (declare (xargs :guard t))
  (fn-sha256-w32
   (logxor (logand (fn-sha256-w32 x) (fn-sha256-w32 y))
           (logxor (logand (fn-sha256-w32 x) (fn-sha256-w32 z))
                   (logand (fn-sha256-w32 y) (fn-sha256-w32 z))))))

(defun fn-sha256-bsig0 (x)
  ; Sigma-0 (big): ROTR 2 xor ROTR 13 xor ROTR 22.
  (declare (xargs :guard t))
  (fn-sha256-w32 (logxor (fn-sha256-rotr32 2 x)
                         (logxor (fn-sha256-rotr32 13 x)
                                 (fn-sha256-rotr32 22 x)))))

(defun fn-sha256-bsig1 (x)
  ; Sigma-1 (big): ROTR 6 xor ROTR 11 xor ROTR 25.
  (declare (xargs :guard t))
  (fn-sha256-w32 (logxor (fn-sha256-rotr32 6 x)
                         (logxor (fn-sha256-rotr32 11 x)
                                 (fn-sha256-rotr32 25 x)))))

(defun fn-sha256-ssig0 (x)
  ; sigma-0 (small): ROTR 7 xor ROTR 18 xor SHR 3.
  (declare (xargs :guard t))
  (fn-sha256-w32 (logxor (fn-sha256-rotr32 7 x)
                         (logxor (fn-sha256-rotr32 18 x)
                                 (fn-sha256-shr32 3 x)))))

(defun fn-sha256-ssig1 (x)
  ; sigma-1 (small): ROTR 17 xor ROTR 19 xor SHR 10.
  (declare (xargs :guard t))
  (fn-sha256-w32 (logxor (fn-sha256-rotr32 17 x)
                         (logxor (fn-sha256-rotr32 19 x)
                                 (fn-sha256-shr32 10 x)))))

; -----------------------------------------------------------------------------
; FIPS 180-4 sections 4.2.2 and 5.3.3: the round constants and the initial
; hash value.  Transcribed from the standard; the test vectors are what check
; the transcription.

(defconst *fn-sha256-k*
  '(#x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5
    #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
    #xd807aa98 #x12835b01 #x243185be #x550c7dc3
    #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
    #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc
    #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
    #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7
    #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
    #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13
    #x650a7354 #x766a0abb #x81c2c92e #x92722c85
    #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3
    #xd192e819 #xd6990624 #xf40e3585 #x106aa070
    #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5
    #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
    #x748f82ee #x78a5636f #x84c87814 #x8cc70208
    #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2))

(defconst *fn-sha256-h0*
  '(#x6a09e667 #xbb67ae85 #x3c6ef372 #xa54ff53a
    #x510e527f #x9b05688c #x1f83d9ab #x5be0cd19))

; -----------------------------------------------------------------------------
; Padding (section 5.1.1) and parsing (section 5.2.1).

(defun fn-sha256-zeros (n)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) nil (cons 0 (fn-sha256-zeros (- n 1))))))

(defthm fn-sha256-octet-listp-of-zeros
  (fn-sha256-octet-listp (fn-sha256-zeros n)))

(defthm fn-sha256-len-of-zeros
  (equal (len (fn-sha256-zeros n)) (nfix n)))

(defun fn-sha256-u64-be (n)
  ; The 64-bit big-endian encoding of a natural, as 8 octets.
  (declare (xargs :guard t))
  (let ((n (ifix n)))
    (list (fn-sha256-byte (ash n -56)) (fn-sha256-byte (ash n -48))
          (fn-sha256-byte (ash n -40)) (fn-sha256-byte (ash n -32))
          (fn-sha256-byte (ash n -24)) (fn-sha256-byte (ash n -16))
          (fn-sha256-byte (ash n -8))  (fn-sha256-byte n))))

(defthm fn-sha256-octet-listp-of-u64-be
  (fn-sha256-octet-listp (fn-sha256-u64-be n)))

(defthm fn-sha256-len-of-u64-be
  (equal (len (fn-sha256-u64-be n)) 8))

(defun fn-sha256-pad (msg)
  ; msg || 0x80 || 0x00^k || uint64-be(8*len), with k the least count making
  ; the total a multiple of 64 octets.  55 - len modulo 64 is -(len+9) mod 64.
  (declare (xargs :guard t))
  (fn-sha256-appx
   msg
   (cons 128
         (fn-sha256-appx (fn-sha256-zeros (mod (- 55 (len msg)) 64))
                         (fn-sha256-u64-be (* 8 (len msg)))))))

(defthm fn-sha256-octet-listp-of-pad
  (implies (fn-sha256-octet-listp msg)
           (fn-sha256-octet-listp (fn-sha256-pad msg))))

(defun fn-sha256-words16 (block)
  ; 64 octets to 16 big-endian words.
  (declare (xargs :guard t :measure (len block)
                  :hints (("Goal" :in-theory (enable fn-sha256-len-of-nthcdrx-decreases)))))
  (if (atom block)
      nil
    (cons (fn-sha256-w32
           (logior (ash (fn-sha256-byte (fn-sha256-nthx 0 block)) 24)
                   (logior (ash (fn-sha256-byte (fn-sha256-nthx 1 block)) 16)
                           (logior (ash (fn-sha256-byte (fn-sha256-nthx 2 block)) 8)
                                   (fn-sha256-byte (fn-sha256-nthx 3 block))))))
          (fn-sha256-words16 (fn-sha256-nthcdrx 4 block)))))

; -----------------------------------------------------------------------------
; The message schedule (section 6.2.2 step 1).
;
; The accumulator holds W in REVERSE, newest first, so W[t-2], W[t-7], W[t-15]
; and W[t-16] are at offsets 1, 6, 14 and 15: a fixed, shallow walk rather than
; an index into a growing list.

(defun fn-sha256-schedule-aux (n wrev)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
   (if (zp n)
      wrev
    (fn-sha256-schedule-aux
     (- n 1)
     (cons (fn-sha256-w32
            (+ (fn-sha256-ssig1 (fn-sha256-nthx 1 wrev))
               (fn-sha256-w32 (fn-sha256-nthx 6 wrev))
               (fn-sha256-ssig0 (fn-sha256-nthx 14 wrev))
               (fn-sha256-w32 (fn-sha256-nthx 15 wrev))))
           wrev)))))

(defun fn-sha256-schedule (ws16)
  ; W[0..63] in order.
  (declare (xargs :guard t))
  (fn-sha256-revx (fn-sha256-schedule-aux 48 (fn-sha256-revx ws16 nil)) nil))

; -----------------------------------------------------------------------------
; The compression function (section 6.2.2 steps 2 to 4).

(defun fn-sha256-rounds (ws ks a b c d e f g h)
  (declare (xargs :guard t :measure (len ws)))
  (if (or (atom ws) (atom ks))
      (list a b c d e f g h)
    (let ((t1 (fn-sha256-w32 (+ (fn-sha256-w32 h)
                                (fn-sha256-bsig1 e)
                                (fn-sha256-ch e f g)
                                (fn-sha256-w32 (car ks))
                                (fn-sha256-w32 (car ws)))))
          (t2 (fn-sha256-w32 (+ (fn-sha256-bsig0 a)
                                (fn-sha256-maj a b c)))))
      (fn-sha256-rounds (cdr ws) (cdr ks)
                        (fn-sha256-w32 (+ t1 t2)) a b c
                        (fn-sha256-w32 (+ (fn-sha256-w32 d) t1)) e f g))))

(defun fn-sha256-add8 (xs ys)
  (declare (xargs :guard t))
  (if (or (atom xs) (atom ys))
      nil
    (cons (fn-sha256-w32 (+ (fn-sha256-w32 (car xs)) (fn-sha256-w32 (car ys))))
          (fn-sha256-add8 (cdr xs) (cdr ys)))))

(defun fn-sha256-compress (block hs)
  (declare (xargs :guard t))
  (let ((ws (fn-sha256-schedule (fn-sha256-words16 block))))
    (fn-sha256-add8
     hs
     (fn-sha256-rounds ws *fn-sha256-k*
                       (fn-sha256-nthx 0 hs) (fn-sha256-nthx 1 hs)
                       (fn-sha256-nthx 2 hs) (fn-sha256-nthx 3 hs)
                       (fn-sha256-nthx 4 hs) (fn-sha256-nthx 5 hs)
                       (fn-sha256-nthx 6 hs) (fn-sha256-nthx 7 hs)))))

(defun fn-sha256-blocks (padded hs)
  (declare (xargs :guard t :measure (len padded)))
  (if (atom padded)
      hs
    (fn-sha256-blocks (fn-sha256-nthcdrx 64 padded)
                      (fn-sha256-compress (fn-sha256-firstn 64 padded) hs))))

; -----------------------------------------------------------------------------
; The digest

(defun fn-sha256-words-octets (ws)
  ; Words to big-endian octets.
  (declare (xargs :guard t))
  (if (atom ws)
      nil
    (let ((w (fn-sha256-w32 (car ws))))
      (cons (fn-sha256-byte (ash w -24))
            (cons (fn-sha256-byte (ash w -16))
                  (cons (fn-sha256-byte (ash w -8))
                        (cons (fn-sha256-byte w)
                              (fn-sha256-words-octets (cdr ws)))))))))

(defthm fn-sha256-octet-listp-of-words-octets
  (fn-sha256-octet-listp (fn-sha256-words-octets ws)))

(defthm fn-sha256-len-of-words-octets
  (equal (len (fn-sha256-words-octets ws)) (* 4 (len ws))))

(defun fn-sha256-fix-octets (m)
  ; Any object as an octet list.  The identity on octet lists; see
  ; `fn-sha256-fix-octets-is-identity' in books/crypto-attach.lisp.
  (declare (xargs :guard t))
  (if (consp m)
      (cons (fn-sha256-byte (car m)) (fn-sha256-fix-octets (cdr m)))
    nil))

(defthm fn-sha256-octet-listp-of-fix-octets
  (fn-sha256-octet-listp (fn-sha256-fix-octets m)))

(defthm fn-sha256-len-of-fix-octets
  (equal (len (fn-sha256-fix-octets m)) (len m)))

(defun fn-sha256-of-octets (msg)
  ; SHA-256 of an octet list, as 32 octets.
  (declare (xargs :guard (fn-sha256-octet-listp msg)))
  (fn-sha256-words-octets
   (fn-sha256-firstn 8 (fn-sha256-blocks (fn-sha256-pad msg) *fn-sha256-h0*))))

(defun fn-sha256 (m)
  ; SHA-256 of any object, read as octets.  This is the function the seams
  ; attach to.
  (declare (xargs :guard t))
  (fn-sha256-of-octets (fn-sha256-fix-octets m)))

; -----------------------------------------------------------------------------
; Shape.  The only property proved of the algorithm itself: it always yields
; exactly 32 octets, whatever it is handed.  That is what the two seams'
; constraints ask for, and all they ask for.

(defthm fn-sha256-len-of-firstn-8
  (implies (equal (len xs) 8)
           (equal (len (fn-sha256-firstn 8 xs)) 8))
  :hints (("Goal" :expand ((fn-sha256-firstn 8 xs)
                           (fn-sha256-firstn 7 (cdr xs))
                           (fn-sha256-firstn 6 (cddr xs))
                           (fn-sha256-firstn 5 (cdddr xs))
                           (fn-sha256-firstn 4 (cddddr xs))
                           (fn-sha256-firstn 3 (cdr (cddddr xs)))
                           (fn-sha256-firstn 2 (cddr (cddddr xs)))
                           (fn-sha256-firstn 1 (cdddr (cddddr xs)))))))

(defthm fn-sha256-len-of-add8
  (equal (len (fn-sha256-add8 xs ys))
         (min (len xs) (len ys))))

(defthm fn-sha256-len-of-rounds
  (equal (len (fn-sha256-rounds ws ks a b c d e f g h)) 8))

(defthm fn-sha256-len-of-compress
  (implies (equal (len hs) 8)
           (equal (len (fn-sha256-compress block hs)) 8)))

(defthm fn-sha256-len-of-blocks
  (implies (equal (len hs) 8)
           (equal (len (fn-sha256-blocks padded hs)) 8)))

(defthm fn-sha256-of-octets-shape
  (and (fn-sha256-octet-listp (fn-sha256-of-octets msg))
       (true-listp (fn-sha256-of-octets msg))
       (equal (len (fn-sha256-of-octets msg)) 32)))

(defthm fn-sha256-shape
  (and (fn-sha256-octet-listp (fn-sha256 m))
       (true-listp (fn-sha256 m))
       (equal (len (fn-sha256 m)) 32)))

(defthm fn-sha256-octet-listp-implies-true-listp
  (implies (fn-sha256-octet-listp xs)
           (true-listp xs))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The algorithm's internals are not proof vocabulary for any other book: what
; leaves here is the shape of the digest and the recognizer, plus the
; executable counterparts, which is what `defattach' and the test vectors need.
; Only the `:definition' runes are withdrawn, so ground terms still evaluate.

(deftheory fn-sha256-internals
  '((:d fn-sha256-w32) (:d fn-sha256-byte)
    (:d fn-sha256-nthx) (:d fn-sha256-firstn) (:d fn-sha256-nthcdrx)
    (:d fn-sha256-appx) (:d fn-sha256-revx)
    (:d fn-sha256-rotr32) (:d fn-sha256-shr32)
    (:d fn-sha256-ch) (:d fn-sha256-maj)
    (:d fn-sha256-bsig0) (:d fn-sha256-bsig1)
    (:d fn-sha256-ssig0) (:d fn-sha256-ssig1)
    (:d fn-sha256-zeros) (:d fn-sha256-u64-be) (:d fn-sha256-pad)
    (:d fn-sha256-words16) (:d fn-sha256-schedule-aux) (:d fn-sha256-schedule)
    (:d fn-sha256-rounds) (:d fn-sha256-add8) (:d fn-sha256-compress)
    (:d fn-sha256-blocks) (:d fn-sha256-words-octets)
    (:d fn-sha256-of-octets) (:d fn-sha256)))

(in-theory (disable fn-sha256-internals))
