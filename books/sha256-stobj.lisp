; fn: SHA-256 executed over a word stobj, proved equal to the list model.
;
; Why this book exists (D27, planning/design-2026-09-25-representation.md,
; boundary 3).  `books/sha256.lisp' is the logical model of FIPS 180-4: octet
; lists in, a 32-octet list out, every word a natural under `fn-sha256-w32'.
; Executed, it costs about four conses per message octet (the padding copy,
; the per-block slices, the schedule consed and reversed twice) and generic
; integer arithmetic on undeclared words; on the POST path it was a third of
; the CPU.  This book computes the same digest over a single-threaded object:
; the schedule W[0..63] and the hash state H[0..7] in `(unsigned-byte 32)'
; arrays, the eight working registers as typed arguments, and the padded
; message read in place -- an octet list by `car'/`cdr' as the words are
; loaded, a string by `char' at an index -- with the padding synthesised from
; the length instead of built.  Nothing is copied and nothing is consed per
; octet; a digest allocates the local stobj (288 bytes of arrays), eight
; conses per block for the registers, and the 32-octet result the seam's
; shape demands.
;
; What is proved.  `fn-sha256-stobj-is-sha256' states that the stobj
; computation equals `fn-sha256' on EVERY object, with no hypothesis;
; `fn-sha256-stobj-is-sha256-of-octets' is its instance on octet lists
; against `fn-sha256-of-octets'; and `fn-sha256-of-string-is-sha256-of-octets'
; says the string entry digests the string's character codes.  The proof is
; the compression function's correspondence, block by block: the padded
; octet at every index (`fn-shs-pb-is-nthx-of-pad'), the sixteen loaded
; words (`fn-shs-load-list-block-loads-words16', `-str-'), the extended
; schedule against the list model's reversed accumulator
; (`fn-shs-extend-yields-schedule'), the sixty-four rounds
; (`fn-shs-rounds-is-rounds'), one block (`fn-shs-compress-loaded-is-compress')
; and all blocks (`fn-shs-blocks-list-is-blocks', `-str-').  It is a named
; correspondence rather than an `mbe' because the two computations have
; different signatures (a stobj threads through one of them); the word
; primitives, whose signatures agree, ARE `mbe's whose `:logic' is the list
; model's own term, so the correspondence is about data flow alone.
;
; What is not proved, and stays A-CRYPTO: that either function is collision
; resistant.  Agreement with the standard is evidence by evaluation
; (tests/acl2/sha256-stobj-tests.lisp runs the FIPS vectors through both).
;
; The attachment (books/crypto-attach.lisp) binds `fn-digest' and
; `fn-frame-digest' to `fn-sha256-stobj' under the equality above; it
; introduces no axiom and changes no theorem.
;
; Proof style.  Constant-index `nth' and `update-nth' open into car/cdr/cons
; forms and case-split; from the stobj on, both stay closed and the stobj
; facts go through `nth-update-nth'.  Array reads are bridged to the model's
; `fn-sha256-nthx' by one rule restricted to reads of an array field.

(in-package "ACL2")
(include-book "sha256")

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod truncate rem ash)))

; -----------------------------------------------------------------------------
; Word facts.  `fn-sha256-w32' is reduction modulo 2^32 and `fn-sha256-byte'
; modulo 2^8; on a word or an octet each is the identity.  The executable
; branches below reduce with `mod' by the same constants, which SBCL compiles
; to a mask on a non-negative fixnum, so every `mbe' obligation is one of
; these facts.

(local
 (defthm fn-shs-w32-of-u32
   (implies (unsigned-byte-p 32 x)
            (equal (fn-sha256-w32 x) x))
   :hints (("Goal" :in-theory (enable fn-sha256-w32)))))

(local
 (defthm fn-shs-byte-of-u8
   (implies (unsigned-byte-p 8 x)
            (equal (fn-sha256-byte x) x))
   :hints (("Goal" :in-theory (enable fn-sha256-byte)))))

(local
 (defthm fn-shs-u32-of-w32
   (unsigned-byte-p 32 (fn-sha256-w32 x))))

(local
 (defthm fn-shs-u8-of-byte
   (unsigned-byte-p 8 (fn-sha256-byte x))))

(local
 (defthm fn-shs-w32-of-w32
   (equal (fn-sha256-w32 (fn-sha256-w32 x)) (fn-sha256-w32 x))))

(local
 (defthm fn-shs-w32-is-mod
   (implies (integerp z)
            (equal (fn-sha256-w32 z) (mod z 4294967296)))
   :hints (("Goal" :in-theory (enable fn-sha256-w32)))))

(local
 (defthm fn-shs-byte-is-mod
   (implies (integerp z)
            (equal (fn-sha256-byte z) (mod z 256)))
   :hints (("Goal" :in-theory (enable fn-sha256-byte)))))

(local
 (defthm fn-shs-u32-of-mod
   (implies (integerp z)
            (unsigned-byte-p 32 (mod z 4294967296)))
   :hints (("Goal" :use ((:instance fn-shs-u32-of-w32 (x z)))))))

(local
 (defthm fn-shs-u8-of-mod
   (implies (integerp z)
            (unsigned-byte-p 8 (mod z 256)))
   :hints (("Goal" :use ((:instance fn-shs-u8-of-byte (x z)))))))

; The two `mod' forms are for the guard proofs of the primitives only; the
; correspondence below is between `fn-sha256-w32' terms on both sides.
(local (in-theory (disable fn-shs-w32-is-mod fn-shs-byte-is-mod)))

(local
 (defthm fn-shs-u8-of-char-code
   (unsigned-byte-p 8 (char-code c))))

(local (deftheory fn-shs-primitive-guards
         '(fn-shs-w32-is-mod fn-shs-byte-is-mod
           fn-sha256-rotr32 fn-sha256-shr32 fn-sha256-ch fn-sha256-maj
           fn-sha256-bsig0 fn-sha256-bsig1 fn-sha256-ssig0 fn-sha256-ssig1)))

; -----------------------------------------------------------------------------
; Word primitives.  Each is an `mbe' whose `:logic' is the list model's term
; verbatim and whose `:exec' is the same arithmetic on declared 32-bit words.
; Guard verification proves the two agree; nothing below reasons about bits.

(defun-inline fn-shs-add (x y)
  (declare (type (unsigned-byte 32) x y)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-w32 (+ (fn-sha256-w32 x) (fn-sha256-w32 y)))
       :exec (the (unsigned-byte 32) (mod (+ x y) 4294967296))))

(defun-inline fn-shs-rotr (n x)
  (declare (type (integer 1 31) n) (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-rotr32 n x)
       :exec (the (unsigned-byte 32)
                  (mod (logior (ash x (- n)) (ash x (- 32 n))) 4294967296))))

(defun-inline fn-shs-shr (n x)
  (declare (type (integer 1 31) n) (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-shr32 n x)
       :exec (the (unsigned-byte 32) (mod (ash x (- n)) 4294967296))))

(defun-inline fn-shs-ch (x y z)
  (declare (type (unsigned-byte 32) x y z)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-ch x y z)
       :exec (the (unsigned-byte 32)
                  (mod (logxor (logand x y) (logand (lognot x) z)) 4294967296))))

(defun-inline fn-shs-maj (x y z)
  (declare (type (unsigned-byte 32) x y z)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-maj x y z)
       :exec (the (unsigned-byte 32)
                  (mod (logxor (logand x y) (logxor (logand x z) (logand y z)))
                       4294967296))))

(defun-inline fn-shs-bsig0 (x)
  (declare (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-bsig0 x)
       :exec (the (unsigned-byte 32)
                  (mod (logxor (fn-shs-rotr 2 x)
                               (logxor (fn-shs-rotr 13 x) (fn-shs-rotr 22 x)))
                       4294967296))))

(defun-inline fn-shs-bsig1 (x)
  (declare (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-bsig1 x)
       :exec (the (unsigned-byte 32)
                  (mod (logxor (fn-shs-rotr 6 x)
                               (logxor (fn-shs-rotr 11 x) (fn-shs-rotr 25 x)))
                       4294967296))))

(defun-inline fn-shs-ssig0 (x)
  (declare (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-ssig0 x)
       :exec (the (unsigned-byte 32)
                  (mod (logxor (fn-shs-rotr 7 x)
                               (logxor (fn-shs-rotr 18 x) (fn-shs-shr 3 x)))
                       4294967296))))

(defun-inline fn-shs-ssig1 (x)
  (declare (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-ssig1 x)
       :exec (the (unsigned-byte 32)
                  (mod (logxor (fn-shs-rotr 17 x)
                               (logxor (fn-shs-rotr 19 x) (fn-shs-shr 10 x)))
                       4294967296))))

; The two temporaries of a round (section 6.2.2 step 3) and the schedule
; word (step 1), each the list model's term verbatim in the logic.
(defun-inline fn-shs-t1 (h e f g k w)
  (declare (type (unsigned-byte 32) h e f g k w)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-w32 (+ (fn-sha256-w32 h)
                                (fn-sha256-bsig1 e)
                                (fn-sha256-ch e f g)
                                (fn-sha256-w32 k)
                                (fn-sha256-w32 w)))
       :exec (the (unsigned-byte 32)
                  (mod (+ h (fn-shs-bsig1 e) (fn-shs-ch e f g) k w) 4294967296))))

(defun-inline fn-shs-t2 (a b c)
  (declare (type (unsigned-byte 32) a b c)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-w32 (+ (fn-sha256-bsig0 a) (fn-sha256-maj a b c)))
       :exec (the (unsigned-byte 32)
                  (mod (+ (fn-shs-bsig0 a) (fn-shs-maj a b c)) 4294967296))))

(defun-inline fn-shs-sched-word (w2 w7 w15 w16)
  (declare (type (unsigned-byte 32) w2 w7 w15 w16)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-w32 (+ (fn-sha256-ssig1 w2)
                                (fn-sha256-w32 w7)
                                (fn-sha256-ssig0 w15)
                                (fn-sha256-w32 w16)))
       :exec (the (unsigned-byte 32)
                  (mod (+ (fn-shs-ssig1 w2) w7 (fn-shs-ssig0 w15) w16) 4294967296))))

(defun-inline fn-shs-be-word (b0 b1 b2 b3)
  ; Four octets to a big-endian word: `fn-sha256-words16's term.
  (declare (type (unsigned-byte 8) b0 b1 b2 b3)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (fn-sha256-w32
               (logior (ash (fn-sha256-byte b0) 24)
                       (logior (ash (fn-sha256-byte b1) 16)
                               (logior (ash (fn-sha256-byte b2) 8)
                                       (fn-sha256-byte b3)))))
       :exec (the (unsigned-byte 32)
                  (mod (logior (ash b0 24) (logior (ash b1 16) (logior (ash b2 8) b3)))
                       4294967296))))

(defun-inline fn-shs-word-byte (s w)
  ; Octet of a word at bit offset s in {0, 8, 16, 24}: `fn-sha256-words-octets's
  ; terms, which shift by 24, 16 and 8 and take the low octet unshifted.
  (declare (type (integer 0 24) s) (type (unsigned-byte 32) w)
           (xargs :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (if (zp s)
                  (fn-sha256-byte (fn-sha256-w32 w))
                (fn-sha256-byte (ash (fn-sha256-w32 w) (- s))))
       :exec (the (unsigned-byte 8) (mod (if (= s 0) w (ash w (- s))) 256))))

(defun-inline fn-shs-len-byte (q n)
  ; Octet q (0 = most significant) of the 64-bit big-endian bit length:
  ; `fn-sha256-u64-be's term at position q, whose last octet is unshifted.
  (declare (type (integer 0 7) q)
           (xargs :guard (natp n)
                  :guard-hints (("Goal" :in-theory (enable fn-shs-primitive-guards)))))
  (mbe :logic (if (= q 7)
                  (fn-sha256-byte (* 8 n))
                (fn-sha256-byte (ash (* 8 n) (- (* 8 (- 7 q))))))
       :exec (the (unsigned-byte 8)
                  (mod (if (= q 7) (* 8 n) (ash (* 8 n) (- (* 8 (- 7 q))))) 256))))

(defun-inline fn-shs-octet (x)
  ; Any object as an octet: `fn-sha256-fix-octets's per-element coercion.
  (declare (xargs :guard t))
  (mbe :logic (fn-sha256-byte x)
       :exec (if (and (integerp x) (<= 0 x) (< x 256)) x (fn-sha256-byte x))))

(defun fn-shs-word-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (unsigned-byte-p 32 (car xs)) (fn-shs-word-listp (cdr xs)))
    (null xs)))

; -----------------------------------------------------------------------------
; The padding (section 5.1.1), by index.  The padded length is the list
; model's own expression; the number of blocks is what `floor-mod-elim'
; makes of it, so that "the padded length is 64 blocks" is one linear fact.

(defun fn-shs-pad-len (n)
  (declare (xargs :guard (natp n)))
  (+ n 9 (mod (- 55 n) 64)))

(defun fn-shs-nblocks (n)
  (declare (xargs :guard (natp n)))
  (- 1 (floor (- 55 n) 64)))

(defthm fn-shs-pad-len-type
  (implies (natp n)
           (and (integerp (fn-shs-pad-len n))
                (<= (+ n 9) (fn-shs-pad-len n))))
  :rule-classes ((:type-prescription :corollary (implies (integerp n) (integerp (fn-shs-pad-len n))))
                 (:type-prescription :corollary (implies (natp n) (natp (fn-shs-pad-len n))))
                 (:linear :corollary (implies (natp n) (<= (+ n 9) (fn-shs-pad-len n))))))

(defthm fn-shs-pad-len-is-blocks
  (implies (natp n)
           (equal (* 64 (fn-shs-nblocks n)) (fn-shs-pad-len n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance floor-mod-elim (x (- 55 n)) (y 64)))
           :in-theory (disable floor-mod-elim))))

(defthm fn-shs-nblocks-type
  (implies (natp n)
           (and (integerp (fn-shs-nblocks n))
                (<= 1 (fn-shs-nblocks n))))
  :rule-classes ((:type-prescription :corollary (implies (integerp n) (integerp (fn-shs-nblocks n))))
                 (:type-prescription :corollary (implies (natp n) (natp (fn-shs-nblocks n))))
                 (:linear :corollary (implies (natp n) (<= 1 (fn-shs-nblocks n)))))
  :hints (("Goal" :use ((:instance floor-mod-elim (x (- 55 n)) (y 64)))
           :in-theory (disable floor-mod-elim))))

(in-theory (disable fn-shs-pad-len fn-shs-nblocks))

(defun fn-shs-tail-byte (i n)
  ; The padded octet at index i past the message: 0x80, the zeros, the length.
  (declare (type (integer 0 *) i n)
           (xargs :guard (< i (fn-shs-pad-len n))))
  (cond ((= i n) 128)
        ((< i (- (fn-shs-pad-len n) 8)) 0)
        (t (fn-shs-len-byte (- i (- (fn-shs-pad-len n) 8)) n))))

; The octet facts, in the three forms guard proofs use: `unsigned-byte-p'
; opens into a type and a bound, so each fact is a type prescription and a
; linear rule as well as the closed form.
(defthm fn-shs-u8-of-tail-byte
  (and (integerp (fn-shs-tail-byte i n))
       (<= 0 (fn-shs-tail-byte i n))
       (< (fn-shs-tail-byte i n) 256))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-shs-tail-byte i n))
                                  (<= 0 (fn-shs-tail-byte i n))))
                 (:linear :corollary (< (fn-shs-tail-byte i n) 256))
                 (:rewrite :corollary (unsigned-byte-p 8 (fn-shs-tail-byte i n)))))

(defun fn-shs-pb (i n msg)
  ; The padded message's octet at index i, for a message of n octets.  This
  ; is the logical reading both loaders below are proved to agree with.
  (declare (xargs :guard (and (natp i) (natp n) (< i (fn-shs-pad-len n)))))
  (if (< i n) (fn-sha256-nthx i msg) (fn-shs-tail-byte i n)))

; The readers stay closed from here: opened, each read case-splits on the
; padding, and a loader proof sees sixteen words of it.  The octet facts
; above are all their callers need.
(local (in-theory (disable fn-shs-tail-byte)))

; -----------------------------------------------------------------------------
; The stobj: the schedule W[0..63] and the hash state H[0..7].

(defstobj fn-shs
  (fn-shs-w :type (array (unsigned-byte 32) (64)) :initially 0)
  (fn-shs-h :type (array (unsigned-byte 32) (8)) :initially 0)
  :inline t
  :renaming ((fn-shsp fn-shs-p)
             (fn-shs-wi fn-shs-w-ref) (update-fn-shs-wi fn-shs-w-set)
             (fn-shs-w-length fn-shs-w-len)
             (fn-shs-hi fn-shs-h-ref) (update-fn-shs-hi fn-shs-h-set)
             (fn-shs-h-length fn-shs-h-len)))

(defconst *fn-shs-w* 0)
(defconst *fn-shs-h* 1)

(local
 (defthm fn-shs-wp-nth
   (implies (and (fn-shs-wp w) (natp i) (< i (len w)))
            (unsigned-byte-p 32 (nth i w)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-shs-hp-nth
   (implies (and (fn-shs-hp h) (natp i) (< i (len h)))
            (unsigned-byte-p 32 (nth i h)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-shs-wp-of-update-nth
   (implies (and (fn-shs-wp w) (natp i) (< i (len w)) (unsigned-byte-p 32 v))
            (fn-shs-wp (update-nth i v w)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-shs-hp-of-update-nth
   (implies (and (fn-shs-hp h) (natp i) (< i (len h)) (unsigned-byte-p 32 v))
            (fn-shs-hp (update-nth i v h)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-shs-len-of-update-nth
   (equal (len (update-nth i v l))
          (max (+ 1 (nfix i)) (len l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

; From here on the two list primitives stay closed (see the header).
(local (in-theory (disable nth update-nth)))

; The recognizer survives an in-range update, so every stobj function below
; preserves `fn-shs-p'; the callers' guards need that stated per function.
(local
 (defthm fn-shs-p-of-update-w
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 64) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 0 (update-nth i v (nth 0 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-shs-p-of-update-h
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 1 (update-nth i v (nth 1 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t))))

; The recognizer's parts, for reads of a stobj a function returned.
(local
 (defthm fn-shs-p-parts
   (implies (fn-shs-p fn-shs)
            (and (fn-shs-wp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-hp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8)))))

; -----------------------------------------------------------------------------
; The two message readers.  A string is read at an index; an octet list is
; consumed by `cdr' as the index advances, so the list reader threads the
; remaining list.

(defun fn-shs-str-byte (i n s)
  (declare (type (integer 0 *) i n) (type string s)
           (xargs :guard (and (= n (length s)) (< i (fn-shs-pad-len n)))))
  (if (< i n)
      (mbe :logic (fn-sha256-byte (char-code (char s i)))
           :exec (the (unsigned-byte 8) (char-code (char s i))))
    (fn-shs-tail-byte i n)))

(defthm fn-shs-u8-of-str-byte
  (and (integerp (fn-shs-str-byte i n s))
       (<= 0 (fn-shs-str-byte i n s))
       (< (fn-shs-str-byte i n s) 256))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-shs-str-byte i n s))
                                  (<= 0 (fn-shs-str-byte i n s))))
                 (:linear :corollary (< (fn-shs-str-byte i n s) 256))
                 (:rewrite :corollary (unsigned-byte-p 8 (fn-shs-str-byte i n s)))))

(defun fn-shs-list-byte (i n rest)
  (declare (type (integer 0 *) i n)
           (xargs :guard (< i (fn-shs-pad-len n))))
  (if (consp rest)
      (mv (fn-shs-octet (car rest)) (cdr rest))
    (mv (fn-shs-tail-byte i n) rest)))

(defthm fn-shs-u8-of-list-byte
  (and (integerp (car (fn-shs-list-byte i n rest)))
       (<= 0 (car (fn-shs-list-byte i n rest)))
       (< (car (fn-shs-list-byte i n rest)) 256))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (car (fn-shs-list-byte i n rest)))
                                  (<= 0 (car (fn-shs-list-byte i n rest)))))
                 (:linear :corollary (< (car (fn-shs-list-byte i n rest)) 256))
                 (:rewrite :corollary (unsigned-byte-p 8 (car (fn-shs-list-byte i n rest))))))

(local (in-theory (disable fn-shs-str-byte fn-shs-list-byte)))

(defun fn-shs-load-str-word (j base n s fn-shs)
  (declare (type (integer 0 15) j) (type (integer 0 *) base n) (type string s)
           (xargs :stobjs fn-shs
                  :guard (and (= n (length s))
                              (<= (+ base 64) (fn-shs-pad-len n)))))
  (let ((i (+ base (* 4 j))))
    (fn-shs-w-set j
                  (fn-shs-be-word (fn-shs-str-byte i n s)
                                  (fn-shs-str-byte (+ i 1) n s)
                                  (fn-shs-str-byte (+ i 2) n s)
                                  (fn-shs-str-byte (+ i 3) n s))
                  fn-shs)))

(local
 (defthm fn-shs-p-of-load-str-word
   (implies (and (fn-shs-p fn-shs) (natp j) (< j 16))
            (fn-shs-p (fn-shs-load-str-word j base n s fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable fn-shs-load-str-word)))

(defun fn-shs-load-str-block (j base n s fn-shs)
  (declare (type (integer 0 16) j) (type (integer 0 *) base n) (type string s)
           (xargs :stobjs fn-shs
                  :guard (and (= n (length s))
                              (<= (+ base 64) (fn-shs-pad-len n)))
                  :measure (nfix (- 16 j))))
  (if (mbe :logic (zp (- 16 j)) :exec (= j 16))
      fn-shs
    (let ((fn-shs (fn-shs-load-str-word j base n s fn-shs)))
      (fn-shs-load-str-block (+ j 1) base n s fn-shs))))

(local
 (defthm fn-shs-p-of-load-str-block
   (implies (and (fn-shs-p fn-shs) (natp j))
            (fn-shs-p (fn-shs-load-str-block j base n s fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-load-str-block))))

(defun fn-shs-load-list-word (j base n rest fn-shs)
  (declare (type (integer 0 15) j) (type (integer 0 *) base n)
           (xargs :stobjs fn-shs
                  :guard (<= (+ base 64) (fn-shs-pad-len n))))
  (let ((i (+ base (* 4 j))))
    (mv-let (b0 rest) (fn-shs-list-byte i n rest)
      (mv-let (b1 rest) (fn-shs-list-byte (+ i 1) n rest)
        (mv-let (b2 rest) (fn-shs-list-byte (+ i 2) n rest)
          (mv-let (b3 rest) (fn-shs-list-byte (+ i 3) n rest)
            (let ((fn-shs (fn-shs-w-set j (fn-shs-be-word b0 b1 b2 b3) fn-shs)))
              (mv rest fn-shs))))))))

(local
 (defthm fn-shs-p-of-load-list-word
   (implies (and (fn-shs-p fn-shs) (natp j) (< j 16))
            (fn-shs-p (mv-nth 1 (fn-shs-load-list-word j base n rest fn-shs))))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable fn-shs-load-list-word)))

(defun fn-shs-load-list-block (j base n rest fn-shs)
  (declare (type (integer 0 16) j) (type (integer 0 *) base n)
           (xargs :stobjs fn-shs
                  :guard (<= (+ base 64) (fn-shs-pad-len n))
                  :measure (nfix (- 16 j))))
  (if (mbe :logic (zp (- 16 j)) :exec (= j 16))
      (mv rest fn-shs)
    (mv-let (rest fn-shs) (fn-shs-load-list-word j base n rest fn-shs)
      (fn-shs-load-list-block (+ j 1) base n rest fn-shs))))

(local
 (defthm fn-shs-p-of-load-list-block
   (implies (and (fn-shs-p fn-shs) (natp j))
            (fn-shs-p (mv-nth 1 (fn-shs-load-list-block j base n rest fn-shs))))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-load-list-block))))

; -----------------------------------------------------------------------------
; The message schedule (step 1), the rounds (steps 2 and 3) and the state
; update (step 4), over the arrays.

(defun fn-shs-extend (t0 fn-shs)
  (declare (type (integer 16 64) t0)
           (xargs :stobjs fn-shs :measure (nfix (- 64 t0))))
  (if (mbe :logic (zp (- 64 t0)) :exec (= t0 64))
      fn-shs
    (let ((fn-shs (fn-shs-w-set t0
                                (fn-shs-sched-word (fn-shs-w-ref (- t0 2) fn-shs)
                                                   (fn-shs-w-ref (- t0 7) fn-shs)
                                                   (fn-shs-w-ref (- t0 15) fn-shs)
                                                   (fn-shs-w-ref (- t0 16) fn-shs))
                                fn-shs)))
      (fn-shs-extend (+ t0 1) fn-shs))))

(local
 (defthm fn-shs-p-of-extend
   (implies (and (fn-shs-p fn-shs) (natp t0))
            (fn-shs-p (fn-shs-extend t0 fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local
 (defthm fn-shs-extend-frame
   (equal (nth 1 (fn-shs-extend t0 fn-shs))
          (nth 1 fn-shs))))

(local (in-theory (disable (:d fn-shs-extend))))

(defun fn-shs-rounds (i ks a b c d e f g h fn-shs)
  ; Rounds i..63 with the round constants ks walked in step, as
  ; `fn-sha256-rounds' walks its two lists; the eight registers as values.
  (declare (type (integer 0 64) i) (type (unsigned-byte 32) a b c d e f g h)
           (xargs :stobjs fn-shs :guard (fn-shs-word-listp ks)
                  :measure (nfix (- 64 i))))
  (if (or (mbe :logic (zp (- 64 i)) :exec (= i 64)) (atom ks))
      (list a b c d e f g h)
    (let ((t1 (fn-shs-t1 h e f g (car ks) (fn-shs-w-ref i fn-shs)))
          (t2 (fn-shs-t2 a b c)))
      (fn-shs-rounds (+ i 1) (cdr ks)
                     (fn-shs-add t1 t2) a b c
                     (fn-shs-add d t1) e f g
                     fn-shs))))

(local
 (defthm fn-shs-word-listp-of-rounds
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b)
                 (unsigned-byte-p 32 c) (unsigned-byte-p 32 d)
                 (unsigned-byte-p 32 e) (unsigned-byte-p 32 f)
                 (unsigned-byte-p 32 g) (unsigned-byte-p 32 h))
            (fn-shs-word-listp (fn-shs-rounds i ks a b c d e f g h fn-shs)))))

(local (in-theory (disable (:d fn-shs-rounds))))

(defun fn-shs-h-add (i regs fn-shs)
  (declare (type (integer 0 8) i)
           (xargs :stobjs fn-shs :guard (fn-shs-word-listp regs)
                  :measure (nfix (- 8 i))))
  (if (or (mbe :logic (zp (- 8 i)) :exec (= i 8)) (atom regs))
      fn-shs
    (let ((fn-shs (fn-shs-h-set i (fn-shs-add (fn-shs-h-ref i fn-shs) (car regs)) fn-shs)))
      (fn-shs-h-add (+ i 1) (cdr regs) fn-shs))))

(local
 (defthm fn-shs-p-of-h-add
   (implies (and (fn-shs-p fn-shs) (natp i))
            (fn-shs-p (fn-shs-h-add i regs fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-h-add))))

(defun fn-shs-compress-loaded (fn-shs)
  ; One block, once W[0..15] hold it.
  (declare (xargs :stobjs fn-shs))
  (let ((fn-shs (fn-shs-extend 16 fn-shs)))
    (fn-shs-h-add 0
                  (fn-shs-rounds 0 *fn-sha256-k*
                                 (fn-shs-h-ref 0 fn-shs) (fn-shs-h-ref 1 fn-shs)
                                 (fn-shs-h-ref 2 fn-shs) (fn-shs-h-ref 3 fn-shs)
                                 (fn-shs-h-ref 4 fn-shs) (fn-shs-h-ref 5 fn-shs)
                                 (fn-shs-h-ref 6 fn-shs) (fn-shs-h-ref 7 fn-shs)
                                 fn-shs)
                  fn-shs)))

(local
 (defthm fn-shs-p-of-compress-loaded
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-compress-loaded fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-compress-loaded))))

(defun fn-shs-compress-str (b n s fn-shs)
  (declare (type (integer 0 *) b n) (type string s)
           (xargs :stobjs fn-shs
                  :guard (and (= n (length s)) (< b (fn-shs-nblocks n)))))
  (let ((fn-shs (fn-shs-load-str-block 0 (* 64 b) n s fn-shs)))
    (fn-shs-compress-loaded fn-shs)))

(local
 (defthm fn-shs-p-of-compress-str
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-compress-str b n s fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-compress-str))))

(defun fn-shs-compress-list (b n rest fn-shs)
  (declare (type (integer 0 *) b n)
           (xargs :stobjs fn-shs :guard (< b (fn-shs-nblocks n))))
  (mv-let (rest fn-shs) (fn-shs-load-list-block 0 (* 64 b) n rest fn-shs)
    (let ((fn-shs (fn-shs-compress-loaded fn-shs)))
      (mv rest fn-shs))))

(local
 (defthm fn-shs-p-of-compress-list
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (mv-nth 1 (fn-shs-compress-list b n rest fn-shs))))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-compress-list))))

(defun fn-shs-blocks-str (b nb n s fn-shs)
  (declare (type (integer 0 *) b nb n) (type string s)
           (xargs :stobjs fn-shs
                  :guard (and (= n (length s)) (= nb (fn-shs-nblocks n)) (<= b nb))
                  :measure (nfix (- nb b))))
  (if (mbe :logic (zp (- nb b)) :exec (= b nb))
      fn-shs
    (let ((fn-shs (fn-shs-compress-str b n s fn-shs)))
      (fn-shs-blocks-str (+ b 1) nb n s fn-shs))))

(local
 (defthm fn-shs-p-of-blocks-str
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-blocks-str b nb n s fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-blocks-str))))

(defun fn-shs-blocks-list (b nb n rest fn-shs)
  (declare (type (integer 0 *) b nb n)
           (xargs :stobjs fn-shs
                  :guard (and (= nb (fn-shs-nblocks n)) (<= b nb))
                  :measure (nfix (- nb b))))
  (if (mbe :logic (zp (- nb b)) :exec (= b nb))
      fn-shs
    (mv-let (rest fn-shs) (fn-shs-compress-list b n rest fn-shs)
      (fn-shs-blocks-list (+ b 1) nb n rest fn-shs))))

(local
 (defthm fn-shs-p-of-blocks-list
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-blocks-list b nb n rest fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-blocks-list))))

; -----------------------------------------------------------------------------
; The initial hash value in, the digest octets out.

(defun fn-shs-h-init (i hs fn-shs)
  (declare (type (integer 0 8) i)
           (xargs :stobjs fn-shs :guard (fn-shs-word-listp hs)
                  :measure (nfix (- 8 i))))
  (if (or (mbe :logic (zp (- 8 i)) :exec (= i 8)) (atom hs))
      fn-shs
    (let ((fn-shs (fn-shs-h-set i (car hs) fn-shs)))
      (fn-shs-h-init (+ i 1) (cdr hs) fn-shs))))

(local
 (defthm fn-shs-p-of-h-init
   (implies (and (fn-shs-p fn-shs) (natp i) (fn-shs-word-listp hs))
            (fn-shs-p (fn-shs-h-init i hs fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shs-h-init))))

(defun fn-shs-h-octets (i fn-shs)
  (declare (type (integer 0 8) i)
           (xargs :stobjs fn-shs :measure (nfix (- 8 i))))
  (if (mbe :logic (zp (- 8 i)) :exec (= i 8))
      nil
    (let ((w (fn-shs-h-ref i fn-shs)))
      (cons (fn-shs-word-byte 24 w)
            (cons (fn-shs-word-byte 16 w)
                  (cons (fn-shs-word-byte 8 w)
                        (cons (fn-shs-word-byte 0 w)
                              (fn-shs-h-octets (+ i 1) fn-shs))))))))

(local (in-theory (disable (:d fn-shs-h-octets))))

(defun fn-shs-digest-list (m fn-shs)
  (declare (xargs :stobjs fn-shs :guard t))
  (let* ((n (len m))
         (fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))
         (fn-shs (fn-shs-blocks-list 0 (fn-shs-nblocks n) n m fn-shs)))
    (mv (fn-shs-h-octets 0 fn-shs) fn-shs)))

(defun fn-shs-digest-str (s fn-shs)
  (declare (type string s) (xargs :stobjs fn-shs))
  (let* ((n (length s))
         (fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))
         (fn-shs (fn-shs-blocks-str 0 (fn-shs-nblocks n) n s fn-shs)))
    (mv (fn-shs-h-octets 0 fn-shs) fn-shs)))

(defun fn-sha256-stobj (m)
  ; SHA-256 of any object read as octets, over a local stobj.  This is the
  ; function the seams attach to; it has `fn-sha256's signature.
  (declare (xargs :guard t))
  (with-local-stobj fn-shs
    (mv-let (digest fn-shs) (fn-shs-digest-list m fn-shs)
      digest)))

(defun fn-sha256-of-string (s)
  ; SHA-256 of a string's character codes, read in place at an index.
  (declare (xargs :guard (stringp s)))
  (with-local-stobj fn-shs
    (mv-let (digest fn-shs) (fn-shs-digest-str s fn-shs)
      digest)))

(defun fn-shs-char-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-shs-char-octets (cdr chars)))
    nil))

(defun fn-shs-string-octets (s)
  ; The octets a string denotes: its character codes in order.
  (declare (xargs :guard (stringp s)))
  (fn-shs-char-octets (coerce s 'list)))

; =============================================================================
; The correspondence.

; The string's octets stay a closed term in this section; one lemma opens it.
(local (in-theory (disable fn-shs-string-octets)))

; -----------------------------------------------------------------------------
; List primitives of the model: `nthx', `firstn', `nthcdrx', `appx', `revx'.
; Their definitions stay closed (sha256's export theory) and open only in
; the lemma that inducts on them; below, the stobj proofs see these rules
; and nothing else, so a symbolic index is never unrolled.

(local
 (defthm fn-shs-nthx-is-nth
   (implies (< (nfix i) (len xs))
            (equal (fn-sha256-nthx i xs) (nth i xs)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth fn-sha256-nthx)))))

; The bridge: a read of an array field, `(nth i (nth k fn-shs))', is the
; model's `nthx' of that array.  Restricted to that shape so that the field
; selectors themselves and `nth-update-nth' are left alone.
(local
 (defthm fn-shs-nth-of-array-is-nthx
   (implies (and (syntaxp (and (consp xs) (eq (car xs) 'nth)))
                 (< (nfix i) (len xs)))
            (equal (nth i xs) (fn-sha256-nthx i xs)))
   :hints (("Goal" :use fn-shs-nthx-is-nth))))

(local
 (defthm fn-shs-nthx-of-update-nth
   (implies (and (< (nfix i) (len xs)) (< (nfix j) (len xs)))
            (equal (fn-sha256-nthx i (update-nth j v xs))
                   (if (equal (nfix i) (nfix j)) v (fn-sha256-nthx i xs))))
   :hints (("Goal" :use ((:instance fn-shs-nthx-is-nth (i i) (xs (update-nth j v xs)))
                         (:instance fn-shs-nthx-is-nth (i i) (xs xs)))))))

(local
 (defthm fn-shs-nthx-of-cons
   (equal (fn-sha256-nthx i (cons a b))
          (if (zp i) a (fn-sha256-nthx (- i 1) b)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthx)))))

(local
 (defthm fn-shs-nthcdrx-0
   (implies (zp i)
            (equal (fn-sha256-nthcdrx i xs) xs))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)))))

(local
 (defthm fn-shs-firstn-0
   (implies (zp n)
            (equal (fn-sha256-firstn n xs) nil))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn)))))

; Over a natural index, so that relieving the bound needs no `nfix'.
(local
 (defthm fn-shs-nthcdrx-consp-below
   (implies (and (natp i) (< i (len xs)))
            (consp (fn-sha256-nthcdrx i xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx i xs)))))

(local
 (defthm fn-shs-nthcdrx-atom-past
   (implies (and (natp i) (<= (len xs) i))
            (not (consp (fn-sha256-nthcdrx i xs))))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx i xs)))))

; The same two facts the other way, for a case split on the remaining list.
(local
 (defthm fn-shs-nthcdrx-consp-forward
   (implies (and (natp i) (consp (fn-sha256-nthcdrx i xs)))
            (< i (len xs)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use fn-shs-nthcdrx-atom-past))))

(local
 (defthm fn-shs-nthcdrx-atom-forward
   (implies (and (natp i) (not (consp (fn-sha256-nthcdrx i xs))))
            (<= (len xs) i))
   :rule-classes :forward-chaining
   :hints (("Goal" :use fn-shs-nthcdrx-consp-below))))

(local
 (defthm fn-shs-car-of-nthcdrx
   (implies (< (nfix i) (len xs))
            (equal (car (fn-sha256-nthcdrx i xs)) (fn-sha256-nthx i xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx fn-sha256-nthx)
            :induct (fn-sha256-nthcdrx i xs)))))

(local
 (defthm fn-shs-cdr-of-nthcdrx
   (implies (and (natp i) (< i (len xs)))
            (equal (cdr (fn-sha256-nthcdrx i xs))
                   (fn-sha256-nthcdrx (+ 1 i) xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx i xs)))))

(local
 (defthm fn-shs-nthcdrx-succ-past-end
   (implies (and (natp i) (<= (len xs) i))
            (equal (fn-sha256-nthcdrx (+ 1 i) xs)
                   (fn-sha256-nthcdrx i xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx i xs)))))

(local
 (defthm fn-shs-nthcdrx-of-nthcdrx
   (implies (and (natp i) (natp j))
            (equal (fn-sha256-nthcdrx i (fn-sha256-nthcdrx j xs))
                   (fn-sha256-nthcdrx (+ i j) xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx j xs)))))

(local
 (defthm fn-shs-nthx-of-nthcdrx
   (implies (and (natp i) (natp j))
            (equal (fn-sha256-nthx i (fn-sha256-nthcdrx j xs))
                   (fn-sha256-nthx (+ i j) xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx fn-sha256-nthx)
            :induct (fn-sha256-nthcdrx j xs)))))

(local
 (defthm fn-shs-len-of-nthcdrx
   (implies (natp i)
            (equal (len (fn-sha256-nthcdrx i xs))
                   (nfix (- (len xs) i))))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-sha256-nthcdrx i xs)))))

(local
 (defthm fn-shs-len-of-firstn
   (equal (len (fn-sha256-firstn n xs))
          (min (nfix n) (len xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn)))))

(local
 (defthm fn-shs-true-listp-of-firstn
   (true-listp (fn-sha256-firstn n xs))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn)))))

; An induction that steps an index, a count and a list together.
(local
 (defun fn-shs-ij-ind (i j xs)
   (if (or (zp i) (zp j) (atom xs))
       (list i j xs)
     (fn-shs-ij-ind (- i 1) (- j 1) (cdr xs)))))

(local
 (defthm fn-shs-nthx-of-firstn
   (implies (< (nfix i) (nfix n))
            (equal (fn-sha256-nthx i (fn-sha256-firstn n xs))
                   (fn-sha256-nthx i xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn fn-sha256-nthx)
            :induct (fn-shs-ij-ind i n xs)
            :expand ((fn-sha256-firstn n xs))))))

(local
 (defthm fn-shs-firstn-of-len
   (implies (and (true-listp xs) (<= (len xs) (nfix n)))
            (equal (fn-sha256-firstn n xs) xs))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn)))))

; Not on a constant count: ACL2 unifies (+ 1 j) with 16, and the rule
; would unroll every (firstn 16 ...) below into sixteen appends.
(local
 (defthm fn-shs-firstn-snoc
   (implies (and (syntaxp (not (quotep j))) (natp j) (< j (len xs)))
            (equal (fn-sha256-firstn (+ 1 j) xs)
                   (append (fn-sha256-firstn j xs) (list (fn-sha256-nthx j xs)))))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn fn-sha256-nthx)
            :induct (fn-sha256-firstn j xs)))))

; Both need the update in range: past the end `update-nth' extends the list.
; The induction steps the index, the count and the list together.
(local
 (defthm fn-shs-firstn-of-update-nth-above
   (implies (and (<= (nfix j) (nfix i)) (< (nfix i) (len xs)))
            (equal (fn-sha256-firstn j (update-nth i v xs))
                   (fn-sha256-firstn j xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-firstn)
            :induct (fn-shs-ij-ind i j xs)
            :expand ((update-nth i v xs))))))

(local
 (defthm fn-shs-nthcdrx-of-update-nth-above
   (implies (and (< (nfix i) (nfix j)) (< (nfix i) (len xs)))
            (equal (fn-sha256-nthcdrx j (update-nth i v xs))
                   (fn-sha256-nthcdrx j xs)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthcdrx)
            :induct (fn-shs-ij-ind i j xs)
            :expand ((update-nth i v xs))))))

(local
 (defthm fn-shs-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-shs-append-nil
   (implies (true-listp x)
            (equal (append x nil) x))))

(local
 (defthm fn-shs-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-shs-true-listp-of-append
   (implies (true-listp b)
            (true-listp (append a b)))))

(local
 (defthm fn-shs-cons-car-cdr
   (implies (consp x)
            (equal (cons (car x) (cdr x)) x))))

(local
 (defthm fn-shs-len-0
   (implies (true-listp x)
            (equal (equal (len x) 0) (equal x nil)))))

(local
 (defthm fn-shs-nthx-of-append
   (equal (fn-sha256-nthx i (append a b))
          (if (< (nfix i) (len a))
              (fn-sha256-nthx i a)
            (fn-sha256-nthx (- (nfix i) (len a)) b)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthx)
            :induct (fn-sha256-nthx i a)))))

(local
 (defthm fn-shs-nthx-of-appx
   (equal (fn-sha256-nthx i (fn-sha256-appx xs ys))
          (if (< (nfix i) (len xs))
              (fn-sha256-nthx i xs)
            (fn-sha256-nthx (- (nfix i) (len xs)) ys)))
   :hints (("Goal" :in-theory (enable fn-sha256-nthx fn-sha256-appx)
            :induct (fn-sha256-nthx i xs)))))

(local
 (defun fn-shs-nthx-zeros-ind (i k)
   (if (or (zp i) (zp k)) (list i k) (fn-shs-nthx-zeros-ind (- i 1) (- k 1)))))

(local
 (defthm fn-shs-nthx-of-zeros
   (equal (fn-sha256-nthx i (fn-sha256-zeros k)) 0)
   :hints (("Goal" :in-theory (enable fn-sha256-zeros fn-sha256-nthx)
            :induct (fn-shs-nthx-zeros-ind i k)
            :expand ((fn-sha256-zeros k))))))

(local
 (defthm fn-shs-revx-of-append
   (equal (fn-sha256-revx (append a b) acc)
          (fn-sha256-revx b (fn-sha256-revx a acc)))
   :hints (("Goal" :in-theory (enable fn-sha256-revx)))))

(local
 (defthm fn-shs-revx-of-cons
   (equal (fn-sha256-revx (cons a b) acc)
          (fn-sha256-revx b (cons a acc)))
   :hints (("Goal" :in-theory (enable fn-sha256-revx)))))

(local
 (defthm fn-shs-revx-of-atom
   (implies (not (consp xs))
            (equal (fn-sha256-revx xs acc) acc))
   :hints (("Goal" :in-theory (enable fn-sha256-revx)))))

(local
 (defthm fn-shs-nthx-of-fix-octets
   (implies (< (nfix i) (len m))
            (equal (fn-sha256-nthx i (fn-sha256-fix-octets m))
                   (fn-sha256-byte (fn-sha256-nthx i m))))
   :hints (("Goal" :in-theory (enable fn-sha256-fix-octets fn-sha256-nthx)
            :induct (fn-sha256-nthx i m)))))

(local
 (defthm fn-shs-nthx-of-char-octets
   (implies (< (nfix i) (len cs))
            (equal (fn-sha256-nthx i (fn-shs-char-octets cs))
                   (char-code (fn-sha256-nthx i cs))))
   :hints (("Goal" :in-theory (enable fn-sha256-nthx)
            :induct (fn-sha256-nthx i cs)))))

(local
 (defthm fn-shs-len-of-char-octets
   (equal (len (fn-shs-char-octets cs)) (len cs))))

(local
 (defthm fn-shs-len-of-string-octets
   (equal (len (fn-shs-string-octets s)) (len (coerce s 'list)))
   :hints (("Goal" :in-theory (enable fn-shs-string-octets)))))

; -----------------------------------------------------------------------------
; The padding.  The padded length, and the octet at every index.

(local
 (defthm fn-shs-len-of-pad
   (equal (len (fn-sha256-pad msg))
          (fn-shs-pad-len (len msg)))
   :hints (("Goal" :in-theory (enable fn-sha256-pad fn-shs-pad-len)))))

(local
 (defthm fn-shs-true-listp-of-pad
   (true-listp (fn-sha256-pad msg))
   :hints (("Goal" :in-theory (enable fn-sha256-pad)))))

(local
 (defthm fn-shs-nthx-of-u64-be
   (implies (and (natp q) (< q 8))
            (equal (fn-sha256-nthx q (fn-sha256-u64-be x))
                   (if (= q 7)
                       (fn-sha256-byte (ifix x))
                     (fn-sha256-byte (ash (ifix x) (- (* 8 (- 7 q))))))))
   :hints (("Goal" :in-theory (enable fn-sha256-u64-be)
            :cases ((= q 0) (= q 1) (= q 2) (= q 3) (= q 4) (= q 5) (= q 6) (= q 7))))))

(local
 (defthm fn-shs-byte-of-ifix
   (equal (fn-sha256-byte (ifix x)) (fn-sha256-byte x))
   :hints (("Goal" :in-theory (enable fn-sha256-byte)))))

(local
 (defthm fn-shs-pb-is-nthx-of-pad
   (implies (and (natp i) (< i (fn-shs-pad-len (len msg))))
            (equal (fn-sha256-nthx i (fn-sha256-pad msg))
                   (fn-shs-pb i (len msg) msg)))
   :hints (("Goal" :in-theory (enable fn-sha256-pad fn-shs-pad-len fn-shs-pb fn-shs-tail-byte)
            :do-not-induct t))))

(local (in-theory (disable fn-shs-pb)))

; -----------------------------------------------------------------------------
; The two readers agree with `fn-shs-pb'.

(local
 (defthm fn-shs-str-byte-is-pb
   (implies (and (stringp s) (natp i) (equal n (length s)))
            (equal (fn-shs-str-byte i n s)
                   (fn-shs-pb i n (fn-shs-string-octets s))))
   :hints (("Goal" :in-theory (enable fn-shs-pb fn-shs-str-byte fn-shs-string-octets char)
            :use ((:instance fn-shs-nthx-is-nth (i i) (xs (coerce s 'list))))))))

(local
 (defthm fn-shs-list-byte-is-pb
   (implies (and (natp i) (equal n (len m)))
            (and (equal (car (fn-shs-list-byte i n (fn-sha256-nthcdrx i m)))
                        (fn-shs-pb i n (fn-sha256-fix-octets m)))
                 (equal (mv-nth 1 (fn-shs-list-byte i n (fn-sha256-nthcdrx i m)))
                        (fn-sha256-nthcdrx (+ 1 i) m))))
   :hints (("Goal" :in-theory (enable fn-shs-pb fn-shs-list-byte)
            :do-not-induct t))))

; -----------------------------------------------------------------------------
; The schedule.  W[t] as a function of t (the standard's recurrence), the
; reversed accumulator the list model keeps, and the in-order list.

(local
 (defun fn-shs-W (t0 ws16)
   (declare (xargs :measure (nfix t0)))
   (let ((t0 (nfix t0)))
     (if (< t0 16)
         (fn-sha256-nthx t0 ws16)
       (fn-shs-sched-word (fn-shs-W (- t0 2) ws16)
                          (fn-shs-W (- t0 7) ws16)
                          (fn-shs-W (- t0 15) ws16)
                          (fn-shs-W (- t0 16) ws16))))))

(local
 (defun fn-shs-Wr (m ws16)
   ; (W[m-1] ... W[0]): the accumulator `fn-sha256-schedule-aux' keeps.
   (if (zp m)
       nil
     (cons (fn-shs-W (- m 1) ws16) (fn-shs-Wr (- m 1) ws16)))))

(local
 (defun fn-shs-Wl (m ws16)
   ; (W[0] ... W[m-1]).
   (if (zp m)
       nil
     (append (fn-shs-Wl (- m 1) ws16) (list (fn-shs-W (- m 1) ws16))))))

(local
 (defthm fn-shs-len-of-Wl
   (equal (len (fn-shs-Wl m ws16)) (nfix m))))

(local
 (defthm fn-shs-true-listp-of-Wl
   (true-listp (fn-shs-Wl m ws16))))

(local
 (defun fn-shs-im-ind (i m)
   (if (or (zp i) (zp m)) (list i m) (fn-shs-im-ind (- i 1) (- m 1)))))

(local
 (defthm fn-shs-nthx-of-Wr
   (implies (and (natp i) (natp m) (< i m))
            (equal (fn-sha256-nthx i (fn-shs-Wr m ws16))
                   (fn-shs-W (- m (+ 1 i)) ws16)))
   :hints (("Goal" :induct (fn-shs-im-ind i m)
            :expand ((fn-shs-Wr m ws16))))))

(local
 (defthm fn-shs-nthx-of-Wl
   (implies (and (natp i) (natp m) (< i m))
            (equal (fn-sha256-nthx i (fn-shs-Wl m ws16))
                   (fn-shs-W i ws16)))
   :hints (("Goal" :induct (fn-shs-Wl m ws16)))))

(local
 (defun fn-shs-aux-ind (n m)
   (if (zp n) (list n m) (fn-shs-aux-ind (- n 1) (+ m 1)))))

(local
 (defthm fn-shs-schedule-aux-on-Wr
   (implies (and (natp n) (natp m) (<= 16 m))
            (equal (fn-sha256-schedule-aux n (fn-shs-Wr m ws16))
                   (fn-shs-Wr (+ m n) ws16)))
   :hints (("Goal" :induct (fn-shs-aux-ind n m)
            :in-theory (enable fn-sha256-schedule-aux)
            :expand ((fn-sha256-schedule-aux n (fn-shs-Wr m ws16))
                     (fn-shs-Wr (+ 1 m) ws16)
                     (fn-shs-W m ws16))))))

(local
 (defun fn-shs-revx-Wr-ind (m ws16 acc)
   ; The accumulator grows as the reversed list is walked.
   (if (zp m)
       (list m ws16 acc)
     (fn-shs-revx-Wr-ind (- m 1) ws16 (cons (fn-shs-W (- m 1) ws16) acc)))))

(local
 (defthm fn-shs-revx-of-Wr
   (equal (fn-sha256-revx (fn-shs-Wr m ws16) acc)
          (append (fn-shs-Wl m ws16) acc))
   :hints (("Goal" :induct (fn-shs-revx-Wr-ind m ws16 acc)
            :expand ((fn-shs-Wr m ws16) (fn-shs-Wl m ws16))))))

; `firstn-snoc' for a symbolic count, so the two inductions below see it
; at m without a :use (which an :induct hint cannot carry); withdrawn after.
(local
 (defthm fn-shs-firstn-snoc-var
   (implies (and (syntaxp (symbolp m)) (natp m) (< 0 m) (<= m (len xs)))
            (equal (fn-sha256-firstn m xs)
                   (append (fn-sha256-firstn (+ -1 m) xs)
                           (list (fn-sha256-nthx (+ -1 m) xs)))))
   :hints (("Goal" :use ((:instance fn-shs-firstn-snoc (j (+ -1 m))))))))

(local
 (defthm fn-shs-Wr-is-revx-of-firstn
   (implies (and (natp m) (<= m 16) (<= m (len ws16)))
            (equal (fn-shs-Wr m ws16)
                   (fn-sha256-revx (fn-sha256-firstn m ws16) nil)))
   :hints (("Goal" :induct (fn-shs-Wr m ws16)
            :expand ((fn-shs-W (+ -1 m) ws16))))))

(local
 (defthm fn-shs-revx-is-Wr-16
   (implies (and (true-listp ws16) (equal (len ws16) 16))
            (equal (fn-sha256-revx ws16 nil) (fn-shs-Wr 16 ws16)))
   :hints (("Goal" :use ((:instance fn-shs-Wr-is-revx-of-firstn (m 16)))
            :in-theory (disable fn-shs-Wr-is-revx-of-firstn fn-shs-Wr
                                fn-shs-firstn-snoc)))))

(local
 (defthm fn-shs-Wl-is-firstn
   (implies (and (natp m) (<= m 16) (<= m (len ws16)))
            (equal (fn-shs-Wl m ws16) (fn-sha256-firstn m ws16)))
   :hints (("Goal" :induct (fn-shs-Wl m ws16)
            :expand ((fn-shs-W (+ -1 m) ws16))))))

(local (in-theory (disable fn-shs-firstn-snoc-var)))

; Closed from here: on a constant count both unroll (16 and 64 times), and
; the schedule rule below matches the closed form.
(local (in-theory (disable (:d fn-shs-Wr) (:d fn-shs-Wl))))

(local
 (defthm fn-shs-schedule-is-Wl
   (implies (and (true-listp ws16) (equal (len ws16) 16))
            (equal (fn-sha256-schedule ws16) (fn-shs-Wl 64 ws16)))
   :hints (("Goal" :in-theory (e/d (fn-sha256-schedule) (fn-shs-Wr-is-revx-of-firstn))))))

; The sixteen words of a block, by index.
(local
 (defun fn-shs-w16-ind (j blk)
   (if (zp j) (list j blk) (fn-shs-w16-ind (- j 1) (fn-sha256-nthcdrx 4 blk)))))

(local
 (defthm fn-shs-nthx-of-words16
   (implies (and (natp j) (< (* 4 j) (len blk)))
            (equal (fn-sha256-nthx j (fn-sha256-words16 blk))
                   (fn-shs-be-word (fn-sha256-nthx (* 4 j) blk)
                                   (fn-sha256-nthx (+ 1 (* 4 j)) blk)
                                   (fn-sha256-nthx (+ 2 (* 4 j)) blk)
                                   (fn-sha256-nthx (+ 3 (* 4 j)) blk))))
   :hints (("Goal" :induct (fn-shs-w16-ind j blk)
            :in-theory (enable fn-sha256-words16)))))

(local
 (defun fn-shs-ceil4 (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) 0 (+ 1 (fn-shs-ceil4 (- n 4))))))

(local
 (defthm fn-shs-len-of-words16
   (equal (len (fn-sha256-words16 blk))
          (fn-shs-ceil4 (len blk)))
   :hints (("Goal" :in-theory (enable fn-sha256-words16)
            :induct (fn-sha256-words16 blk)
            :expand ((fn-shs-ceil4 (len blk)))))))

(local
 (defthm fn-shs-true-listp-of-words16
   (true-listp (fn-sha256-words16 blk))
   :hints (("Goal" :in-theory (enable fn-sha256-words16)))))

; The block the list model slices out at offset base, as words.
(local
 (defun fn-shs-block-words (base msg)
   (fn-sha256-words16
    (fn-sha256-firstn 64 (fn-sha256-nthcdrx base (fn-sha256-pad msg))))))

(local
 (defthm fn-shs-len-of-block-slice
   (implies (and (natp base) (<= (+ base 64) (fn-shs-pad-len (len msg))))
            (equal (len (fn-sha256-firstn 64 (fn-sha256-nthcdrx base (fn-sha256-pad msg)))) 64))))

(local
 (defthm fn-shs-nthx-of-block-words
   (implies (and (natp j) (< j 16) (natp base)
                 (<= (+ base 64) (fn-shs-pad-len (len msg))))
            (equal (fn-sha256-nthx j (fn-shs-block-words base msg))
                   (fn-shs-be-word (fn-shs-pb (+ base (* 4 j)) (len msg) msg)
                                   (fn-shs-pb (+ 1 base (* 4 j)) (len msg) msg)
                                   (fn-shs-pb (+ 2 base (* 4 j)) (len msg) msg)
                                   (fn-shs-pb (+ 3 base (* 4 j)) (len msg) msg))))))

(local
 (defthm fn-shs-len-of-block-words
   (implies (and (natp base) (<= (+ base 64) (fn-shs-pad-len (len msg))))
            (equal (len (fn-shs-block-words base msg)) 16))))

(local
 (defthm fn-shs-true-listp-of-block-words
   (true-listp (fn-shs-block-words base msg))))

(local (in-theory (disable fn-shs-block-words)))

; -----------------------------------------------------------------------------
; The loaders: W[0..15] are the block's words.  The invariant is a named
; predicate with a step lemma, so the induction never opens `firstn'.

(local
 (defun fn-shs-prefix-ok (j w bw)
   (equal (fn-sha256-firstn j w) (fn-sha256-firstn j bw))))

(local
 (defthm fn-shs-prefix-ok-step
   (implies (and (fn-shs-prefix-ok j w bw)
                 (natp j) (< j (len w)) (< j (len bw))
                 (equal v (fn-sha256-nthx j bw)))
            (fn-shs-prefix-ok (+ 1 j) (update-nth j v w) bw))))

(local
 (defthm fn-shs-prefix-ok-done
   (implies (and (fn-shs-prefix-ok 16 w bw) (true-listp bw) (equal (len bw) 16))
            (equal (fn-sha256-firstn 16 w) bw))))

(local
 (defthm fn-shs-prefix-ok-0
   (fn-shs-prefix-ok 0 w bw)))

(local (in-theory (disable fn-shs-prefix-ok)))

(local
 (defthm fn-shs-load-str-word-w
   (implies (and (stringp s) (equal n (length s)) (natp base) (natp j))
            (equal (nth 0 (fn-shs-load-str-word j base n s fn-shs))
                   (update-nth j
                               (fn-shs-be-word (fn-shs-pb (+ base (* 4 j)) n (fn-shs-string-octets s))
                                               (fn-shs-pb (+ 1 base (* 4 j)) n (fn-shs-string-octets s))
                                               (fn-shs-pb (+ 2 base (* 4 j)) n (fn-shs-string-octets s))
                                               (fn-shs-pb (+ 3 base (* 4 j)) n (fn-shs-string-octets s)))
                               (nth 0 fn-shs))))
   :hints (("Goal" :in-theory (enable fn-shs-load-str-word)))))

(local
 (defthm fn-shs-load-str-word-h
   (equal (nth 1 (fn-shs-load-str-word j base n s fn-shs))
          (nth 1 fn-shs))
   :hints (("Goal" :in-theory (enable fn-shs-load-str-word)))))

(local
 (defthm fn-shs-load-str-block-w
   (implies (and (stringp s) (equal n (length s)) (natp base) (natp j) (<= j 16)
                 (<= (+ base 64) (fn-shs-pad-len n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-prefix-ok j (nth 0 fn-shs) (fn-shs-block-words base (fn-shs-string-octets s))))
            (equal (fn-sha256-firstn 16 (nth 0 (fn-shs-load-str-block j base n s fn-shs)))
                   (fn-shs-block-words base (fn-shs-string-octets s))))
   :hints (("Goal" :induct (fn-shs-load-str-block j base n s fn-shs)
            :in-theory (enable fn-shs-load-str-block)))))

(local
 (defthm fn-shs-load-str-block-loads-words16
   (implies (and (stringp s) (equal n (length s)) (natp base)
                 (<= (+ base 64) (fn-shs-pad-len n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64))
            (equal (fn-sha256-firstn 16 (nth 0 (fn-shs-load-str-block 0 base n s fn-shs)))
                   (fn-shs-block-words base (fn-shs-string-octets s))))
   :hints (("Goal" :use ((:instance fn-shs-load-str-block-w (j 0)))
            :in-theory (disable fn-shs-load-str-block-w)))))

(local
 (defthm fn-shs-load-str-block-frame
   (and (equal (nth 1 (fn-shs-load-str-block j base n s fn-shs))
               (nth 1 fn-shs))
        (implies (and (true-listp (nth 0 fn-shs))
                      (equal (len (nth 0 fn-shs)) 64)
                      (natp j))
                 (and (true-listp (nth 0 (fn-shs-load-str-block j base n s fn-shs)))
                      (equal (len (nth 0 (fn-shs-load-str-block j base n s fn-shs))) 64))))
   :hints (("Goal" :induct (fn-shs-load-str-block j base n s fn-shs)
            :in-theory (enable fn-shs-load-str-block fn-shs-load-str-word)))))

; The rules about the list loaders carry the remaining list as the explicit
; term, so that the message is bound by the left-hand side; a hypothesis
; naming it would be a free variable once the goal has substituted it.
(local
 (defthm fn-shs-load-list-word-w
   (implies (and (equal n (len m)) (natp base) (natp j))
            (and (equal (nth 0 (mv-nth 1 (fn-shs-load-list-word j base n (fn-sha256-nthcdrx (+ base (* 4 j)) m) fn-shs)))
                        (update-nth j
                                    (fn-shs-be-word (fn-shs-pb (+ base (* 4 j)) n (fn-sha256-fix-octets m))
                                                    (fn-shs-pb (+ 1 base (* 4 j)) n (fn-sha256-fix-octets m))
                                                    (fn-shs-pb (+ 2 base (* 4 j)) n (fn-sha256-fix-octets m))
                                                    (fn-shs-pb (+ 3 base (* 4 j)) n (fn-sha256-fix-octets m)))
                                    (nth 0 fn-shs)))
                 (equal (car (fn-shs-load-list-word j base n (fn-sha256-nthcdrx (+ base (* 4 j)) m) fn-shs))
                        (fn-sha256-nthcdrx (+ 4 base (* 4 j)) m))))
   :hints (("Goal" :in-theory (enable fn-shs-load-list-word)))))

(local
 (defthm fn-shs-load-list-word-h
   (equal (nth 1 (mv-nth 1 (fn-shs-load-list-word j base n rest fn-shs)))
          (nth 1 fn-shs))
   :hints (("Goal" :in-theory (enable fn-shs-load-list-word)))))

(local
 (defthm fn-shs-load-list-block-w
   (implies (and (equal n (len m)) (natp base) (natp j) (<= j 16)
                 (<= (+ base 64) (fn-shs-pad-len n))
                 (equal rest (fn-sha256-nthcdrx (+ base (* 4 j)) m))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-prefix-ok j (nth 0 fn-shs) (fn-shs-block-words base (fn-sha256-fix-octets m))))
            (and (equal (fn-sha256-firstn 16 (nth 0 (mv-nth 1 (fn-shs-load-list-block j base n rest fn-shs))))
                        (fn-shs-block-words base (fn-sha256-fix-octets m)))
                 (equal (car (fn-shs-load-list-block j base n rest fn-shs))
                        (fn-sha256-nthcdrx (+ base 64) m))))
   :hints (("Goal" :induct (fn-shs-load-list-block j base n rest fn-shs)
            :in-theory (enable fn-shs-load-list-block)))))

(local
 (defthm fn-shs-load-list-block-loads-words16
   (implies (and (equal n (len m)) (natp base)
                 (<= (+ base 64) (fn-shs-pad-len n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64))
            (and (equal (fn-sha256-firstn 16 (nth 0 (mv-nth 1 (fn-shs-load-list-block 0 base n (fn-sha256-nthcdrx base m) fn-shs))))
                        (fn-shs-block-words base (fn-sha256-fix-octets m)))
                 (equal (car (fn-shs-load-list-block 0 base n (fn-sha256-nthcdrx base m) fn-shs))
                        (fn-sha256-nthcdrx (+ base 64) m))))
   :hints (("Goal" :use ((:instance fn-shs-load-list-block-w (j 0) (rest (fn-sha256-nthcdrx base m))))
            :in-theory (disable fn-shs-load-list-block-w)))))

(local
 (defthm fn-shs-load-list-block-frame
   (and (equal (nth 1 (mv-nth 1 (fn-shs-load-list-block j base n rest fn-shs)))
               (nth 1 fn-shs))
        (implies (and (true-listp (nth 0 fn-shs))
                      (equal (len (nth 0 fn-shs)) 64)
                      (natp j))
                 (and (true-listp (nth 0 (mv-nth 1 (fn-shs-load-list-block j base n rest fn-shs))))
                      (equal (len (nth 0 (mv-nth 1 (fn-shs-load-list-block j base n rest fn-shs)))) 64))))
   :hints (("Goal" :induct (fn-shs-load-list-block j base n rest fn-shs)
            :in-theory (enable fn-shs-load-list-block fn-shs-load-list-word)))))

; -----------------------------------------------------------------------------
; Extend: W[0..t-1] agree with the recurrence, so W[0..63] do.

(local
 (defun fn-shs-W-ok (t0 w ws16)
   (equal (fn-sha256-firstn t0 w) (fn-shs-Wl t0 ws16))))

(local
 (defthm fn-shs-W-ok-read
   (implies (and (fn-shs-W-ok t0 w ws16) (natp i) (natp t0) (< i t0))
            (equal (fn-sha256-nthx i w) (fn-shs-W i ws16)))
   :hints (("Goal" :use ((:instance fn-shs-nthx-of-firstn (i i) (n t0) (xs w)))
            :in-theory (disable fn-shs-nthx-of-firstn)))))

(local
 (defthm fn-shs-W-ok-step
   (implies (and (fn-shs-W-ok t0 w ws16) (natp t0) (< t0 (len w))
                 (equal v (fn-shs-W t0 ws16)))
            (fn-shs-W-ok (+ 1 t0) (update-nth t0 v w) ws16))
   :hints (("Goal" :expand ((fn-shs-Wl (+ 1 t0) ws16))))))

(local
 (defthm fn-shs-W-ok-done
   (implies (and (fn-shs-W-ok 64 w ws16) (true-listp w) (equal (len w) 64))
            (equal (equal w (fn-shs-Wl 64 ws16)) t))))

(local
 (defthm fn-shs-W-ok-16
   (implies (and (true-listp ws16) (equal (len ws16) 16)
                 (equal (fn-sha256-firstn 16 w) ws16))
            (fn-shs-W-ok 16 w ws16))))

(local (in-theory (disable fn-shs-W-ok)))

(local
 (defthm fn-shs-extend-w
   (implies (and (natp t0) (<= 16 t0) (<= t0 64)
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-W-ok t0 (nth 0 fn-shs) ws16))
            (equal (nth 0 (fn-shs-extend t0 fn-shs))
                   (fn-shs-Wl 64 ws16)))
   :hints (("Goal" :induct (fn-shs-extend t0 fn-shs)
            :in-theory (enable fn-shs-extend)
            :expand ((fn-shs-W t0 ws16))))))

(local
 (defthm fn-shs-extend-shape
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (natp t0))
            (and (true-listp (nth 0 (fn-shs-extend t0 fn-shs)))
                 (equal (len (nth 0 (fn-shs-extend t0 fn-shs))) 64)))
   :hints (("Goal" :induct (fn-shs-extend t0 fn-shs)
            :in-theory (enable fn-shs-extend)))))

(local
 (defthm fn-shs-extend-yields-schedule
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp ws16)
                 (equal (len ws16) 16)
                 (equal (fn-sha256-firstn 16 (nth 0 fn-shs)) ws16))
            (equal (nth 0 (fn-shs-extend 16 fn-shs))
                   (fn-sha256-schedule ws16)))
   :hints (("Goal" :use ((:instance fn-shs-extend-w (t0 16)))
            :in-theory (disable fn-shs-extend-w)))))

; -----------------------------------------------------------------------------
; Rounds: the stobj rounds from i are the list rounds over W[i..63].

(local
 (defthm fn-shs-rounds-is-rounds
   (implies (and (natp i) (<= i 64)
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64))
            (equal (fn-shs-rounds i ks a b c d e f g h fn-shs)
                   (fn-sha256-rounds (fn-sha256-nthcdrx i (nth 0 fn-shs))
                                     ks a b c d e f g h)))
   :hints (("Goal" :induct (fn-shs-rounds i ks a b c d e f g h fn-shs)
            :in-theory (enable fn-shs-rounds fn-sha256-rounds)
            :expand ((fn-sha256-rounds (fn-sha256-nthcdrx i (nth 0 fn-shs))
                                       ks a b c d e f g h))))))

; H += registers is `fn-sha256-add8', given registers for every remaining
; word: on a short list the stobj keeps the rest of H and `add8' drops it.
(local
 (defthm fn-shs-h-add-h
   (implies (and (natp i) (<= i 8)
                 (<= (- 8 i) (len regs))
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (equal (nth 1 (fn-shs-h-add i regs fn-shs))
                   (append (fn-sha256-firstn i (nth 1 fn-shs))
                           (fn-sha256-add8 (fn-sha256-nthcdrx i (nth 1 fn-shs)) regs))))
   :hints (("Goal" :induct (fn-shs-h-add i regs fn-shs)
            :in-theory (enable fn-shs-h-add fn-sha256-add8)))))

(local
 (defthm fn-shs-h-add-frame
   (and (equal (nth 0 (fn-shs-h-add i regs fn-shs))
               (nth 0 fn-shs))
        (implies (and (true-listp (nth 1 fn-shs))
                      (equal (len (nth 1 fn-shs)) 8)
                      (natp i))
                 (and (true-listp (nth 1 (fn-shs-h-add i regs fn-shs)))
                      (equal (len (nth 1 (fn-shs-h-add i regs fn-shs))) 8))))
   :hints (("Goal" :induct (fn-shs-h-add i regs fn-shs)
            :in-theory (enable fn-shs-h-add)))))

; -----------------------------------------------------------------------------
; One block, and all blocks.

(local
 (defthm fn-shs-true-listp-of-rounds
   (true-listp (fn-sha256-rounds ws ks a b c d e f g h))
   :hints (("Goal" :in-theory (enable fn-sha256-rounds)))))

(local
 (defthm fn-shs-compress-loaded-is-compress
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8)
                 (equal (len blk) 64)
                 (equal (fn-sha256-firstn 16 (nth 0 fn-shs))
                        (fn-sha256-words16 blk)))
            (equal (nth 1 (fn-shs-compress-loaded fn-shs))
                   (fn-sha256-compress blk (nth 1 fn-shs))))
   :hints (("Goal" :in-theory (enable fn-shs-compress-loaded fn-sha256-compress)
            :use ((:instance fn-shs-extend-yields-schedule (ws16 (fn-sha256-words16 blk))))))))

(local
 (defthm fn-shs-compress-loaded-frame
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (and (true-listp (nth 0 (fn-shs-compress-loaded fn-shs)))
                 (equal (len (nth 0 (fn-shs-compress-loaded fn-shs))) 64)
                 (true-listp (nth 1 (fn-shs-compress-loaded fn-shs)))
                 (equal (len (nth 1 (fn-shs-compress-loaded fn-shs))) 8)))
   :hints (("Goal" :in-theory (enable fn-shs-compress-loaded)))))

(local
 (defthm fn-shs-compress-str-is-compress
   (implies (and (stringp s) (equal n (length s)) (natp b)
                 (< b (fn-shs-nblocks n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (equal (nth 1 (fn-shs-compress-str b n s fn-shs))
                   (fn-sha256-compress
                    (fn-sha256-firstn 64 (fn-sha256-nthcdrx (* 64 b) (fn-sha256-pad (fn-shs-string-octets s))))
                    (nth 1 fn-shs))))
   :hints (("Goal" :in-theory (enable fn-shs-compress-str fn-shs-block-words)
            :use ((:instance fn-shs-compress-loaded-is-compress
                             (fn-shs (fn-shs-load-str-block 0 (* 64 b) n s fn-shs))
                             (blk (fn-sha256-firstn 64 (fn-sha256-nthcdrx (* 64 b) (fn-sha256-pad (fn-shs-string-octets s)))))))))))

(local
 (defthm fn-shs-compress-list-is-compress
   (implies (and (equal n (len m)) (natp b)
                 (< b (fn-shs-nblocks n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (and (equal (nth 1 (mv-nth 1 (fn-shs-compress-list b n (fn-sha256-nthcdrx (* 64 b) m) fn-shs)))
                        (fn-sha256-compress
                         (fn-sha256-firstn 64 (fn-sha256-nthcdrx (* 64 b) (fn-sha256-pad (fn-sha256-fix-octets m))))
                         (nth 1 fn-shs)))
                 (equal (car (fn-shs-compress-list b n (fn-sha256-nthcdrx (* 64 b) m) fn-shs))
                        (fn-sha256-nthcdrx (+ 64 (* 64 b)) m))))
   :hints (("Goal" :in-theory (enable fn-shs-compress-list fn-shs-block-words)
            :use ((:instance fn-shs-compress-loaded-is-compress
                             (fn-shs (mv-nth 1 (fn-shs-load-list-block 0 (* 64 b) n (fn-sha256-nthcdrx (* 64 b) m) fn-shs)))
                             (blk (fn-sha256-firstn 64 (fn-sha256-nthcdrx (* 64 b) (fn-sha256-pad (fn-sha256-fix-octets m)))))))))))

(local
 (defthm fn-shs-compress-str-frame
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (and (true-listp (nth 0 (fn-shs-compress-str b n s fn-shs)))
                 (equal (len (nth 0 (fn-shs-compress-str b n s fn-shs))) 64)
                 (true-listp (nth 1 (fn-shs-compress-str b n s fn-shs)))
                 (equal (len (nth 1 (fn-shs-compress-str b n s fn-shs))) 8)))
   :hints (("Goal" :in-theory (enable fn-shs-compress-str)))))

(local
 (defthm fn-shs-compress-list-frame
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (and (true-listp (nth 0 (mv-nth 1 (fn-shs-compress-list b n rest fn-shs))))
                 (equal (len (nth 0 (mv-nth 1 (fn-shs-compress-list b n rest fn-shs)))) 64)
                 (true-listp (nth 1 (mv-nth 1 (fn-shs-compress-list b n rest fn-shs))))
                 (equal (len (nth 1 (mv-nth 1 (fn-shs-compress-list b n rest fn-shs)))) 8)))
   :hints (("Goal" :in-theory (enable fn-shs-compress-list)))))

; The shape of the model's compressed state (sha256's own version is local).
(local
 (defthm fn-shs-true-listp-of-add8
   (true-listp (fn-sha256-add8 xs ys))
   :hints (("Goal" :in-theory (enable fn-sha256-add8)))))

(local
 (defthm fn-shs-len-of-compress
   (implies (equal (len hs) 8)
            (equal (len (fn-sha256-compress blk hs)) 8))
   :hints (("Goal" :in-theory (enable fn-sha256-compress)))))

(local
 (defthm fn-shs-true-listp-of-compress
   (true-listp (fn-sha256-compress blk hs))
   :hints (("Goal" :in-theory (enable fn-sha256-compress)))))

; The model's block loop, opened by rule: a sliced tail that is empty is
; the state, and one that is not is one block and the rest.  Restricted to
; a sliced tail so the whole padded message is never unrolled.
(local
 (defthm fn-shs-blocks-of-atom
   (implies (not (consp p))
            (equal (fn-sha256-blocks p hs) hs))
   :hints (("Goal" :in-theory (enable fn-sha256-blocks)))))

(local
 (defthm fn-shs-blocks-of-consp
   (implies (and (syntaxp (and (consp p) (eq (car p) 'fn-sha256-nthcdrx)))
                 (consp p))
            (equal (fn-sha256-blocks p hs)
                   (fn-sha256-blocks (fn-sha256-nthcdrx 64 p)
                                     (fn-sha256-compress (fn-sha256-firstn 64 p) hs))))
   :hints (("Goal" :in-theory (enable fn-sha256-blocks)))))

(local
 (defthm fn-shs-blocks-str-is-blocks
   (implies (and (stringp s) (equal n (length s)) (natp b) (natp nb) (<= b nb)
                 (equal nb (fn-shs-nblocks n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (equal (nth 1 (fn-shs-blocks-str b nb n s fn-shs))
                   (fn-sha256-blocks
                    (fn-sha256-nthcdrx (* 64 b) (fn-sha256-pad (fn-shs-string-octets s)))
                    (nth 1 fn-shs))))
   :hints (("Goal" :induct (fn-shs-blocks-str b nb n s fn-shs)
            :in-theory (enable fn-shs-blocks-str)))))

(local
 (defthm fn-shs-blocks-list-is-blocks-aux
   (implies (and (equal n (len m)) (natp b) (natp nb) (<= b nb)
                 (equal nb (fn-shs-nblocks n))
                 (equal rest (fn-sha256-nthcdrx (* 64 b) m))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (equal (nth 1 (fn-shs-blocks-list b nb n rest fn-shs))
                   (fn-sha256-blocks
                    (fn-sha256-nthcdrx (* 64 b) (fn-sha256-pad (fn-sha256-fix-octets m)))
                    (nth 1 fn-shs))))
   :hints (("Goal" :induct (fn-shs-blocks-list b nb n rest fn-shs)
            :in-theory (enable fn-shs-blocks-list)))))

; From the start of the message, as the digest calls it.
(local
 (defthm fn-shs-blocks-list-is-blocks
   (implies (and (equal n (len m)) (natp nb)
                 (equal nb (fn-shs-nblocks n))
                 (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (equal (nth 1 (fn-shs-blocks-list 0 nb n m fn-shs))
                   (fn-sha256-blocks (fn-sha256-pad (fn-sha256-fix-octets m))
                                     (nth 1 fn-shs))))
   :hints (("Goal" :use ((:instance fn-shs-blocks-list-is-blocks-aux (b 0) (rest m)))))))

(local
 (defthm fn-shs-blocks-str-frame
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (and (true-listp (nth 1 (fn-shs-blocks-str b nb n s fn-shs)))
                 (equal (len (nth 1 (fn-shs-blocks-str b nb n s fn-shs))) 8)))
   :hints (("Goal" :induct (fn-shs-blocks-str b nb n s fn-shs)
            :in-theory (enable fn-shs-blocks-str)))))

(local
 (defthm fn-shs-blocks-list-frame
   (implies (and (true-listp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (and (true-listp (nth 1 (fn-shs-blocks-list b nb n rest fn-shs)))
                 (equal (len (nth 1 (fn-shs-blocks-list b nb n rest fn-shs))) 8)))
   :hints (("Goal" :induct (fn-shs-blocks-list b nb n rest fn-shs)
            :in-theory (enable fn-shs-blocks-list)))))

; -----------------------------------------------------------------------------
; The state in and the octets out.

(local
 (defthm fn-shs-h-init-h
   (implies (and (natp i) (<= i 8)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8)
                 (true-listp hs)
                 (equal (len hs) (- 8 i)))
            (equal (nth 1 (fn-shs-h-init i hs fn-shs))
                   (append (fn-sha256-firstn i (nth 1 fn-shs)) hs)))
   :hints (("Goal" :induct (fn-shs-h-init i hs fn-shs)
            :in-theory (enable fn-shs-h-init)))))

(local
 (defthm fn-shs-h-init-frame
   (equal (nth 0 (fn-shs-h-init i hs fn-shs))
          (nth 0 fn-shs))
   :hints (("Goal" :in-theory (enable fn-shs-h-init)))))

(local
 (defthm fn-shs-h-octets-is-words-octets
   (implies (and (natp i) (<= i 8)
                 (true-listp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))
            (equal (fn-shs-h-octets i fn-shs)
                   (fn-sha256-words-octets (fn-sha256-nthcdrx i (nth 1 fn-shs)))))
   :hints (("Goal" :induct (fn-shs-h-octets i fn-shs)
            :in-theory (enable fn-shs-h-octets fn-sha256-words-octets)
            :expand ((fn-sha256-words-octets
                      (fn-sha256-nthcdrx i (nth 1 fn-shs))))))))

; -----------------------------------------------------------------------------
; The digests.

(local
 (defthm fn-shs-len-of-blocks
   (implies (equal (len hs) 8)
            (equal (len (fn-sha256-blocks p hs)) 8))
   :hints (("Goal" :in-theory (enable fn-sha256-blocks fn-sha256-compress)))))

(local
 (defthm fn-shs-true-listp-of-blocks
   (implies (true-listp hs)
            (true-listp (fn-sha256-blocks p hs)))
   :hints (("Goal" :in-theory (enable fn-sha256-blocks fn-sha256-compress)))))

(local
 (defthm fn-shs-create-shape
   (and (true-listp (nth 0 (create-fn-shs)))
        (equal (len (nth 0 (create-fn-shs))) 64)
        (true-listp (nth 1 (create-fn-shs)))
        (equal (len (nth 1 (create-fn-shs))) 8))))

(local
 (defthm fn-shs-digest-list-is-of-octets-of-fix
   (equal (car (fn-shs-digest-list m (create-fn-shs)))
          (fn-sha256-of-octets (fn-sha256-fix-octets m)))
   :hints (("Goal" :in-theory (enable fn-sha256-of-octets)))))

(local
 (defthm fn-shs-digest-str-is-of-octets
   (implies (stringp s)
            (equal (car (fn-shs-digest-str s (create-fn-shs)))
                   (fn-sha256-of-octets (fn-shs-string-octets s))))
   :hints (("Goal" :in-theory (enable fn-sha256-of-octets)))))

(local (in-theory (disable fn-shs-digest-list fn-shs-digest-str)))

; The creator stays a term in the two proofs below (its executable
; counterpart would turn it into the concrete arrays before the digest rules,
; stated over the creator, can match).
(defthm fn-sha256-stobj-is-sha256
  ; The keystone: the stobj computation is the list model on every object.
  (equal (fn-sha256-stobj m) (fn-sha256 m))
  :hints (("Goal" :in-theory (e/d (fn-sha256) ((:e create-fn-shs) (:d create-fn-shs))))))

(defthm fn-sha256-stobj-is-sha256-of-octets
  ; Its instance on the domain fn digests.
  (implies (fn-sha256-octet-listp m)
           (equal (fn-sha256-stobj m) (fn-sha256-of-octets m)))
  :rule-classes nil
  :hints (("Goal" :use fn-sha256-is-of-octets-on-octets)))

(defthm fn-sha256-of-string-is-sha256-of-octets
  ; The string entry digests the string's character codes.
  (implies (stringp s)
           (equal (fn-sha256-of-string s)
                  (fn-sha256-of-octets (fn-shs-string-octets s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable (:e create-fn-shs) (:d create-fn-shs)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  The stobj functions are the
; executable path and nothing else's proof vocabulary; what leaves is the
; correspondence.  Only `:definition' runes are withdrawn.

(deftheory fn-shs-internals
  '((:d fn-shs-add$inline) (:d fn-shs-rotr$inline) (:d fn-shs-shr$inline)
    (:d fn-shs-ch$inline) (:d fn-shs-maj$inline)
    (:d fn-shs-bsig0$inline) (:d fn-shs-bsig1$inline)
    (:d fn-shs-ssig0$inline) (:d fn-shs-ssig1$inline)
    (:d fn-shs-t1$inline) (:d fn-shs-t2$inline) (:d fn-shs-sched-word$inline)
    (:d fn-shs-be-word$inline) (:d fn-shs-word-byte$inline)
    (:d fn-shs-len-byte$inline) (:d fn-shs-octet$inline)
    (:d fn-shs-word-listp) (:d fn-shs-pad-len) (:d fn-shs-nblocks)
    (:d fn-shs-tail-byte) (:d fn-shs-pb)
    (:d fn-shs-str-byte) (:d fn-shs-list-byte)
    (:d fn-shs-load-str-word) (:d fn-shs-load-str-block)
    (:d fn-shs-load-list-word) (:d fn-shs-load-list-block)
    (:d fn-shs-extend) (:d fn-shs-rounds) (:d fn-shs-h-add)
    (:d fn-shs-compress-loaded) (:d fn-shs-compress-str) (:d fn-shs-compress-list)
    (:d fn-shs-blocks-str) (:d fn-shs-blocks-list)
    (:d fn-shs-h-init) (:d fn-shs-h-octets)
    (:d fn-shs-digest-list) (:d fn-shs-digest-str)
    (:d fn-sha256-stobj) (:d fn-sha256-of-string)
    (:d fn-shs-char-octets) (:d fn-shs-string-octets)))

(in-theory (disable fn-shs-internals))
