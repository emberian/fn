;; fn: the page store's word digest is SHA-256 (lane arena-store,
;; 2026-09-27; the SHA part of A-PGS-OBSERVE).  Prefix pgs-.
;;
;; What is proved.  `pgs-x-words-digest-is-sha256' (the keystone): the
;; digest the host calls, `pgs-x-words-digest' (books/proto/pagestore-words;
;; host/native/proto-pagestore.lisp calls it for the table check, the table
;; commit and the image digest), is `fn-sha256' of the octets of the 8*NB
;; words from BASE of the array SEL names, each word least significant octet
;; first (`pgs-words-le-octets'), read as a big-endian natural
;; (`pgs-octets-be-nat').  Its hypotheses are the word stobj's recognizer
;; and naturals BASE and NB.  It needs no `pgs-memp', no bound on NB and no
;; bound on BASE + 8*NB: past the array's end both sides read zero words
;; (`nth' and `take' give NIL, whose octets are zero), and the bit count's
;; 64-bit field is the same octets on both sides for every NB.  The
;; incoming `fn-shs' matters only through its shape: H is initialised and
;; each block loads all sixteen schedule words before the compression reads
;; them.
;;
;; How.  The page digest drives books/sha256-stobj.lisp's compression
;; (`fn-shs-compress-loaded') with its own loaders, so the proof is that
;; book's block correspondence (`fn-shs-compress-loaded-is-compress',
;; restated here with its local lemmas, since that book keeps them local)
;; applied to the page loaders: a block of eight words loads the list
;; model's sixteen words (`pgs-load-block-loads', `pgs-words16-of-octets'),
;; the padding block loads the model's final block (`pgs-pad-block-w',
;; `pgs-words16-of-pad-tail'), the block loop is the model's
;; (`pgs-blocks-h', `pgs-blocks-of-octets'), and the H words read as a
;; natural are the digest's octets read as one (`pgs-h-nat-is-be-nat').
;; The octet arithmetic (a 32-bit half's octets are the word's, and the
;; length field's octets reassemble to its halves) is proved under
;; arithmetic-5 in a scope of its own.
;;
;; Ground witness: `pgs-x-words-digest-witness' evaluates the host function
;; on a concrete stobj whose words hold the octets 00..3f and gets the
;; standard SHA-256 of those 64 octets.
(in-package "ACL2")
(include-book "pagestore-words")

; -----------------------------------------------------------------------------
; The specification's vocabulary: plain list functions.

(defun-nx pgs-x-arr (sel pgs-mem)
  ; The value of the word array SEL names (as `pgs-x-len' and `pgs-x-word').
  (case sel
    (1 (nth *pgs-mi* pgs-mem))
    (2 (nth *pgs-ti* pgs-mem))
    (otherwise (nth *pgs-wi* pgs-mem))))

(defun pgs-word-le-octets (w)
  ; The eight octets of a 64-bit word, least significant first.
  (declare (xargs :guard t))
  (list (fn-sha256-byte w) (fn-sha256-byte (ash (ifix w) -8))
        (fn-sha256-byte (ash (ifix w) -16)) (fn-sha256-byte (ash (ifix w) -24))
        (fn-sha256-byte (ash (ifix w) -32)) (fn-sha256-byte (ash (ifix w) -40))
        (fn-sha256-byte (ash (ifix w) -48)) (fn-sha256-byte (ash (ifix w) -56))))

(defun pgs-words-le-octets (ws)
  ; The octets of a list of words, each word little-endian, in list order.
  (declare (xargs :guard t))
  (if (consp ws)
      (append (pgs-word-le-octets (car ws)) (pgs-words-le-octets (cdr ws)))
    nil))

(defun pgs-octets-be-nat-acc (os acc)
  (declare (xargs :guard (natp acc)))
  (if (consp os)
      (pgs-octets-be-nat-acc (cdr os) (+ (* 256 (nfix acc)) (nfix (car os))))
    (nfix acc)))

(defun pgs-octets-be-nat (os)
  ; The natural whose big-endian octets OS are.
  (declare (xargs :guard t))
  (pgs-octets-be-nat-acc os 0))

; -----------------------------------------------------------------------------
; Octet arithmetic, under arithmetic-5 in a scope of its own: the words'
; octets are the halves' octets (`pgs-sw-of-lo32', `-hi32'), the length
; words are their octets reassembled (`pgs-lo32-is-be-word', `-hi32-'),
; and a word's four octets accumulate to the word (`pgs-be-acc-word').

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))

   ; The padding's zero count for a whole number of blocks (arithmetic-5
   ; alone loops on this goal; the two steps below do not).
   (local (defthm mod-64-plus
     (implies (and (integerp a) (integerp b) (<= 0 b) (< b 64))
              (equal (mod (+ (* 64 a) b) 64) b))))

   (local (defthm neg-shape (equal (- 55 (* 64 k)) (+ (* 64 (- k)) 55)) :rule-classes nil))

   (defthm pgs-mod-55
     (implies (integerp k) (equal (mod (- 55 (* 64 k)) 64) 55))
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e <) (:e integerp)))
              :use (neg-shape (:instance mod-64-plus (a (- k)) (b 55))))))

   (local (defthm mod-split-256
     (implies (and (integerp x) (posp m))
              (equal (mod x (* 256 m))
                     (+ (* 256 (mod (floor x 256) m)) (mod x 256))))
     :rule-classes nil))

   (local (defthm mod-split-k
     (implies (and (integerp x) (posp m) (equal k (* 256 m)))
              (equal (mod x k)
                     (+ (* 256 (mod (floor x 256) m)) (mod x 256))))
     :rule-classes nil
     :hints (("Goal" :use mod-split-256))))

   (local (defthm floor-floor-k
     (implies (and (integerp x) (posp a) (posp b) (equal k (* a b)))
              (equal (floor (floor x a) b) (floor x k)))
     :rule-classes nil))

   (local (defthm floor-256-lin
     (implies (and (integerp a) (integerp b) (<= 0 b) (< b 256))
              (and (equal (floor (+ (* 256 a) b) 256) a)
                   (equal (mod (+ (* 256 a) b) 256) b)))))

   (local (defthm mod-256-bounds
     (implies (integerp x) (and (integerp (mod x 256)) (<= 0 (mod x 256)) (< (mod x 256) 256)))
     :rule-classes nil))

   (local (defthm int-floor-mod
     (implies (and (integerp x) (integerp y)) (and (integerp (floor x y)) (integerp (mod x y))))
     :rule-classes nil))

   (local (defthm p1p2
     (implies (and (integerp x) (posp m) (equal k (* 256 m)))
              (and (equal (floor (mod x k) 256) (mod (floor x 256) m))
                   (equal (mod (mod x k) 256) (mod x 256))))
     :rule-classes nil
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                '(floor-256-lin (:e posp) posp))
              :use ((:instance mod-split-k) (:instance mod-256-bounds)
                    (:instance int-floor-mod (x (floor x 256)) (y m))
                    (:instance int-floor-mod (x x) (y 256)))))))

   (local (defthm reassemble-32
     (implies (integerp x)
              (equal (+ (* 16777216 (mod (floor x 16777216) 256)) (* 65536 (mod (floor x 65536) 256))
                        (* 256 (mod (floor x 256) 256)) (mod x 256))
                     (mod x 4294967296)))
     :rule-classes nil
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp) (:t floor) (:t mod)))
              :use ((:instance mod-split-k (x x) (m 16777216) (k 4294967296))
                    (:instance mod-split-k (x (floor x 256)) (m 65536) (k 16777216))
                    (:instance mod-split-k (x (floor x 65536)) (m 256) (k 65536))
                    (:instance floor-floor-k (x x) (a 256) (b 256) (k 65536))
                    (:instance floor-floor-k (x x) (a 65536) (b 256) (k 16777216)))))))

   (local (defthm ash-m8 (equal (ash x -8) (floor (ifix x) 256))))
   (local (defthm ash-m16 (equal (ash x -16) (floor (ifix x) 65536))))
   (local (defthm ash-m24 (equal (ash x -24) (floor (ifix x) 16777216))))
   (local (defthm ash-m32 (equal (ash x -32) (floor (ifix x) 4294967296))))
   (local (defthm ash-m40 (equal (ash x -40) (floor (ifix x) 1099511627776))))
   (local (defthm ash-m48 (equal (ash x -48) (floor (ifix x) 281474976710656))))
   (local (defthm ash-m56 (equal (ash x -56) (floor (ifix x) 72057594037927936))))

   (local (defthm int-of-floor-mod
     (implies (and (integerp x) (integerp y)) (and (integerp (floor x y)) (integerp (mod x y))))))

   (local (defthm fm-1
     (implies (integerp x) (equal (floor (mod x 4294967296) 256) (mod (floor x 256) 16777216)))
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp)))
              :use ((:instance p1p2 (x x) (m 16777216) (k 4294967296)))))))

   (local (defthm fm-2
     (implies (integerp x) (equal (floor (mod x 4294967296) 65536) (mod (floor x 65536) 65536)))
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp) fm-1 int-of-floor-mod))
              :use ((:instance floor-floor-k (x (mod x 4294967296)) (a 256) (b 256) (k 65536))
                    (:instance floor-floor-k (x x) (a 256) (b 256) (k 65536))
                    (:instance p1p2 (x (floor x 256)) (m 65536) (k 16777216)))))))

   (local (defthm fm-3
     (implies (integerp x) (equal (floor (mod x 4294967296) 16777216) (mod (floor x 16777216) 256)))
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp) fm-2 int-of-floor-mod))
              :use ((:instance floor-floor-k (x (mod x 4294967296)) (a 65536) (b 256) (k 16777216))
                    (:instance floor-floor-k (x x) (a 65536) (b 256) (k 16777216))
                    (:instance p1p2 (x (floor x 65536)) (m 256) (k 65536)))))))

   (local (defthm mm-256
     (implies (and (integerp x) (member-equal m '(256 65536 16777216 4294967296)))
              (equal (mod (mod x m) 256) (mod x 256)))
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp) member-equal (:e member-equal)))
              :use ((:instance p1p2 (x x) (m 1) (k 256))
                    (:instance p1p2 (x x) (m 256) (k 65536))
                    (:instance p1p2 (x x) (m 65536) (k 16777216))
                    (:instance p1p2 (x x) (m 16777216) (k 4294967296)))))))

   (local (defthm ff-32
     (implies (integerp x)
              (and (equal (floor (floor x 4294967296) 256) (floor x 1099511627776))
                   (equal (floor (floor x 4294967296) 65536) (floor x 281474976710656))
                   (equal (floor (floor x 4294967296) 16777216) (floor x 72057594037927936))))
     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp)))
              :use ((:instance floor-floor-k (x x) (a 4294967296) (b 256) (k 1099511627776))
                    (:instance floor-floor-k (x x) (a 4294967296) (b 65536) (k 281474976710656))
                    (:instance floor-floor-k (x x) (a 4294967296) (b 16777216) (k 72057594037927936)))))))

   (local (defthm floor-by-1 (implies (integerp x) (equal (floor x 1) x))))

   (local (deftheory byte-theory
     (union-theories (theory 'minimal-theory)
                     '((:e posp) ash-m8 ash-m16 ash-m24 ash-m32 ash-m40 ash-m48 ash-m56
                       int-of-floor-mod fm-1 fm-2 fm-3 mm-256 ff-32 floor-by-1 (:t floor)
                       ifix fn-sha256-byte pgs-sw$inline pgs-lo32$inline pgs-hi32$inline
                       (:e member-equal)))))

   (defthm pgs-sw-of-lo32
     (equal (pgs-sw (pgs-lo32 w))
            (fn-shs-be-word (fn-sha256-byte w) (fn-sha256-byte (ash (ifix w) -8))
                            (fn-sha256-byte (ash (ifix w) -16)) (fn-sha256-byte (ash (ifix w) -24))))
     :hints (("Goal" :in-theory (theory 'byte-theory))))

   (defthm pgs-sw-of-hi32
     (equal (pgs-sw (pgs-hi32 w))
            (fn-shs-be-word (fn-sha256-byte (ash (ifix w) -32)) (fn-sha256-byte (ash (ifix w) -40))
                            (fn-sha256-byte (ash (ifix w) -48)) (fn-sha256-byte (ash (ifix w) -56))))
     :hints (("Goal" :in-theory (theory 'byte-theory))))


   ; `logior' of disjoint bit ranges is the sum.
   (local (defun ind-k (k c) (if (zp k) c (ind-k (1- k) (floor c 2)))))

   (local (defthm half-eq
     (implies (and (acl2-numberp x) (acl2-numberp y))
              (equal (equal (* 1/2 x) y) (equal x (* 2 y))))))

   (local (defthm logior-fm
     (implies (and (integerp x) (integerp y))
              (equal (logior x y) (+ (* 2 (floor (logior x y) 2)) (mod (logior x y) 2))))
     :rule-classes nil))

   (local (defthm logior-disjoint
     (implies (and (natp a) (natp c) (natp k) (< c (expt 2 k)))
              (equal (logior (* a (expt 2 k)) c) (+ (* a (expt 2 k)) c)))
     :rule-classes nil
     :hints (("Goal" :induct (ind-k k c))
             ("Subgoal *1/2" :use ((:instance logior-fm (x c) (y (* a (expt 2 k))))
                                   (:instance |(logior (floor x 2) (floor y 2))| (x c) (y (* a (expt 2 k)))))))))

   (local (defthm be-word-plus
     (equal (fn-shs-be-word b0 b1 b2 b3)
            (fn-sha256-w32 (+ (* 16777216 (fn-sha256-byte b0)) (* 65536 (fn-sha256-byte b1))
                              (* 256 (fn-sha256-byte b2)) (fn-sha256-byte b3))))
     :hints (("Goal" :in-theory (enable fn-shs-be-word$inline)
              :use ((:instance logior-disjoint (a (fn-sha256-byte b2)) (k 8) (c (fn-sha256-byte b3)))
                    (:instance logior-disjoint (a (fn-sha256-byte b1)) (k 16)
                               (c (+ (* 256 (fn-sha256-byte b2)) (fn-sha256-byte b3))))
                    (:instance logior-disjoint (a (fn-sha256-byte b0)) (k 24)
                               (c (+ (* 65536 (fn-sha256-byte b1)) (* 256 (fn-sha256-byte b2))
                                     (fn-sha256-byte b3)))))))))

   (local (defthm byte-of-byte
     (equal (fn-sha256-byte (fn-sha256-byte x)) (fn-sha256-byte x))
     :hints (("Goal" :in-theory (enable fn-sha256-byte)))))

   (local (defthm mod-mod-2^32
     (implies (integerp x) (equal (mod (mod x 4294967296) 4294967296) (mod x 4294967296)))))

   (local (defthm int-of-sum-mods
     (implies (integerp x)
              (integerp (+ (* 16777216 (mod (floor x 16777216) 256)) (* 65536 (mod (floor x 65536) 256))
                           (* 256 (mod (floor x 256) 256)) (mod x 256))))))

   (defthm pgs-lo32-is-be-word
     (implies (integerp n)
              (equal (fn-shs-be-word (fn-sha256-byte (ash n -24)) (fn-sha256-byte (ash n -16))
                                     (fn-sha256-byte (ash n -8)) (fn-sha256-byte n))
                     (pgs-lo32 n)))
     :hints (("Goal" :in-theory (union-theories (theory 'byte-theory)
                                                '(be-word-plus byte-of-byte fn-sha256-w32 mod-mod-2^32 int-of-sum-mods))
              :use ((:instance reassemble-32 (x n))))))

   (defthm pgs-hi32-is-be-word
     (implies (integerp n)
              (equal (fn-shs-be-word (fn-sha256-byte (ash n -56)) (fn-sha256-byte (ash n -48))
                                     (fn-sha256-byte (ash n -40)) (fn-sha256-byte (ash n -32)))
                     (pgs-hi32 n)))
     :hints (("Goal" :in-theory (union-theories (theory 'byte-theory)
                                                '(be-word-plus byte-of-byte fn-sha256-w32 mod-mod-2^32 int-of-sum-mods))
              :use ((:instance reassemble-32 (x (floor n 4294967296)))))))

   (local (defthm natp-mod-256-tp
     (implies (integerp x) (and (integerp (mod x 256)) (<= 0 (mod x 256))))
     :rule-classes :type-prescription))

   (local (defthm natp-mod-2^32-tp
     (implies (integerp x) (and (integerp (mod x 4294967296)) (<= 0 (mod x 4294967296))))
     :rule-classes :type-prescription))

   (local (defthm acc-arith
     (equal (+ (* 256 (+ (* 256 (+ (* 256 (+ (* 256 acc) a)) b)) c)) d)
            (+ (* 4294967296 acc) (+ (* 16777216 a) (* 65536 b) (* 256 c) d)))))

   (defthm pgs-be-acc-word
     (implies (and (natp acc) (integerp w))
              (equal (pgs-octets-be-nat-acc
                      (list* (fn-sha256-byte (ash w -24)) (fn-sha256-byte (ash w -16))
                             (fn-sha256-byte (ash w -8)) (fn-sha256-byte w) rest)
                      acc)
                     (pgs-octets-be-nat-acc rest (+ (* 4294967296 acc) (fn-sha256-w32 w)))))
     :hints (("Goal" :in-theory (union-theories (theory 'byte-theory)
                                                '(fn-sha256-w32 natp-mod-256-tp natp-mod-2^32-tp nfix
                                                  car-cons cdr-cons natp acc-arith))
              :expand ((:free (a b acc) (pgs-octets-be-nat-acc (cons a b) acc)))
              :use ((:instance reassemble-32 (x w))))))

   ))

; =============================================================================
; The compression function over the word stobj, as the list model's
; `fn-sha256-compress' of the loaded block (books/sha256-stobj.lisp proves
; these facts locally; they are restated here verbatim, in the context that
; book proves them in, because the page digest drives the same stobj
; functions with its own loaders).

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable floor mod truncate rem ash)))
(local (in-theory (enable fn-shs-add$inline fn-shs-rotr$inline fn-shs-shr$inline
                          fn-shs-ch$inline fn-shs-maj$inline
                          fn-shs-bsig0$inline fn-shs-bsig1$inline
                          fn-shs-ssig0$inline fn-shs-ssig1$inline
                          fn-shs-t1$inline fn-shs-t2$inline fn-shs-sched-word$inline
                          fn-shs-be-word$inline fn-shs-word-byte$inline
                          fn-shs-len-byte$inline fn-shs-octet$inline fn-shs-word-listp)))


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

(local
 (defthm fn-shs-extend-frame
   (equal (nth 1 (fn-shs-extend t0 fn-shs))
          (nth 1 fn-shs))
   :hints (("Goal" :in-theory (enable fn-shs-extend)))))

(local
 (defthm fn-shs-word-listp-of-rounds
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b)
                 (unsigned-byte-p 32 c) (unsigned-byte-p 32 d)
                 (unsigned-byte-p 32 e) (unsigned-byte-p 32 f)
                 (unsigned-byte-p 32 g) (unsigned-byte-p 32 h))
            (fn-shs-word-listp (fn-shs-rounds i ks a b c d e f g h fn-shs)))
   :hints (("Goal" :in-theory (enable fn-shs-rounds)))))

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


; =============================================================================
; The page digest's correspondence.

(local (in-theory (disable fn-shs-be-word$inline pgs-sw-of-lo32 pgs-sw-of-hi32 pgs-x-arr)))

(local
 (defthm pgs-true-listp-of-wp-hp
   (and (implies (fn-shs-wp x) (true-listp x))
        (implies (fn-shs-hp x) (true-listp x)))
   :hints (("Goal" :in-theory (enable fn-shs-wp fn-shs-hp)))))

(local
 (defthm pgs-shape-of-p
   (implies (fn-shs-p fn-shs)
            (and (true-listp (nth 0 fn-shs)) (equal (len (nth 0 fn-shs)) 64)
                 (true-listp (nth 1 fn-shs)) (equal (len (nth 1 fn-shs)) 8)))
   :hints (("Goal" :use pgs-shs-p-parts :in-theory (disable pgs-shs-p-parts)))))

(local (in-theory (disable fn-shs-p)))

(local
 (defthm pgs-x-word-is-nth
   (equal (pgs-x-word sel i pgs-mem) (nth i (pgs-x-arr sel pgs-mem)))
   :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-x-arr pgs-wi pgs-mi pgs-ti)))))

(local
 (defthm pgs-load-half-w
   (and (equal (nth 0 (pgs-load-half j x fn-shs))
               (update-nth j (pgs-sw x) (nth 0 fn-shs)))
        (equal (nth 1 (pgs-load-half j x fn-shs)) (nth 1 fn-shs)))
   :hints (("Goal" :in-theory (enable pgs-load-half)))))

; The sixteen schedule words of a run of message words.
(local
 (defun pgs-sched16 (ws)
   (if (consp ws)
       (list* (pgs-sw (pgs-lo32 (car ws))) (pgs-sw (pgs-hi32 (car ws))) (pgs-sched16 (cdr ws)))
     nil)))

(local
 (defthm pgs-nthx-of-sched16
   (implies (and (natp k) (< k (len ws)))
            (and (equal (fn-sha256-nthx (* 2 k) (pgs-sched16 ws)) (pgs-sw (pgs-lo32 (nth k ws))))
                 (equal (fn-sha256-nthx (+ 1 (* 2 k)) (pgs-sched16 ws)) (pgs-sw (pgs-hi32 (nth k ws))))))
   :hints (("Goal" :induct (nth k ws) :in-theory (enable nth)))))


(local
 (defthm pgs-nth-of-take
   (implies (and (natp k) (natp n) (< k n))
            (equal (nth k (take n x)) (nth k x)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm pgs-nth-of-nthcdr
   (implies (and (natp k) (natp b))
            (equal (nth k (nthcdr b x)) (nth (+ k b) x)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm pgs-len-of-sched16
   (equal (len (pgs-sched16 ws)) (* 2 (len ws)))))

(local
 (defthm pgs-true-listp-of-sched16
   (true-listp (pgs-sched16 ws))))

(local
 (defthm pgs-len-of-take
   (equal (len (take n x)) (nfix n))))
(local
 (defthm pgs-prefix-ok-step2
   (implies (and (fn-shs-prefix-ok (* 2 k) w bw) (natp k)
                 (< (+ 1 (* 2 k)) (len w)) (< (+ 1 (* 2 k)) (len bw))
                 (equal lo (fn-sha256-nthx (* 2 k) bw))
                 (equal hi (fn-sha256-nthx (+ 1 (* 2 k)) bw)))
            (fn-shs-prefix-ok (+ 2 (* 2 k)) (update-nth (+ 1 (* 2 k)) hi (update-nth (* 2 k) lo w)) bw))
   :hints (("Goal" :use ((:instance fn-shs-prefix-ok-step (j (* 2 k)) (v lo) (w w))
                         (:instance fn-shs-prefix-ok-step (j (+ 1 (* 2 k))) (v hi)
                                    (w (update-nth (* 2 k) lo w))))
            :in-theory (disable fn-shs-prefix-ok-step)))))

(local
 (defthm pgs-load-block-w
   (implies (and (natp k) (<= k 8) (natp base)
                 (true-listp (nth 0 fn-shs)) (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-prefix-ok (* 2 k) (nth 0 fn-shs)
                                   (pgs-sched16 (take 8 (nthcdr base (pgs-x-arr sel pgs-mem))))))
            (equal (fn-sha256-firstn 16 (nth 0 (pgs-load-block k sel base pgs-mem fn-shs)))
                   (pgs-sched16 (take 8 (nthcdr base (pgs-x-arr sel pgs-mem))))))
   :hints (("Goal" :induct (pgs-load-block k sel base pgs-mem fn-shs)
            :in-theory (enable pgs-load-block)))))

(local
 (defthm pgs-load-block-h
   (equal (nth 1 (pgs-load-block k sel base pgs-mem fn-shs)) (nth 1 fn-shs))
   :hints (("Goal" :induct (pgs-load-block k sel base pgs-mem fn-shs)
            :in-theory (enable pgs-load-block)))))

(local
 (defthm pgs-load-block-loads
   (implies (and (natp base) (true-listp (nth 0 fn-shs)) (equal (len (nth 0 fn-shs)) 64))
            (equal (fn-sha256-firstn 16 (nth 0 (pgs-load-block 0 sel base pgs-mem fn-shs)))
                   (pgs-sched16 (take 8 (nthcdr base (pgs-x-arr sel pgs-mem))))))
   :hints (("Goal" :use ((:instance pgs-load-block-w (k 0)))
            :in-theory (disable pgs-load-block-w)))))

(local
 (defthm pgs-words16-of-list*
   (equal (fn-sha256-words16 (list* b0 b1 b2 b3 rest))
          (cons (fn-shs-be-word b0 b1 b2 b3) (fn-sha256-words16 rest)))
   :hints (("Goal" :expand ((fn-sha256-words16 (list* b0 b1 b2 b3 rest)))
            :in-theory (enable fn-shs-be-word$inline fn-sha256-nthx fn-sha256-nthcdrx)))))

(local
 (defthm pgs-words16-of-octets
   (equal (fn-sha256-words16 (pgs-words-le-octets ws)) (pgs-sched16 ws))
   :hints (("Goal" :induct (pgs-sched16 ws)
            :in-theory (enable pgs-sw-of-lo32 pgs-sw-of-hi32 fn-sha256-words16)))))

(local
 (defthm pgs-len-of-octets
   (equal (len (pgs-words-le-octets ws)) (* 8 (len ws)))))

(local
 (defthm pgs-octet-listp-of-octets
   (fn-sha256-octet-listp (pgs-words-le-octets ws))))

(local
 (defthm pgs-true-listp-of-octets
   (true-listp (pgs-words-le-octets ws))))

(local
 (defun pgs-hblocks (n x hs)
   ; The list model's state after the N 64-octet blocks of the words X.
   (if (zp n)
       hs
     (pgs-hblocks (- n 1) (nthcdr 8 x)
                  (fn-sha256-compress (pgs-words-le-octets (take 8 x)) hs)))))

(local
 (defthm pgs-nthcdr-of-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x)))))

(local
 (defthm pgs-compress-block
   (implies (and (fn-shs-p fn-shs) (natp base))
            (equal (nth 1 (fn-shs-compress-loaded (pgs-load-block 0 sel base pgs-mem fn-shs)))
                   (fn-sha256-compress (pgs-words-le-octets (take 8 (nthcdr base (pgs-x-arr sel pgs-mem))))
                                       (nth 1 fn-shs))))
   :hints (("Goal" :use ((:instance fn-shs-compress-loaded-is-compress
                                    (fn-shs (pgs-load-block 0 sel base pgs-mem fn-shs))
                                    (blk (pgs-words-le-octets (take 8 (nthcdr base (pgs-x-arr sel pgs-mem)))))))
            :in-theory (disable fn-shs-compress-loaded-is-compress)))))

(local
 (defthm pgs-blocks-h
   (implies (and (fn-shs-p fn-shs) (natp b) (natp nb) (natp base))
            (equal (nth 1 (pgs-blocks b nb sel base pgs-mem fn-shs))
                   (pgs-hblocks (- nb b) (nthcdr (+ base (* 8 b)) (pgs-x-arr sel pgs-mem))
                                (nth 1 fn-shs))))
   :hints (("Goal" :induct (pgs-blocks b nb sel base pgs-mem fn-shs)
            :in-theory (enable pgs-blocks)))))

(local
 (defun pgs-zeros-at (j bw)
   (declare (xargs :measure (nfix (- 14 (nfix j)))))
   (if (zp (- 14 (nfix j)))
       t
     (and (equal (fn-sha256-nthx j bw) 0)
          (pgs-zeros-at (+ 1 (nfix j)) bw)))))

(local
 (defthm pgs-zero-w-w
   (implies (and (natp j) (<= j 14) (fn-shs-p fn-shs) (equal (len bw) 16)
                 (fn-shs-prefix-ok j (nth 0 fn-shs) bw) (pgs-zeros-at j bw))
            (fn-shs-prefix-ok 14 (nth 0 (pgs-zero-w j fn-shs)) bw))
   :hints (("Goal" :induct (pgs-zero-w j fn-shs)
            :in-theory (enable pgs-zero-w)))))

(local
 (defthm pgs-zero-w-h
   (equal (nth 1 (pgs-zero-w j fn-shs)) (nth 1 fn-shs))
   :hints (("Goal" :induct (pgs-zero-w j fn-shs) :in-theory (enable pgs-zero-w)))))

(local
 (defun pgs-pad-words (n)
   (list #x80000000 0 0 0 0 0 0 0 0 0 0 0 0 0 (pgs-hi32 n) (pgs-lo32 n))))

(local
 (defthm pgs-zeros-at-pad
   (pgs-zeros-at 1 (pgs-pad-words n))
   :hints (("Goal" :expand ((:free (j bw) (pgs-zeros-at j bw)))))))

(local
 (defthm pgs-pad-words-facts
   (and (true-listp (pgs-pad-words n))
        (equal (len (pgs-pad-words n)) 16)
        (equal (fn-sha256-nthx 0 (pgs-pad-words n)) #x80000000)
        (equal (fn-sha256-nthx 14 (pgs-pad-words n)) (pgs-hi32 n))
        (equal (fn-sha256-nthx 15 (pgs-pad-words n)) (pgs-lo32 n)))))

(local
 (defthm pgs-pad-block-w
   (implies (fn-shs-p fn-shs)
            (equal (fn-sha256-firstn 16 (nth 0 (pgs-pad-block n fn-shs)))
                   (pgs-pad-words n)))
   :hints (("Goal" :in-theory (e/d (pgs-pad-block pgs-set-w)
                                   (fn-shs-prefix-ok-step fn-shs-prefix-ok-done pgs-zero-w-w pgs-pad-words))
            :use ((:instance fn-shs-prefix-ok-step (j 0) (v #x80000000) (w (nth 0 fn-shs))
                             (bw (pgs-pad-words n)))
                  (:instance pgs-zero-w-w (j 1) (fn-shs (pgs-set-w 0 #x80000000 fn-shs))
                             (bw (pgs-pad-words n)))
                  (:instance fn-shs-prefix-ok-step (j 14) (v (pgs-hi32 n))
                             (w (nth 0 (pgs-zero-w 1 (pgs-set-w 0 #x80000000 fn-shs))))
                             (bw (pgs-pad-words n)))
                  (:instance fn-shs-prefix-ok-step (j 15) (v (pgs-lo32 n))
                             (w (update-nth 14 (pgs-hi32 n)
                                            (nth 0 (pgs-zero-w 1 (pgs-set-w 0 #x80000000 fn-shs)))))
                             (bw (pgs-pad-words n)))
                  (:instance fn-shs-prefix-ok-done
                             (w (update-nth 15 (pgs-lo32 n)
                                            (update-nth 14 (pgs-hi32 n)
                                                        (nth 0 (pgs-zero-w 1 (pgs-set-w 0 #x80000000 fn-shs))))))
                             (bw (pgs-pad-words n))))))))

(local
 (defthm pgs-pad-block-h
   (equal (nth 1 (pgs-pad-block n fn-shs)) (nth 1 fn-shs))
   :hints (("Goal" :in-theory (enable pgs-pad-block pgs-set-w)))))

(local
 (defun pgs-pad-tail (k)
   ; The padding of a message of K whole blocks: one more block.
   (cons 128 (fn-sha256-appx (fn-sha256-zeros 55) (fn-sha256-u64-be (* 512 k))))))

(local
 (defthm pgs-appx-is-append
   (equal (fn-sha256-appx a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-sha256-appx)))))

(local
 (defthm pgs-pad-of-whole-blocks
   (implies (and (natp k) (equal (len m) (* 64 k)))
            (equal (fn-sha256-pad m) (append m (pgs-pad-tail k))))
   :hints (("Goal" :in-theory (enable fn-sha256-pad)))))

(local (in-theory (disable pgs-pad-tail)))

(local
 (defthm pgs-take-plus
   (implies (and (natp a) (natp b))
            (equal (take (+ a b) x) (append (take a x) (take b (nthcdr a x)))))
   :hints (("Goal" :induct (nthcdr a x) :in-theory (enable take)))))

(local
 (defthm pgs-octets-of-append
   (equal (pgs-words-le-octets (append a b))
          (append (pgs-words-le-octets a) (pgs-words-le-octets b)))))

(local
 (defthm pgs-firstn-of-append-len-aux
   (implies (true-listp a)
            (equal (fn-sha256-firstn (len a) (append a b)) a))
   :rule-classes nil
   :hints (("Goal" :induct (len a)
            :in-theory (e/d (fn-sha256-firstn) (fn-shs-firstn-snoc))))))

(local
 (defthm pgs-firstn-of-append-len
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-sha256-firstn n (append a b)) a))
   :hints (("Goal" :use pgs-firstn-of-append-len-aux))))

(local
 (defthm pgs-nthcdrx-of-append-len-aux
   (equal (fn-sha256-nthcdrx (len a) (append a b)) b)
   :rule-classes nil
   :hints (("Goal" :induct (len a) :in-theory (enable fn-sha256-nthcdrx)))))

(local
 (defthm pgs-nthcdrx-of-append-len
   (implies (equal n (len a))
            (equal (fn-sha256-nthcdrx n (append a b)) b))
   :hints (("Goal" :use pgs-nthcdrx-of-append-len-aux))))

(local
 (defthm pgs-blocks-of-append-block
   (implies (and (true-listp o) (equal (len o) 64))
            (equal (fn-sha256-blocks (append o r) hs)
                   (fn-sha256-blocks r (fn-sha256-compress o hs))))
   :hints (("Goal" :expand ((fn-sha256-blocks (append o r) hs))))))

(local
 (defthm pgs-blocks-of-octets
   (implies (natp n)
            (equal (fn-sha256-blocks (append (pgs-words-le-octets (take (* 8 n) x)) tl) hs)
                   (fn-sha256-blocks tl (pgs-hblocks n x hs))))
   :hints (("Goal" :induct (pgs-hblocks n x hs))
           ("Subgoal *1/2" :use ((:instance pgs-take-plus (a 8) (b (* 8 (- n 1)))))
            :in-theory (disable pgs-take-plus)))))

(local
 (defthm pgs-pad-tail-shape
   (and (true-listp (pgs-pad-tail k))
        (equal (len (pgs-pad-tail k)) 64))
   :hints (("Goal" :in-theory (enable pgs-pad-tail)))))

(local
 (defthm pgs-blocks-of-pad-tail
   (equal (fn-sha256-blocks (pgs-pad-tail k) hs)
          (fn-sha256-compress (pgs-pad-tail k) hs))
   :hints (("Goal" :use ((:instance pgs-blocks-of-append-block (o (pgs-pad-tail k)) (r nil)))
            :in-theory (disable pgs-blocks-of-append-block)))))

(local
 (defthm pgs-words16-of-pad-tail
   (implies (integerp k)
            (equal (fn-sha256-words16 (pgs-pad-tail k))
                   (pgs-pad-words (* 512 k))))
   :hints (("Goal" :in-theory (enable pgs-pad-tail fn-sha256-u64-be)))))

(local (in-theory (disable pgs-octets-be-nat-acc)))

(local
 (defthm pgs-h-word-u32
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8))
            (and (equal (fn-sha256-w32 (fn-sha256-nthx i (nth 1 fn-shs)))
                        (fn-sha256-nthx i (nth 1 fn-shs)))
                 (integerp (fn-sha256-nthx i (nth 1 fn-shs)))
                 (<= 0 (fn-sha256-nthx i (nth 1 fn-shs)))))
   :rule-classes ((:rewrite :corollary
                   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8))
                            (and (equal (fn-sha256-w32 (fn-sha256-nthx i (nth 1 fn-shs)))
                                        (fn-sha256-nthx i (nth 1 fn-shs)))
                                 (integerp (fn-sha256-nthx i (nth 1 fn-shs))))))
                  (:linear :corollary
                   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8))
                            (<= 0 (fn-sha256-nthx i (nth 1 fn-shs)))))
                  (:rewrite :corollary
                   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8) (natp acc))
                            (natp (+ (* 4294967296 acc) (fn-sha256-nthx i (nth 1 fn-shs)))))))
   :hints (("Goal" :use ((:instance fn-shs-nthx-is-nth (xs (nth 1 fn-shs)))
                         (:instance fn-shs-hp-nth (h (nth 1 fn-shs))))
            :in-theory (disable fn-shs-nth-of-array-is-nthx)))))

(local
 (defthm pgs-h-nat-is-be-nat
   (implies (and (natp i) (<= i 8) (natp acc) (fn-shs-p fn-shs))
            (equal (pgs-h-nat i acc fn-shs)
                   (pgs-octets-be-nat-acc
                    (fn-sha256-words-octets (fn-sha256-nthcdrx i (nth 1 fn-shs))) acc)))
   :hints (("Goal" :induct (pgs-h-nat i acc fn-shs)
            :in-theory (enable pgs-h-nat fn-sha256-words-octets))
           ("Subgoal *1/1" :expand ((:free (x) (pgs-octets-be-nat-acc x acc)))))))

(local
 (defthm pgs-len-of-hblocks
   (implies (equal (len hs) 8)
            (equal (len (pgs-hblocks n x hs)) 8))))

(local
 (defthm pgs-true-listp-of-hblocks
   (implies (true-listp hs)
            (true-listp (pgs-hblocks n x hs)))))

; The stobj side: the final state's H.
(local
 (defthm pgs-digest-state-h
   (implies (and (fn-shs-p fn-shs) (natp base) (natp nb))
            (equal (nth 1 (fn-shs-compress-loaded
                           (pgs-pad-block (* 512 nb)
                                          (pgs-blocks 0 nb sel base pgs-mem
                                                      (fn-shs-h-init 0 *fn-sha256-h0* fn-shs)))))
                   (fn-sha256-compress (pgs-pad-tail nb)
                                       (pgs-hblocks nb (nthcdr base (pgs-x-arr sel pgs-mem))
                                                    *fn-sha256-h0*))))
   :hints (("Goal" :in-theory (disable fn-shs-compress-loaded-is-compress nthcdr)
            :use ((:instance fn-shs-compress-loaded-is-compress
                             (fn-shs (pgs-pad-block
                                      (* 512 nb)
                                      (pgs-blocks 0 nb sel base pgs-mem
                                                  (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))))
                             (blk (pgs-pad-tail nb))))))))

; The list side: the model's state after the padded message.
(local
 (defthm pgs-spec-blocks
   (implies (natp nb)
            (equal (fn-sha256-blocks (fn-sha256-pad (pgs-words-le-octets (take (* 8 nb) x))) hs)
                   (fn-sha256-compress (pgs-pad-tail nb) (pgs-hblocks nb x hs))))
   :hints (("Goal" :in-theory (disable nthcdr)))))

; -----------------------------------------------------------------------------
; The keystone: the digest the host calls (`pgs-x-page-digest', and through
; it the page store's verification and commit paths) is SHA-256 of the
; little-endian octets of the word range, as the big-endian natural of its
; 32 octets.

(defthm pgs-x-words-digest-is-sha256
  (implies (and (fn-shs-p fn-shs) (natp base) (natp nb))
           (equal (mv-nth 0 (pgs-x-words-digest sel base nb pgs-mem fn-shs))
                  (pgs-octets-be-nat
                   (fn-sha256 (pgs-words-le-octets
                               (take (* 8 nb) (nthcdr base (pgs-x-arr sel pgs-mem))))))))
  :hints (("Goal" :in-theory (e/d (pgs-x-words-digest fn-sha256 fn-sha256-of-octets pgs-octets-be-nat)
                                  (nthcdr take)))))

; A ground witness of the keystone: the antecedent on concrete arguments,
; the host function's value, and the specification's value, both the
; standard SHA-256 of the octets 00, 01, ..., 3f (two leading words that the
; range skips).
(defthm pgs-x-words-digest-witness
  (let ((words '(#xdeadbeefcafef00d #xffffffffffffffff
                 #x0706050403020100 #x0f0e0d0c0b0a0908 #x1716151413121110 #x1f1e1d1c1b1a1918
                 #x2726252423222120 #x2f2e2d2c2b2a2928 #x3736353433323130 #x3f3e3d3c3b3a3938)))
    (and (fn-shs-p (create-fn-shs)) (natp 2) (natp 1)
         (equal (mv-nth 0 (pgs-x-words-digest 0 2 1 (update-nth *pgs-wi* words (create-pgs-mem))
                                              (create-fn-shs)))
                #xfdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108)
         (equal (pgs-octets-be-nat (fn-sha256 (pgs-words-le-octets (take 8 (nthcdr 2 words)))))
                #xfdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108)))
  :rule-classes nil)
