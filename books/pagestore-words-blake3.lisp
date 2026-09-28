;; fn: the page store's word digest is BLAKE3 (lane arena-store-4,
;; 2026-09-28; the digest part of A-PGS-OBSERVE).  Prefix pgs-.
;;
;; What is proved.  `pgs-x-words-digest-is-blake3' (the keystone): the
;; digest the host calls, `pgs-x-words-digest' (books/pagestore-words;
;; host/native/proto-pagestore.lisp calls it through the record check, the
;; directory and table checks, the commit and the image digest), is
;; `fn-blake3' of the octets of the 8*NB words from BASE of the array SEL
;; names, each word least significant octet first (`pgs-words-le-octets'),
;; read as a big-endian natural (`pgs-octets-be-nat').  `fn-blake3' is the
;; digest `fn-digest' is attached to: books/crypto-attach.lisp attaches
;; `fn-blake3-stobj' (books/blake3-stobj.lisp), proved equal to `fn-blake3'.
;; The hypotheses are naturals BASE and NB; nothing about the word stobj or
;; the octet buffer, and no bound on BASE + 8*NB: past the array's end both
;; sides read zero words (`nth' and `take' give NIL, whose octets are zero),
;; and the buffer is cleared before the words are copied into it.
;;
;; How.  The copy appends each word's low and high u32 halves as four
;; octets each (`pgs-word-halves-octets': together they are the word's
;; eight), so the buffer after the copy is the specification's octet list
;; (`pgs-x-words-load-is-octets').  The digest the host runs is the buffer
;; twin `fn-blake3-of-prefixed-buffer', the `:exec' of an `mbe' whose
;; `:logic' is `fn-blake3' of the buffer's octets; the guard proof of
;; `pgs-x-words-digest' is their equality (books/blake3-stobj.lisp's
;; `fn-blake3-of-prefixed-buffer-is-blake3').
;;
;; Ground witness: `pgs-x-words-digest-witness' evaluates the host function
;; on a concrete stobj whose words hold the octets 00..3f and gets BLAKE3 of
;; those 64 octets, the value ACL2 computes with `fn-blake3'.
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

(defun pgs-octet (x)
  ; Any object as an octet: its low eight bits.
  (declare (xargs :guard t))
  (mod (ifix x) 256))

(defun pgs-word-le-octets (w)
  ; The eight octets of a 64-bit word, least significant first.
  (declare (xargs :guard t))
  (list (pgs-octet w) (pgs-octet (ash (ifix w) -8))
        (pgs-octet (ash (ifix w) -16)) (pgs-octet (ash (ifix w) -24))
        (pgs-octet (ash (ifix w) -32)) (pgs-octet (ash (ifix w) -40))
        (pgs-octet (ash (ifix w) -48)) (pgs-octet (ash (ifix w) -56))))

(defun pgs-words-le-octets (ws)
  ; The octets of a list of words, each word little-endian, in list order.
  (declare (xargs :guard t))
  (if (consp ws)
      (append (pgs-word-le-octets (car ws)) (pgs-words-le-octets (cdr ws)))
    nil))

; -----------------------------------------------------------------------------
; A word's two u32 halves, four octets each, are its eight octets (the
; arithmetic under arithmetic-5 in a scope of its own, driven in the
; minimal theory: arithmetic-5 alone takes seconds on these goals).

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm pgs-octet-type
    (and (integerp (pgs-octet x))
         (<= 0 (pgs-octet x))
         (<= (pgs-octet x) 255))
    :rule-classes ((:type-prescription
                    :corollary (and (integerp (pgs-octet x)) (<= 0 (pgs-octet x))))
                   (:linear
                    :corollary (and (<= 0 (pgs-octet x)) (<= (pgs-octet x) 255)))
                   (:rewrite
                    :corollary (integerp (pgs-octet x)))))

  (local (defthm mod-split-256
    (implies (and (integerp x) (posp m))
             (equal (mod x (* 256 m))
                    (+ (* 256 (mod (floor x 256) m)) (mod x 256))))
    :hints (("Goal" :in-theory (enable mod) :nonlinearp nil))
    :rule-classes nil))

  (local (defthm mod-split-k
    (implies (and (integerp x) (posp m) (equal k (* 256 m)))
             (equal (mod x k)
                    (+ (* 256 (mod (floor x 256) m)) (mod x 256))))
    :rule-classes nil
    :hints (("Goal" :in-theory (theory 'minimal-theory) :use mod-split-256))))

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

  (local (defthm int-of-floor-mod
    (implies (and (integerp x) (integerp y)) (and (integerp (floor x y)) (integerp (mod x y))))))

  (local (defthm nat-of-mod
    (implies (and (integerp x) (posp m)) (and (integerp (mod x m)) (<= 0 (mod x m))))))

  (local (defthm fm
    (implies (integerp x)
             (and (equal (floor (mod x 4294967296) 256) (mod (floor x 256) 16777216))
                  (equal (floor (mod x 16777216) 256) (mod (floor x 256) 65536))
                  (equal (floor (mod x 65536) 256) (mod (floor x 256) 256))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp)))
             :use ((:instance p1p2 (x x) (m 16777216) (k 4294967296))
                   (:instance p1p2 (x x) (m 65536) (k 16777216))
                   (:instance p1p2 (x x) (m 256) (k 65536)))))))

  (local (defthm mm-256
    (implies (and (integerp x) (member-equal m '(256 65536 16777216 4294967296)))
             (equal (mod (mod x m) 256) (mod x 256)))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp) member-equal (:e member-equal)))
             :use ((:instance p1p2 (x x) (m 1) (k 256))
                   (:instance p1p2 (x x) (m 256) (k 65536))
                   (:instance p1p2 (x x) (m 65536) (k 16777216))
                   (:instance p1p2 (x x) (m 16777216) (k 4294967296)))))))

  (local (defthm ff
    (implies (integerp x)
             (and (equal (floor (floor x 256) 256) (floor x 65536))
                  (equal (floor (floor x 65536) 256) (floor x 16777216))
                  (equal (floor (floor x 4294967296) 256) (floor x 1099511627776))
                  (equal (floor (floor x 1099511627776) 256) (floor x 281474976710656))
                  (equal (floor (floor x 281474976710656) 256) (floor x 72057594037927936))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp)))
             :use ((:instance floor-floor-k (x x) (a 256) (b 256) (k 65536))
                   (:instance floor-floor-k (x x) (a 65536) (b 256) (k 16777216))
                   (:instance floor-floor-k (x x) (a 4294967296) (b 256) (k 1099511627776))
                   (:instance floor-floor-k (x x) (a 1099511627776) (b 256) (k 281474976710656))
                   (:instance floor-floor-k (x x) (a 281474976710656) (b 256) (k 72057594037927936)))))))

  (local (defthm ash-m
    (and (equal (ash x -8) (floor (ifix x) 256))
         (equal (ash x -16) (floor (ifix x) 65536))
         (equal (ash x -24) (floor (ifix x) 16777216))
         (equal (ash x -32) (floor (ifix x) 4294967296))
         (equal (ash x -40) (floor (ifix x) 1099511627776))
         (equal (ash x -48) (floor (ifix x) 281474976710656))
         (equal (ash x -56) (floor (ifix x) 72057594037927936)))))

  (local (defthm floor-32-of-floor-8
    (implies (integerp x)
             (and (equal (floor (floor x 4294967296) 65536) (floor x 281474976710656))
                  (equal (floor (floor x 4294967296) 16777216) (floor x 72057594037927936))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e posp)))
             :use ((:instance floor-floor-k (x x) (a 4294967296) (b 65536) (k 281474976710656))
                   (:instance floor-floor-k (x x) (a 4294967296) (b 16777216) (k 72057594037927936)))))))

  (local (defthm word4
    (implies (integerp y)
             (equal (fn-oct-word-octets (mod y 4294967296) 4)
                    (list (mod y 256) (mod (floor y 256) 256)
                          (mod (floor y 65536) 256) (mod (floor y 16777216) 256))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '((:e posp) (:e member-equal) (:e zp) nfix natp
                                                 int-of-floor-mod nat-of-mod fm mm-256 ff))
             :expand ((:free (x) (fn-oct-word-octets x 4)) (:free (x) (fn-oct-word-octets x 3))
                      (:free (x) (fn-oct-word-octets x 2)) (:free (x) (fn-oct-word-octets x 1))
                      (:free (x) (fn-oct-word-octets x 0)))))))

  (defthm pgs-word-halves-octets
    (equal (append (fn-oct-word-octets (pgs-lo32 w) 4)
                   (fn-oct-word-octets (pgs-hi32 w) 4))
           (pgs-word-le-octets w))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '(word4 ash-m ff floor-32-of-floor-8 int-of-floor-mod
                                                 ifix (:t ifix) pgs-octet pgs-word-le-octets
                                                 pgs-lo32$inline pgs-hi32$inline
                                                 binary-append car-cons cdr-cons (:e binary-append)))))))

(in-theory (disable pgs-octet))

(local (defthm pgs-append-assoc
  (equal (append (append a b) c) (append a b c))
  :rule-classes nil))

(defthm pgs-word-halves-octets-tail
  (equal (append (fn-oct-word-octets (pgs-lo32 w) 4)
                 (fn-oct-word-octets (pgs-hi32 w) 4) rest)
         (append (pgs-word-le-octets w) rest))
  :hints (("Goal" :use (pgs-word-halves-octets
                        (:instance pgs-append-assoc
                                   (a (fn-oct-word-octets (pgs-lo32 w) 4))
                                   (b (fn-oct-word-octets (pgs-hi32 w) 4)) (c rest)))
           :in-theory (disable pgs-word-halves-octets pgs-word-le-octets fn-oct-word-octets))))

; -----------------------------------------------------------------------------
; The copy: the buffer after `pgs-x-words-load' is the specification's
; octets appended to what it held.

(local (defthm pgs-x-word-is-nth
  (equal (pgs-x-word sel i pgs-mem) (nth i (pgs-x-arr sel pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-wi pgs-mi pgs-ti)))))

(local (defthm pgs-take-nthcdr-step
  (implies (and (natp j) (posp m))
           (equal (take m (nthcdr j l))
                  (cons (nth j l) (take (- m 1) (nthcdr (+ 1 j) l)))))
  :hints (("Goal" :in-theory (enable nth nthcdr take) :induct (nthcdr j l)))))

(local (defthm pgs-take-zero (equal (take 0 l) nil)))

(defthm pgs-x-words-load-is-octets
  (implies (and (natp k) (natp base) (true-listp fn-octets-pg))
           (equal (pgs-x-words-load k n sel base pgs-mem fn-octets-pg)
                  (append fn-octets-pg
                          (pgs-words-le-octets
                           (take (nfix (- (nfix n) k)) (nthcdr (+ base k) (pgs-x-arr sel pgs-mem)))))))
  :hints (("Goal" :induct (pgs-x-words-load k n sel base pgs-mem fn-octets-pg)
           :in-theory (e/d (pgs-x-words-load) (pgs-word-le-octets pgs-x-arr take nthcdr)))))

; -----------------------------------------------------------------------------
; KEYSTONE: the page digest the host calls is BLAKE3 of the words'
; little-endian octets, as the big-endian natural of its 32 octets.

(defthm pgs-x-words-digest-is-blake3
  (implies (and (natp base) (natp nb))
           (equal (mv-nth 0 (pgs-x-words-digest sel base nb pgs-mem fn-octets-pg))
                  (pgs-octets-be-nat
                   (fn-blake3 (pgs-words-le-octets
                               (take (* 8 nb) (nthcdr base (pgs-x-arr sel pgs-mem))))))))
  :hints (("Goal" :in-theory (e/d (pgs-x-words-digest)
                                  (pgs-words-le-octets pgs-x-arr take nthcdr pgs-octets-be-nat fn-blake3)))))

; A ground witness of the keystone: the antecedent on concrete arguments,
; the host function's value, and the specification's value, both BLAKE3 of
; the octets 00, 01, ..., 3f (two leading words that the range skips), the
; value ACL2 computes with `fn-blake3' (it is also BLAKE3's published test
; vector for 64 octets).
(defthm pgs-x-words-digest-witness
  (let ((words '(#xdeadbeefcafef00d #xffffffffffffffff
                 #x0706050403020100 #x0f0e0d0c0b0a0908 #x1716151413121110 #x1f1e1d1c1b1a1918
                 #x2726252423222120 #x2f2e2d2c2b2a2928 #x3736353433323130 #x3f3e3d3c3b3a3938)))
    (and (natp 2) (natp 1)
         (equal (mv-nth 0 (pgs-x-words-digest 0 2 1 (update-nth *pgs-wi* words (create-pgs-mem))
                                              (create-fn-octets-pg)))
                #x4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98)
         (equal (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets (take 8 (nthcdr 2 words)))))
                #x4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98)))
  :rule-classes nil)
