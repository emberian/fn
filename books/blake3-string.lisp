; fn: BLAKE3 over a string, read by index, consing nothing: the executable
; twin of books/blake3.lisp for a short text the served path digests whole
; (lane served-incremental-3, 2026-10-02; the Message-ID's keyed tag,
; books/msgid-linear-exec `fn-mlh-tag').
;
; What this book is.  The message is the octets of a string S, the character
; at I read as its code (`fn-b3s-byte'), with no list built: a block's
; sixteen words go straight from the string into the compression function
; (`fn-b3s-block'), a chunk keeps its chaining value in eight multiple
; values, a node of the tree returns its chaining value as eight values, and
; the root returns its eight output words.  Nothing is consed beyond what
; SBCL boxes, and every value is a 32-bit word: a fixnum.  The compression
; function and the tree's split are books/blake3.lisp's own functions; only
; the reading of the message and the shape of the results are new.  The
; reader is books/blake3-stobj.lisp's design with the octet buffer replaced
; by a string, so that a caller holding the text needs no buffer at all.
;
; What is proved.  `fn-b3s-root-is-hash' (the keystone): the four octets of
; each of the root's eight words, least significant first, are `fn-b3-hash'
; of the string's octets (`fn-b3s-msg') under the key words K0..K7 and the
; mode FLAGS, for every string, of any length.  Its parts: the block
; (`fn-b3s-block-is-compress'), the chunk (`fn-b3s-chunk-is-chunk'), the node
; (`fn-b3s-node-is-node').  The logical message is a list; the reader's
; :exec reads the string, and the two agree by guard verification of
; `fn-b3s-byte' alone (`fn-b3s-msg-nthx').

(in-package "ACL2")
(include-book "blake3")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod truncate rem unsigned-byte-p mv-nth)))

; -----------------------------------------------------------------------------
; The logical message: the string's character codes.

(defun fn-b3s-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs)
      (cons (char-code (car cs)) (fn-b3s-codes (cdr cs)))
    nil))

(defun fn-b3s-msg (s)
  (declare (xargs :guard t))
  (if (stringp s) (fn-b3s-codes (coerce s 'list)) nil))

(local
 (defthm fn-b3s-len-of-codes
   (equal (len (fn-b3s-codes cs)) (len cs))))

(defthm fn-b3s-len-of-msg
  (equal (len (fn-b3s-msg s)) (if (stringp s) (length s) 0)))

(local
 (defthm fn-b3s-nth-of-codes
   (implies (< (nfix i) (len cs))
            (equal (fn-b3-nthx i (fn-b3s-codes cs))
                   (char-code (nth i cs))))
   :hints (("Goal" :in-theory (enable fn-b3-nthx)))))

(defthm fn-b3s-msg-nthx
  (implies (and (stringp s) (< (nfix i) (length s)))
           (equal (fn-b3-nthx i (fn-b3s-msg s))
                  (char-code (char s i)))))

(local
 (defthm fn-b3s-octet-listp-of-codes
   (fn-b3-octet-listp (fn-b3s-codes cs))))

(in-theory (disable fn-b3s-msg))

(defthm fn-b3s-octet-listp-of-msg
  (fn-b3-octet-listp (fn-b3s-msg s))
  :hints (("Goal" :in-theory (enable fn-b3s-msg))))

; -----------------------------------------------------------------------------
; The reader.  Positions at and past E read as zero: the zero padding of a
; short last block, which the list model gets from `fn-b3-nthx' past the end
; of the node's octets.

(defun fn-b3s-byte (i e s)
  (declare (type (integer 0 *) i e)
           (xargs :guard (and (stringp s) (<= e (length s)))))
  (if (< i e)
      (mbe :logic (fn-b3-nthx i (fn-b3s-msg s))
           :exec (char-code (char s i)))
    0))

(defun fn-b3s-word (p e s)
  ; The little-endian word of the four octets at P.
  (declare (type (integer 0 *) p e)
           (xargs :guard (and (stringp s) (<= e (length s)))))
  (fn-b3-le-word (fn-b3s-byte p e s)
                 (fn-b3s-byte (+ p 1) e s)
                 (fn-b3s-byte (+ p 2) e s)
                 (fn-b3s-byte (+ p 3) e s)))

; One compression of the block at Q: the chaining value in C0..C7, the
; output chaining value as eight values.
(defun fn-b3s-block (c0 c1 c2 c3 c4 c5 c6 c7 q e counter blen fl s)
  (declare (type (integer 0 *) q e)
           (xargs :guard (and (stringp s) (<= e (length s)))))
  (mv-let (o0 o1 o2 o3 o4 o5 o6 o7)
    (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7
                       (fn-b3s-word q e s) (fn-b3s-word (+ q 4) e s)
                       (fn-b3s-word (+ q 8) e s) (fn-b3s-word (+ q 12) e s)
                       (fn-b3s-word (+ q 16) e s) (fn-b3s-word (+ q 20) e s)
                       (fn-b3s-word (+ q 24) e s) (fn-b3s-word (+ q 28) e s)
                       (fn-b3s-word (+ q 32) e s) (fn-b3s-word (+ q 36) e s)
                       (fn-b3s-word (+ q 40) e s) (fn-b3s-word (+ q 44) e s)
                       (fn-b3s-word (+ q 48) e s) (fn-b3s-word (+ q 52) e s)
                       (fn-b3s-word (+ q 56) e s) (fn-b3s-word (+ q 60) e s)
                       counter blen fl)
    (mv o0 o1 o2 o3 o4 o5 o6 o7)))

; A chunk: the octets [Q, E), the chaining value in C0..C7.  The last block
; is compressed with CHUNK_END and ROOTFL (0 below the root, ROOT for a
; message of one chunk, whose counter is 0): the result is the chunk's
; chaining value, or the root's output words.
(defun fn-b3s-chunk (c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
  (declare (type (integer 0 *) q e)
           (xargs :guard (and (natp counter) (natp flags) (natp rootfl) (<= q e)
                              (stringp s) (<= e (length s)))
                  :measure (nfix (- e q))))
  (let ((fl (logior (ifix flags) (if startp *fn-b3-chunk-start* 0))))
    (if (and (mbt (and (natp q) (natp e))) (< 64 (- e q)))
        (mv-let (c0 c1 c2 c3 c4 c5 c6 c7)
          (fn-b3s-block c0 c1 c2 c3 c4 c5 c6 c7 q e counter 64 fl s)
          (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 (+ q 64) e counter flags nil rootfl s))
      (fn-b3s-block c0 c1 c2 c3 c4 c5 c6 c7 q e counter (nfix (- e q))
                    (if (zp rootfl)
                        (logior fl *fn-b3-chunk-end*)
                      (logior (logior fl *fn-b3-chunk-end*) rootfl))
                    s))))

; A node below the root: the octets [S0, E), split as books/blake3.lisp
; `fn-b3-node' splits; its chaining value as eight values.
(defun fn-b3s-node (k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)
  (declare (type (integer 0 *) s0 e)
           (xargs :guard (and (natp counter) (natp flags) (<= s0 e)
                              (stringp s) (<= e (length s)))
                  :measure (nfix (- e s0))))
  (if (and (mbt (and (natp s0) (natp e))) (< 1024 (- e s0)))
      (let* ((lc (fn-b3-left-chunks 1 (- e s0)))
             (ll (* 1024 lc)))
        (mv-let (l0 l1 l2 l3 l4 l5 l6 l7)
          (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 (+ s0 ll) counter flags s)
          (mv-let (r0 r1 r2 r3 r4 r5 r6 r7)
            (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 (+ s0 ll) e (+ (nfix counter) lc) flags s)
            (mv-let (o0 o1 o2 o3 o4 o5 o6 o7)
              (fn-b3-compress-core k0 k1 k2 k3 k4 k5 k6 k7
                                   l0 l1 l2 l3 l4 l5 l6 l7 r0 r1 r2 r3 r4 r5 r6 r7
                                   0 64 (logior (ifix flags) *fn-b3-parent*))
              (mv o0 o1 o2 o3 o4 o5 o6 o7)))))
    (fn-b3s-chunk k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags t 0 s)))

; The root: the eight output words of the whole string under K0..K7.
(defun fn-b3s-root (k0 k1 k2 k3 k4 k5 k6 k7 flags s)
  (declare (xargs :guard (and (natp flags) (stringp s))))
  (let ((n (length s)))
    (if (< 1024 n)
        (let* ((lc (fn-b3-left-chunks 1 n))
               (ll (* 1024 lc)))
          (mv-let (l0 l1 l2 l3 l4 l5 l6 l7)
            (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 0 ll 0 flags s)
            (mv-let (r0 r1 r2 r3 r4 r5 r6 r7)
              (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 ll n lc flags s)
              (mv-let (o0 o1 o2 o3 o4 o5 o6 o7)
                (fn-b3-compress-core k0 k1 k2 k3 k4 k5 k6 k7
                                     l0 l1 l2 l3 l4 l5 l6 l7 r0 r1 r2 r3 r4 r5 r6 r7
                                     0 64 (logior (logior (ifix flags) *fn-b3-parent*) *fn-b3-root*))
                (mv o0 o1 o2 o3 o4 o5 o6 o7)))))
      (fn-b3s-chunk k0 k1 k2 k3 k4 k5 k6 k7 0 n 0 flags t *fn-b3-root* s))))

; =============================================================================
; The correspondence.  M is the string's octets (`fn-b3s-msg'); a node or a
; chunk is the span [Q, E) of it, `(fn-b3-firstn (- e q) (fn-b3-nthcdrx q
; M))'.  Each level is proved as books/blake3-stobj.lisp proves its own: the
; step and base cases apart, the induction only composing them.

(local
 (defthm fn-b3s-nthx-of-firstn
   (equal (fn-b3-nthx j (fn-b3-firstn n l))
          (if (< (nfix j) (nfix n)) (fn-b3-nthx j l) 0))
   :hints (("Goal" :induct (list (fn-b3-nthx j l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3s-nthx-of-nthcdrx
   (equal (fn-b3-nthx j (fn-b3-nthcdrx a l))
          (fn-b3-nthx (+ (nfix a) (nfix j)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx a l)))))

(local
 (defthm fn-b3s-nthcdrx-of-firstn
   (equal (fn-b3-nthcdrx k (fn-b3-firstn n l))
          (fn-b3-firstn (- (nfix n) (nfix k)) (fn-b3-nthcdrx k l)))
   :hints (("Goal" :induct (list (fn-b3-nthcdrx k l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3s-nthcdrx-of-nthcdrx
   (equal (fn-b3-nthcdrx k (fn-b3-nthcdrx p l))
          (fn-b3-nthcdrx (+ (nfix k) (nfix p)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx p l)))))

(local
 (defthm fn-b3s-firstn-of-firstn
   (implies (<= (nfix k) (nfix n))
            (equal (fn-b3-firstn k (fn-b3-firstn n l))
                   (fn-b3-firstn k l)))
   :hints (("Goal" :induct (list (fn-b3-firstn k l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3s-nthcdrx-of-zero
   (equal (fn-b3-nthcdrx 0 l) l)))

(local
 (defthm fn-b3s-firstn-of-len
   (implies (and (true-listp l) (equal n (len l)))
            (equal (fn-b3-firstn n l) l))))

(local
 (defthm fn-b3s-true-listp-of-codes
   (true-listp (fn-b3s-codes cs))))

(local
 (defthm fn-b3s-true-listp-of-msg
   (true-listp (fn-b3s-msg s))
   :hints (("Goal" :in-theory (enable fn-b3s-msg)))))

(local
 (defthm fn-b3s-nthx-of-cons
   (equal (fn-b3-nthx i (cons x y))
          (if (zp (nfix i)) x (fn-b3-nthx (- (nfix i) 1) y)))))

(local
 (defthm fn-b3s-nthx-of-non-cons
   (implies (not (consp x)) (equal (fn-b3-nthx i x) 0))))

(local
 (defun fn-b3s-ind-words (j k x)
   (declare (xargs :measure (nfix k)))
   (if (zp (nfix k)) (list j x)
     (fn-b3s-ind-words (- (nfix j) 1) (- (nfix k) 1) (fn-b3-nthcdrx 4 x)))))

(local
 (defthm fn-b3s-nthx-of-words
   (implies (natp j)
            (equal (fn-b3-nthx j (fn-b3-words k x))
                   (if (< j (nfix k))
                       (fn-b3-le-word (fn-b3-nthx (* 4 j) x) (fn-b3-nthx (+ 1 (* 4 j)) x)
                                      (fn-b3-nthx (+ 2 (* 4 j)) x) (fn-b3-nthx (+ 3 (* 4 j)) x))
                     0)))
   :hints (("Goal" :induct (fn-b3s-ind-words j k x)
            :expand ((fn-b3-words k x))))))

(local
 (defun fn-b3s-ind-mv-nth (i x)
   (if (zp i) x (fn-b3s-ind-mv-nth (- i 1) (cdr x)))))

(local
 (defthm fn-b3s-mv-nth-is-nthx
   (implies (and (natp i) (< i (len x)))
            (equal (mv-nth i x) (fn-b3-nthx i x)))
   :hints (("Goal" :induct (fn-b3s-ind-mv-nth i x)
            :in-theory (enable mv-nth)))))

(local (in-theory (disable fn-b3-nthx fn-b3-nthcdrx fn-b3-firstn)))

; -----------------------------------------------------------------------------
; The block.

(local
 (defthm fn-b3s-nthx-of-span-words
   (implies (and (natp q) (natp e) (natp j) (< j 16))
            (equal (fn-b3-nthx j (fn-b3-words 16 (fn-b3-firstn (- e q) (fn-b3-nthcdrx q (fn-b3s-msg s)))))
                   (fn-b3s-word (+ q (* 4 j)) e s)))))

(local (in-theory (disable fn-b3s-word fn-b3s-nthx-of-words)))

(defthm fn-b3s-block-is-compress
  (implies (and (natp q) (natp e))
           (equal (fn-b3s-block c0 c1 c2 c3 c4 c5 c6 c7 q e counter blen fl s)
                  (fn-b3-compress (list c0 c1 c2 c3 c4 c5 c6 c7)
                                  (fn-b3-words 16 (fn-b3-firstn (- e q) (fn-b3-nthcdrx q (fn-b3s-msg s))))
                                  counter blen fl)))
  :hints (("Goal" :in-theory (e/d (fn-b3-compress) (fn-b3-compress-core)))))

(in-theory (disable fn-b3s-block))

; -----------------------------------------------------------------------------
; The chunk.  FINISH is the last compression of a node's output, with ROOTFL
; added to its flags: below the root (ROOTFL 0) the chaining value
; `fn-b3-output-cv' computes.

(defun fn-b3s-finish (out rootfl)
  (declare (xargs :guard (natp rootfl)))
  (fn-b3-compress (fn-b3-nthx 0 out) (fn-b3-nthx 1 out) (fn-b3-nthx 2 out) (fn-b3-nthx 3 out)
                  (if (zp rootfl)
                      (fn-b3-nthx 4 out)
                    (logior (ifix (fn-b3-nthx 4 out)) rootfl))))

(defthm fn-b3s-finish-of-zero-is-output-cv
  (equal (fn-b3s-finish out 0) (fn-b3-output-cv out))
  :hints (("Goal" :in-theory (enable fn-b3-output-cv))))

(local
 (defthm fn-b3s-chunk-exec-base
   (implies (and (natp q) (natp e) (not (< 64 (- e q))))
            (equal (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
                   (fn-b3s-block c0 c1 c2 c3 c4 c5 c6 c7 q e counter (nfix (- e q))
                                 (if (zp rootfl)
                                     (logior (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)) *fn-b3-chunk-end*)
                                   (logior (logior (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)) *fn-b3-chunk-end*) rootfl))
                                 s)))
   :hints (("Goal" :expand ((fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s))))))

(local
 (defthm fn-b3s-chunk-exec-step
   (implies (and (natp q) (natp e) (< 64 (- e q)))
            (equal (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
                   (let ((b (fn-b3s-block c0 c1 c2 c3 c4 c5 c6 c7 q e counter 64
                                          (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)) s)))
                     (fn-b3s-chunk (mv-nth 0 b) (mv-nth 1 b) (mv-nth 2 b) (mv-nth 3 b)
                                   (mv-nth 4 b) (mv-nth 5 b) (mv-nth 6 b) (mv-nth 7 b)
                                   (+ 64 q) e counter flags nil rootfl s))))
   :hints (("Goal" :expand ((fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s))))))

(local
 (defthm fn-b3s-chunk-model-base
   (implies (not (< 64 (len x)))
            (equal (fn-b3-chunk cv x counter flags startp)
                   (fn-b3-output (fn-b3-cv8 cv)
                     (fn-b3-words 16 x)
                     counter (len x)
                     (logior (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)) *fn-b3-chunk-end*))))
   :hints (("Goal" :expand ((fn-b3-chunk cv x counter flags startp))))))

(local
 (defthm fn-b3s-chunk-model-step
   (implies (< 64 (len x))
            (equal (fn-b3-chunk cv x counter flags startp)
                   (fn-b3-chunk (fn-b3-compress cv (fn-b3-words 16 x) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))
                                (fn-b3-nthcdrx 64 x) counter flags nil)))
   :hints (("Goal" :expand ((fn-b3-chunk cv x counter flags startp))))))

(local
 (defthm fn-b3s-compress-of-cv8
   (equal (fn-b3-compress (list (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv) (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv)) words counter blen flags)
          (fn-b3-compress cv words counter blen flags))
   :hints (("Goal" :in-theory (enable fn-b3-compress)))))

(local
 (defthm fn-b3s-chunk-of-cv8
   (equal (fn-b3-chunk (list (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv) (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv)) x counter flags startp)
          (fn-b3-chunk cv x counter flags startp))
   :hints (("Goal" :cases ((< 64 (len x)))
            :in-theory (disable (:d fn-b3-chunk))))))

(local
 (defthm fn-b3s-mv-nths-of-compress
   (equal (list (mv-nth 0 (fn-b3-compress cv w c b f)) (mv-nth 1 (fn-b3-compress cv w c b f))
                (mv-nth 2 (fn-b3-compress cv w c b f)) (mv-nth 3 (fn-b3-compress cv w c b f))
                (mv-nth 4 (fn-b3-compress cv w c b f)) (mv-nth 5 (fn-b3-compress cv w c b f))
                (mv-nth 6 (fn-b3-compress cv w c b f)) (mv-nth 7 (fn-b3-compress cv w c b f)))
          (fn-b3-compress cv w c b f))
   :hints (("Goal" :in-theory (enable fn-b3-compress mv-nth)))))

(local
 (defthm fn-b3s-chunk-of-mv-nths
   (equal (fn-b3-chunk (list (mv-nth 0 (fn-b3-compress cv w c b f)) (mv-nth 1 (fn-b3-compress cv w c b f))
                             (mv-nth 2 (fn-b3-compress cv w c b f)) (mv-nth 3 (fn-b3-compress cv w c b f))
                             (mv-nth 4 (fn-b3-compress cv w c b f)) (mv-nth 5 (fn-b3-compress cv w c b f))
                             (mv-nth 6 (fn-b3-compress cv w c b f)) (mv-nth 7 (fn-b3-compress cv w c b f)))
                       x counter flags startp)
          (fn-b3-chunk (fn-b3-compress cv w c b f) x counter flags startp))
   :hints (("Goal" :in-theory (disable fn-b3s-mv-nths-of-compress)
            :use fn-b3s-mv-nths-of-compress))))

(local
 (defthm fn-b3s-len-of-span
   (implies (and (natp q) (natp e) (<= q e) (<= e (len m)))
            (equal (len (fn-b3-firstn (- e q) (fn-b3-nthcdrx q m)))
                   (- e q)))))

(defthm fn-b3s-chunk-base
  (implies (and (natp q) (natp e) (<= q e) (<= e (len (fn-b3s-msg s)))
                (not (< 64 (- e q))))
           (equal (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
                  (fn-b3s-finish (fn-b3-chunk (list c0 c1 c2 c3 c4 c5 c6 c7)
                                              (fn-b3-firstn (- e q) (fn-b3-nthcdrx q (fn-b3s-msg s)))
                                              counter flags startp)
                                 rootfl)))
  :hints (("Goal" :in-theory (disable fn-b3s-chunk fn-b3-chunk fn-b3-compress-core))))

(defthm fn-b3s-chunk-is-chunk
  (implies (and (natp q) (natp e) (<= q e) (<= e (len (fn-b3s-msg s))))
           (equal (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
                  (fn-b3s-finish (fn-b3-chunk (list c0 c1 c2 c3 c4 c5 c6 c7)
                                              (fn-b3-firstn (- e q) (fn-b3-nthcdrx q (fn-b3s-msg s)))
                                              counter flags startp)
                                 rootfl)))
  :hints (("Goal" :induct (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
           :in-theory (disable fn-b3s-finish fn-b3-compress-core (:d fn-b3s-chunk) (:d fn-b3-chunk)))))

; -----------------------------------------------------------------------------
; The node.

(local
 (defthm fn-b3s-nthx-of-append
   (equal (fn-b3-nthx i (append p w))
          (if (< (nfix i) (len p))
              (fn-b3-nthx i p)
            (fn-b3-nthx (- (nfix i) (len p)) w)))
   :hints (("Goal" :induct (fn-b3-nthx i p) :in-theory (enable fn-b3-nthx)))))

(local
 (defthm fn-b3s-output-cv-of-output
   (equal (fn-b3-output-cv (fn-b3-output cv w c b f))
          (fn-b3-compress cv w c b f))
   :hints (("Goal" :in-theory (enable fn-b3-output-cv)))))

(local
 (defthm fn-b3s-output-root-of-output
   (equal (fn-b3-output-root (fn-b3-output cv w c b f))
          (fn-b3-words-octets (fn-b3-compress cv w 0 b (logior (ifix f) *fn-b3-root*))))
   :hints (("Goal" :in-theory (enable fn-b3-output-root)))))

(local
 (defthm fn-b3s-node-exec-base
   (implies (and (natp s0) (natp e) (not (< 1024 (- e s0))))
            (equal (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)
                   (fn-b3s-chunk k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags t 0 s)))
   :hints (("Goal" :expand ((fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s))))))

(defun fn-b3s-parent-cv (k0 k1 k2 k3 k4 k5 k6 k7 nl nr f)
  ; A parent's compression of its children's chaining values NL and NR (the
  ; logical form of the mv-lets of `fn-b3s-node' and `fn-b3s-root').
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (o0 o1 o2 o3 o4 o5 o6 o7)
    (fn-b3-compress-core k0 k1 k2 k3 k4 k5 k6 k7
                         (mv-nth 0 nl) (mv-nth 1 nl) (mv-nth 2 nl) (mv-nth 3 nl)
                         (mv-nth 4 nl) (mv-nth 5 nl) (mv-nth 6 nl) (mv-nth 7 nl)
                         (mv-nth 0 nr) (mv-nth 1 nr) (mv-nth 2 nr) (mv-nth 3 nr)
                         (mv-nth 4 nr) (mv-nth 5 nr) (mv-nth 6 nr) (mv-nth 7 nr)
                         0 64 f)
    (list o0 o1 o2 o3 o4 o5 o6 o7)))

(local
 (defthm fn-b3s-parent-step
   (implies (and (equal (len cl) 8) (equal (len cr) 8))
            (equal (fn-b3s-parent-cv k0 k1 k2 k3 k4 k5 k6 k7 cl cr f)
                   (fn-b3-compress (list k0 k1 k2 k3 k4 k5 k6 k7) (append cl cr) 0 64 f)))
   :hints (("Goal" :in-theory (e/d (fn-b3-compress) (fn-b3-compress-core))))))

(local
 (defthm fn-b3s-node-exec-step
   (implies (and (natp s0) (natp e) (< 1024 (- e s0)))
            (equal (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)
                   (let* ((lc (fn-b3-left-chunks 1 (- e s0)))
                          (ll (* 1024 lc)))
                     (fn-b3s-parent-cv k0 k1 k2 k3 k4 k5 k6 k7
                                       (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 (+ s0 ll) counter flags s)
                                       (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 (+ s0 ll) e (+ (nfix counter) lc) flags s)
                                       (logior (ifix flags) *fn-b3-parent*)))))
   :hints (("Goal" :expand ((fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s))
            :in-theory (disable fn-b3-compress-core fn-b3s-node fn-b3s-chunk fn-b3-left-chunks)))))

(in-theory (disable fn-b3s-parent-cv))

(local
 (defthm fn-b3s-node-model-base
   (implies (not (< 1024 (len x)))
            (equal (fn-b3-node key x counter flags)
                   (fn-b3-chunk key x counter flags t)))
   :hints (("Goal" :expand ((fn-b3-node key x counter flags))))))

(local
 (defthm fn-b3s-node-model-step
   (implies (< 1024 (len x))
            (equal (fn-b3-node key x counter flags)
                   (let* ((lc (fn-b3-left-chunks 1 (len x)))
                          (ll (* 1024 lc)))
                     (fn-b3-output key
                                   (append (fn-b3-output-cv
                                            (fn-b3-node key (fn-b3-firstn ll x) counter flags))
                                           (fn-b3-output-cv
                                            (fn-b3-node key (fn-b3-nthcdrx ll x)
                                                        (+ (nfix counter) lc) flags)))
                                   0 64 (logior (ifix flags) *fn-b3-parent*)))))
   :hints (("Goal" :expand ((fn-b3-node key x counter flags))))))

(local
 (defthm fn-b3s-len-of-block
   (equal (len (fn-b3s-block c0 c1 c2 c3 c4 c5 c6 c7 q e counter blen fl s)) 8)
   :hints (("Goal" :in-theory (e/d (fn-b3s-block) (fn-b3-compress-core))))))

(local
 (defthm fn-b3s-len-of-chunk
   (equal (len (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)) 8)
   :hints (("Goal" :induct (fn-b3s-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp rootfl s)
            :in-theory (e/d () (fn-b3s-block-is-compress))))))

(local
 (defthm fn-b3s-len-of-parent-cv
   (equal (len (fn-b3s-parent-cv k0 k1 k2 k3 k4 k5 k6 k7 nl nr f)) 8)
   :hints (("Goal" :in-theory (e/d (fn-b3s-parent-cv) (fn-b3-compress-core))))))

(local
 (defthm fn-b3s-len-of-node
   (equal (len (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)) 8)
   :hints (("Goal" :induct (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)
            :in-theory (disable fn-b3s-chunk fn-b3s-chunk-is-chunk fn-b3s-chunk-base fn-b3-left-chunks)))))

(defthm fn-b3s-node-is-node
  (implies (and (natp s0) (natp e) (<= s0 e) (<= e (len (fn-b3s-msg s))) (natp counter))
           (equal (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)
                  (fn-b3-output-cv
                   (fn-b3-node (list k0 k1 k2 k3 k4 k5 k6 k7)
                               (fn-b3-firstn (- e s0) (fn-b3-nthcdrx s0 (fn-b3s-msg s)))
                               counter flags))))
  :hints (("Goal" :induct (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 s0 e counter flags s)
           :in-theory (disable fn-b3s-finish fn-b3-compress-core (:d fn-b3s-node) (:d fn-b3-node)
                               (:d fn-b3s-chunk) (:d fn-b3-chunk) fn-b3s-mv-nth-is-nthx fn-b3-left-chunks
                               binary-logior fn-b3-output))))

; -----------------------------------------------------------------------------
; The root: THE KEYSTONE.

(local
 (defthm fn-b3s-nthx-2-of-chunk
   (equal (fn-b3-nthx 2 (fn-b3-chunk cv x counter flags startp))
          counter)
   :hints (("Goal" :induct (fn-b3-chunk cv x counter flags startp)
            :in-theory (enable fn-b3-nthx)))))

(local
 (defthm fn-b3s-true-listp-of-nthcdrx
   (implies (true-listp l) (true-listp (fn-b3-nthcdrx k l)))
   :hints (("Goal" :in-theory (enable fn-b3-nthcdrx)))))

(local
 (defthm fn-b3s-root-exec
   (equal (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 flags s)
          (if (< 1024 (length s))
              (let* ((lc (fn-b3-left-chunks 1 (length s)))
                     (ll (* 1024 lc)))
                (fn-b3s-parent-cv k0 k1 k2 k3 k4 k5 k6 k7
                                  (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 0 ll 0 flags s)
                                  (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 ll (length s) lc flags s)
                                  (logior (logior (ifix flags) *fn-b3-parent*) *fn-b3-root*)))
            (fn-b3s-chunk k0 k1 k2 k3 k4 k5 k6 k7 0 (length s) 0 flags t *fn-b3-root* s)))
   :hints (("Goal" :in-theory (union-theories '(fn-b3s-root fn-b3s-parent-cv)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-b3s-finish-of-root
   (implies (equal (fn-b3-nthx 2 out) 0)
            (equal (fn-b3-words-octets (fn-b3s-finish out *fn-b3-root*))
                   (fn-b3-output-root out)))
   :hints (("Goal" :in-theory (enable fn-b3-output-root)))))

(local
 (defthm fn-b3s-firstn-of-msg-rest
   (implies (and (stringp s) (natp k) (<= k (len (coerce s 'list))))
            (equal (fn-b3-firstn (+ (len (coerce s 'list)) (- k)) (fn-b3-nthcdrx k (fn-b3s-msg s)))
                   (fn-b3-nthcdrx k (fn-b3s-msg s))))
   :hints (("Goal" :use ((:instance fn-b3s-firstn-of-len
                                    (n (+ (len (coerce s 'list)) (- k)))
                                    (l (fn-b3-nthcdrx k (fn-b3s-msg s)))))
            :in-theory (disable fn-b3s-firstn-of-len)))))

(defthm fn-b3s-root-is-hash
  (implies (stringp s)
           (equal (fn-b3-words-octets (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 flags s))
                  (fn-b3-hash (list k0 k1 k2 k3 k4 k5 k6 k7) flags (fn-b3s-msg s))))
  :hints (("Goal" :in-theory (e/d (fn-b3-hash)
                                  (fn-b3-compress-core fn-b3s-node fn-b3-node fn-b3s-chunk fn-b3-chunk
                                   fn-b3-words-octets fn-b3s-finish fn-b3-left-chunks binary-logior
                                   fn-b3-output fn-b3s-mv-nth-is-nthx))
           :cases ((< 1024 (length s))))))

(defthm fn-b3s-root-shape
  (and (true-listp (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 flags s))
       (equal (len (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 flags s)) 8))
  :hints (("Goal" :in-theory (disable fn-b3s-node fn-b3s-chunk fn-b3s-parent-cv fn-b3-left-chunks
                                      fn-b3s-chunk-is-chunk fn-b3s-chunk-base)
                  :use ((:instance fn-b3s-len-of-chunk (c0 k0) (c1 k1) (c2 k2) (c3 k3) (c4 k4) (c5 k5) (c6 k6) (c7 k7)
                                   (q 0) (e (length s)) (counter 0) (startp t) (rootfl *fn-b3-root*))
                        (:instance fn-b3s-len-of-parent-cv
                                   (nl (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 0 (* 1024 (fn-b3-left-chunks 1 (length s))) 0 flags s))
                                   (nr (fn-b3s-node k0 k1 k2 k3 k4 k5 k6 k7 (* 1024 (fn-b3-left-chunks 1 (length s))) (length s)
                                                    (fn-b3-left-chunks 1 (length s)) flags s))
                                   (f (logior (logior (ifix flags) *fn-b3-parent*) *fn-b3-root*)))))))

; Its words reassembled from their octets (books/msgid-pages-exec reads the
; first eight octets as a natural): a fact about `mod' and `floor' alone.
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-b3s-a1 (implies (natp x) (equal (+ (mod x 256) (* 256 (floor x 256))) x)))
   (defthm fn-b3s-a2 (implies (natp x) (equal (floor (floor x 256) 256) (floor x 65536))))
   (defthm fn-b3s-a3 (implies (natp x) (equal (floor (floor x 65536) 256) (floor x 16777216))))
   (defthm fn-b3s-a4 (implies (and (natp x) (< x 4294967296)) (equal (mod (floor x 16777216) 256) (floor x 16777216))))
   (defthm fn-b3s-a5 (implies (natp x) (natp (floor x 256))) :rule-classes :type-prescription)
   (defthm fn-b3s-a6 (implies (natp x) (natp (floor x 65536))) :rule-classes :type-prescription)))

(defthm fn-b3s-word-of-octets
  (implies (unsigned-byte-p 32 w)
           (equal (+ (mod w 256) (* 256 (mod (floor w 256) 256)) (* 65536 (mod (floor w 65536) 256)) (* 16777216 (mod (floor w 16777216) 256)))
                  w))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (floor mod fn-b3s-a1 fn-b3s-a2 fn-b3s-a3))
           :use ((:instance fn-b3s-a1 (x w))
                 (:instance fn-b3s-a1 (x (floor w 256)))
                 (:instance fn-b3s-a1 (x (floor w 65536)))
                 (:instance fn-b3s-a2 (x w))
                 (:instance fn-b3s-a3 (x w))))))

(in-theory (disable fn-b3s-word-of-octets))

(deftheory fn-b3s-internals
  '(fn-b3s-byte fn-b3s-word fn-b3s-block fn-b3s-chunk fn-b3s-node fn-b3s-root fn-b3s-finish
    fn-b3s-block-is-compress fn-b3s-chunk-base fn-b3s-chunk-is-chunk fn-b3s-node-is-node
    fn-b3s-finish-of-zero-is-output-cv))

(in-theory (disable fn-b3s-internals))
