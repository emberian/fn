;; fn: BLAKE3 over the octet buffer, read by index: the executable twin of
;; books/blake3.lisp (D27: the served path never builds an octet list).
;;
;; What this book is.  The message is a short list PREFIX followed by a window
;; of WN octets at A in the octet buffer `fn-octets' (books/octets-stobj.lisp):
;; the shape of every digest fn takes -- a frame's protected prefix before its
;; payload, a subject preimage's head before the article, a log entry in the
;; file read into one buffer.  The octet at message position I is the
;; prefix's below its length and the buffer's cell A + I - LP above it
;; (`fn-b3x-byte'); a node of the tree is a span [S, E) of positions; a chunk
;; runs its blocks with the chaining value in eight multiple values, reading
;; each block's sixteen words straight from the buffer into the compression
;; function, so a chunk conses only its final output (8 + 16 words per 1024
;; octets).  The compression function, the output and the tree's split are
;; books/blake3.lisp's own functions; only the reading of the message is new.
;;
;; What is proved.  `fn-b3x-hash-is-hash' (the keystone): the buffer hash of
;; PREFIX and the window is `fn-b3-hash' of the octets of
;; (append PREFIX window), with no hypothesis beyond the window lying in the
;; buffer.  It is the correspondence of the two readers, level by level: the
;; octet (`fn-b3x-byte-is-nthx'), the words of a block
;; (`fn-b3x-words-is-words'), the chunk (`fn-b3x-chunk-is-chunk'), the node
;; (`fn-b3x-node-is-node').  The three entry points follow:
;; `fn-blake3-of-prefixed-range' (a window), `fn-blake3-of-prefixed-buffer'
;; (the whole buffer) and `fn-blake3-stobj' (any object, copied once into a
;; local buffer: an array of octets, not a list), each equal to `fn-blake3'
;; (`fn-blake3-stobj-is-blake3' and the two others).

(in-package "ACL2")
(include-book "blake3")
(include-book "octets-stobj")
(include-book "octet-window")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (e/d (fn-shr-win) (floor mod truncate rem unsigned-byte-p mv-nth))))

; -----------------------------------------------------------------------------
; The logical message: the prefix, then the window.

(defun fn-b3x-msg (prefix a wn l)
  (declare (xargs :guard t :verify-guards nil))
  (fn-b3-fix-octets (append prefix (fn-shr-win a wn l))))

; -----------------------------------------------------------------------------
; The reader.  Positions at and past the node's end E read as zero: the zero
; padding of a short last block, which the list model gets from `fn-b3-nthx'
; past the end of the node's octets.

(defun fn-b3x-byte (i e prefix lp a fn-octets)
  (declare (type (integer 0 *) i e lp a)
           (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (<= (+ a (- e lp)) (fn-octets-len fn-octets)))))
  (cond ((<= e i) 0)
        ((< i lp) (fn-b3-octet (nth i prefix)))
        (t (mbe :logic (fn-b3-byte (fn-octets-get (+ a (- i lp)) fn-octets))
                :exec (fn-octets-get (+ a (- i lp)) fn-octets)))))

(defun fn-b3x-word (p e prefix lp a fn-octets)
  ; The little-endian word of the four octets at P.
  (declare (type (integer 0 *) p e lp a)
           (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (<= (+ a (- e lp)) (fn-octets-len fn-octets)))))
  (fn-b3-le-word (fn-b3x-byte p e prefix lp a fn-octets)
                 (fn-b3x-byte (+ p 1) e prefix lp a fn-octets)
                 (fn-b3x-byte (+ p 2) e prefix lp a fn-octets)
                 (fn-b3x-byte (+ p 3) e prefix lp a fn-octets)))

(defun fn-b3x-words (k p e prefix lp a fn-octets)
  ; K words from P, as a list: a chunk's LAST block only.
  (declare (type (integer 0 *) p e lp a)
           (xargs :stobjs fn-octets
                  :guard (and (natp k) (true-listp prefix) (= lp (len prefix))
                              (<= (+ a (- e lp)) (fn-octets-len fn-octets)))
                  :measure (nfix k)))
  (if (zp k)
      nil
    (cons (fn-b3x-word p e prefix lp a fn-octets)
          (fn-b3x-words (- k 1) (+ p 4) e prefix lp a fn-octets))))

; -----------------------------------------------------------------------------
; A chunk: the octets [Q, E), the chaining value in C0..C7.

(defun fn-b3x-chunk (c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets)
  (declare (type (integer 0 *) q e lp a)
           (xargs :stobjs fn-octets
                  :guard (and (natp counter) (natp flags) (<= q e)
                              (true-listp prefix) (= lp (len prefix))
                              (<= (+ a (- e lp)) (fn-octets-len fn-octets)))
                  :measure (nfix (- e q))))
  (let ((fl (logior (ifix flags) (if startp *fn-b3-chunk-start* 0))))
    (if (and (mbt (and (natp q) (natp e))) (< 64 (- e q)))
        (mv-let (c0 c1 c2 c3 c4 c5 c6 c7)
          (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7
                               (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ q 4) e prefix lp a fn-octets) (fn-b3x-word (+ q 8) e prefix lp a fn-octets) (fn-b3x-word (+ q 12) e prefix lp a fn-octets) (fn-b3x-word (+ q 16) e prefix lp a fn-octets) (fn-b3x-word (+ q 20) e prefix lp a fn-octets) (fn-b3x-word (+ q 24) e prefix lp a fn-octets) (fn-b3x-word (+ q 28) e prefix lp a fn-octets) (fn-b3x-word (+ q 32) e prefix lp a fn-octets) (fn-b3x-word (+ q 36) e prefix lp a fn-octets) (fn-b3x-word (+ q 40) e prefix lp a fn-octets) (fn-b3x-word (+ q 44) e prefix lp a fn-octets) (fn-b3x-word (+ q 48) e prefix lp a fn-octets) (fn-b3x-word (+ q 52) e prefix lp a fn-octets) (fn-b3x-word (+ q 56) e prefix lp a fn-octets) (fn-b3x-word (+ q 60) e prefix lp a fn-octets)
                               counter 64 fl)
          (fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 (+ q 64) e counter flags nil prefix lp a fn-octets))
      (fn-b3-output (list c0 c1 c2 c3 c4 c5 c6 c7)
                    (fn-b3x-words 16 q e prefix lp a fn-octets)
                    counter (nfix (- e q))
                    (logior fl *fn-b3-chunk-end*)))))

; -----------------------------------------------------------------------------
; A node: the octets [S, E), split as books/blake3.lisp `fn-b3-node' splits.

(defun fn-b3x-node (key s e counter flags prefix lp a fn-octets)
  (declare (type (integer 0 *) s e lp a)
           (xargs :stobjs fn-octets
                  :guard (and (natp counter) (natp flags) (<= s e)
                              (true-listp prefix) (= lp (len prefix))
                              (<= (+ a (- e lp)) (fn-octets-len fn-octets)))
                  :measure (nfix (- e s))))
  (if (and (mbt (and (natp s) (natp e))) (< 1024 (- e s)))
      (let* ((lc (fn-b3-left-chunks 1 (- e s)))
             (ll (* 1024 lc)))
        (fn-b3-output key
                      (append (fn-b3-output-cv
                               (fn-b3x-node key s (+ s ll) counter flags prefix lp a fn-octets))
                              (fn-b3-output-cv
                               (fn-b3x-node key (+ s ll) e (+ (nfix counter) lc) flags prefix lp a fn-octets)))
                      0 64 (logior (ifix flags) *fn-b3-parent*)))
    (fn-b3x-chunk (fn-b3-nthx 0 key) (fn-b3-nthx 1 key) (fn-b3-nthx 2 key) (fn-b3-nthx 3 key) (fn-b3-nthx 4 key) (fn-b3-nthx 5 key) (fn-b3-nthx 6 key) (fn-b3-nthx 7 key)
                  s e counter flags t prefix lp a fn-octets)))

(defun fn-b3x-hash (key flags prefix a wn fn-octets)
  ; The root output of PREFIX followed by the WN octets at A.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp flags) (true-listp prefix) (natp a) (natp wn)
                              (<= (+ a wn) (fn-octets-len fn-octets)))))
  (let ((lp (len prefix)))
    (fn-b3-output-root (fn-b3x-node key 0 (+ lp wn) 0 flags prefix lp a fn-octets))))


; =============================================================================
; The correspondence.  Every level is stated against the logical message
; `fn-b3x-msg0' (the prefix, then the buffer from A to its end), and a node's
; octets are the span [S, E) of it: `(fn-b3-firstn (- e s) (fn-b3-nthcdrx s
; msg0))'.  The step and base cases of the chunk and the node are proved
; apart and the induction only composes them: a single induction that opens
; both definitions spends minutes clausifying the mv-let of sixteen word
; reads (measured: 126 s at 228 prover steps).

(defun fn-b3x-msg0 (prefix a l)
  (declare (xargs :guard t :verify-guards nil))
  (fn-b3-fix-octets (append prefix (fn-b3-nthcdrx a l))))

(local
 (defthm fn-b3x-nthx-of-fix-octets
   (equal (fn-b3-nthx i (fn-b3-fix-octets l))
          (fn-b3-octet (fn-b3-nthx i l)))
   :hints (("Goal" :in-theory (enable fn-b3-octet fn-b3-fix-octets)
            :induct (fn-b3-nthx i l)))))

(local
 (defthm fn-b3x-nthx-of-append
   (equal (fn-b3-nthx i (append p w))
          (if (< (nfix i) (len p))
              (fn-b3-nthx i p)
            (fn-b3-nthx (- (nfix i) (len p)) w)))
   :hints (("Goal" :induct (fn-b3-nthx i p)))))

(local
 (defthm fn-b3x-nthx-of-nthcdrx
   (equal (fn-b3-nthx j (fn-b3-nthcdrx a l))
          (fn-b3-nthx (+ (nfix a) (nfix j)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx a l)))))

(local
 (defthm fn-b3x-nthx-is-nth
   (implies (< (nfix i) (len p))
            (equal (fn-b3-nthx i p) (nth i p)))
   :hints (("Goal" :induct (fn-b3-nthx i p)))))

(local
 (defthm fn-b3x-byte-of-nth
   (implies (natp k)
            (equal (fn-b3-byte (nth k l))
                   (fn-b3-octet (fn-b3-nthx k l))))
   :hints (("Goal" :induct (fn-b3-nthx k l)
            :in-theory (enable fn-b3-octet fn-b3-byte)))))

(local (in-theory (disable fn-b3x-nthx-is-nth)))

(local
 (defthm fn-b3x-octet-of-nth
   (implies (natp k)
            (equal (fn-b3-octet (nth k l))
                   (fn-b3-octet (fn-b3-nthx k l))))
   :hints (("Goal" :use fn-b3x-byte-of-nth
            :in-theory (e/d (fn-b3-octet) (fn-b3x-byte-of-nth))))))

(local (in-theory (disable fn-b3-fix-octets)))

(defthm fn-b3x-byte-is-nthx
  (implies (and (natp i) (natp e) (natp a) (equal lp (len prefix)))
           (equal (fn-b3x-byte i e prefix lp a fn-octets)
                  (if (< i e) (fn-b3-nthx i (fn-b3x-msg0 prefix a fn-octets)) 0))))

(local
 (defthm fn-b3x-nthx-of-firstn
   (equal (fn-b3-nthx j (fn-b3-firstn n l))
          (if (< (nfix j) (nfix n)) (fn-b3-nthx j l) 0))
   :hints (("Goal" :induct (list (fn-b3-nthx j l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3x-nthcdrx-of-firstn
   (equal (fn-b3-nthcdrx k (fn-b3-firstn n l))
          (fn-b3-firstn (- (nfix n) (nfix k)) (fn-b3-nthcdrx k l)))
   :hints (("Goal" :induct (list (fn-b3-nthcdrx k l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3x-nthcdrx-of-nthcdrx
   (equal (fn-b3-nthcdrx k (fn-b3-nthcdrx p l))
          (fn-b3-nthcdrx (+ (nfix k) (nfix p)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx p l)))))

(local
 (defthm fn-b3x-firstn-of-firstn
   (implies (<= (nfix k) (nfix n))
            (equal (fn-b3-firstn k (fn-b3-firstn n l))
                   (fn-b3-firstn k l)))
   :hints (("Goal" :induct (list (fn-b3-firstn k l) (fn-b3-firstn n l))))))

(local (in-theory (disable fn-b3-nthx fn-b3-nthcdrx fn-b3-firstn)))

(local
 (defthm fn-b3x-firstn-of-nonpositive
   (implies (and (integerp n) (<= n 0))
            (equal (fn-b3-firstn n l) nil))
   :hints (("Goal" :in-theory (enable fn-b3-firstn)))))

(defthm fn-b3x-words-is-words
  (implies (and (natp p) (natp e) (natp a) (equal lp (len prefix)))
           (equal (fn-b3x-words k p e prefix lp a fn-octets)
                  (fn-b3-words k (fn-b3-firstn (- e p)
                                               (fn-b3-nthcdrx p (fn-b3x-msg0 prefix a fn-octets))))))
  :hints (("Goal" :induct (fn-b3x-words k p e prefix lp a fn-octets)
           :expand ((:free (x) (fn-b3-words k x)))
           :in-theory (disable fn-b3x-msg0))))

(local
 (defthm fn-b3x-nthx-of-cons
   (equal (fn-b3-nthx i (cons x y))
          (if (zp (nfix i)) x (fn-b3-nthx (- (nfix i) 1) y)))
   :hints (("Goal" :in-theory (enable fn-b3-nthx)))))

(local
 (defun fn-b3x-ind-words (j k x)
   (declare (xargs :measure (nfix k)))
   (if (zp (nfix k)) (list j x)
     (fn-b3x-ind-words (- (nfix j) 1) (- (nfix k) 1) (fn-b3-nthcdrx 4 x)))))

(local
 (defthm fn-b3x-nthx-of-non-cons
   (implies (not (consp x)) (equal (fn-b3-nthx i x) 0))
   :hints (("Goal" :in-theory (enable fn-b3-nthx)))))

(local
 (defthm fn-b3x-nthx-of-words
   (implies (natp j)
            (equal (fn-b3-nthx j (fn-b3-words k x))
                   (if (< j (nfix k))
                       (fn-b3-le-word (fn-b3-nthx (* 4 j) x) (fn-b3-nthx (+ 1 (* 4 j)) x)
                                      (fn-b3-nthx (+ 2 (* 4 j)) x) (fn-b3-nthx (+ 3 (* 4 j)) x))
                     0)))
   :hints (("Goal" :induct (fn-b3x-ind-words j k x)
            :expand ((fn-b3-words k x))))))

(local
 (defun fn-b3x-ind-xwords (j k p)
   (declare (xargs :measure (nfix k)))
   (if (zp (nfix k)) (list j p)
     (fn-b3x-ind-xwords (- (nfix j) 1) (- (nfix k) 1) (+ p 4)))))

(defthm fn-b3x-nthx-of-xwords
  (implies (and (natp j) (natp p))
           (equal (fn-b3-nthx j (fn-b3x-words k p e prefix lp a fn-octets))
                  (if (< j (nfix k)) (fn-b3x-word (+ p (* 4 j)) e prefix lp a fn-octets) 0)))
  :hints (("Goal" :induct (fn-b3x-ind-xwords j k p)
           :in-theory (disable fn-b3x-word fn-b3x-words-is-words)
           :expand ((fn-b3x-words k p e prefix lp a fn-octets)))))

(defthm fn-b3x-words-of-msg0
  (implies (and (natp q) (natp n) (natp a))
           (equal (fn-b3-words k (fn-b3-firstn n (fn-b3-nthcdrx q (fn-b3x-msg0 prefix a fn-octets))))
                  (fn-b3x-words k q (+ q n) prefix (len prefix) a fn-octets)))
  :hints (("Goal" :use ((:instance fn-b3x-words-is-words (p q) (e (+ q n)) (lp (len prefix))))
           :in-theory (disable fn-b3x-words-is-words))))

(local (in-theory (disable fn-b3x-words-is-words fn-b3x-word)))

(defthm fn-b3x-compress-step
  (implies (and (natp q) (natp e) (equal lp (len prefix)))
           (equal (fn-b3-compress (list c0 c1 c2 c3 c4 c5 c6 c7)
                                  (fn-b3x-words 16 q e prefix lp a fn-octets)
                                  counter blen fl)
                  (list (mv-nth 0 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 1 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 2 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 3 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 4 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 5 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 6 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)) (mv-nth 7 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter blen fl)))))
  :hints (("Goal" :in-theory (enable fn-b3-compress))))

(local
 (defthm fn-b3x-len-of-span
   (implies (and (natp q) (natp e) (natp a) (<= e (len (fn-b3x-msg0 prefix a fn-octets))))
            (equal (len (fn-b3-firstn (- e q) (fn-b3-nthcdrx q (fn-b3x-msg0 prefix a fn-octets))))
                   (nfix (- e q))))
   :hints (("Goal" :in-theory (disable fn-b3x-msg0)))))

(local
 (defthm fn-b3x-chunk-exec-base
   (implies (and (natp q) (natp e) (not (< 64 (- e q))))
            (equal (fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets)
                   (fn-b3-output (list c0 c1 c2 c3 c4 c5 c6 c7)
                     (fn-b3x-words 16 q e prefix lp a fn-octets)
                     counter (nfix (- e q))
                     (logior (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)) *fn-b3-chunk-end*))))
   :hints (("Goal" :expand ((fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets))
            :in-theory (disable fn-b3x-msg0 fn-b3-compress-core)))))

(local
 (defthm fn-b3x-chunk-model-base
   (implies (not (< 64 (len x)))
            (equal (fn-b3-chunk cv x counter flags startp)
                   (fn-b3-output (fn-b3-cv8 cv)
                     (fn-b3-words 16 x)
                     counter (len x)
                     (logior (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)) *fn-b3-chunk-end*))))
   :hints (("Goal" :expand ((fn-b3-chunk cv x counter flags startp))))))

(defthm fn-b3x-chunk-base
  (implies (and (natp q) (natp e) (natp a) (equal lp (len prefix))
                (<= e (len (fn-b3x-msg0 prefix a fn-octets)))
                (<= q e) (not (< 64 (- e q))))
           (equal (fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets)
                  (fn-b3-chunk (list c0 c1 c2 c3 c4 c5 c6 c7)
                               (fn-b3-firstn (- e q)
                                             (fn-b3-nthcdrx q (fn-b3x-msg0 prefix a fn-octets)))
                               counter flags startp)))
  :hints (("Goal" :in-theory (disable fn-b3x-msg0 fn-b3-compress-core fn-b3x-chunk fn-b3-chunk))))

(local
 (defthm fn-b3x-chunk-exec-step
   (implies (and (natp q) (natp e) (< 64 (- e q)))
            (equal (fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets)
                   (fn-b3x-chunk (mv-nth 0 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 1 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 2 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 3 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 4 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 5 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 6 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))) (mv-nth 7 (fn-b3-compress-core c0 c1 c2 c3 c4 c5 c6 c7 (fn-b3x-word q e prefix lp a fn-octets) (fn-b3x-word (+ 4 q) e prefix lp a fn-octets) (fn-b3x-word (+ 8 q) e prefix lp a fn-octets) (fn-b3x-word (+ 12 q) e prefix lp a fn-octets) (fn-b3x-word (+ 16 q) e prefix lp a fn-octets) (fn-b3x-word (+ 20 q) e prefix lp a fn-octets) (fn-b3x-word (+ 24 q) e prefix lp a fn-octets) (fn-b3x-word (+ 28 q) e prefix lp a fn-octets) (fn-b3x-word (+ 32 q) e prefix lp a fn-octets) (fn-b3x-word (+ 36 q) e prefix lp a fn-octets) (fn-b3x-word (+ 40 q) e prefix lp a fn-octets) (fn-b3x-word (+ 44 q) e prefix lp a fn-octets) (fn-b3x-word (+ 48 q) e prefix lp a fn-octets) (fn-b3x-word (+ 52 q) e prefix lp a fn-octets) (fn-b3x-word (+ 56 q) e prefix lp a fn-octets) (fn-b3x-word (+ 60 q) e prefix lp a fn-octets) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0))))
                                 (+ 64 q) e counter flags nil prefix lp a fn-octets)))
   :hints (("Goal" :expand ((fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets))
            :in-theory (disable fn-b3-compress-core)))))

(local
 (defthm fn-b3x-chunk-model-step
   (implies (< 64 (len x))
            (equal (fn-b3-chunk cv x counter flags startp)
                   (fn-b3-chunk (fn-b3-compress cv (fn-b3-words 16 x) counter 64 (logior (ifix flags) (if startp *fn-b3-chunk-start* 0)))
                                (fn-b3-nthcdrx 64 x) counter flags nil)))
   :hints (("Goal" :expand ((fn-b3-chunk cv x counter flags startp))))))

(defthm fn-b3x-chunk-is-chunk
  (implies (and (natp q) (natp e) (natp a) (equal lp (len prefix))
                (<= e (len (fn-b3x-msg0 prefix a fn-octets)))
                (<= q e))
           (equal (fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets)
                  (fn-b3-chunk (list c0 c1 c2 c3 c4 c5 c6 c7)
                               (fn-b3-firstn (- e q)
                                             (fn-b3-nthcdrx q (fn-b3x-msg0 prefix a fn-octets)))
                               counter flags startp)))
  :hints (("Goal" :induct (fn-b3x-chunk c0 c1 c2 c3 c4 c5 c6 c7 q e counter flags startp prefix lp a fn-octets)
           :in-theory (disable fn-b3x-msg0 fn-b3-compress-core (:d fn-b3x-chunk) (:d fn-b3-chunk)))))

(local
 (defthm fn-b3x-compress-of-cv8
   (equal (fn-b3-compress (list (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv) (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv)) words counter blen flags)
          (fn-b3-compress cv words counter blen flags))
   :hints (("Goal" :in-theory (enable fn-b3-compress)))))

(local
 (defthm fn-b3x-chunk-of-cv8
   (equal (fn-b3-chunk (list (fn-b3-nthx 0 cv) (fn-b3-nthx 1 cv) (fn-b3-nthx 2 cv) (fn-b3-nthx 3 cv) (fn-b3-nthx 4 cv) (fn-b3-nthx 5 cv) (fn-b3-nthx 6 cv) (fn-b3-nthx 7 cv)) x counter flags startp)
          (fn-b3-chunk cv x counter flags startp))
   :hints (("Goal" :cases ((< 64 (len x)))
            :in-theory (disable (:d fn-b3-chunk))))))

(local
 (defthm fn-b3x-node-exec-base
   (implies (and (natp s) (natp e) (not (< 1024 (- e s))))
            (equal (fn-b3x-node key s e counter flags prefix lp a fn-octets)
                   (fn-b3x-chunk (fn-b3-nthx 0 key) (fn-b3-nthx 1 key) (fn-b3-nthx 2 key) (fn-b3-nthx 3 key) (fn-b3-nthx 4 key) (fn-b3-nthx 5 key) (fn-b3-nthx 6 key) (fn-b3-nthx 7 key) s e counter flags t prefix lp a fn-octets)))
   :hints (("Goal" :expand ((fn-b3x-node key s e counter flags prefix lp a fn-octets))))))

(local
 (defthm fn-b3x-node-exec-step
   (implies (and (natp s) (natp e) (< 1024 (- e s)))
            (equal (fn-b3x-node key s e counter flags prefix lp a fn-octets)
                   (let* ((lc (fn-b3-left-chunks 1 (- e s)))
                          (ll (* 1024 lc)))
                     (fn-b3-output key
                                   (append (fn-b3-output-cv
                                            (fn-b3x-node key s (+ s ll) counter flags prefix lp a fn-octets))
                                           (fn-b3-output-cv
                                            (fn-b3x-node key (+ s ll) e (+ (nfix counter) lc) flags prefix lp a fn-octets)))
                                   0 64 (logior (ifix flags) *fn-b3-parent*)))))
   :hints (("Goal" :expand ((fn-b3x-node key s e counter flags prefix lp a fn-octets))))))

(local
 (defthm fn-b3x-node-model-base
   (implies (not (< 1024 (len x)))
            (equal (fn-b3-node key x counter flags)
                   (fn-b3-chunk key x counter flags t)))
   :hints (("Goal" :expand ((fn-b3-node key x counter flags))))))

(local
 (defthm fn-b3x-node-model-step
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

(defthm fn-b3x-node-is-node
  (implies (and (natp s) (natp e) (natp a) (equal lp (len prefix))
                (<= e (len (fn-b3x-msg0 prefix a fn-octets)))
                (<= s e))
           (equal (fn-b3x-node key s e counter flags prefix lp a fn-octets)
                  (fn-b3-node key
                              (fn-b3-firstn (- e s)
                                            (fn-b3-nthcdrx s (fn-b3x-msg0 prefix a fn-octets)))
                              counter flags)))
  :hints (("Goal" :induct (fn-b3x-node key s e counter flags prefix lp a fn-octets)
           :in-theory (disable fn-b3x-msg0 fn-b3-compress-core (:d fn-b3x-node) (:d fn-b3-node)
                               (:d fn-b3x-chunk) (:d fn-b3-chunk)))))

(local
 (defthm fn-b3x-firstn-of-fix-octets
   (equal (fn-b3-firstn n (fn-b3-fix-octets l))
          (fn-b3-fix-octets (fn-b3-firstn n l)))
   :hints (("Goal" :in-theory (enable fn-b3-fix-octets fn-b3-firstn)))))

(local
 (defthm fn-b3x-firstn-of-append
   (implies (natp k)
            (equal (fn-b3-firstn (+ (len p) k) (append p w))
                   (append p (fn-b3-firstn k w))))
   :hints (("Goal" :in-theory (enable fn-b3-firstn)))))

(local
 (defthm fn-b3x-nthcdrx-is-nthcdr
   (implies (and (natp a) (<= a (len l)))
            (equal (fn-b3-nthcdrx a l) (nthcdr a l)))
   :hints (("Goal" :in-theory (enable fn-b3-nthcdrx)))))

(local
 (defthm fn-b3x-firstn-is-take
   (implies (and (natp k) (<= k (len l)))
            (equal (fn-b3-firstn k l) (take k l)))
   :hints (("Goal" :in-theory (enable fn-b3-firstn)))))

(local
 (defthm fn-b3x-len-of-append
   (equal (len (append p w)) (+ (len p) (len w)))))

(local
 (defthm fn-b3x-len-of-nthcdr
   (implies (and (natp a) (<= a (len l)))
            (equal (len (nthcdr a l)) (- (len l) a)))))

(local
 (defthm fn-b3x-len-of-msg0
   (implies (and (natp a) (<= a (len l)))
            (equal (len (fn-b3x-msg0 prefix a l))
                   (+ (len prefix) (- (len l) a))))))

(local
 (defun fn-b3x-ind-np (n p)
   (if (consp p) (fn-b3x-ind-np (- n 1) (cdr p)) n)))

(local
 (defthm fn-b3x-firstn-of-append-2
   (implies (and (natp n) (<= (len p) n))
            (equal (fn-b3-firstn n (append p w))
                   (append p (fn-b3-firstn (- n (len p)) w))))
   :hints (("Goal" :in-theory (enable fn-b3-firstn)
            :induct (fn-b3x-ind-np n p)))))

(local
 (defthm fn-b3x-firstn-of-nthcdrx-is-take
   (implies (and (natp a) (natp wn) (<= (+ a wn) (len l)))
            (equal (fn-b3-firstn wn (fn-b3-nthcdrx a l))
                   (take wn (nthcdr a l))))
   :hints (("Goal" :in-theory (disable fn-b3x-firstn-is-take fn-b3x-nthcdrx-is-nthcdr)
            :use (fn-b3x-nthcdrx-is-nthcdr
                  (:instance fn-b3x-firstn-is-take (k wn) (l (nthcdr a l))))))))

(local
 (defthm fn-b3x-firstn-of-msg0
   (implies (and (natp a) (natp wn) (<= (+ a wn) (len l)))
            (equal (fn-b3-firstn (+ (len prefix) wn) (fn-b3x-msg0 prefix a l))
                   (fn-b3x-msg prefix a wn l)))
   :hints (("Goal" :in-theory (disable fn-b3x-firstn-is-take fn-b3x-nthcdrx-is-nthcdr
                                       fn-b3x-firstn-of-append)))))

(local
 (defthm fn-b3x-nthcdrx-of-zero
   (equal (fn-b3-nthcdrx 0 l) l)
   :hints (("Goal" :in-theory (enable fn-b3-nthcdrx)))))

(local
 (defthm fn-b3x-firstn-of-msg0-2
   (implies (and (natp a) (natp wn) (<= (+ a wn) (len l)))
            (equal (fn-b3-firstn (+ wn (len prefix)) (fn-b3x-msg0 prefix a l))
                   (fn-b3x-msg prefix a wn l)))
   :hints (("Goal" :use fn-b3x-firstn-of-msg0))))

(defthm fn-b3x-hash-is-hash
  (implies (and (natp a) (natp wn) (<= (+ a wn) (len fn-octets)))
           (equal (fn-b3x-hash key flags prefix a wn fn-octets)
                  (fn-b3-hash key flags (fn-b3x-msg prefix a wn fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-b3-hash) (fn-b3x-msg0 fn-b3x-msg fn-b3x-firstn-is-take
                                                fn-b3x-nthcdrx-is-nthcdr fn-b3x-firstn-of-nthcdrx-is-take))
           :do-not-induct t
           :use ((:instance fn-b3x-node-is-node (s 0) (e (+ (len prefix) wn))
                            (counter 0) (lp (len prefix)))))))

(defun fn-blake3-of-prefixed-range (prefix a wn fn-octets)
  ; BLAKE3 of PREFIX followed by the WN octets at A of the buffer.
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (natp a) (natp wn)
                              (<= (+ a wn) (fn-octets-len fn-octets)))))
  (fn-b3x-hash *fn-b3-iv* 0 prefix a wn fn-octets))

(defthm fn-blake3-of-prefixed-range-is-blake3
  (implies (and (natp a) (natp wn) (<= (+ a wn) (len fn-octets)))
           (equal (fn-blake3-of-prefixed-range prefix a wn fn-octets)
                  (fn-blake3 (append prefix (fn-shr-win a wn fn-octets)))))
  :hints (("Goal" :in-theory (enable fn-blake3))))

(defun fn-blake3-of-prefixed-buffer (prefix fn-octets)
  ; BLAKE3 of PREFIX followed by the whole buffer.
  (declare (xargs :stobjs fn-octets :guard (true-listp prefix)))
  (fn-blake3-of-prefixed-range prefix 0 (fn-octets-len fn-octets) fn-octets))

(local
 (defthm fn-b3x-fix-octets-of-append-true-list-fix
   (equal (fn-b3-fix-octets (append p (true-list-fix w)))
          (fn-b3-fix-octets (append p w)))
   :hints (("Goal" :in-theory (enable fn-b3-fix-octets)))))

(local
 (defthm fn-b3x-take-len
   (equal (take (len l) l) (true-list-fix l))))

(defthm fn-blake3-of-prefixed-buffer-is-blake3
  (equal (fn-blake3-of-prefixed-buffer prefix fn-octets)
         (fn-blake3 (append prefix fn-octets)))
  :hints (("Goal" :in-theory (enable fn-blake3))))

(local
 (defthm fn-b3x-octet-listp-is-cbor
   (implies (fn-b3-octet-listp x) (fn-cbor-octet-listp x))))

(defun fn-blake3-stobj (m)
  ; BLAKE3 of any object read as octets: the octets copied once into a local
  ; buffer (an array, not a list), then hashed in place.  The function the
  ; digest seams attach to; it has `fn-blake3's signature.
  (declare (xargs :guard t))
  (with-local-stobj fn-octets
    (mv-let (digest fn-octets)
      (let ((fn-octets (fn-octets-from-list (fn-b3-fix-octets m) fn-octets)))
        (mv (fn-blake3-of-prefixed-buffer nil fn-octets) fn-octets))
      digest)))

(defthm fn-blake3-stobj-is-blake3
  (equal (fn-blake3-stobj m) (fn-blake3 m))
  :hints (("Goal" :in-theory (enable fn-blake3))))

; -----------------------------------------------------------------------------
; Export theory.

(deftheory fn-b3x-internals
  '(fn-b3x-byte fn-b3x-word fn-b3x-words fn-b3x-chunk fn-b3x-node fn-b3x-hash
    fn-b3x-msg0 fn-b3x-msg
    fn-b3x-byte-is-nthx fn-b3x-words-is-words fn-b3x-nthx-of-xwords fn-b3x-words-of-msg0
    fn-b3x-compress-step fn-b3x-chunk-base fn-b3x-chunk-is-chunk fn-b3x-node-is-node
    fn-b3x-hash-is-hash))

(in-theory (disable fn-b3x-internals fn-blake3-of-prefixed-range fn-blake3-of-prefixed-buffer
                    fn-blake3-stobj))
