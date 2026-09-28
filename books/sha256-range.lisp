;; fn: SHA-256 of a prefixed WINDOW of an octet buffer, read by index (lane
;; snapshot-open-2, 2026-09-27).  Prefix `fn-shr-'.
;
; books/sha256-buffer.lisp digests (append PREFIX buffer) with the WHOLE
; buffer in place.  A file the host reads into one buffer holds many frames
; (the checkpoint's segments, the log's entries), and each frame's trailer
; is the digest of a WINDOW of it: before this book the readers sliced the
; window into an octet list and digested the list (fn-sccb-slice-acc, then
; fn-shs-digest-list by car/cdr).  This book is sha256-buffer's reader with
; a base offset A and a window length WN: the message's octet at index i is
; the prefix's below LP, the buffer's cell A + (i - LP) below LP + WN, and
; the padding past it (`fn-shr-byte').  The proof is sha256-buffer's,
; stated over the window's list model `fn-shr-win' (take WN octets after
; A) in place of the whole buffer.
;
; KEYSTONE `fn-sha256-of-prefixed-range-is-sha256': the window digest is
; `fn-sha256' of (append PREFIX (fn-shr-win A WN buffer)), with no
; hypothesis.  `fn-shr-win-is-slice' relates the window to the reader's
; slice (fn-oct-slice-list) inside the buffer.

(in-package "ACL2")
(include-book "sha256-stobj")
(include-book "octets-stobj")

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod truncate rem ash)))

; The window's list model: WN octets of the buffer's value after A (take pads
; past the end, so its length is WN on every value).
(defun fn-shr-win (a wn l)
  (declare (xargs :guard t :verify-guards nil))
  (take (nfix wn) (nthcdr (nfix a) l)))

(local
 (defthm fn-shr-len-of-take
   (equal (len (take n l)) (nfix n))))

(local
 (defthm fn-shr-nth-of-take
   (implies (and (natp k) (< k (nfix n)))
            (equal (nth k (take n l)) (nth k l)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-shr-nth-of-nthcdr
   (implies (and (natp k) (natp a))
            (equal (nth k (nthcdr a l)) (nth (+ a k) l)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(defthm fn-shr-len-of-win
  (equal (len (fn-shr-win a wn l)) (nfix wn)))

(defthm fn-shr-nth-of-win
  (implies (and (natp k) (< k (nfix wn)))
           (equal (nth k (fn-shr-win a wn l))
                  (nth (+ (nfix a) k) l))))

(in-theory (disable fn-shr-win))

; -----------------------------------------------------------------------------
; Word and octet facts (sha256-stobj keeps its own local).

(local
 (defthm fn-shr-u32-of-w32
   (unsigned-byte-p 32 (fn-sha256-w32 x))))

(local
 (defthm fn-shr-byte-of-octet
   (implies (and (integerp x) (<= 0 x) (< x 256))
            (equal (fn-sha256-byte x) x))
   :hints (("Goal" :in-theory (enable fn-sha256-byte)))))

; -----------------------------------------------------------------------------
; The stobj recognizer survives in-range updates (sha256-stobj's local facts,
; restated: the guards of the loaders below need them).

(local
 (defthm fn-shr-wp-of-update-nth
   (implies (and (fn-shs-wp w) (natp i) (< i (len w)) (unsigned-byte-p 32 v))
            (fn-shs-wp (update-nth i v w)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-shr-hp-of-update-nth
   (implies (and (fn-shs-hp h) (natp i) (< i (len h)) (unsigned-byte-p 32 v))
            (fn-shs-hp (update-nth i v h)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-shr-len-of-update-nth
   (equal (len (update-nth i v l))
          (max (+ 1 (nfix i)) (len l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local (in-theory (disable nth update-nth)))

(local
 (defthm fn-shr-p-of-update-w
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 64) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 0 (update-nth i v (nth 0 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-shr-p-of-update-h
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 1 (update-nth i v (nth 1 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-shr-p-parts
   (implies (fn-shs-p fn-shs)
            (and (fn-shs-wp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-hp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8)))))

; The sha256-stobj functions this book calls keep the recognizer.

(local
 (defthm fn-shr-p-of-h-init
   (implies (and (fn-shs-p fn-shs) (natp i) (fn-shs-word-listp hs))
            (fn-shs-p (fn-shs-h-init i hs fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-h-init fn-shs-word-listp) (fn-shs-p))))))

(local
 (defthm fn-shr-p-of-extend
   (implies (and (fn-shs-p fn-shs) (natp t0))
            (fn-shs-p (fn-shs-extend t0 fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-extend fn-shs-sched-word$inline) (fn-shs-p))))))

(local
 (defthm fn-shr-p-of-h-add
   (implies (and (fn-shs-p fn-shs) (natp i))
            (fn-shs-p (fn-shs-h-add i regs fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-h-add fn-shs-add$inline) (fn-shs-p))))))

(local
 (defthm fn-shr-p-of-compress-loaded
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-compress-loaded fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-compress-loaded) (fn-shs-p))))))

; -----------------------------------------------------------------------------
; The third message reader: the padded message (append PREFIX buffer) at an
; index.  LP is the prefix length and N the message length, carried so that
; no byte read walks the prefix for its length.

(defun fn-shr-byte (i n prefix lp a fn-octets)
  (declare (type (integer 0 *) i n lp a)
           (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (natp a) (<= lp n) (<= (+ a (- n lp)) (fn-octets-len fn-octets))
                              (< i (fn-shs-pad-len n)))))
  (cond ((< i lp) (fn-shs-octet (nth i prefix)))
        ((< i n) (mbe :logic (fn-sha256-byte (fn-octets-get (+ (nfix a) (- i lp)) fn-octets))
                      :exec (fn-octets-get (+ a (- i lp)) fn-octets)))
        (t (fn-shs-tail-byte i n))))

(defthm fn-shr-u8-of-byte
  (and (integerp (fn-shr-byte i n prefix lp a fn-octets))
       (<= 0 (fn-shr-byte i n prefix lp a fn-octets))
       (< (fn-shr-byte i n prefix lp a fn-octets) 256))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-shr-byte i n prefix lp a fn-octets))
                                  (<= 0 (fn-shr-byte i n prefix lp a fn-octets))))
                 (:linear :corollary (< (fn-shr-byte i n prefix lp a fn-octets) 256))
                 (:rewrite :corollary (unsigned-byte-p 8 (fn-shr-byte i n prefix lp a fn-octets))))
  :hints (("Goal" :in-theory (enable fn-shs-octet$inline))))

(local (in-theory (disable fn-shr-byte)))

(defun fn-shr-load-word (j base n prefix lp a fn-octets fn-shs)
  (declare (type (integer 0 15) j) (type (integer 0 *) base n lp a)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (natp a) (<= lp n) (<= (+ a (- n lp)) (fn-octets-len fn-octets))
                              (<= (+ base 64) (fn-shs-pad-len n)))
                  :guard-hints (("Goal" :in-theory (enable fn-shs-be-word$inline)))))
  (let ((i (+ base (* 4 j))))
    (fn-shs-w-set j
                  (fn-shs-be-word (fn-shr-byte i n prefix lp a fn-octets)
                                  (fn-shr-byte (+ i 1) n prefix lp a fn-octets)
                                  (fn-shr-byte (+ i 2) n prefix lp a fn-octets)
                                  (fn-shr-byte (+ i 3) n prefix lp a fn-octets))
                  fn-shs)))

(local
 (defthm fn-shr-p-of-load-word
   (implies (and (fn-shs-p fn-shs) (natp j) (< j 16))
            (fn-shs-p (fn-shr-load-word j base n prefix lp a fn-octets fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-be-word$inline) (fn-shs-p))))))

(local (in-theory (disable fn-shr-load-word)))

(defun fn-shr-load-block (j base n prefix lp a fn-octets fn-shs)
  (declare (type (integer 0 16) j) (type (integer 0 *) base n lp a)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (natp a) (<= lp n) (<= (+ a (- n lp)) (fn-octets-len fn-octets))
                              (<= (+ base 64) (fn-shs-pad-len n)))
                  :measure (nfix (- 16 j))))
  (if (mbe :logic (zp (- 16 j)) :exec (= j 16))
      fn-shs
    (let ((fn-shs (fn-shr-load-word j base n prefix lp a fn-octets fn-shs)))
      (fn-shr-load-block (+ j 1) base n prefix lp a fn-octets fn-shs))))

(local
 (defthm fn-shr-p-of-load-block
   (implies (and (fn-shs-p fn-shs) (natp j))
            (fn-shs-p (fn-shr-load-block j base n prefix lp a fn-octets fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shr-load-block))))

(defun fn-shr-compress (b n prefix lp a fn-octets fn-shs)
  (declare (type (integer 0 *) b n lp a)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (natp a) (<= lp n) (<= (+ a (- n lp)) (fn-octets-len fn-octets))
                              (< b (fn-shs-nblocks n)))))
  (let ((fn-shs (fn-shr-load-block 0 (* 64 b) n prefix lp a fn-octets fn-shs)))
    (fn-shs-compress-loaded fn-shs)))

(local
 (defthm fn-shr-p-of-compress
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shr-compress b n prefix lp a fn-octets fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shr-compress))))

(defun fn-shr-blocks (b nb n prefix lp a fn-octets fn-shs)
  (declare (type (integer 0 *) b nb n lp a)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (natp a) (<= lp n) (<= (+ a (- n lp)) (fn-octets-len fn-octets))
                              (= nb (fn-shs-nblocks n)) (<= b nb))
                  :measure (nfix (- nb b))))
  (if (mbe :logic (zp (- nb b)) :exec (= b nb))
      fn-shs
    (let ((fn-shs (fn-shr-compress b n prefix lp a fn-octets fn-shs)))
      (fn-shr-blocks (+ b 1) nb n prefix lp a fn-octets fn-shs))))

(local
 (defthm fn-shr-p-of-blocks
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shr-blocks b nb n prefix lp a fn-octets fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shr-blocks))))

; From here the window length is carried as (nfix wn), closed, the form
; `fn-shr-len-of-win' gives.
(local (in-theory (disable nfix)))

(defun fn-shr-digest (prefix a wn fn-octets fn-shs)
  (declare (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (natp a) (natp wn)
                              (<= (+ a wn) (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :in-theory (enable nfix)))))
  (let* ((lp (len prefix))
         (n (mbe :logic (+ (len prefix) (nfix wn))
                 :exec (+ lp wn)))
         (fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))
         (fn-shs (fn-shr-blocks 0 (fn-shs-nblocks n) n prefix lp a fn-octets fn-shs)))
    (mv (fn-shs-h-octets 0 fn-shs) fn-shs)))

(defun fn-sha256-of-prefixed-range (prefix a wn fn-octets)
  ; SHA-256 of (append PREFIX buffer[a, a+wn)): the prefix read from the
  ; list, the window in place by index, over a local word stobj.
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (natp a) (natp wn)
                              (<= (+ a wn) (fn-octets-len fn-octets)))))
  (with-local-stobj fn-shs
    (mv-let (digest fn-shs) (fn-shr-digest prefix a wn fn-octets fn-shs)
      digest)))

; =============================================================================
; The correspondence: the buffer reader is the list reader on the suffix.

; The list reader's remaining message at index i: the suffix, stopping at an
; atom, so that an improper value is carried without a hypothesis.
(local
 (defun fn-shr-rest (i m)
   (declare (xargs :guard (natp i)))
   (if (zp i)
       m
     (if (consp m) (fn-shr-rest (1- i) (cdr m)) m))))

(local
 (defthm fn-shr-rest-0
   (equal (fn-shr-rest 0 m) m)))

(local
 (defthm fn-shr-consp-rest-below
   (implies (and (natp i) (< i (len m)))
            (consp (fn-shr-rest i m)))
   :hints (("Goal" :induct (fn-shr-rest i m)))))

(local
 (defthm fn-shr-consp-rest-past
   (implies (and (natp i) (<= (len m) i))
            (not (consp (fn-shr-rest i m))))
   :hints (("Goal" :induct (fn-shr-rest i m)))))

(local
 (defthm fn-shr-car-rest
   (implies (natp i)
            (equal (car (fn-shr-rest i m)) (nth i m)))
   :hints (("Goal" :in-theory (enable nth) :induct (fn-shr-rest i m)))))

(local
 (defthm fn-shr-rest-succ
   (implies (natp i)
            (equal (fn-shr-rest (+ 1 i) m)
                   (if (consp (fn-shr-rest i m))
                       (cdr (fn-shr-rest i m))
                     (fn-shr-rest i m))))
   :hints (("Goal" :induct (fn-shr-rest i m)))))

(local
 (defthm fn-shr-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-shr-nth-of-append
   (implies (natp i)
            (equal (nth i (append a b))
                   (if (< i (len a)) (nth i a) (nth (- i (len a)) b))))
   :hints (("Goal" :in-theory (enable nth) :induct (nth i a)))))

(local (in-theory (disable fn-shr-rest)))

; The message length is written as ACL2 orders the sum, (+ (len fn-octets)
; (len prefix)), so that each lemma below is a rewrite rule that matches
; the normalised goal; `len' and `append' stay closed so that the message
; and its length stay one term each.

; The byte: on the message (append prefix value) at any index, by cases on
; whether the index is within the message.
(local
 (defthm fn-shr-list-byte-is-byte
   (implies (natp i)
            (equal (fn-shs-list-byte i (+ (len prefix) (nfix wn))
                                     (fn-shr-rest i (append prefix (fn-shr-win a wn fn-octets))))
                   (list (fn-shr-byte i (+ (len prefix) (nfix wn))
                                      prefix (len prefix) a fn-octets)
                         (fn-shr-rest (+ 1 i) (append prefix (fn-shr-win a wn fn-octets))))))
   :hints (("Goal" :cases ((< i (+ (len prefix) (nfix wn))))
            :in-theory (enable fn-shs-list-byte fn-shs-octet$inline fn-shr-byte)))))

; From here on the suffix facts are cited, never rewritten with: as rules
; they open the suffix term the lemmas carry.
(local (deftheory fn-shr-suffix-rules
         '(fn-shr-rest-succ fn-shr-car-rest fn-shr-consp-rest-below
           fn-shr-consp-rest-past fn-shr-list-byte-is-byte len binary-append)))

(local
 (defthm fn-shr-load-list-word-is-load-word
   (implies (and (natp j) (natp base))
            (equal (fn-shs-load-list-word j base (+ (len prefix) (nfix wn))
                                          (fn-shr-rest (+ base (* 4 j)) (append prefix (fn-shr-win a wn fn-octets)))
                                          fn-shs)
                   (list (fn-shr-rest (+ 4 base (* 4 j)) (append prefix (fn-shr-win a wn fn-octets)))
                         (fn-shr-load-word j base (+ (len prefix) (nfix wn))
                                           prefix (len prefix) a fn-octets fn-shs))))
   :hints (("Goal" :in-theory (e/d (fn-shs-load-list-word fn-shr-load-word)
                                   (fn-shr-suffix-rules))
            :use ((:instance fn-shr-list-byte-is-byte (i (+ base (* 4 j))))
                  (:instance fn-shr-list-byte-is-byte (i (+ 1 base (* 4 j))))
                  (:instance fn-shr-list-byte-is-byte (i (+ 2 base (* 4 j))))
                  (:instance fn-shr-list-byte-is-byte (i (+ 3 base (* 4 j)))))))))

; The two list loops, opened one step at a time (the rewriter does not
; unfold them under the induction below).
(local
 (defthm fn-shr-open-load-list-block-step
   (implies (and (natp j) (< j 16))
            (equal (fn-shs-load-list-block j base n rest fn-shs)
                   (fn-shs-load-list-block
                    (+ 1 j) base n
                    (mv-nth 0 (fn-shs-load-list-word j base n rest fn-shs))
                    (mv-nth 1 (fn-shs-load-list-word j base n rest fn-shs)))))
   :hints (("Goal" :expand ((fn-shs-load-list-block j base n rest fn-shs))))))

(local
 (defthm fn-shr-open-load-list-block-end
   (implies (zp (- 16 j))
            (equal (fn-shs-load-list-block j base n rest fn-shs) (list rest fn-shs)))
   :hints (("Goal" :expand ((fn-shs-load-list-block j base n rest fn-shs))))))

(local
 (defthm fn-shr-open-blocks-list-step
   (implies (and (natp b) (natp nb) (< b nb))
            (equal (fn-shs-blocks-list b nb n rest fn-shs)
                   (fn-shs-blocks-list
                    (+ 1 b) nb n
                    (mv-nth 0 (fn-shs-compress-list b n rest fn-shs))
                    (mv-nth 1 (fn-shs-compress-list b n rest fn-shs)))))
   :hints (("Goal" :expand ((fn-shs-blocks-list b nb n rest fn-shs))))))

(local
 (defthm fn-shr-open-blocks-list-end
   (implies (zp (- nb b))
            (equal (fn-shs-blocks-list b nb n rest fn-shs) fn-shs))
   :hints (("Goal" :expand ((fn-shs-blocks-list b nb n rest fn-shs))))))

(local
 (defthm fn-shr-load-list-block-is-load-block
   (implies (and (natp j) (<= j 16) (natp base))
            (equal (fn-shs-load-list-block j base (+ (len prefix) (nfix wn))
                                           (fn-shr-rest (+ base (* 4 j)) (append prefix (fn-shr-win a wn fn-octets)))
                                           fn-shs)
                   (list (fn-shr-rest (+ 64 base) (append prefix (fn-shr-win a wn fn-octets)))
                         (fn-shr-load-block j base (+ (len prefix) (nfix wn))
                                            prefix (len prefix) a fn-octets fn-shs))))
   :hints (("Goal" :induct (fn-shr-load-block j base (+ (len prefix) (nfix wn))
                                              prefix (len prefix) a fn-octets fn-shs)
            :in-theory (e/d (fn-shr-load-block) (fn-shr-suffix-rules))))))

(local
 (defthm fn-shr-compress-list-is-compress
   (implies (natp b)
            (equal (fn-shs-compress-list b (+ (len prefix) (nfix wn))
                                         (fn-shr-rest (* 64 b) (append prefix (fn-shr-win a wn fn-octets)))
                                         fn-shs)
                   (list (fn-shr-rest (+ 64 (* 64 b)) (append prefix (fn-shr-win a wn fn-octets)))
                         (fn-shr-compress b (+ (len prefix) (nfix wn))
                                          prefix (len prefix) a fn-octets fn-shs))))
   ; The openers stay closed here: on the constant word index they would
   ; unroll the sixteen words instead of leaving the block lemma's instance.
   :hints (("Goal" :in-theory (e/d (fn-shs-compress-list fn-shr-compress)
                                   (fn-shr-suffix-rules
                                    fn-shr-open-load-list-block-step
                                    fn-shr-open-load-list-block-end))
            :use ((:instance fn-shr-load-list-block-is-load-block
                             (j 0) (base (* 64 b))))))))

(local
 (defthm fn-shr-blocks-list-is-blocks
   (implies (and (natp b) (natp nb))
            (equal (fn-shs-blocks-list b nb (+ (len prefix) (nfix wn))
                                       (fn-shr-rest (* 64 b) (append prefix (fn-shr-win a wn fn-octets)))
                                       fn-shs)
                   (fn-shr-blocks b nb (+ (len prefix) (nfix wn))
                                  prefix (len prefix) a fn-octets fn-shs)))
   :hints (("Goal" :induct (fn-shr-blocks b nb (+ (len prefix) (nfix wn))
                                          prefix (len prefix) a fn-octets fn-shs)
            :in-theory (e/d (fn-shr-blocks) (fn-shr-suffix-rules))))))

(local
 (defthm fn-shr-digest-list-is-digest
   (equal (fn-shs-digest-list (append prefix (fn-shr-win a wn fn-octets)) fn-shs)
          (fn-shr-digest prefix a wn fn-octets fn-shs))
   :hints (("Goal" :in-theory (e/d (fn-shs-digest-list fn-shr-digest)
                                   (fn-shr-suffix-rules
                                    fn-shr-open-blocks-list-step
                                    fn-shr-open-blocks-list-end))
            :use ((:instance fn-shr-blocks-list-is-blocks
                             (b 0)
                             (nb (fn-shs-nblocks (+ (len prefix) (nfix wn))))
                             (fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))))))))

(local (in-theory (disable fn-shr-digest)))

; The keystone: the buffer digest is the list model of the appended message,
; on every prefix and every value.  The creator stays a term (as in
; sha256-stobj: its executable counterpart would turn it into the arrays
; before the digest rules can match).
(defthm fn-sha256-of-prefixed-range-is-sha256
  (equal (fn-sha256-of-prefixed-range prefix a wn fn-octets)
         (fn-sha256 (append prefix (fn-shr-win a wn fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-sha256-stobj)
                                  (fn-sha256-stobj-is-sha256
                                   (:e create-fn-shs) (:d create-fn-shs)))
           :use ((:instance fn-sha256-stobj-is-sha256
                            (m (append prefix (fn-shr-win a wn fn-octets))))))))


; The window inside the buffer is the reader's slice.
(defthm fn-shr-win-is-slice
  (implies (and (natp a) (natp wn) (<= (+ a wn) (len l)) (true-listp l))
           (equal (fn-shr-win a wn l)
                  (fn-oct-slice-list a (+ a wn) l)))
  :hints (("Goal" :in-theory (enable fn-shr-win nfix)
           :use ((:instance fn-oct-slice-list-is-take-nthcdr
                            (i a) (n (+ a wn)) (fn-octets l))))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2): the stobj functions are the
; executable path; what leaves is the correspondence.

(deftheory fn-shr-internals
  '((:d fn-shr-byte) (:d fn-shr-load-word) (:d fn-shr-load-block)
    (:d fn-shr-compress) (:d fn-shr-blocks) (:d fn-shr-digest)
    (:d fn-sha256-of-prefixed-range)))

(in-theory (disable fn-shr-internals))
