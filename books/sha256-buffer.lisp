; fn: SHA-256 of a prefixed octet buffer, read by index (D27 wave C: the
; subject digest over the buffer).  Prefix `fn-shb-'.
;
; Why this book exists.  books/sha256-stobj.lisp digests an octet list (by
; `car'/`cdr') or a string (by `char' at an index) over the word stobj
; `fn-shs'.  The served POST's payload sits in the octet buffer `fn-octets'
; (books/octets-stobj.lisp) from the host's fill to the record, except for
; the subject identity (books/identity.lisp `fn-id-subject-of-payload'): its
; preimage is `(append (fn-id-subject-prefix (len payload)) payload)', and
; the host handed the payload back as a fresh octet list to build it.  This
; book adds the third message reader: the padded message's octet at index i
; is the prefix's octet below the prefix length, the buffer's cell at
; i - lp below the message length, and the padding past it
; (`fn-shb-byte'); the block loader, the compression loop and the digest
; are the string reader's, with the buffer and the prefix in place of the
; string.  The entry `fn-sha256-of-prefixed-buffer' has the signature the
; subject preimage needs (a short list prefix, the payload in the buffer),
; and `fn-shb-subject-id' is the subject identity over the buffer.
;
; What is proved.  `fn-sha256-of-prefixed-buffer-is-sha256' (the keystone):
; the buffer digest of PREFIX and the buffer's value is `fn-sha256' of
; `(append PREFIX value)', with no hypothesis.  It is proved as the
; correspondence of the two readers: the buffer's byte at i is the list
; reader's byte at i on the list's suffix (`fn-shb-list-byte-is-byte'), the
; loaded word, the loaded block, the compressed block and the block loop
; follow (`fn-shb-load-list-word-is-load-word', `-block-', `-compress-',
; `fn-shb-blocks-list-is-blocks'), and the digests agree
; (`fn-shb-digest-list-is-digest'); the list model is then sha256-stobj's
; keystone `fn-sha256-stobj-is-sha256'.  `fn-shb-subject-id-is-id-subject-of-sha256-preimage'
; says the buffer identity is `fn-id-subject' of `fn-sha256' over the
; subject preimage: `fn-id-subject-of-payload' with `fn-sha256' in the place
; of the constrained `fn-frame-digest', which is what books/crypto-attach.lisp
; attaches (`fn-sha256-stobj', equal to `fn-sha256' by its keystone), so on
; the host image the two identities are the same octets.
;
; Proof style.  As in sha256-stobj: constant-index `nth' and `update-nth'
; stay closed from the stobj facts on; the list reader's position is
; carried by `fn-shb-rest' (the suffix at an index that stops at an atom,
; so that an improper value needs no hypothesis) and every lemma is stated
; over `(append prefix fn-octets)' with the prefix length and the message
; length written out, never as free variables.

(in-package "ACL2")
(include-book "sha256-stobj")
(include-book "octets-stobj")
(include-book "identity")

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod truncate rem ash)))

; -----------------------------------------------------------------------------
; Word and octet facts (sha256-stobj keeps its own local).

(local
 (defthm fn-shb-u32-of-w32
   (unsigned-byte-p 32 (fn-sha256-w32 x))))

(local
 (defthm fn-shb-byte-of-octet
   (implies (and (integerp x) (<= 0 x) (< x 256))
            (equal (fn-sha256-byte x) x))
   :hints (("Goal" :in-theory (enable fn-sha256-byte)))))

; -----------------------------------------------------------------------------
; The stobj recognizer survives in-range updates (sha256-stobj's local facts,
; restated: the guards of the loaders below need them).

(local
 (defthm fn-shb-wp-of-update-nth
   (implies (and (fn-shs-wp w) (natp i) (< i (len w)) (unsigned-byte-p 32 v))
            (fn-shs-wp (update-nth i v w)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-shb-hp-of-update-nth
   (implies (and (fn-shs-hp h) (natp i) (< i (len h)) (unsigned-byte-p 32 v))
            (fn-shs-hp (update-nth i v h)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-shb-len-of-update-nth
   (equal (len (update-nth i v l))
          (max (+ 1 (nfix i)) (len l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local (in-theory (disable nth update-nth)))

(local
 (defthm fn-shb-p-of-update-w
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 64) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 0 (update-nth i v (nth 0 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-shb-p-of-update-h
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 1 (update-nth i v (nth 1 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-shb-p-parts
   (implies (fn-shs-p fn-shs)
            (and (fn-shs-wp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-hp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8)))))

; The sha256-stobj functions this book calls keep the recognizer.

(local
 (defthm fn-shb-p-of-h-init
   (implies (and (fn-shs-p fn-shs) (natp i) (fn-shs-word-listp hs))
            (fn-shs-p (fn-shs-h-init i hs fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-h-init fn-shs-word-listp) (fn-shs-p))))))

(local
 (defthm fn-shb-p-of-extend
   (implies (and (fn-shs-p fn-shs) (natp t0))
            (fn-shs-p (fn-shs-extend t0 fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-extend fn-shs-sched-word$inline) (fn-shs-p))))))

(local
 (defthm fn-shb-p-of-h-add
   (implies (and (fn-shs-p fn-shs) (natp i))
            (fn-shs-p (fn-shs-h-add i regs fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-h-add fn-shs-add$inline) (fn-shs-p))))))

(local
 (defthm fn-shb-p-of-compress-loaded
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-compress-loaded fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-compress-loaded) (fn-shs-p))))))

; -----------------------------------------------------------------------------
; The third message reader: the padded message (append PREFIX buffer) at an
; index.  LP is the prefix length and N the message length, carried so that
; no byte read walks the prefix for its length.

(defun fn-shb-byte (i n prefix lp fn-octets)
  (declare (type (integer 0 *) i n lp)
           (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (= n (+ lp (fn-octets-len fn-octets)))
                              (< i (fn-shs-pad-len n)))))
  (cond ((< i lp) (fn-shs-octet (nth i prefix)))
        ((< i n) (mbe :logic (fn-sha256-byte (fn-octets-get (- i lp) fn-octets))
                      :exec (fn-octets-get (- i lp) fn-octets)))
        (t (fn-shs-tail-byte i n))))

(defthm fn-shb-u8-of-byte
  (and (integerp (fn-shb-byte i n prefix lp fn-octets))
       (<= 0 (fn-shb-byte i n prefix lp fn-octets))
       (< (fn-shb-byte i n prefix lp fn-octets) 256))
  :rule-classes ((:type-prescription
                  :corollary (and (integerp (fn-shb-byte i n prefix lp fn-octets))
                                  (<= 0 (fn-shb-byte i n prefix lp fn-octets))))
                 (:linear :corollary (< (fn-shb-byte i n prefix lp fn-octets) 256))
                 (:rewrite :corollary (unsigned-byte-p 8 (fn-shb-byte i n prefix lp fn-octets))))
  :hints (("Goal" :in-theory (enable fn-shs-octet$inline))))

(local (in-theory (disable fn-shb-byte)))

(defun fn-shb-load-word (j base n prefix lp fn-octets fn-shs)
  (declare (type (integer 0 15) j) (type (integer 0 *) base n lp)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (= n (+ lp (fn-octets-len fn-octets)))
                              (<= (+ base 64) (fn-shs-pad-len n)))
                  :guard-hints (("Goal" :in-theory (enable fn-shs-be-word$inline)))))
  (let ((i (+ base (* 4 j))))
    (fn-shs-w-set j
                  (fn-shs-be-word (fn-shb-byte i n prefix lp fn-octets)
                                  (fn-shb-byte (+ i 1) n prefix lp fn-octets)
                                  (fn-shb-byte (+ i 2) n prefix lp fn-octets)
                                  (fn-shb-byte (+ i 3) n prefix lp fn-octets))
                  fn-shs)))

(local
 (defthm fn-shb-p-of-load-word
   (implies (and (fn-shs-p fn-shs) (natp j) (< j 16))
            (fn-shs-p (fn-shb-load-word j base n prefix lp fn-octets fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-be-word$inline) (fn-shs-p))))))

(local (in-theory (disable fn-shb-load-word)))

(defun fn-shb-load-block (j base n prefix lp fn-octets fn-shs)
  (declare (type (integer 0 16) j) (type (integer 0 *) base n lp)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (= n (+ lp (fn-octets-len fn-octets)))
                              (<= (+ base 64) (fn-shs-pad-len n)))
                  :measure (nfix (- 16 j))))
  (if (mbe :logic (zp (- 16 j)) :exec (= j 16))
      fn-shs
    (let ((fn-shs (fn-shb-load-word j base n prefix lp fn-octets fn-shs)))
      (fn-shb-load-block (+ j 1) base n prefix lp fn-octets fn-shs))))

(local
 (defthm fn-shb-p-of-load-block
   (implies (and (fn-shs-p fn-shs) (natp j))
            (fn-shs-p (fn-shb-load-block j base n prefix lp fn-octets fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shb-load-block))))

(defun fn-shb-compress (b n prefix lp fn-octets fn-shs)
  (declare (type (integer 0 *) b n lp)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (= n (+ lp (fn-octets-len fn-octets)))
                              (< b (fn-shs-nblocks n)))))
  (let ((fn-shs (fn-shb-load-block 0 (* 64 b) n prefix lp fn-octets fn-shs)))
    (fn-shs-compress-loaded fn-shs)))

(local
 (defthm fn-shb-p-of-compress
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shb-compress b n prefix lp fn-octets fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shb-compress))))

(defun fn-shb-blocks (b nb n prefix lp fn-octets fn-shs)
  (declare (type (integer 0 *) b nb n lp)
           (xargs :stobjs (fn-octets fn-shs)
                  :guard (and (true-listp prefix) (= lp (len prefix))
                              (= n (+ lp (fn-octets-len fn-octets)))
                              (= nb (fn-shs-nblocks n)) (<= b nb))
                  :measure (nfix (- nb b))))
  (if (mbe :logic (zp (- nb b)) :exec (= b nb))
      fn-shs
    (let ((fn-shs (fn-shb-compress b n prefix lp fn-octets fn-shs)))
      (fn-shb-blocks (+ b 1) nb n prefix lp fn-octets fn-shs))))

(local
 (defthm fn-shb-p-of-blocks
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shb-blocks b nb n prefix lp fn-octets fn-shs)))
   :hints (("Goal" :in-theory (disable fn-shs-p)))))

(local (in-theory (disable (:d fn-shb-blocks))))

(defun fn-shb-digest (prefix fn-octets fn-shs)
  (declare (xargs :stobjs (fn-octets fn-shs) :guard (true-listp prefix)))
  (let* ((lp (len prefix))
         (n (+ lp (fn-octets-len fn-octets)))
         (fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))
         (fn-shs (fn-shb-blocks 0 (fn-shs-nblocks n) n prefix lp fn-octets fn-shs)))
    (mv (fn-shs-h-octets 0 fn-shs) fn-shs)))

(defun fn-sha256-of-prefixed-buffer (prefix fn-octets)
  ; SHA-256 of (append PREFIX buffer): the prefix read from the list, the
  ; buffer in place by index, over a local word stobj.
  (declare (xargs :stobjs fn-octets :guard (true-listp prefix)))
  (with-local-stobj fn-shs
    (mv-let (digest fn-shs) (fn-shb-digest prefix fn-octets fn-shs)
      digest)))

; =============================================================================
; The correspondence: the buffer reader is the list reader on the suffix.

; The list reader's remaining message at index i: the suffix, stopping at an
; atom, so that an improper value is carried without a hypothesis.
(local
 (defun fn-shb-rest (i m)
   (declare (xargs :guard (natp i)))
   (if (zp i)
       m
     (if (consp m) (fn-shb-rest (1- i) (cdr m)) m))))

(local
 (defthm fn-shb-rest-0
   (equal (fn-shb-rest 0 m) m)))

(local
 (defthm fn-shb-consp-rest-below
   (implies (and (natp i) (< i (len m)))
            (consp (fn-shb-rest i m)))
   :hints (("Goal" :induct (fn-shb-rest i m)))))

(local
 (defthm fn-shb-consp-rest-past
   (implies (and (natp i) (<= (len m) i))
            (not (consp (fn-shb-rest i m))))
   :hints (("Goal" :induct (fn-shb-rest i m)))))

(local
 (defthm fn-shb-car-rest
   (implies (natp i)
            (equal (car (fn-shb-rest i m)) (nth i m)))
   :hints (("Goal" :in-theory (enable nth) :induct (fn-shb-rest i m)))))

(local
 (defthm fn-shb-rest-succ
   (implies (natp i)
            (equal (fn-shb-rest (+ 1 i) m)
                   (if (consp (fn-shb-rest i m))
                       (cdr (fn-shb-rest i m))
                     (fn-shb-rest i m))))
   :hints (("Goal" :induct (fn-shb-rest i m)))))

(local
 (defthm fn-shb-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-shb-nth-of-append
   (implies (natp i)
            (equal (nth i (append a b))
                   (if (< i (len a)) (nth i a) (nth (- i (len a)) b))))
   :hints (("Goal" :in-theory (enable nth) :induct (nth i a)))))

(local (in-theory (disable fn-shb-rest)))

; The message length is written as ACL2 orders the sum, (+ (len fn-octets)
; (len prefix)), so that each lemma below is a rewrite rule that matches
; the normalised goal; `len' and `append' stay closed so that the message
; and its length stay one term each.

; The byte: on the message (append prefix value) at any index, by cases on
; whether the index is within the message.
(local
 (defthm fn-shb-list-byte-is-byte
   (implies (natp i)
            (equal (fn-shs-list-byte i (+ (len fn-octets) (len prefix))
                                     (fn-shb-rest i (append prefix fn-octets)))
                   (list (fn-shb-byte i (+ (len fn-octets) (len prefix))
                                      prefix (len prefix) fn-octets)
                         (fn-shb-rest (+ 1 i) (append prefix fn-octets)))))
   :hints (("Goal" :cases ((< i (+ (len fn-octets) (len prefix))))
            :in-theory (enable fn-shs-list-byte fn-shs-octet$inline fn-shb-byte)))))

; From here on the suffix facts are cited, never rewritten with: as rules
; they open the suffix term the lemmas carry.
(local (deftheory fn-shb-suffix-rules
         '(fn-shb-rest-succ fn-shb-car-rest fn-shb-consp-rest-below
           fn-shb-consp-rest-past fn-shb-list-byte-is-byte len binary-append)))

(local
 (defthm fn-shb-load-list-word-is-load-word
   (implies (and (natp j) (natp base))
            (equal (fn-shs-load-list-word j base (+ (len fn-octets) (len prefix))
                                          (fn-shb-rest (+ base (* 4 j)) (append prefix fn-octets))
                                          fn-shs)
                   (list (fn-shb-rest (+ 4 base (* 4 j)) (append prefix fn-octets))
                         (fn-shb-load-word j base (+ (len fn-octets) (len prefix))
                                           prefix (len prefix) fn-octets fn-shs))))
   :hints (("Goal" :in-theory (e/d (fn-shs-load-list-word fn-shb-load-word)
                                   (fn-shb-suffix-rules))
            :use ((:instance fn-shb-list-byte-is-byte (i (+ base (* 4 j))))
                  (:instance fn-shb-list-byte-is-byte (i (+ 1 base (* 4 j))))
                  (:instance fn-shb-list-byte-is-byte (i (+ 2 base (* 4 j))))
                  (:instance fn-shb-list-byte-is-byte (i (+ 3 base (* 4 j)))))))))

; The two list loops, opened one step at a time (the rewriter does not
; unfold them under the induction below).
(local
 (defthm fn-shb-open-load-list-block-step
   (implies (and (natp j) (< j 16))
            (equal (fn-shs-load-list-block j base n rest fn-shs)
                   (fn-shs-load-list-block
                    (+ 1 j) base n
                    (mv-nth 0 (fn-shs-load-list-word j base n rest fn-shs))
                    (mv-nth 1 (fn-shs-load-list-word j base n rest fn-shs)))))
   :hints (("Goal" :expand ((fn-shs-load-list-block j base n rest fn-shs))))))

(local
 (defthm fn-shb-open-load-list-block-end
   (implies (zp (- 16 j))
            (equal (fn-shs-load-list-block j base n rest fn-shs) (list rest fn-shs)))
   :hints (("Goal" :expand ((fn-shs-load-list-block j base n rest fn-shs))))))

(local
 (defthm fn-shb-open-blocks-list-step
   (implies (and (natp b) (natp nb) (< b nb))
            (equal (fn-shs-blocks-list b nb n rest fn-shs)
                   (fn-shs-blocks-list
                    (+ 1 b) nb n
                    (mv-nth 0 (fn-shs-compress-list b n rest fn-shs))
                    (mv-nth 1 (fn-shs-compress-list b n rest fn-shs)))))
   :hints (("Goal" :expand ((fn-shs-blocks-list b nb n rest fn-shs))))))

(local
 (defthm fn-shb-open-blocks-list-end
   (implies (zp (- nb b))
            (equal (fn-shs-blocks-list b nb n rest fn-shs) fn-shs))
   :hints (("Goal" :expand ((fn-shs-blocks-list b nb n rest fn-shs))))))

(local
 (defthm fn-shb-load-list-block-is-load-block
   (implies (and (natp j) (<= j 16) (natp base))
            (equal (fn-shs-load-list-block j base (+ (len fn-octets) (len prefix))
                                           (fn-shb-rest (+ base (* 4 j)) (append prefix fn-octets))
                                           fn-shs)
                   (list (fn-shb-rest (+ 64 base) (append prefix fn-octets))
                         (fn-shb-load-block j base (+ (len fn-octets) (len prefix))
                                            prefix (len prefix) fn-octets fn-shs))))
   :hints (("Goal" :induct (fn-shb-load-block j base (+ (len fn-octets) (len prefix))
                                              prefix (len prefix) fn-octets fn-shs)
            :in-theory (e/d (fn-shb-load-block) (fn-shb-suffix-rules))))))

(local
 (defthm fn-shb-compress-list-is-compress
   (implies (natp b)
            (equal (fn-shs-compress-list b (+ (len fn-octets) (len prefix))
                                         (fn-shb-rest (* 64 b) (append prefix fn-octets))
                                         fn-shs)
                   (list (fn-shb-rest (+ 64 (* 64 b)) (append prefix fn-octets))
                         (fn-shb-compress b (+ (len fn-octets) (len prefix))
                                          prefix (len prefix) fn-octets fn-shs))))
   ; The openers stay closed here: on the constant word index they would
   ; unroll the sixteen words instead of leaving the block lemma's instance.
   :hints (("Goal" :in-theory (e/d (fn-shs-compress-list fn-shb-compress)
                                   (fn-shb-suffix-rules
                                    fn-shb-open-load-list-block-step
                                    fn-shb-open-load-list-block-end))
            :use ((:instance fn-shb-load-list-block-is-load-block
                             (j 0) (base (* 64 b))))))))

(local
 (defthm fn-shb-blocks-list-is-blocks
   (implies (and (natp b) (natp nb))
            (equal (fn-shs-blocks-list b nb (+ (len fn-octets) (len prefix))
                                       (fn-shb-rest (* 64 b) (append prefix fn-octets))
                                       fn-shs)
                   (fn-shb-blocks b nb (+ (len fn-octets) (len prefix))
                                  prefix (len prefix) fn-octets fn-shs)))
   :hints (("Goal" :induct (fn-shb-blocks b nb (+ (len fn-octets) (len prefix))
                                          prefix (len prefix) fn-octets fn-shs)
            :in-theory (e/d (fn-shb-blocks) (fn-shb-suffix-rules))))))

(local
 (defthm fn-shb-digest-list-is-digest
   (equal (fn-shs-digest-list (append prefix fn-octets) fn-shs)
          (fn-shb-digest prefix fn-octets fn-shs))
   :hints (("Goal" :in-theory (e/d (fn-shs-digest-list fn-shb-digest)
                                   (fn-shb-suffix-rules
                                    fn-shb-open-blocks-list-step
                                    fn-shb-open-blocks-list-end))
            :use ((:instance fn-shb-blocks-list-is-blocks
                             (b 0)
                             (nb (fn-shs-nblocks (+ (len fn-octets) (len prefix))))
                             (fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))))))))

(local (in-theory (disable fn-shb-digest)))

; The keystone: the buffer digest is the list model of the appended message,
; on every prefix and every value.  The creator stays a term (as in
; sha256-stobj: its executable counterpart would turn it into the arrays
; before the digest rules can match).
(defthm fn-sha256-of-prefixed-buffer-is-sha256
  (equal (fn-sha256-of-prefixed-buffer prefix fn-octets)
         (fn-sha256 (append prefix fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-sha256-stobj)
                                  (fn-sha256-stobj-is-sha256
                                   (:e create-fn-shs) (:d create-fn-shs)))
           :use ((:instance fn-sha256-stobj-is-sha256
                            (m (append prefix fn-octets)))))))

(local
 (defthm fn-shb-sha256-octet-listp-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-sha256-octet-listp (append a b)))
   :hints (("Goal" :in-theory (enable fn-sha256-octet-listp fn-cbor-octet-listp
                                      fn-cbor-octetp)))))

(defthm fn-sha256-of-prefixed-buffer-is-sha256-of-octets
  ; Its instance on the domain fn digests: an octet prefix and a buffer value
  ; (the recognizer of every live buffer).  The two sides agree on every
  ; object (the keystone); the hypotheses are proof support, as in
  ; sha256-stobj's instance.
  (implies (and (fn-cbor-octet-listp prefix) (fn-octets-p fn-octets))
           (equal (fn-sha256-of-prefixed-buffer prefix fn-octets)
                  (fn-sha256-of-octets (append prefix fn-octets))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sha256-is-of-octets-on-octets
                                   (m (append prefix fn-octets)))))))

; -----------------------------------------------------------------------------
; The subject identity over the buffer.

(local
 (defthm fn-shb-cbor-octet-listp-of-sha256-octet-listp
   (implies (fn-sha256-octet-listp xs)
            (fn-cbor-octet-listp xs))
   :hints (("Goal" :in-theory (enable fn-sha256-octet-listp fn-cbor-octet-listp
                                      fn-cbor-octetp)))))

(local
 (defthm fn-shb-true-listp-of-subject-prefix
   (true-listp (fn-id-subject-prefix n))
   :hints (("Goal" :in-theory (enable fn-id-subject-prefix fn-cbor-u32-bytes)))))

(defun fn-shb-subject-id (fn-octets)
  ; `fn-id-subject-of-payload' with the payload in the buffer: the subject
  ; preimage is the fixed head for the buffer's length, then the buffer.
  (declare (xargs :stobjs fn-octets
                  :guard (<= (fn-octets-len fn-octets) *fn-cbor-max-uint*)
                  :guard-hints (("Goal" :in-theory (enable fn-id-digestp)))))
  (fn-id-subject
   (fn-sha256-of-prefixed-buffer (fn-id-subject-prefix (fn-octets-len fn-octets))
                                 fn-octets)))

(defthm fn-shb-subject-id-is-id-subject-of-sha256-preimage
  ; The buffer identity is the specification's identity with `fn-sha256' as
  ; the digest: `fn-id-subject-of-payload' under books/crypto-attach.lisp,
  ; which binds `fn-frame-digest' to `fn-sha256-stobj' (= `fn-sha256').
  (equal (fn-shb-subject-id fn-octets)
         (fn-id-subject (fn-sha256 (fn-id-subject-preimage fn-octets))))
  :hints (("Goal" :in-theory (enable fn-id-subject-preimage))))

;; The entry the served POST calls (host/native/io.lisp fnn-subject-id-buffer
;; through fnn-core): the digest when the buffer's length is in the CBOR uint
;; domain, else NIL.  It is guard-verified with guard T, so the host's call runs
;; the compiled stobj code directly.  Its :program predecessor in
;; host/owner-host.lisp (fn-owner-subject-id-buffer) reached the local fn-shs
;; updaters from an unverified caller, which ACL2 reports as invariant risk on
;; standard output at every first POST (qual-e747dbcc A4).
(defun fn-shb-subject-id-bounded (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (<= (fn-octets-len fn-octets) *fn-cbor-max-uint*)
      (fn-shb-subject-id fn-octets)
    nil))

(defthm fn-shb-subject-id-bounded-unfolds
  (equal (fn-shb-subject-id-bounded fn-octets)
         (if (<= (fn-octets-len fn-octets) *fn-cbor-max-uint*)
             (fn-id-subject (fn-sha256 (fn-id-subject-preimage fn-octets)))
           nil))
  :hints (("Goal" :in-theory '(fn-shb-subject-id-bounded
                               fn-shb-subject-id-is-id-subject-of-sha256-preimage))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2): the stobj functions are the
; executable path; what leaves is the correspondence.  Only `:definition'
; runes are withdrawn.

(deftheory fn-shb-internals
  '((:d fn-shb-byte) (:d fn-shb-load-word) (:d fn-shb-load-block)
    (:d fn-shb-compress) (:d fn-shb-blocks) (:d fn-shb-digest)
    (:d fn-sha256-of-prefixed-buffer) (:d fn-shb-subject-id)))

(in-theory (disable fn-shb-internals))
