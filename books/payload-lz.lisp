; fn: the LZ payload codec's decoder and seal check (lane codec-c1, brief C1
; of planning/evidence/article-compression-2026-09-27.md section 6).
; Prefix `fn-lz-'.
;
; The format is the LZ4 block format (lz4/doc/lz4_Block_format.md): a run
; of sequences, each a token (high nibble the literal count, low nibble the
; match length less 4, a nibble of 15 continued by octets that add until
; one is not 255), the literals, then a two-octet little-endian offset and
; the match; the last sequence is literals only and ends the block.  The
; dictionary is a prefix: an offset may reach back past the start of the
; output into the dictionary's tail, as `LZ4_decompress_safe_usingDict'
; reads it.  Any block liblz4 or liblz4-HC writes (with or without a
; dictionary) decodes here; the decoder also accepts blocks the encoder's
; end-of-block conventions would not produce (a match ending within the
; last five octets), which are harmless: what the decoder produces is the
; only thing a seal trusts.
;
; The decoder is `fn-lz-run', a tail-recursive loop over three octet
; buffers (abstract stobjs congruent to `fn-octets', books/octets-stobj.lisp;
; one byte per octet at run time, the octet list logically): the block in
; `fn-octets' cells [START, END), the dictionary in `fn-lz-dict' and the
; output appended to `fn-lz-out'.  Its unit of work is `fn-lz-step', a
; state machine that reads at most one input octet and appends at most one
; output octet; `fn-lz-advance' takes a whole sequence (`fn-lz-seq'), a
; whole literal run (`fn-lz-copy-lits') or a whole match
; (`fn-lz-copy-match') in one tight loop when it fits the input, LIM and
; the budget, and one step otherwise.  The budget B counts steps (a copy
; of K octets counts K, a sequence L + M + 9, what its single steps would
; count), so a caller runs the decoder in quanta and resumes from the
; state it returns (status :more), which is the D27 shape: exhausting a
; quantum yields, it never truncates.  The output never grows past LIM,
; the length the row records (`fn-lz-run-out-len-bound'), a length
; extension that would pass LIM is refused as it is read, the run only
; appends (`fn-lz-run-extends-out'), and nothing is allocated by an input
; field: the one reservation is LIM.
;
; `fn-lz-decode-buf' is the whole block in one budget (three steps per
; input octet and one per output octet cover every well-formed block);
; `fn-lz-decode' is the same function over octet lists (local buffers).
;
; The seal (the brief's check-at-seal).  `fn-lz-seal-form dict octets
; candidate' runs the decoder over the CANDIDATE encoding and answers
; (:lz n candidate) when it decodes to exactly OCTETS, else (:raw octets).
; `fn-lz-denote' is what a reader serves from a form: the decode of an :lz
; form, the octets of a :raw one.  KEYSTONE `fn-lz-seal-form-denotes': with
; no hypothesis, the denotation of the sealed form is the octets it was
; sealed from, whatever the candidate.  Nothing is assumed about the
; encoder: a wrong or hostile encoding costs ratio (it seals :raw), never
; octets.  The served octets come from the decoder that the denotation
; names, which is the function a reader runs (C2 wires the reader).
;
; `fn-lz-literal-block' is a trivial encoder (one literal-only sequence),
; and `fn-lz-seal-form-of-literal-block' says it always seals as :lz:
; the :lz arm is reachable for every payload, so the keystone is not
; carried by the :raw arm alone.

(in-package "ACL2")
(include-book "octets-stobj")


(defabsstobj fn-lz-dict
  :foundation fn-octets$c
  :recognizer (fn-lz-dict-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-lz-dict :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-lz-dict-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-lz-dict-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-lz-dict-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-lz-dict-append-octet :logic fn-octets$a-append-octet
                                     :exec fn-octets$c-append-octet :protect t)
            (fn-lz-dict-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-lz-dict-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                :protect t)
            (fn-lz-dict-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-lz-dict-from-list :logic fn-octets$a-from-list
                                  :exec fn-octets$c-from-list :protect t)
            (fn-lz-dict-append-list :logic fn-octets$a-append-list
                                    :exec fn-oct-write-list :protect t)
            (fn-lz-dict-append-back :logic fn-octets$a-append-back
                                    :exec fn-octets$c-append-back :protect t)
            (fn-lz-dict-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-lz-dict-append-word :logic fn-octets$a-append-word
                                    :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(defabsstobj fn-lz-out
  :foundation fn-octets$c
  :recognizer (fn-lz-out-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-lz-out :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-lz-out-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-lz-out-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-lz-out-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-lz-out-append-octet :logic fn-octets$a-append-octet
                                    :exec fn-octets$c-append-octet :protect t)
            (fn-lz-out-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-lz-out-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                               :protect t)
            (fn-lz-out-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-lz-out-from-list :logic fn-octets$a-from-list
                                 :exec fn-octets$c-from-list :protect t)
            (fn-lz-out-append-list :logic fn-octets$a-append-list
                                   :exec fn-oct-write-list :protect t)
            (fn-lz-out-append-back :logic fn-octets$a-append-back
                                   :exec fn-octets$c-append-back :protect t)
            (fn-lz-out-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-lz-out-append-word :logic fn-octets$a-append-word
                                   :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(local
 (defthm fn-lz-octets-p-is-octet-listp
   (and (equal (fn-octets-p x) (fn-cbor-octet-listp x))
        (equal (fn-lz-dict-p x) (fn-cbor-octet-listp x))
        (equal (fn-lz-out-p x) (fn-cbor-octet-listp x)))
   :hints (("Goal" :in-theory (enable fn-octets-p)))))

(local
 (defthm fn-lz-nth-of-octet-list
   (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
            (and (fn-cbor-octetp (nth i x))
                 (natp (nth i x))
                 (< (nth i x) 256)))
   :rule-classes
   ((:rewrite)
    (:type-prescription
     :corollary (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
                         (natp (nth i x))))
    (:linear
     :corollary (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
                         (and (<= 0 (nth i x)) (< (nth i x) 256)))))))

(local
 (defthm fn-lz-len-of-snoc
   (equal (len (fn-oct-snoc x o)) (1+ (len x)))))

(local
 (defthm fn-lz-octet-listp-true
   (implies (fn-cbor-octet-listp x) (true-listp x))))

(local
 (defthm fn-lz-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; -----------------------------------------------------------------------------
; One octet back from the end of dict ++ out.

(defun fn-lz-back-octet (off fn-lz-dict fn-lz-out)
  (declare (xargs :stobjs (fn-lz-dict fn-lz-out)
                  :guard (and (natp off) (<= 1 off)
                              (<= off (+ (fn-lz-out-len fn-lz-out)
                                         (fn-lz-dict-len fn-lz-dict))))))
  (let ((p (- (fn-lz-out-len fn-lz-out) off)))
    (if (<= 0 p)
        (fn-lz-out-get p fn-lz-out)
      (fn-lz-dict-get (+ (fn-lz-dict-len fn-lz-dict) p) fn-lz-dict))))

(defthm fn-lz-back-octet-octetp
  (implies (and (fn-cbor-octet-listp fn-lz-dict) (fn-cbor-octet-listp fn-lz-out)
                (natp off) (<= 1 off)
                (<= off (+ (len fn-lz-out) (len fn-lz-dict))))
           (fn-cbor-octetp (fn-lz-back-octet off fn-lz-dict fn-lz-out))))

(local (in-theory (disable fn-lz-back-octet)))

; -----------------------------------------------------------------------------
; The state machine.  MODE: 0 token, 1 literal-length extension,
; 2 literals (K left), 3 offset low octet, 4 offset high octet,
; 5 match-length extension, 6 match (K left, OFF back).  M is the token's
; match nibble, IP the input position, END the block's end in FN-OCTETS.
; One step answers (mv status ip mode k m off fn-lz-out): status nil to go
; on, :done (the block ended after a literal run), or a refusal:
; :truncated (input ended inside a sequence), :overflow (the output would
; pass LIM), :offset (an offset of 0 or past dict ++ out), :mode.  A step
; reads at most one input octet and appends at most one output octet.

;; The token's nibbles, closed below; arithmetic-5 for these two only.
(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defun fn-lz-hi (x)
    (declare (xargs :guard (fn-cbor-octetp x)))
    (mbe :logic (nfix (floor (nfix x) 16)) :exec (ash x -4)))

  (defun fn-lz-lo (x)
    (declare (xargs :guard (fn-cbor-octetp x)))
    (mbe :logic (nfix (mod (nfix x) 16)) :exec (- x (* 16 (ash x -4)))))

  (defthm fn-lz-nibbles-natp
    (and (natp (fn-lz-hi x)) (natp (fn-lz-lo x)))
    :rule-classes ((:type-prescription :corollary (natp (fn-lz-hi x)))
                   (:type-prescription :corollary (natp (fn-lz-lo x)))))

  ; A literal-only token: count N in the high nibble, match nibble 0.
  (defthm fn-lz-nibbles-of-literal-token
    (implies (and (natp n) (< n 16))
             (and (equal (fn-lz-hi (* 16 n)) n)
                  (equal (fn-lz-lo (* 16 n)) 0)))))

(local (in-theory (disable fn-lz-hi fn-lz-lo)))

(defun fn-lz-step (ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)
  ; Every state field is read through `nfix', so the guard is the block's
  ; end alone.
  (declare (xargs :stobjs (fn-octets fn-lz-dict fn-lz-out)
                  :guard (and (natp end) (<= end (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :in-theory (disable nfix)))))
  (let ((inlen (min (nfix end) (fn-octets-len fn-octets)))
        (olen (fn-lz-out-len fn-lz-out))
        (ip (nfix ip)) (mode (nfix mode)) (k (nfix k)) (m (nfix m)) (off (nfix off))
        (lim (nfix lim)))
    (case mode
      (0 (if (< ip inlen)
             (let* ((tok (fn-octets-get ip fn-octets))
                    (l (fn-lz-hi tok)))
               (mv nil (1+ ip) (if (eql l 15) 1 2) l (fn-lz-lo tok) off fn-lz-out))
           (mv :truncated ip mode k m off fn-lz-out)))
      (1 (if (< ip inlen)
             (let* ((x (fn-octets-get ip fn-octets))
                    (k (+ k x)))
               (if (< (- lim olen) k)
                   (mv :overflow ip mode k m off fn-lz-out)
                 (mv nil (1+ ip) (if (eql x 255) 1 2) k m off fn-lz-out)))
           (mv :truncated ip mode k m off fn-lz-out)))
      (2 (cond ((zp k)
                (if (<= inlen ip)
                    (mv :done ip mode k m off fn-lz-out)
                  (mv nil ip 3 0 m off fn-lz-out)))
               ((<= inlen ip) (mv :truncated ip mode k m off fn-lz-out))
               ((<= lim olen) (mv :overflow ip mode k m off fn-lz-out))
               (t (let ((fn-lz-out (fn-lz-out-append-octet (fn-octets-get ip fn-octets)
                                                           fn-lz-out)))
                    (mv nil (1+ ip) 2 (1- k) m off fn-lz-out)))))
      (3 (if (< ip inlen)
             (mv nil (1+ ip) 4 k m (fn-octets-get ip fn-octets) fn-lz-out)
           (mv :truncated ip mode k m off fn-lz-out)))
      (4 (if (< ip inlen)
             (let ((off (+ off (* 256 (fn-octets-get ip fn-octets)))))
               (if (or (eql off 0)
                       (< (+ olen (fn-lz-dict-len fn-lz-dict)) off))
                   (mv :offset ip mode k m off fn-lz-out)
                 (mv nil (1+ ip) (if (eql m 15) 5 6) (+ m 4) m off fn-lz-out)))
           (mv :truncated ip mode k m off fn-lz-out)))
      (5 (if (< ip inlen)
             (let* ((x (fn-octets-get ip fn-octets))
                    (k (+ k x)))
               (if (< (- lim olen) k)
                   (mv :overflow ip mode k m off fn-lz-out)
                 (mv nil (1+ ip) (if (eql x 255) 5 6) k m off fn-lz-out)))
           (mv :truncated ip mode k m off fn-lz-out)))
      (6 (cond ((zp k) (mv nil ip 0 0 m off fn-lz-out))
               ((or (zp off) (< (+ olen (fn-lz-dict-len fn-lz-dict)) off))
                (mv :offset ip mode k m off fn-lz-out))
               ((<= lim olen) (mv :overflow ip mode k m off fn-lz-out))
               (t (let ((fn-lz-out (fn-lz-out-append-octet
                                    (fn-lz-back-octet off fn-lz-dict fn-lz-out)
                                    fn-lz-out)))
                    (mv nil ip 6 (1- k) m off fn-lz-out)))))
      (otherwise (mv :mode ip mode k m off fn-lz-out)))))

(defthm fn-lz-step-out-octet-listp
  (implies (and (fn-cbor-octet-listp fn-octets) (fn-cbor-octet-listp fn-lz-dict)
                (fn-cbor-octet-listp fn-lz-out))
           (fn-cbor-octet-listp
            (mv-nth 6 (fn-lz-step ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out))))
  :hints (("Goal" :in-theory (disable nfix))))

; A step appends at most one octet, and only below LIM; what it had is kept.
(local
 (defthm fn-lz-take-of-append-within
   (implies (and (natp n) (<= n (len x)))
            (equal (take n (append x y)) (take n x)))))

(local
 (defthm fn-lz-take-of-snoc-within
   (implies (and (natp n) (<= n (len x)))
            (equal (take n (fn-oct-snoc x o)) (take n x)))))

(local
 (defthm fn-lz-true-listp-of-snoc
   (implies (true-listp x) (true-listp (fn-oct-snoc x o)))))

(local
 (defthm fn-lz-step-out-len-bound
   (<= (len (mv-nth 6 (fn-lz-step ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)))
       (max (nfix lim) (len fn-lz-out)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defthm fn-lz-step-keeps-prefix
   (implies (and (true-listp fn-lz-out) (<= (len p) (len fn-lz-out))
                 (equal (take (len p) fn-lz-out) p))
            (let ((out2 (mv-nth 6 (fn-lz-step ip end mode k m off lim
                                              fn-octets fn-lz-dict fn-lz-out))))
              (and (true-listp out2)
                   (<= (len p) (len out2))
                   (equal (take (len p) out2) p))))
   :hints (("Goal" :in-theory (disable nfix)))))

(local (in-theory (disable fn-lz-step)))

; The two copies, each one tight loop.  A literal run or a match that fits
; the budget, the input and LIM is copied whole; it is what K single steps
; would append (the steps check the same bounds one octet at a time), and
; the steps remain for a run that does not fit, where they stop exactly
; where the bound is met.

(local
 (defthm fn-lz-nfix-when-natp
   (implies (natp x) (equal (nfix x) x))))

;; The bulk executables (lane octets-bulk).  A literal run moves from the
;; block to the output, and a match's dictionary part from the dictionary,
;; seven octets per word (`fn-octets-get-word', `fn-octets-append-word':
;; an export cannot name a second buffer); a match's part within the
;; output is one `append-back', whose logic is octet by octet, so an
;; overlapping match repeats as LZ4 requires.  Each is the :exec of the
;; octet-at-a-time definition below it, and the `-is-' theorems between
;; them are the equalities its guard proof uses.

(defun fn-lz-lits-words (ip n fn-octets fn-lz-out)
  (declare (xargs :stobjs (fn-octets fn-lz-out)
                  :guard (and (natp ip) (natp n)
                              (<= (+ ip n) (fn-octets-len fn-octets)))
                  :measure (nfix n)))
  (if (zp n)
      fn-lz-out
    (let* ((k (min n 7))
           (fn-lz-out (fn-lz-out-append-word (fn-octets-get-word ip k fn-octets) k
                                             fn-lz-out)))
      (fn-lz-lits-words (+ (nfix ip) k) (- n k) fn-octets fn-lz-out))))

(defun fn-lz-dict-words (s n fn-lz-dict fn-lz-out)
  (declare (xargs :stobjs (fn-lz-dict fn-lz-out)
                  :guard (and (natp s) (natp n)
                              (<= (+ s n) (fn-lz-dict-len fn-lz-dict)))
                  :measure (nfix n)))
  (if (zp n)
      fn-lz-out
    (let* ((k (min n 7))
           (fn-lz-out (fn-lz-out-append-word (fn-lz-dict-get-word s k fn-lz-dict) k
                                             fn-lz-out)))
      (fn-lz-dict-words (+ (nfix s) k) (- n k) fn-lz-dict fn-lz-out))))

(defthm fn-lz-len-of-dict-words
  (implies (natp n)
           (equal (len (fn-lz-dict-words s n fn-lz-dict fn-lz-out))
                  (+ (len fn-lz-out) n))))

(defun fn-lz-match-bulk (off n fn-lz-dict fn-lz-out)
  (declare (xargs :stobjs (fn-lz-dict fn-lz-out)
                  :guard (and (natp off) (<= 1 off) (natp n)
                              (<= off (+ (fn-lz-out-len fn-lz-out)
                                         (fn-lz-dict-len fn-lz-dict))))))
  (let ((olen (fn-lz-out-len fn-lz-out)))
    (if (<= off olen)
        (fn-lz-out-append-back off n fn-lz-out)
      (let* ((d (- off olen))
             (j (min d n))
             (fn-lz-out (fn-lz-dict-words (- (fn-lz-dict-len fn-lz-dict) d) j
                                          fn-lz-dict fn-lz-out)))
        (if (< j n)
            (fn-lz-out-append-back off (- n j) fn-lz-out)
          fn-lz-out)))))

(defun fn-lz-copy-lits (ip n fn-octets fn-lz-out)
  (declare (xargs :stobjs (fn-octets fn-lz-out)
                  :guard (and (natp ip) (natp n)
                              (<= (+ ip n) (fn-octets-len fn-octets)))
                  :measure (nfix n)
                  :verify-guards nil))
  (mbe :logic
       (if (zp n)
           fn-lz-out
         (let ((fn-lz-out (fn-lz-out-append-octet (fn-octets-get ip fn-octets) fn-lz-out)))
           (fn-lz-copy-lits (1+ (nfix ip)) (1- n) fn-octets fn-lz-out)))
       :exec (fn-lz-lits-words ip n fn-octets fn-lz-out)))

(defun fn-lz-copy-match (off n fn-lz-dict fn-lz-out)
  (declare (xargs :stobjs (fn-lz-dict fn-lz-out)
                  :guard (and (natp off) (<= 1 off) (natp n)
                              (<= off (+ (fn-lz-out-len fn-lz-out)
                                         (fn-lz-dict-len fn-lz-dict))))
                  :measure (nfix n)
                  :verify-guards nil))
  (mbe :logic
       (if (or (zp n) (zp off)
               (< (+ (fn-lz-out-len fn-lz-out) (fn-lz-dict-len fn-lz-dict)) off))
           fn-lz-out
         (let ((fn-lz-out (fn-lz-out-append-octet (fn-lz-back-octet off fn-lz-dict fn-lz-out)
                                                  fn-lz-out)))
           (fn-lz-copy-match off (1- n) fn-lz-dict fn-lz-out)))
       :exec (fn-lz-match-bulk off n fn-lz-dict fn-lz-out)))

; The equalities the two :exec bodies rest on, over octet lists.
(local
 (defthm fn-lz-minus-minus
   (implies (acl2-numberp x) (equal (- (- x)) x))))

(local
 (defthm fn-lz-append-assoc-early
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthmd fn-lz-nthcdr-cons-split
   (implies (and (natp i) (< i (len xs)))
            (equal (nthcdr i xs) (cons (nth i xs) (nthcdr (1+ i) xs))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defun fn-lz-ts-ind (i k)
   (if (zp k) i (fn-lz-ts-ind (1+ i) (1- k)))))

(local
 (defthm fn-lz-take-nthcdr-split
   (implies (and (equal j (+ i k))
                 (natp i) (natp k) (natp m) (<= (+ i k m) (len xs)))
            (equal (append (take k (nthcdr i xs)) (take m (nthcdr j xs)))
                   (take (+ k m) (nthcdr i xs))))
   :hints (("Goal" :induct (fn-lz-ts-ind i k)
            :in-theory (enable fn-lz-nthcdr-cons-split)))))

(local
 (defthm fn-lz-take-zero
   (equal (take 0 x) nil)))

(local
 (defthm fn-lz-copy-lits-is-append
   (implies (and (natp ip) (natp n) (<= (+ ip n) (len fn-octets)) (true-listp fn-lz-out))
            (equal (fn-lz-copy-lits ip n fn-octets fn-lz-out)
                   (append fn-lz-out (take n (nthcdr ip fn-octets)))))
   :hints (("Goal" :induct (fn-lz-copy-lits ip n fn-octets fn-lz-out)
            :in-theory (enable fn-lz-nthcdr-cons-split)))))

(defthm fn-lz-lits-words-is-append
  (implies (and (fn-cbor-octet-listp fn-octets) (true-listp fn-lz-out)
                (natp ip) (natp n) (<= (+ ip n) (len fn-octets)))
           (equal (fn-lz-lits-words ip n fn-octets fn-lz-out)
                  (append fn-lz-out (take n (nthcdr ip fn-octets)))))
  :hints (("Goal" :induct (fn-lz-lits-words ip n fn-octets fn-lz-out)
           :in-theory (disable take))))

(local
 (defthm fn-lz-dict-words-is-append
   (implies (and (fn-cbor-octet-listp fn-lz-dict) (true-listp fn-lz-out)
                 (natp s) (natp n) (<= (+ s n) (len fn-lz-dict)))
            (equal (fn-lz-dict-words s n fn-lz-dict fn-lz-out)
                   (append fn-lz-out (take n (nthcdr s fn-lz-dict)))))
   :hints (("Goal" :induct (fn-lz-dict-words s n fn-lz-dict fn-lz-out)
            :in-theory (disable take)))))

(local
 (defthm fn-lz-copy-match-within-out
   (implies (and (posp off) (<= off (len fn-lz-out)) (true-listp fn-lz-out))
            (equal (fn-lz-copy-match off n fn-lz-dict fn-lz-out)
                   (fn-oct-back-copy off n fn-lz-out)))
   :hints (("Goal" :induct (fn-lz-copy-match off n fn-lz-dict fn-lz-out)
            :in-theory (enable fn-lz-back-octet)
            :expand ((fn-oct-back-copy off n fn-lz-out))))))

(local
 (defthm fn-lz-copy-match-within-dict
   (implies (and (natp n) (posp off) (<= (+ (len fn-lz-out) n) off)
                 (<= off (+ (len fn-lz-out) (len fn-lz-dict)))
                 (true-listp fn-lz-out))
            (equal (fn-lz-copy-match off n fn-lz-dict fn-lz-out)
                   (append fn-lz-out
                           (take n (nthcdr (+ (len fn-lz-dict) (len fn-lz-out) (- off))
                                           fn-lz-dict)))))
   :hints (("Goal" :induct (fn-lz-copy-match off n fn-lz-dict fn-lz-out)
            :in-theory (e/d (fn-lz-back-octet fn-lz-nthcdr-cons-split) (nth nthcdr))))))

(local
 (defthm fn-lz-copy-match-split
   (implies (and (natp a) (natp b))
            (equal (fn-lz-copy-match off (+ a b) fn-lz-dict fn-lz-out)
                   (fn-lz-copy-match off b fn-lz-dict
                                     (fn-lz-copy-match off a fn-lz-dict fn-lz-out))))
   :hints (("Goal" :induct (fn-lz-copy-match off a fn-lz-dict fn-lz-out)))))

(local
 (defthm fn-lz-dict-words-is-copy-match
   (implies (and (natp n) (posp off) (<= (+ (len fn-lz-out) n) off)
                 (<= off (+ (len fn-lz-out) (len fn-lz-dict)))
                 (fn-cbor-octet-listp fn-lz-dict) (true-listp fn-lz-out)
                 (equal s (+ (len fn-lz-dict) (len fn-lz-out) (- off))))
            (equal (fn-lz-dict-words s n fn-lz-dict fn-lz-out)
                   (fn-lz-copy-match off n fn-lz-dict fn-lz-out)))
   :rule-classes nil))

(local
 (defthm fn-lz-true-listp-of-copy-match
   (implies (true-listp fn-lz-out)
            (true-listp (fn-lz-copy-match off n fn-lz-dict fn-lz-out)))))

(defthm fn-lz-match-bulk-is-copy-match
  (implies (and (fn-cbor-octet-listp fn-lz-dict) (true-listp fn-lz-out)
                (natp off) (<= 1 off) (natp n)
                (<= off (+ (len fn-lz-out) (len fn-lz-dict))))
           (equal (fn-lz-match-bulk off n fn-lz-dict fn-lz-out)
                  (fn-lz-copy-match off n fn-lz-dict fn-lz-out)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lz-copy-match fn-lz-copy-match-split
                               fn-lz-dict-words-is-append fn-lz-copy-match-within-dict)
           :use ((:instance fn-lz-dict-words-is-copy-match
                            (s (+ (len fn-lz-dict) (len fn-lz-out) (- off)))
                            (n (min n (- off (len fn-lz-out)))))
                 (:instance fn-lz-copy-match-split
                            (a (- off (len fn-lz-out))) (b (- n (- off (len fn-lz-out)))))
                 (:instance fn-lz-copy-match-within-dict
                            (n (- off (len fn-lz-out))))))))

(local
 (defthm fn-lz-octet-listp-of-nthcdr
   (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr i xs)))))

(local
 (defthm fn-lz-octet-listp-of-take
   (implies (and (fn-cbor-octet-listp xs) (<= (nfix n) (len xs)))
            (fn-cbor-octet-listp (take n xs)))))

(verify-guards fn-lz-copy-lits
  :hints (("Goal" :in-theory (e/d (fn-lz-nthcdr-cons-split) (nth nthcdr)))))
(verify-guards fn-lz-copy-match
  :hints (("Goal" :in-theory (disable nth nthcdr))))

(local (in-theory (disable fn-lz-copy-lits-is-append fn-lz-lits-words-is-append
                           fn-lz-dict-words-is-append fn-lz-copy-match-within-out
                           fn-lz-copy-match-within-dict fn-lz-copy-match-split
                           fn-lz-match-bulk-is-copy-match)))
(in-theory (disable fn-lz-lits-words-is-append fn-lz-match-bulk-is-copy-match))

(defthm fn-lz-copy-lits-octet-listp
  (implies (and (fn-cbor-octet-listp fn-octets) (fn-cbor-octet-listp fn-lz-out)
                (natp ip) (natp n) (<= (+ ip n) (len fn-octets)))
           (fn-cbor-octet-listp (fn-lz-copy-lits ip n fn-octets fn-lz-out))))

(defthm fn-lz-copy-match-octet-listp
  (implies (and (fn-cbor-octet-listp fn-lz-dict) (fn-cbor-octet-listp fn-lz-out))
           (fn-cbor-octet-listp (fn-lz-copy-match off n fn-lz-dict fn-lz-out))))

(defthm fn-lz-len-of-copy-lits
  (implies (natp n)
           (equal (len (fn-lz-copy-lits ip n fn-octets fn-lz-out))
                  (+ (len fn-lz-out) n))))

(defthm fn-lz-len-of-copy-match
  (implies (natp n)
           (<= (len (fn-lz-copy-match off n fn-lz-dict fn-lz-out))
               (+ (len fn-lz-out) n)))
  :rule-classes :linear)

(defthm fn-lz-len-of-copy-match-lower
  (<= (len fn-lz-out) (len (fn-lz-copy-match off n fn-lz-dict fn-lz-out)))
  :rule-classes :linear)

(local
 (defthm fn-lz-copy-lits-keeps-prefix
   (implies (and (true-listp fn-lz-out) (<= (len p) (len fn-lz-out))
                 (equal (take (len p) fn-lz-out) p))
            (and (true-listp (fn-lz-copy-lits ip n fn-octets fn-lz-out))
                 (equal (take (len p) (fn-lz-copy-lits ip n fn-octets fn-lz-out)) p)))))

(local
 (defthm fn-lz-copy-match-keeps-prefix
   (implies (and (true-listp fn-lz-out) (<= (len p) (len fn-lz-out))
                 (equal (take (len p) fn-lz-out) p))
            (and (true-listp (fn-lz-copy-match off n fn-lz-dict fn-lz-out))
                 (equal (take (len p) (fn-lz-copy-match off n fn-lz-dict fn-lz-out)) p)))))

(local (in-theory (disable fn-lz-copy-lits fn-lz-copy-match)))

; A whole sequence without length extensions, when it fits the input,
; LIM and the budget: the token, L literals, the offset and the match of
; M + 4, what the L + M + 9 single steps from mode 0 would do.  Answers
; (mv ok b2 ip2 m2 off2 fn-lz-out); OK nil (and the output untouched) when
; the sequence does not fit, and the steps take it.

(defun fn-lz-seq (b ip end lim fn-octets fn-lz-dict fn-lz-out)
  (declare (xargs :stobjs (fn-octets fn-lz-dict fn-lz-out)
                  :guard (and (natp b) (natp end) (<= end (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :in-theory (disable nth fn-cbor-octet-listp)))))
  (let ((olen (fn-lz-out-len fn-lz-out))
        (inlen (min (nfix end) (fn-octets-len fn-octets))))
    (if (and (natp ip) (< ip inlen) (natp lim) (natp b))
        (let* ((tok (fn-octets-get ip fn-octets))
               (l (fn-lz-hi tok))
               (mm (fn-lz-lo tok)))
          (if (and (< l 15) (< mm 15)
                   (<= (+ ip 3 l) inlen)
                   (<= (+ l mm 9) b)
                   (<= (+ olen l mm 4) lim))
              (let ((o (+ (fn-octets-get (+ ip 1 l) fn-octets)
                          (* 256 (fn-octets-get (+ ip 2 l) fn-octets)))))
                (if (and (<= 1 o) (<= o (+ olen l (fn-lz-dict-len fn-lz-dict))))
                    (let* ((fn-lz-out (fn-lz-copy-lits (+ ip 1) l fn-octets fn-lz-out))
                           (fn-lz-out (fn-lz-copy-match o (+ mm 4) fn-lz-dict fn-lz-out)))
                      (mv t (- b (+ l mm 9)) (+ ip 3 l) mm o fn-lz-out))
                  (mv nil b ip 0 0 fn-lz-out)))
            (mv nil b ip 0 0 fn-lz-out)))
      (mv nil b ip 0 0 fn-lz-out))))

(defthm fn-lz-seq-budget
  (implies (car (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out))
           (and (integerp (mv-nth 1 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out)))
                (<= 0 (mv-nth 1 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out)))
                (< (mv-nth 1 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out))
                   (nfix b))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (car (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out))
                           (< (mv-nth 1 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out))
                              (nfix b))))))

(defthm fn-lz-seq-declined
  (implies (not (car (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out)))
           (equal (mv-nth 5 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out))
                  fn-lz-out)))

(defthm fn-lz-seq-out-octet-listp
  (implies (and (fn-cbor-octet-listp fn-octets) (fn-cbor-octet-listp fn-lz-dict)
                (fn-cbor-octet-listp fn-lz-out))
           (fn-cbor-octet-listp
            (mv-nth 5 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out)))))

(defthm fn-lz-seq-out-len-bound
  (<= (len (mv-nth 5 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out)))
      (max (nfix lim) (len fn-lz-out)))
  :rule-classes :linear)

(local
 (defthm fn-lz-seq-keeps-prefix
   (implies (and (true-listp fn-lz-out) (<= (len p) (len fn-lz-out))
                 (equal (take (len p) fn-lz-out) p))
            (let ((out2 (mv-nth 5 (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out))))
              (and (true-listp out2)
                   (<= (len p) (len out2))
                   (equal (take (len p) out2) p))))))

(local (in-theory (disable fn-lz-seq)))

; One advance of the machine: a whole sequence, a whole literal run or a
; whole match when it fits (each what its single steps would do), else one
; step.  Answers (mv status b2 ip mode k m off fn-lz-out), B2 the budget
; left.

(defun fn-lz-advance (b ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)
  (declare (xargs :stobjs (fn-octets fn-lz-dict fn-lz-out)
                  :guard (and (natp b) (natp end) (<= end (fn-octets-len fn-octets)))))
  (let ((olen (fn-lz-out-len fn-lz-out))
        (b (nfix b)))
    (cond ((eql mode 0)
           (mv-let (ok b2 ip2 m2 off2 fn-lz-out)
             (fn-lz-seq b ip end lim fn-octets fn-lz-dict fn-lz-out)
             (if ok
                 (mv nil b2 ip2 0 0 m2 off2 fn-lz-out)
               (mv-let (st ip mode k m off fn-lz-out)
                 (fn-lz-step ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)
                 (mv st (1- b) ip mode k m off fn-lz-out)))))
          ((and (eql mode 2) (posp k) (natp ip) (<= k b) (natp end)
                (<= (+ ip k) (min end (fn-octets-len fn-octets)))
                (natp lim) (<= (+ olen k) lim))
           (let ((fn-lz-out (fn-lz-copy-lits ip k fn-octets fn-lz-out)))
             (mv nil (- b k) (+ ip k) 2 0 m off fn-lz-out)))
          ((and (eql mode 6) (posp k) (<= k b) (posp off)
                (<= off (+ olen (fn-lz-dict-len fn-lz-dict)))
                (natp lim) (<= (+ olen k) lim))
           (let ((fn-lz-out (fn-lz-copy-match off k fn-lz-dict fn-lz-out)))
             (mv nil (- b k) ip 6 0 m off fn-lz-out)))
          (t
           (mv-let (st ip mode k m off fn-lz-out)
             (fn-lz-step ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)
             (mv st (1- b) ip mode k m off fn-lz-out))))))

(defthm fn-lz-advance-budget
  (implies (not (zp b))
           (let ((b2 (mv-nth 1 (fn-lz-advance b ip end mode k m off lim
                                              fn-octets fn-lz-dict fn-lz-out))))
             (and (integerp b2) (<= 0 b2) (< b2 b))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (not (zp b))
                           (< (mv-nth 1 (fn-lz-advance b ip end mode k m off lim
                                                       fn-octets fn-lz-dict fn-lz-out))
                              b)))))

(defthm fn-lz-advance-out-octet-listp
  (implies (and (fn-cbor-octet-listp fn-octets) (fn-cbor-octet-listp fn-lz-dict)
                (fn-cbor-octet-listp fn-lz-out))
           (fn-cbor-octet-listp
            (mv-nth 7 (fn-lz-advance b ip end mode k m off lim fn-octets fn-lz-dict
                                     fn-lz-out))))
  :hints (("Goal" :in-theory (disable nfix))))

(defthm fn-lz-advance-out-len-bound
  (<= (len (mv-nth 7 (fn-lz-advance b ip end mode k m off lim fn-octets fn-lz-dict
                                    fn-lz-out)))
      (max (nfix lim) (len fn-lz-out)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable nfix))))

(local
 (defthm fn-lz-advance-keeps-prefix
   (implies (and (true-listp fn-lz-out) (<= (len p) (len fn-lz-out))
                 (equal (take (len p) fn-lz-out) p))
            (let ((out2 (mv-nth 7 (fn-lz-advance b ip end mode k m off lim
                                                 fn-octets fn-lz-dict fn-lz-out))))
              (and (true-listp out2)
                   (<= (len p) (len out2))
                   (equal (take (len p) out2) p))))
   :hints (("Goal" :in-theory (disable nfix)))))

(local (in-theory (disable fn-lz-advance)))

(defun fn-lz-run (b ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)
  ; B steps at most, a whole copy of K octets counting K; status :more when
  ; they are spent (resumable from the state answered), else the first
  ; stopping step's status.
  (declare (xargs :stobjs (fn-octets fn-lz-dict fn-lz-out)
                  :guard (and (natp b) (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (nfix b)
                  :verify-guards nil))
  (if (zp b)
      (mv :more ip mode k m off fn-lz-out)
    (mv-let (st b ip mode k m off fn-lz-out)
      (fn-lz-advance b ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)
      (if st
          (mv st ip mode k m off fn-lz-out)
        (fn-lz-run b ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)))))

(defthm fn-lz-run-out-octet-listp
  (implies (and (fn-cbor-octet-listp fn-octets) (fn-cbor-octet-listp fn-lz-dict)
                (fn-cbor-octet-listp fn-lz-out))
           (fn-cbor-octet-listp
            (mv-nth 6 (fn-lz-run b ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)))))

(verify-guards fn-lz-run)

; The output never passes LIM (or its starting length, if that was
; already past): the D27 bound, the only allocation the run makes.
(defthm fn-lz-run-out-len-bound
  (<= (len (mv-nth 6 (fn-lz-run b ip end mode k m off lim fn-octets fn-lz-dict fn-lz-out)))
      (max (nfix lim) (len fn-lz-out)))
  :rule-classes :linear)

; The run only appends: a prefix of the output it started with is a
; prefix of the output it answers.
(local
 (defthm fn-lz-run-keeps-prefix
   (implies (and (true-listp fn-lz-out) (<= (len p) (len fn-lz-out))
                 (equal (take (len p) fn-lz-out) p))
            (equal (take (len p)
                         (mv-nth 6 (fn-lz-run b ip end mode k m off lim
                                              fn-octets fn-lz-dict fn-lz-out)))
                   p))))

(local
 (defthm fn-lz-take-of-own-len
   (implies (true-listp x) (equal (take (len x) x) x))))

(defthm fn-lz-run-extends-out
  (implies (true-listp fn-lz-out)
           (equal (take (len fn-lz-out)
                        (mv-nth 6 (fn-lz-run b ip end mode k m off lim
                                             fn-octets fn-lz-dict fn-lz-out)))
                  fn-lz-out))
  :hints (("Goal" :use ((:instance fn-lz-run-keeps-prefix (p fn-lz-out)))
           :in-theory (disable fn-lz-run-keeps-prefix))))

; -----------------------------------------------------------------------------
; The whole block in one budget.

(defun fn-lz-budget (clen n)
  (declare (xargs :guard (and (natp clen) (natp n))))
  ; three steps per input octet (a token, a zero-length literal run's
  ; transition, a match's end) and one per output octet
  (+ 2 (nfix n) (nfix clen) (nfix clen) (nfix clen)))

(defun fn-lz-decode-buf (start end n fn-octets fn-lz-dict fn-lz-out)
  ; Decode the block in FN-OCTETS cells [START, END) against the dictionary
  ; FN-LZ-DICT into a cleared FN-LZ-OUT; :ok when the block ends exactly at
  ; N octets.
  (declare (xargs :stobjs (fn-octets fn-lz-dict fn-lz-out)
                  :guard (and (natp start) (natp end) (<= start end)
                              (<= end (fn-octets-len fn-octets)) (natp n))))
  (let* ((fn-lz-out (fn-lz-out-clear fn-lz-out))
         (fn-lz-out (fn-lz-out-reserve n fn-lz-out)))
    (mv-let (st ip mode k m off fn-lz-out)
      (fn-lz-run (fn-lz-budget (- end start) n) start end 0 0 0 0 n
                 fn-octets fn-lz-dict fn-lz-out)
      (declare (ignore ip mode k m off))
      (mv (cond ((not (eq st :done)) (if (eq st :more) :budget st))
                ((eql (fn-lz-out-len fn-lz-out) (nfix n)) :ok)
                (t :short))
          fn-lz-out))))

(defthm fn-lz-decode-buf-out-len-bound
  (<= (len (mv-nth 1 (fn-lz-decode-buf start end n fn-octets fn-lz-dict fn-lz-out)))
      (nfix n))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-lz-run-out-len-bound
                                   (b (fn-lz-budget (- end start) n))
                                   (ip start) (mode 0) (k 0) (m 0) (off 0) (lim n)
                                   (fn-lz-out nil)))
           :in-theory (disable fn-lz-run-out-len-bound fn-lz-budget))))

; -----------------------------------------------------------------------------
; Over octet lists: the same decoder on local buffers.  Answers (:ok octets)
; or (:error why).

(defun fn-lz-decode (dict c n)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c)
                              (natp n))))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (with-local-stobj fn-lz-dict
        (mv-let (r fn-lz-dict fn-octets)
          (with-local-stobj fn-lz-out
            (mv-let (r fn-lz-out fn-lz-dict fn-octets)
              (let* ((fn-octets (fn-octets-from-list c fn-octets))
                     (fn-lz-dict (fn-lz-dict-from-list dict fn-lz-dict)))
                (mv-let (st fn-lz-out)
                  (fn-lz-decode-buf 0 (fn-octets-len fn-octets) n fn-octets fn-lz-dict fn-lz-out)
                  (mv (if (eq st :ok)
                          (list :ok (fn-lz-out-list fn-lz-out))
                        (list :error st))
                      fn-lz-out fn-lz-dict fn-octets)))
              (mv r fn-lz-dict fn-octets)))
          (mv r fn-octets)))
      r)))

; -----------------------------------------------------------------------------
; The seal and its denotation.

(defun fn-lz-seal-form (dict octets candidate)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp octets)
                              (fn-cbor-octet-listp candidate))))
  (let ((r (fn-lz-decode dict candidate (len octets))))
    (if (and (eq (car r) :ok) (equal (cadr r) octets))
        (list :lz (len octets) candidate)
      (list :raw octets))))

(defun fn-lz-formp (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (or (and (eq (car form) :raw) (equal (len form) 2)
                (fn-cbor-octet-listp (cadr form)))
           (and (eq (car form) :lz) (equal (len form) 3)
                (natp (cadr form)) (fn-cbor-octet-listp (caddr form))))))

(defun fn-lz-denote (dict form)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-lz-formp form))))
  (if (eq (car form) :lz)
      (let ((r (fn-lz-decode dict (caddr form) (cadr form))))
        (if (eq (car r) :ok) (cadr r) nil))
    (cadr form)))

(defthm fn-lz-seal-form-formp
  (implies (and (fn-cbor-octet-listp octets) (fn-cbor-octet-listp candidate))
           (fn-lz-formp (fn-lz-seal-form dict octets candidate)))
  :hints (("Goal" :in-theory (disable fn-lz-decode))))

; KEYSTONE.
(defthm fn-lz-seal-form-denotes
  (equal (fn-lz-denote dict (fn-lz-seal-form dict octets candidate))
         octets)
  :hints (("Goal" :in-theory (disable fn-lz-decode))))

; -----------------------------------------------------------------------------
; The trivial encoder: one literal-only sequence.  The token's literal
; nibble is 15 (continued by the length less 15 in 255s and a remainder)
; unless the length is under 15.

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-lz-length-ext-loop (r acc)
  (declare (xargs :measure (nfix r) :guard (and (natp r) (true-listp acc)) :verify-guards nil))
  (if (or (zp r) (< r 255))
      (revappend acc (list (nfix r)))
    (fn-lz-length-ext-loop (- r 255) (cons 255 acc))))

(defun fn-lz-length-ext (r)
  ; The extension octets for R = length - 15: 255 while R >= 255, then R.
  (declare (xargs :verify-guards nil :guard (natp r) :measure (nfix r)))
  (mbe :logic
       (if (or (zp r) (< r 255))
           (list (nfix r))
         (cons 255 (fn-lz-length-ext (- r 255))))
       :exec (fn-lz-length-ext-loop r nil)))

(local
 (defthm fn-lz-length-ext-loop-is-revappend
   (equal (fn-lz-length-ext-loop r acc)
          (revappend acc (fn-lz-length-ext r)))
   :hints (("Goal" :induct (fn-lz-length-ext-loop r acc)
                   :in-theory (union-theories '(fn-lz-length-ext-loop fn-lz-length-ext revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-lz-length-ext-loop)

(verify-guards fn-lz-length-ext
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-lz-length-ext)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-lz-length-ext-loop-is-revappend (acc nil))))))


(defun fn-lz-literal-block (x)
  (declare (xargs :guard (true-listp x)))
  (let ((n (len x)))
    (if (< n 15)
        (cons (* 16 n) x)
      (cons 240 (append (fn-lz-length-ext (- n 15)) x)))))

; The literal block decodes to its payload, so it seals as :lz.  The
; proof runs the machine: the token, the extension octets
; (`fn-lz-run-length-ext'), the literal copy (`fn-lz-run-literals').

(local
 (defthm fn-lz-nth-of-len-append
   (equal (nth (len a) (append a b)) (car b))))

(local
 (defthm fn-lz-len-append-lt
   (implies (consp b) (< (len a) (len (append a b))))
   :rule-classes (:rewrite :linear)))

(local
 (defthm fn-lz-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-lz-append-nil
   (implies (true-listp a) (equal (append a nil) a))))

(local
 (defun fn-lz-lit-ind (y pre b out)
   (if (consp y)
       (fn-lz-lit-ind (cdr y) (append pre (list (car y))) (1- b)
                      (append out (list (car y))))
     (list pre b out))))

(local
 (defthm fn-lz-len-pos-when-consp
   (implies (consp y) (< 0 (len y)))
   :rule-classes (:linear :rewrite)))

(local
 (defthm fn-lz-copy-lits-of-literals
   (implies (and (true-listp y) (true-listp out))
            (equal (fn-lz-copy-lits (len pre) (len y) (append pre (append y rest)) out)
                   (append out y)))
   :hints (("Goal" :induct (fn-lz-lit-ind y pre b out)
            :in-theory (enable fn-lz-copy-lits)))))

; The literal copy: at PRE's end, K = |Y| literals Y are appended to OUT.
(local
 (defthm fn-lz-run-literals
   (implies (and (consp y) (true-listp y)
                 (<= (+ (len out) (len y)) lim) (< (len y) (nfix b))
                 (natp b) (natp lim) (true-listp out) (natp m) (natp off))
            (equal (fn-lz-run b (len pre) (len (append pre (append y rest))) 2 (len y)
                              m off lim (append pre (append y rest)) dict out)
                   (fn-lz-run (- b (len y)) (+ (len pre) (len y))
                              (len (append pre (append y rest))) 2 0 m off lim
                              (append pre (append y rest)) dict (append out y))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-lz-advance)
            :expand ((:free (end c)
                                    (fn-lz-run b (len pre) end 2 (len y) m off lim
                                               c dict out)))))))

(local
 (defun fn-lz-ext-ind (r pre b k)
   (declare (xargs :measure (nfix r)))
   (if (or (zp r) (< r 255))
       (list pre b k)
     (fn-lz-ext-ind (- r 255) (append pre (list 255)) (1- b) (+ k 255)))))

; The length extension: at PRE's end, the octets for R take mode 1 with
; K to mode 2 with K + R.
(local
 (defthm fn-lz-run-length-ext
   (implies (and (natp r) (natp k) (natp b) (natp m) (natp off)
                 (<= (+ (len out) k r) (nfix lim))
                 (< (len (fn-lz-length-ext r)) b))
            (equal (fn-lz-run b (len pre)
                              (len (append pre (append (fn-lz-length-ext r) rest)))
                              1 k m off lim
                              (append pre (append (fn-lz-length-ext r) rest)) dict out)
                   (fn-lz-run (- b (len (fn-lz-length-ext r)))
                              (+ (len pre) (len (fn-lz-length-ext r)))
                              (len (append pre (append (fn-lz-length-ext r) rest)))
                              2 (+ k r) m off lim
                              (append pre (append (fn-lz-length-ext r) rest)) dict out)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-lz-ext-ind r pre b k)
            :in-theory (enable fn-lz-advance fn-lz-seq fn-lz-step nfix))
           ("Subgoal *1/2" :expand ((:free (ip k end c)
                                     (fn-lz-run b ip end 1 k m off lim c dict out))
                                    (fn-lz-length-ext r)))
           ("Subgoal *1/1" :expand ((:free (ip k end c)
                                     (fn-lz-run b ip end 1 k m off lim c dict out))
                                    (fn-lz-length-ext r))))))

(local
 (defthm fn-lz-run-literal-block-short
   (implies (and (true-listp x) (< (len x) 15) (natp b) (< (+ 1 (len x)) b))
            (equal (fn-lz-run b 0 (+ 1 (len x)) 0 0 0 0 (len x)
                              (cons (* 16 (len x)) x) dict nil)
                   (list :done (+ 1 (len x)) 2 0 0 0 x)))
   :hints (("Goal" :in-theory (enable fn-lz-advance fn-lz-seq fn-lz-step nfix)
            :expand ((fn-lz-run b 0 (+ 1 (len x)) 0 0 0 0 (len x)
                                (cons (* 16 (len x)) x) dict nil)
                     (:free (b2 ip end lim c out) (fn-lz-run b2 ip end 2 0 0 0 lim c dict out)))
            :use ((:instance fn-lz-run-literals
                             (pre (list (* 16 (len x)))) (y x) (rest nil) (out nil)
                             (b (1- b)) (m 0) (off 0) (lim (len x))))))))

(local
 (defthm fn-lz-run-literal-block-long
   (implies (and (true-listp x) (<= 15 (len x)) (natp b)
                 (< (+ 2 (len (fn-lz-length-ext (- (len x) 15))) (len x)) b))
            (let ((c (cons 240 (append (fn-lz-length-ext (- (len x) 15)) x))))
              (equal (fn-lz-run b 0 (len c) 0 0 0 0 (len x) c dict nil)
                     (list :done (len c) 2 0 0 0 x))))
   :hints (("Goal" :in-theory (enable fn-lz-advance fn-lz-seq fn-lz-step nfix)
            :expand ((fn-lz-run b 0 (+ 1 (len (fn-lz-length-ext (- (len x) 15))) (len x))
                                0 0 0 0 (len x)
                                (cons 240 (append (fn-lz-length-ext (- (len x) 15)) x))
                                dict nil)
                     (:free (b2 ip end lim c out) (fn-lz-run b2 ip end 2 0 0 0 lim c dict out)))
            :use ((:instance fn-lz-run-length-ext
                             (pre (list 240)) (r (- (len x) 15)) (rest x) (out nil)
                             (b (1- b)) (k 15) (m 0) (off 0) (lim (len x)))
                  (:instance fn-lz-run-literals
                             (pre (cons 240 (fn-lz-length-ext (- (len x) 15))))
                             (y x) (rest nil) (out nil)
                             (b (- (1- b) (len (fn-lz-length-ext (- (len x) 15)))))
                             (m 0) (off 0) (lim (len x))))))))

(defthm fn-lz-decode-of-literal-block
  (implies (fn-cbor-octet-listp x)
           (equal (fn-lz-decode dict (fn-lz-literal-block x) (len x))
                  (list :ok x)))
  :hints (("Goal" :in-theory (disable fn-lz-length-ext)
           :use ((:instance fn-lz-run-literal-block-short
                            (b (fn-lz-budget (len (fn-lz-literal-block x)) (len x))))
                 (:instance fn-lz-run-literal-block-long
                            (b (fn-lz-budget (len (fn-lz-literal-block x)) (len x))))))))

(defthm fn-lz-seal-form-of-literal-block
  (implies (fn-cbor-octet-listp x)
           (equal (fn-lz-seal-form dict x (fn-lz-literal-block x))
                  (list :lz (len x) (fn-lz-literal-block x))))
  :hints (("Goal" :in-theory (disable fn-lz-decode fn-lz-literal-block))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-lz-run)))
