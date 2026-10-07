; fn: the BLAKE3 tree decomposition at window granularity (card B,
; build/coordinator/PERF-REGRESSION-20261005.md item 2).  Each 16 KiB window
; job re-hashes the whole protected prefix because the digest is only defined
; monolithically (`fn-blake3' of the whole message).  This book decomposes it:
; the digest of a whole input equals the tree composition of the windows'
; subtree chaining values at a fixed window granularity W = 1024*2^k octets
; (16 KiB is k = 4), and appending a window to a held chaining state equals
; digesting the whole.  Octet lists are the logical model (D27); the concrete
; twin comes after.  Proof vocabulary only, beside books/blake3.lisp.
;
; The reference's tree (its section 2.1, as books/blake3.lisp models it): a
; parent holds the largest power-of-two number of whole chunks strictly
; shorter than the input to its left, the rest to its right.  Two facts carry
; the decomposition.  (1) LOCKSTEP (fn-b3-left-chunks-of-windows): for an
; input of m windows (the last 1..W octets, m >= 2), that largest chunk count
; is exactly 2^k times the largest power-of-two WINDOW count below m — the
; split lands on a window boundary, recursively, so the whole tree is the
; window tree.  (2) PAIRING: the binary-counter stack over the windows'
; subtree outputs folds to the same tree, which is what a held chaining state
; absorbs window by window.
(in-package "ACL2")
(include-book "blake3")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; Vocabulary: the parent of two subtree outputs, and a subtree's chaining
; value.  `fn-b3-parent-out' is exactly the parent `fn-b3-node' builds (its
; section 2.1): the children's chaining values under the key, counter 0,
; block length 64, PARENT.

(defun fn-b3-parent-out (key lout rout flags)
  (declare (xargs :guard t))
  (fn-b3-output key
                (append (fn-b3-output-cv lout) (fn-b3-output-cv rout))
                0 64 (logior (ifix flags) *fn-b3-parent*)))

(defun fn-b3-node-cv (key octets counter flags)
  (declare (xargs :guard t))
  (fn-b3-output-cv (fn-b3-node key octets counter flags)))

(in-theory (disable fn-b3-parent-out fn-b3-node-cv))

; The anchor the rest unfolds from: a multi-chunk input's node IS the parent
; of its two subtree nodes — one unfolding of `fn-b3-node'.
(defthm fn-b3-node-splits-at-left-chunks
  (implies (< 1024 (len octets))
           (equal (fn-b3-node key octets counter flags)
                  (fn-b3-parent-out key
                    (fn-b3-node key
                      (fn-b3-firstn (* 1024 (fn-b3-left-chunks 1 (len octets))) octets)
                      counter flags)
                    (fn-b3-node key
                      (fn-b3-nthcdrx (* 1024 (fn-b3-left-chunks 1 (len octets))) octets)
                      (+ (nfix counter) (fn-b3-left-chunks 1 (len octets)))
                      flags)
                    flags)))
  :hints (("Goal" :do-not-induct t
                   :expand ((fn-b3-node key octets counter flags))
                   :in-theory (enable fn-b3-parent-out))))

; -----------------------------------------------------------------------------
; Windows: granularity k fixes the window size W = 1024*2^k octets.  All but
; the last window of an input are exactly W octets; the last is 1..W (D27:
; the granularity is a stream parameter, never a ceiling on stored data —
; any input length digests, the last window simply shorter).

(defun fn-b3-left-windows (p j)
  ; The largest power-of-two number of windows p below j, as `fn-b3-left-chunks'
  ; counts chunks below an octet length: doubled while twice it still leaves
  ; windows to its right.
  (declare (xargs :guard (and (natp p) (natp j))
                  :measure (nfix (- (nfix j) (nfix p)))))
  (if (and (posp p) (natp j) (< (* 2 p) j))
      (fn-b3-left-windows (* 2 p) j)
    p))

(defthm fn-b3-left-windows-posp
  (implies (posp p) (posp (fn-b3-left-windows p j)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-b3-left-windows-below
  (implies (and (posp p) (natp j) (< p j))
           (< (fn-b3-left-windows p j) j))
  :rule-classes (:rewrite :linear))

; A window split that does not double is itself, and one that does doubles —
; the two halves of `fn-b3-left-windows''s test, as rewrites.

(defthm fn-b3-left-windows-of-not
  (implies (and (posp p) (natp j) (not (< (* 2 p) j)))
           (equal (fn-b3-left-windows p j) p))
  :hints (("Goal" :expand ((fn-b3-left-windows p j)))))

(defthm fn-b3-left-windows-step
  (implies (and (posp p) (natp j) (< (* 2 p) j))
           (equal (fn-b3-left-windows p j)
                  (fn-b3-left-windows (* 2 p) j)))
  :hints (("Goal" :expand ((fn-b3-left-windows p j)))))

(defun fn-b3-split-windows (k octets)
  ; The windows of OCTETS at granularity k: all but the last exactly
  ; 1024*2^k octets, the last 1..1024*2^k.
  (declare (xargs :guard t :measure (len octets)))
  (let ((w (* 1024 (expt 2 (nfix k)))))
    (if (< w (len octets))
        (cons (fn-b3-firstn w octets)
              (fn-b3-split-windows k (fn-b3-nthcdrx w octets)))
      (list octets))))

(defun fn-b3-window-outs (key k base octets flags)
  ; The subtree output of each window, window i rooted at chunk counter
  ; base + i*2^k (the counter of a subtree is its first chunk's index, as
  ; `fn-b3-node' passes it down).
  (declare (xargs :guard t :measure (len octets)))
  (let ((w (* 1024 (expt 2 (nfix k)))))
    (if (< w (len octets))
        (cons (fn-b3-node key (fn-b3-firstn w octets) (nfix base) flags)
              (fn-b3-window-outs key k
                (+ (nfix base) (expt 2 (nfix k)))
                (fn-b3-nthcdrx w octets) flags))
      (list (fn-b3-node key octets (nfix base) flags)))))

(defun fn-b3-window-tree (key flags outs)
  ; The tree over window subtree outputs: the same largest-power-of-two
  ; split `fn-b3-node' applies, counted in windows.
  (declare (xargs :guard t :measure (len outs)))
  (if (consp outs)
      (if (consp (cdr outs))
          (fn-b3-parent-out key
            (fn-b3-window-tree key flags
              (fn-b3-firstn (fn-b3-left-windows 1 (len outs)) outs))
            (fn-b3-window-tree key flags
              (fn-b3-nthcdrx (fn-b3-left-windows 1 (len outs)) outs))
            flags)
        (car outs))
    nil))

; -----------------------------------------------------------------------------
; LOCKSTEP: the chunk split of an input of m windows is the window split
; scaled by 2^k.  The conditions of the two doublings coincide (any positive
; chunk-group size s; no power of two needed at this altitude)...

(defthm fn-b3-scale-condition
  (implies (and (posp s) (posp p) (posp m) (posp r)
                (<= r (* 1024 s)))
           (equal (< (* 2048 (* s p)) (+ (* (- m 1) (* 1024 s)) r))
                  (< (* 2 p) m)))
  :hints (("Goal" :nonlinearp t)))

(defthm fn-b3-left-chunks-of-not
  ; The same non-doubling half for `fn-b3-left-chunks'.
  (implies (and (posp q) (natp n) (not (< (* 2048 q) n)))
           (equal (fn-b3-left-chunks q n) q))
  :hints (("Goal" :expand ((fn-b3-left-chunks q n)))))

(defthm fn-b3-left-chunks-scale
  (implies (and (posp s) (posp p) (posp m) (posp r)
                (<= r (* 1024 s)))
           (equal (fn-b3-left-chunks (* s p)
                     (+ (* (- m 1) (* 1024 s)) r))
                  (* s (fn-b3-left-windows p m))))
  :hints (("Goal" :induct (fn-b3-left-windows p m)
                   :nonlinearp t)))

(defun fn-b3-k-ind (k n)
  ; Induction driver for the climb: one step per power of two.
  (declare (xargs :guard (and (natp k) (natp n)) :measure (nfix k)))
  (if (zp k)
      (list k n)
    (fn-b3-k-ind (- k 1) n)))

(defthm fn-b3-left-chunks-climb
  ; From chunk 1 the doubling passes through 2^k (every step below it doubles
  ; while the input still holds a second window), so a multi-window input's
  ; split starts at the first window boundary.
  (implies (and (natp k) (natp n)
                (< (* 1024 (expt 2 (nfix k))) n))
           (equal (fn-b3-left-chunks 1 n)
                  (fn-b3-left-chunks (expt 2 (nfix k)) n)))
  :hints (("Goal" :induct (fn-b3-k-ind k n)
                   :nonlinearp t)))

(defthm fn-b3-left-chunks-of-windows
  ; THE LOCKSTEP: an input of m >= 2 windows (the last 1..W octets) splits
  ; its chunks exactly at 2^k times its window split.
  (implies (and (natp k) (natp m) (<= 2 m) (posp r)
                (<= r (* 1024 (expt 2 (nfix k)))))
           (equal (fn-b3-left-chunks 1
                     (+ (* (- m 1) (* 1024 (expt 2 (nfix k)))) r))
                  (* (expt 2 (nfix k))
                     (fn-b3-left-windows 1 m))))
  :hints (("Goal" :use ((:instance fn-b3-left-chunks-climb
                         (n (+ (* (- m 1) (* 1024 (expt 2 (nfix k)))) r)))
                        (:instance fn-b3-left-chunks-scale
                         (s (expt 2 (nfix k))) (p 1)))
                   :in-theory (disable fn-b3-left-chunks-climb
                                       fn-b3-left-chunks-scale)
                   :nonlinearp t)))

; -----------------------------------------------------------------------------
; PAIRING: the binary-counter stack over window outputs.

(defun fn-b3-pair-outs (key flags outs)
  ; Consecutive pairs of outputs parented, as one level of the tree.
  (declare (xargs :guard t :measure (len outs)))
  (if (and (consp outs) (consp (cdr outs)))
      (cons (fn-b3-parent-out key (car outs) (cadr outs) flags)
            (fn-b3-pair-outs key flags (cddr outs)))
    nil))

(defun fn-b3-cv-push (key flags h out st)
  ; Absorb OUT at height h into the held chaining state: a stack of
  ; (height subtree-output) entries, the front the highest.  Equal heights
  ; merge upward (the stack entry covers earlier windows, so it is the LEFT
  ; child).  Entries read through the total `fn-b3-nthx', so every object is
  ; a state.
  (declare (xargs :guard t :measure (nfix (len st))))
  (if (and (consp st)
           (equal (nfix (fn-b3-nthx 0 (car st))) (nfix h)))
      (fn-b3-cv-push key flags (+ 1 (nfix h))
                    (fn-b3-parent-out key (fn-b3-nthx 1 (car st)) out flags)
                    (cdr st))
    (cons (list (nfix h) out) st)))

(defun fn-b3-stack-spine (key flags st acc)
  ; Walk the stack front-to-back (heights strictly increasing) absorbing
  ; each entry's subtree as the LEFT child over the trees absorbed so far:
  ; the right spine of the reference's tree, built from its innermost (last,
  ; highest) parent outward.  ACC nil names an empty right side.
  (declare (xargs :guard t :measure (nfix (len st))))
  (if (consp st)
      (fn-b3-stack-spine key flags (cdr st)
        (if (null acc)
            (fn-b3-nthx 1 (car st))
          (fn-b3-parent-out key (fn-b3-nthx 1 (car st)) acc flags)))
    acc))

(defun fn-b3-stack-fold (key flags st)
  ; The whole-tree denotation of a held chaining state.
  (declare (xargs :guard t))
  (fn-b3-stack-spine key flags st nil))

(defun fn-b3-stack-push-all (key flags h outs st)
  ; Absorb a run of subtree outputs at one height, in order.
  (declare (xargs :guard t :measure (nfix (len outs))))
  (if (atom outs)
      st
    (fn-b3-stack-push-all key flags h (cdr outs)
      (fn-b3-cv-push key flags h (car outs) st))))

(defthm fn-b3-stack-push-all-of-append
  (equal (fn-b3-stack-push-all key flags h (append outs more) st)
         (fn-b3-stack-push-all key flags h more
           (fn-b3-stack-push-all key flags h outs st)))
  :hints (("Goal" :induct (fn-b3-stack-push-all key flags h outs st))))

(defun fn-b3-stack-above (h st)
  ; Every entry of ST sits strictly above height H; the empty stack does.
  (declare (xargs :guard t))
  (if (atom st)
      t
    (and (< (nfix h) (nfix (fn-b3-nthx 0 (car st))))
         (fn-b3-stack-above h (cdr st)))))

(defthm fn-b3-cv-push-of-no-match
  ; The cons half of `fn-b3-cv-push''s test, as a rewrite.
  (implies (not (and (consp st)
                     (equal (nfix (fn-b3-nthx 0 (car st))) (nfix h))))
           (equal (fn-b3-cv-push key flags h out st)
                  (cons (list (nfix h) out) st)))
  :hints (("Goal" :expand ((fn-b3-cv-push key flags h out st)))))

(defthm fn-b3-cv-push-of-above
  ; Absorbing above an above-H stack keeps it above H: the cascade only
  ; replaces the front by an entry at least as high, and leaves the rest.
  (implies (and (natp h) (< (nfix h) (nfix g))
                (fn-b3-stack-above h st))
           (fn-b3-stack-above h
             (fn-b3-cv-push key flags g out st)))
  :hints (("Goal" :induct (fn-b3-cv-push key flags g out st))))

(defthm fn-b3-cv-push-two-singles
  ; Two singles at h on an above-h stack = their pair at h+1 (the merge
  ; cascade continues identically below).
  (implies (and (natp h) (fn-b3-stack-above h st))
           (equal (fn-b3-cv-push key flags h b
                     (fn-b3-cv-push key flags h a st))
                  (fn-b3-cv-push key flags (+ 1 (nfix h))
                    (fn-b3-parent-out key a b flags) st)))
  :hints (("Goal" :expand ((fn-b3-cv-push key flags h a st)
                           (fn-b3-stack-above h st)))))

(defun fn-b3-lpair-ind (key flags h outs st)
  ; L-pair induction: step TWO outputs, the stack absorbing their pair.
  (declare (xargs :measure (len outs) :verify-guards nil))
  (if (or (atom outs) (atom (cdr outs)))
      (list h outs st)
    (fn-b3-lpair-ind key flags h (cddr outs)
      (fn-b3-cv-push key flags (+ 1 (nfix h))
        (fn-b3-parent-out key (car outs) (cadr outs) flags) st))))

(local
 (defthm fn-b3-stack-push-all-of-pairs
    ; L-PAIR: absorbing an EVEN run of singles at height h onto a stack already
    ; above h is absorbing their consecutive pairs at h+1 — the binary counter
    ; merges each two exactly once.
    (implies (and (natp h)
                  (fn-b3-stack-above h st)
                  (true-listp outs) (evenp (len outs)))
             (equal (fn-b3-stack-push-all key flags h outs st)
                    (fn-b3-stack-push-all key flags (+ 1 (nfix h))
                      (fn-b3-pair-outs key flags outs) st)))
    :hints (("Goal" :induct (fn-b3-lpair-ind key flags h outs st)
                     :expand ((fn-b3-stack-push-all key flags h outs st)
                              (fn-b3-stack-push-all key flags (+ 1 (nfix h))
                                (fn-b3-pair-outs key flags outs) st)
                              (fn-b3-pair-outs key flags outs))))))

(defun fn-b3-e-ind (key flags h outs st)
  ; E induction: same two-step shape as L-pair, the stack absorbing pairs.
  (declare (xargs :measure (len outs) :verify-guards nil))
  (if (or (atom outs) (atom (cdr outs)))
      (list h outs st)
    (fn-b3-e-ind key flags h (cddr outs)
      (fn-b3-cv-push key flags (+ 1 (nfix h))
        (fn-b3-parent-out key (car outs) (cadr outs) flags) st))))

(defthm fn-b3-stack-push-all-even-above
  ; E: absorbing an EVEN run of singles at height h leaves the whole stack
  ; above h — nothing single-height survives pairing.
  (implies (and (natp h) (fn-b3-stack-above h st)
                (true-listp outs) (evenp (len outs)))
           (fn-b3-stack-above h
             (fn-b3-stack-push-all key flags h outs st)))
  :hints (("Goal" :induct (fn-b3-e-ind key flags h outs st)
                   :expand ((fn-b3-stack-push-all key flags h outs st)))))

(defthm fn-b3-stack-above-means-no-match
  ; An above-h stack has no h-height front to merge with.
  (implies (and (fn-b3-stack-above h st) (consp st))
           (not (equal (nfix (fn-b3-nthx 0 (car st))) (nfix h))))
  :hints (("Goal" :in-theory (enable fn-b3-stack-above))))

(defthm fn-b3-cv-push-of-above-front
  ; Pushing at exactly h onto an above-h stack: no front can match, so it
  ; conses (empty or full stack alike).
  (implies (fn-b3-stack-above h st)
           (equal (fn-b3-cv-push key flags h out st)
                  (cons (list (nfix h) out) st)))
  :hints (("Goal" :in-theory (enable fn-b3-stack-above)
                   :expand ((fn-b3-cv-push key flags h out st)))))

(defthm fn-b3-stack-push-all-append-single
  ; R: after an EVEN run of singles at h (from empty), one more single at h
  ; does not merge — the stack is above h — it conses at the front.
  (implies (and (natp h) (true-listp os) (evenp (len os)))
           (equal (fn-b3-stack-push-all key flags h (append os (list x)) nil)
                  (cons (list (nfix h) x)
                        (fn-b3-stack-push-all key flags h os nil))))
  :hints (("Goal" :do-not-induct t
                   :in-theory (disable fn-b3-stack-push-all-of-pairs)
                   :use ((:instance fn-b3-stack-push-all-even-above (st nil)))
                   :expand ((fn-b3-stack-above h nil)
                            (fn-b3-stack-push-all key flags h (list x)
                              (fn-b3-stack-push-all key flags h os nil))))))

(defthm fn-b3-stack-spine-of-cons
  ; One unfolding of the spine walk: the front (lowest) entry absorbed as the
  ; LEFT child over the accumulator; nil names an empty right side.
  (equal (fn-b3-stack-spine key flags (cons e st) acc)
         (fn-b3-stack-spine key flags st
           (if (null acc)
               (fn-b3-nthx 1 e)
             (fn-b3-parent-out key (fn-b3-nthx 1 e) acc flags))))
  :hints (("Goal" :expand ((fn-b3-stack-spine key flags (cons e st) acc)))))

(defthm fn-b3-stack-spine-of-append
  ; B: the spine walk distributes over stack concatenation, front run first.
  (equal (fn-b3-stack-spine key flags (append st1 st2) acc)
         (fn-b3-stack-spine key flags st2
           (fn-b3-stack-spine key flags st1 acc)))
  :hints (("Goal" :induct (fn-b3-stack-spine key flags st1 acc))))

; -----------------------------------------------------------------------------
; List alignment: the lw doubling identities, and pair/take/drop commutations
; the tree-pairing lemmas rewrite through.

(defthm fn-b3-left-windows-double
  ; lw doubling: an even count splits at twice the halved count's split.
  (implies (and (posp p) (natp u) (< p u))
           (equal (fn-b3-left-windows p (* 2 u))
                  (* 2 (fn-b3-left-windows p u))))
  :hints (("Goal" :induct (fn-b3-left-windows p u)
                   :nonlinearp t)))

(defthm fn-b3-left-windows-double-minus
  ; The odd twin: an odd count splits at the same doubled split.
  (implies (and (posp p) (natp u) (< p u))
           (equal (fn-b3-left-windows p (+ -1 (* 2 u)))
                  (* 2 (fn-b3-left-windows p u))))
  :hints (("Goal" :induct (fn-b3-left-windows p u)
                   :nonlinearp t)))

(defun fn-b3-pf-ind (i outs)
  ; Pair/firstn induction: one pair per step, i counting halves.
  (declare (xargs :measure (nfix i) :verify-guards nil))
  (if (or (zp i) (atom outs) (atom (cdr outs)))
      (list i outs)
    (fn-b3-pf-ind (- i 1) (cddr outs))))

(defthm fn-b3-len-of-pair-outs
  (equal (len (fn-b3-pair-outs key flags outs))
         (floor (len outs) 2))
  :hints (("Goal" :induct (fn-b3-pair-outs key flags outs))))

(defthm fn-b3-pair-outs-of-firstn
  ; Pairing commutes with taking an EVEN prefix.
  (implies (and (natp i) (<= (* 2 i) (len outs)) (true-listp outs))
           (equal (fn-b3-pair-outs key flags (fn-b3-firstn (* 2 i) outs))
                  (fn-b3-firstn i (fn-b3-pair-outs key flags outs))))
  :hints (("Goal" :induct (fn-b3-pf-ind i outs)
                   :expand ((fn-b3-firstn (* 2 i) outs)))))

(defthm fn-b3-pair-outs-of-nthcdrx
  ; Pairing commutes with dropping any prefix.
  (implies (natp i)
           (equal (fn-b3-pair-outs key flags (fn-b3-nthcdrx (* 2 i) outs))
                  (fn-b3-nthcdrx i (fn-b3-pair-outs key flags outs))))
  :hints (("Goal" :induct (fn-b3-pf-ind i outs)
                   :expand ((fn-b3-nthcdrx (* 2 i) outs)))))

(defthm fn-b3-pair-outs-of-append-two
  ; Pairing an even run followed by two singles pairs the run, then the two —
  ; the alignment the odd Q' step needs (its last single pairs with the
  ; appended A).
  (implies (and (natp i) (true-listp os) (equal (len os) (* 2 i)))
           (equal (fn-b3-pair-outs key flags (append os (list x y)))
                  (append (fn-b3-pair-outs key flags os)
                          (list (fn-b3-parent-out key x y flags)))))
  :hints (("Goal" :induct (fn-b3-pf-ind i os)
                   :expand ((fn-b3-pair-outs key flags (append os (list x y)))))))

(defthm fn-b3-firstn-all
  (implies (true-listp x)
           (equal (fn-b3-firstn (len x) x) x)))

(defthm fn-b3-nthcdrx-all
  (implies (true-listp x)
           (equal (fn-b3-nthcdrx (len x) x) nil)))

(defthm fn-b3-firstn-of-append-le
  ; A take within the first part does not see the second.
  (implies (and (natp a) (<= a (len x)) (true-listp x))
           (equal (fn-b3-firstn a (append x y))
                  (fn-b3-firstn a x))))

(defthm fn-b3-nthcdrx-of-append-le
  ; A drop within the first part leaves the second appended.
  (implies (and (natp a) (<= a (len x)) (true-listp x))
           (equal (fn-b3-nthcdrx a (append x y))
                  (append (fn-b3-nthcdrx a x) y))))

(defthm fn-b3-firstn-split-sum
  ; Taking a+b is taking a then b of the rest.
  (implies (and (natp a) (natp b))
           (equal (fn-b3-firstn (+ a b) x)
                  (append (fn-b3-firstn a x)
                          (fn-b3-firstn b (fn-b3-nthcdrx a x))))))

(defthm fn-b3-nthcdrx-of-firstn
  ; Dropping past a take takes the remainder of the rest.
  (implies (and (natp a) (natp b))
           (equal (fn-b3-nthcdrx a (fn-b3-firstn b x))
                  (fn-b3-firstn (nfix (- b a)) (fn-b3-nthcdrx a x)))))

(defthm fn-b3-firstn-true-listp
  (true-listp (fn-b3-firstn n x))
  :hints (("Goal" :induct (fn-b3-firstn n x))))

(defthm fn-b3-nthcdrx-true-listp
  (implies (true-listp x)
           (true-listp (fn-b3-nthcdrx n x)))
  :hints (("Goal" :induct (fn-b3-nthcdrx n x))))

; -----------------------------------------------------------------------------
; WTREE PAIRING: the tree over an even run of outputs is the tree over their
; pairs.  The len-equality hypothesis stays explicit so the doubling bridge
; rewrites the split the definition computes; the single-step bridges keep the
; base leaves in list form.

(defun fn-b3-lw-ind (p j)
  ; lw's own climb as an induction driver over p.
  (declare (xargs :measure (nfix (- (nfix j) (nfix p))) :verify-guards nil))
  (if (and (posp p) (natp j) (< (* 2 p) j))
      (fn-b3-lw-ind (* 2 p) j)
    (list p j)))

(defthm fn-b3-left-windows-plus
  ; Climbing past u by ONE window: the split is the same, unless u is exactly
  ; twice it (the doubling edge), where it doubles.  An IF-valued rewrite: each
  ; use site case-splits on the edge itself.
  (implies (and (posp p) (natp u) (< p u))
           (equal (fn-b3-left-windows p (+ 1 u))
                  (if (equal u (* 2 (fn-b3-left-windows p u)))
                      u
                    (fn-b3-left-windows p u))))
  :hints (("Goal" :induct (fn-b3-lw-ind p u)
                   :nonlinearp t)))

(defthm fn-b3-left-windows-1-plus
  ; The p=1 instance, its edge condition phrased on lw(1, u) itself.
  (implies (and (natp u) (<= 2 u))
           (equal (fn-b3-left-windows 1 (+ 1 u))
                  (if (equal u (* 2 (fn-b3-left-windows 1 u)))
                      u
                    (fn-b3-left-windows 1 u))))
  :hints (("Goal" :use ((:instance fn-b3-left-windows-plus (p 1))))))

(defthm fn-b3-left-windows-1-of-2u+1
  ; An odd run of 2u+1 outputs splits at twice lw(1, u+1) — the tail lemmas'
  ; left side, where the appended single makes the count odd.
  (implies (and (natp u) (<= 1 u))
           (equal (fn-b3-left-windows 1 (+ 1 (* 2 u)))
                  (* 2 (fn-b3-left-windows 1 (+ 1 u)))))
  :hints (("Goal" :use ((:instance fn-b3-left-windows-double-minus (p 1) (u (+ 1 u))))
                   :nonlinearp t)))

(defthm fn-b3-lw-of-double-len
  ; Bridge: an even-length run's wtree split is twice the half-count's
  ; split.  Stated with the doubled length as an explicit n so the len
  ; hypothesis relieves from the caller's ancestors.
  (implies (and (posp p) (natp u) (< p u)
                (equal n (* 2 u)))
           (equal (fn-b3-left-windows p n)
                  (* 2 (fn-b3-left-windows p u))))
  :hints (("Goal" :induct (fn-b3-lw-ind p u)
                   :expand ((fn-b3-left-windows p n)))))

(defthm fn-b3-left-windows-1-double
  ; p=1 instance of the doubling, as a rewrite.
  (implies (and (natp u) (<= 2 u))
           (equal (fn-b3-left-windows 1 (* 2 u))
                  (* 2 (fn-b3-left-windows 1 u))))
  :hints (("Goal" :use ((:instance fn-b3-left-windows-double (p 1) (u u))))))

(defthm fn-b3-window-tree-split
  ; One unfolding of the window tree: the split at lw(1, count).
  (implies (and (consp outs) (consp (cdr outs)))
           (equal (fn-b3-window-tree key flags outs)
                  (fn-b3-parent-out key
                    (fn-b3-window-tree key flags
                      (fn-b3-firstn (fn-b3-left-windows 1 (len outs)) outs))
                    (fn-b3-window-tree key flags
                      (fn-b3-nthcdrx (fn-b3-left-windows 1 (len outs)) outs))
                    flags)))
  :hints (("Goal" :expand ((fn-b3-window-tree key flags outs)))))

(defthm fn-b3-window-tree-of-single
  (equal (fn-b3-window-tree key flags (list x)) x)
  :hints (("Goal" :expand ((fn-b3-window-tree key flags (list x))))))

(defthm fn-b3-firstn-of-1
  (implies (consp x)
           (equal (fn-b3-firstn 1 x) (list (car x))))
  :hints (("Goal" :expand ((fn-b3-firstn 1 x)))))

(defthm fn-b3-nthcdrx-of-1
  (implies (consp x)
           (equal (fn-b3-nthcdrx 1 x) (cdr x)))
  :hints (("Goal" :expand ((fn-b3-nthcdrx 1 x)))))

(defthm fn-b3-car-of-pair-outs
  (implies (and (consp outs) (consp (cdr outs)))
           (equal (car (fn-b3-pair-outs key flags outs))
                  (fn-b3-parent-out key (car outs) (cadr outs) flags)))
  :hints (("Goal" :expand ((fn-b3-pair-outs key flags outs)))))

(defthm fn-b3-pair-outs-consp
  (implies (and (consp outs) (consp (cdr outs)))
           (consp (fn-b3-pair-outs key flags outs)))
  :hints (("Goal" :expand ((fn-b3-pair-outs key flags outs)))))

(defthm fn-b3-cdr-of-pair-outs-consp
  ; Four or more outputs pair into at least two.
  (implies (and (consp (cddr outs)) (consp (cdddr outs)))
           (consp (cdr (fn-b3-pair-outs key flags outs))))
  :hints (("Goal" :expand ((fn-b3-pair-outs key flags outs)))))

(defthm fn-b3-cddr-consp-of-even
  ; An even run of 2u outputs, u >= 2, has a fourth element: its pairs
  ; are at least two, never a singleton.
  (implies (and (natp u) (<= 2 u) (equal (len outs) (* 2 u)))
           (and (consp (cddr outs)) (consp (cdddr outs))))
  :hints (("Goal" :expand ((len outs)))))

(defthm fn-b3-window-tree-of-1-list
  (implies (and (consp outs) (atom (cdr outs)))
           (equal (fn-b3-window-tree key flags outs) (car outs)))
  :hints (("Goal" :expand ((fn-b3-window-tree key flags outs)))))

(defthm fn-b3-window-tree-of-pair-outs-2
  ; The pairs of exactly two outputs tree to their parent.
  (implies (and (consp outs) (consp (cdr outs)) (atom (cddr outs)))
           (equal (fn-b3-window-tree key flags
                     (fn-b3-pair-outs key flags outs))
                  (fn-b3-parent-out key (car outs) (cadr outs) flags)))
  :hints (("Goal" :expand ((fn-b3-pair-outs key flags outs)))))

(defthm fn-b3-atom-cdr-of-len-1
  (implies (equal (len x) 1)
           (atom (cdr x)))
  :hints (("Goal" :expand ((len x)))))

(defun fn-b3-wt-pair-ind (u outs)
  ; wtree-pairing induction: split an even run of outs at its wtree split
  ; (2*lw of the half-count), both children strictly fewer pairs.
  (declare (xargs :measure (nfix u) :verify-guards nil))
  (if (or (<= (nfix u) 1) (atom outs) (atom (cdr outs)))
      (list u outs)
    (list (fn-b3-wt-pair-ind (fn-b3-left-windows 1 u)
            (fn-b3-firstn (* 2 (fn-b3-left-windows 1 u)) outs))
          (fn-b3-wt-pair-ind (- u (fn-b3-left-windows 1 u))
            (fn-b3-nthcdrx (* 2 (fn-b3-left-windows 1 u)) outs)))))

(defthm fn-b3-window-tree-of-pairs
  ; L-WTREE-PAIR: the tree over an EVEN run of outputs is the tree over
  ; their pairs — one pairing level of the reference tree.
  (implies (and (equal (len outs) (* 2 u)) (natp u) (true-listp outs))
           (equal (fn-b3-window-tree key flags outs)
                  (fn-b3-window-tree key flags
                    (fn-b3-pair-outs key flags outs))))
  :hints (("Goal" :induct (fn-b3-wt-pair-ind u outs)
                   :in-theory (disable fn-b3-window-tree)
                   :expand ((fn-b3-window-tree key flags outs)
                            (fn-b3-window-tree key flags
                              (fn-b3-pair-outs key flags outs))))
          ("Subgoal *1/1.4'" :cases ((consp (cddr outs)))
                            :expand ((fn-b3-pair-outs key flags outs)))))

(local
 (defthm fn-b3-consp-of-len-pos
   ; A positive length means a cons.
   (implies (< 0 (len x)) (consp x))))

(local
 (defthm fn-b3-len-of-cdr
   ; The cdr's length, without opening LEN's definition.
   (implies (consp x) (equal (len (cdr x)) (- (len x) 1)))))

(defthm fn-b3-consp-of-append-single
  ; A run with one appended single is always a cons.
  (consp (append xs (list A)))
  :hints (("Goal" :expand ((append xs (list A))))))

(defthm fn-b3-cdr-consp-of-append-single
  ; With at least one element before it, the second position is a cons too.
  (implies (consp xs)
           (consp (cdr (append xs (list A)))))
  :hints (("Goal" :expand ((append xs (list A))))))

(defthm fn-b3-firstn-all-when-len
  ; firstn over the whole run, the length hypothesis linearly relievable from
  ; the caller's own length hypothesis.
  (implies (and (natp n) (true-listp x) (equal n (len x)))
           (equal (fn-b3-firstn n x) x))
  :hints (("Goal" :induct (fn-b3-firstn n x))))

(defthm fn-b3-nthcdrx-all-when-len
  ; nthcdrx past the whole run, the same linearly relievable form.
  (implies (and (natp n) (true-listp x) (equal n (len x)))
           (equal (fn-b3-nthcdrx n x) nil))
  :hints (("Goal" :induct (fn-b3-nthcdrx n x))))

(defthm fn-b3-pair-outs-true-listp
  (true-listp (fn-b3-pair-outs key flags outs))
  :hints (("Goal" :induct (fn-b3-pair-outs key flags outs))))

(defthm fn-b3-window-tree-of-even-prefix
  ; The even prefix of a run trees as the prefix of its pairs.  The
  ; non-edge step of L-wtree-pair-tail reads this as its left child:
  ; off the doubling edge that child is the even prefix of length
  ; 2*lw(1,u), and the pairs' tree splits at the same prefix.
  (implies (and (natp i)
                (true-listp outs)
                (<= (* 2 i) (len outs)))
           (equal (fn-b3-window-tree key flags
                    (fn-b3-firstn (* 2 i) outs))
                  (fn-b3-window-tree key flags
                    (fn-b3-firstn i
                      (fn-b3-pair-outs key flags outs)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-b3-window-tree
                               fn-b3-window-tree-of-pairs
                               fn-b3-pair-outs)
           :use ((:instance fn-b3-window-tree-of-pairs
                   (u i)
                   (outs (fn-b3-firstn (* 2 i) outs)))))))

;
; The two list-length helpers above served the pairing proofs and are slow
; to backchain through everywhere after; the rest of the book leaves them off.
(local (in-theory (disable fn-b3-consp-of-len-pos fn-b3-len-of-cdr
                           fn-b3-window-tree-of-1-list)))

;
; The window alignment: the first j windows' outputs, and the rest, are the
; window outputs of the first j windows' octets and of the remainder (at the
; advanced chunk counter), whenever j whole windows leave octets over.
;
(local
 (defthm fn-b3-window-outs-count
    ; The window count m of an input of n >= 1 octets: (m-1) full windows
    ; leave 1..W octets for the last.
    (implies (posp (len octets))
             (and (< (* (+ -1 (len (fn-b3-window-outs key k base octets flags)))
                        (* 1024 (expt 2 (nfix k))))
                     (len octets))
                  (<= (len octets)
                      (* (len (fn-b3-window-outs key k base octets flags))
                         (* 1024 (expt 2 (nfix k)))))))
    :hints (("Goal" :induct (fn-b3-window-outs key k base octets flags)
                    :in-theory (disable fn-b3-node)))))

(local
 (defthm fn-b3-firstn-of-firstn
    (implies (and (natp a) (natp b) (<= a b))
             (equal (fn-b3-firstn a (fn-b3-firstn b x))
                    (fn-b3-firstn a x)))))

(local
 (defthm fn-b3-nthcdrx-of-nthcdrx
    (implies (and (natp a) (natp b))
             (equal (fn-b3-nthcdrx a (fn-b3-nthcdrx b x))
                    (fn-b3-nthcdrx (+ a b) x)))))

(local
 (defthm fn-b3-window-le-multiple-norm
   (implies (and (natp k) (posp j))
            (<= (expt 2 (+ 10 k)) (* j (expt 2 (+ 10 k)))))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(defun fn-b3-wa-ind (j k base octets flags)
  ; Window-count induction: one window per step.
  (declare (xargs :measure (nfix j) :verify-guards nil))
  (if (or (zp j) (not (< (* 1024 (expt 2 (nfix k))) (len octets))))
      (list j k base octets flags)
    (fn-b3-wa-ind (- j 1) k (+ (nfix base) (expt 2 (nfix k)))
                  (fn-b3-nthcdrx (* 1024 (expt 2 (nfix k))) octets) flags)))

(defthm fn-b3-firstn-of-window-outs
  ; The first j windows' outputs are the window outputs of the first j
  ; windows' octets.
  (implies (and (natp k) (posp j)
                (< (* j (* 1024 (expt 2 (nfix k)))) (len octets)))
           (equal (fn-b3-firstn j (fn-b3-window-outs key k base octets flags))
                  (fn-b3-window-outs key k base
                    (fn-b3-firstn (* j (* 1024 (expt 2 (nfix k)))) octets)
                    flags)))
  :hints (("Goal" :induct (fn-b3-wa-ind j k base octets flags)
                  :in-theory (disable fn-b3-node))
          ("Subgoal *1/2" :expand ((fn-b3-window-outs key k base octets flags)))))


(defthm fn-b3-nthcdrx-of-window-outs
  ; Dropping j windows' outputs leaves the outputs of the rest, at the
  ; advanced chunk counter.
  (implies (and (natp k) (natp base) (natp j)
                (< (* j (* 1024 (expt 2 (nfix k)))) (len octets)))
           (equal (fn-b3-nthcdrx j (fn-b3-window-outs key k base octets flags))
                  (fn-b3-window-outs key k
                    (+ base (* j (expt 2 (nfix k))))
                    (fn-b3-nthcdrx (* j (* 1024 (expt 2 (nfix k)))) octets)
                    flags)))
  :hints (("Goal" :induct (fn-b3-wa-ind j k base octets flags)
                  :in-theory (disable fn-b3-node))
          ("Subgoal *1/1" :cases ((equal j 0)))
          ("Subgoal *1/2" :expand ((fn-b3-window-outs key k base octets flags)))))

(defthm fn-b3-left-chunks-of-count
  (implies (and (natp k) (natp m) (<= 2 m) (natp n)
                (< (* (+ -1 m) (* 1024 (expt 2 k))) n)
                (<= n (* m (* 1024 (expt 2 k)))))
           (equal (fn-b3-left-chunks 1 n)
                  (* (expt 2 k) (fn-b3-left-windows 1 m))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-b3-left-chunks-of-windows
                   (r (- n (* (+ -1 m) (* 1024 (expt 2 k)))))))
           :in-theory (disable fn-b3-left-chunks-of-windows))))

(local
 (defthm fn-b3-window-count-at-least-two
    ; More octets than one window means at least two windows.
    (implies (and (natp k) (< (* 1024 (expt 2 k)) (len octets)))
             (<= 2 (len (fn-b3-window-outs key k base octets flags))))
    :rule-classes :linear
    :hints (("Goal" :use fn-b3-window-outs-count
                    :in-theory (disable fn-b3-window-outs-count)
                    :nonlinearp t))))

(local
 (defthm fn-b3-window-tree-of-single-window
    ; An input of one window: its window tree is its own node.
    (implies (<= (len octets) (* 1024 (expt 2 (nfix k))))
             (equal (fn-b3-window-tree key flags
                      (fn-b3-window-outs key k base octets flags))
                    (fn-b3-node key octets (nfix base) flags)))
    :hints (("Goal" :expand ((fn-b3-window-outs key k base octets flags))
                    :in-theory (disable fn-b3-node)))))

(local
 (defthm fn-b3-left-windows-times-window-below
    ; The first subtree's windows are whole windows with octets to spare.
    (implies (and (natp k) (natp m) (<= 2 m) (natp n)
                  (< (* (+ -1 m) (* 1024 (expt 2 k))) n))
             (< (* (fn-b3-left-windows 1 m) (* 1024 (expt 2 k))) n))
    :hints (("Goal" :use ((:instance fn-b3-left-windows-below (p 1) (j m)))
                    :in-theory (disable fn-b3-left-windows-below)
                    :nonlinearp t))))

(defun fn-b3-node-ind (key octets counter flags)
  ; The induction scheme of `fn-b3-node': both children of a multi-chunk split.
  (declare (xargs :measure (len octets) :verify-guards nil))
  (if (< 1024 (len octets))
      (let* ((lc (fn-b3-left-chunks 1 (len octets)))
             (ll (* 1024 lc)))
        (list (fn-b3-node-ind key (fn-b3-firstn ll octets) counter flags)
              (fn-b3-node-ind key (fn-b3-nthcdrx ll octets)
                              (+ (nfix counter) lc) flags)))
    (list key octets counter flags)))

(defthm fn-b3-node-window-tree-step
  ; The multi-window step: given the decomposition for both chunk-split
  ; children, it holds for the parent.
  (implies (and (natp k) (natp counter)
                (< (* 1024 (expt 2 k)) (len octets))
                (equal (fn-b3-node key
                         (fn-b3-firstn (* 1024 (fn-b3-left-chunks 1 (len octets))) octets)
                         counter flags)
                       (fn-b3-window-tree key flags
                         (fn-b3-window-outs key k counter
                           (fn-b3-firstn (* 1024 (fn-b3-left-chunks 1 (len octets))) octets)
                           flags)))
                (equal (fn-b3-node key
                         (fn-b3-nthcdrx (* 1024 (fn-b3-left-chunks 1 (len octets))) octets)
                         (+ counter (fn-b3-left-chunks 1 (len octets))) flags)
                       (fn-b3-window-tree key flags
                         (fn-b3-window-outs key k
                           (+ counter (fn-b3-left-chunks 1 (len octets)))
                           (fn-b3-nthcdrx (* 1024 (fn-b3-left-chunks 1 (len octets))) octets)
                           flags))))
           (equal (fn-b3-node key octets counter flags)
                  (fn-b3-window-tree key flags
                    (fn-b3-window-outs key k counter octets flags))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-left-chunks-of-count
                   (m (len (fn-b3-window-outs key k counter octets flags)))
                   (n (len octets)))
                 (:instance fn-b3-window-outs-count (base counter))
                 (:instance fn-b3-window-count-at-least-two (base counter))
                 (:instance fn-b3-left-windows-times-window-below
                   (m (len (fn-b3-window-outs key k counter octets flags)))
                   (n (len octets)))
                 (:instance fn-b3-firstn-of-window-outs
                   (base counter)
                   (j (fn-b3-left-windows 1 (len (fn-b3-window-outs key k counter octets flags)))))
                 (:instance fn-b3-nthcdrx-of-window-outs
                   (base counter)
                   (j (fn-b3-left-windows 1 (len (fn-b3-window-outs key k counter octets flags))))))
           :expand ((fn-b3-window-tree key flags
                      (fn-b3-window-outs key k counter octets flags)))
           :in-theory (disable fn-b3-node fn-b3-window-outs fn-b3-window-tree
                               fn-b3-left-chunks fn-b3-left-windows
                               fn-b3-window-outs-count
                               fn-b3-window-count-at-least-two
                               fn-b3-firstn-of-window-outs
                               fn-b3-nthcdrx-of-window-outs
                               fn-b3-left-windows-times-window-below)
           :nonlinearp t)))

(defthm fn-b3-node-is-window-tree-core
  (implies (and (natp k) (natp counter))
           (equal (fn-b3-node key octets counter flags)
                  (fn-b3-window-tree key flags
                    (fn-b3-window-outs key k counter octets flags))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-b3-node-ind key octets counter flags)
                  :in-theory (disable fn-b3-node fn-b3-window-outs fn-b3-window-tree
                                      fn-b3-left-chunks fn-b3-left-windows))
          ("Subgoal *1/2" :use ((:instance fn-b3-node-window-tree-step)
                                (:instance fn-b3-window-tree-of-single-window (base counter))))
          ("Subgoal *1/1" :use ((:instance fn-b3-node-window-tree-step)
                                (:instance fn-b3-window-tree-of-single-window (base counter))))))

(defthm fn-b3-window-outs-of-nfix-k
  ; The granularity is read through NFIX everywhere.
  (equal (fn-b3-window-outs key (nfix k) base octets flags)
         (fn-b3-window-outs key k base octets flags))
  :rule-classes nil
  :hints (("Goal" :induct (fn-b3-window-outs key k base octets flags)
                  :in-theory (disable fn-b3-node))))

(defthm fn-b3-node-is-window-tree
  ; The whole input's node equals the window tree over the windows' subtree
  ; outputs: each window hashed only against itself, at its own chunk counter.
  ; (natp counter): a counter that is not a natural number reaches the
  ; compression function raw while the window outputs read it through NFIX,
  ; so the sides differ (counter -1, octets (1 2 3): see the test book).
  (implies (natp counter)
           (equal (fn-b3-node key octets counter flags)
                  (fn-b3-window-tree key flags
                    (fn-b3-window-outs key k counter octets flags))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-b3-node-is-window-tree-core (k (nfix k)))
                        (:instance fn-b3-window-outs-of-nfix-k (base counter))))))

; -----------------------------------------------------------------------------
; THE DECOMPOSITION (statements; proofs in progress, see the lanedump):

; The digest reads its input through the octet coercion (`fn-b3-fix-octets'),
; while the tree reads octets only through `fn-b3-nthx' under `fn-b3-octet'
; and through the length: the node of any object is the node of its
; coercion.  So the composition below needs no octet hypothesis.

(local
 (defthm fn-b3-octet-of-octet
   (equal (fn-b3-octet (fn-b3-octet x)) (fn-b3-octet x))
   :hints (("Goal" :in-theory (enable fn-b3-octet)))))

(local
 (defthm fn-b3-nthx-of-fix-octets
   (equal (fn-b3-nthx i (fn-b3-fix-octets l))
          (fn-b3-octet (fn-b3-nthx i l)))
   :hints (("Goal" :in-theory (enable fn-b3-octet fn-b3-fix-octets)
            :induct (fn-b3-nthx i l)))))

(local
 (defthm fn-b3-le-word-of-octets
   (equal (fn-b3-le-word (fn-b3-octet a) (fn-b3-octet b) (fn-b3-octet c) (fn-b3-octet d))
          (fn-b3-le-word a b c d))
   :hints (("Goal" :in-theory (enable fn-b3-le-word)))))

(local
 (defthm fn-b3-nthcdrx-of-fix-octets
   (equal (fn-b3-nthcdrx n (fn-b3-fix-octets l))
          (fn-b3-fix-octets (fn-b3-nthcdrx n l)))
   :hints (("Goal" :in-theory (enable fn-b3-fix-octets fn-b3-nthcdrx)
            :induct (fn-b3-nthcdrx n l)))))

(local
 (defthm fn-b3-firstn-of-fix-octets
   (equal (fn-b3-firstn n (fn-b3-fix-octets l))
          (fn-b3-fix-octets (fn-b3-firstn n l)))
   :hints (("Goal" :in-theory (enable fn-b3-fix-octets fn-b3-firstn)))))

(local
 (defthm fn-b3-words-of-fix-octets
   (equal (fn-b3-words k (fn-b3-fix-octets l)) (fn-b3-words k l))
   :hints (("Goal" :in-theory (e/d (fn-b3-words) (fn-b3-fix-octets))
            :induct (fn-b3-words k l)))))

(local
 (defthm fn-b3-chunk-of-fix-octets
   (equal (fn-b3-chunk cv (fn-b3-fix-octets l) counter flags startp)
          (fn-b3-chunk cv l counter flags startp))
   :hints (("Goal" :induct (fn-b3-chunk cv l counter flags startp)
            :in-theory (disable fn-b3-fix-octets fn-b3-words)
            :expand ((fn-b3-chunk cv (fn-b3-fix-octets l) counter flags startp)
                     (fn-b3-chunk cv l counter flags startp))))))

(local
 (defthm fn-b3-node-of-fix-octets
   (equal (fn-b3-node key (fn-b3-fix-octets l) counter flags)
          (fn-b3-node key l counter flags))
   :hints (("Goal" :induct (fn-b3-node-ind key l counter flags)
            :in-theory (disable fn-b3-fix-octets fn-b3-chunk fn-b3-firstn fn-b3-nthcdrx)
            :expand ((fn-b3-node key (fn-b3-fix-octets l) counter flags)
                     (fn-b3-node key l counter flags))))))

(defthm fn-blake3-is-window-composition
  ; The digest of the whole is the root of the window composition, for ANY
  ; object read as octets (no octet hypothesis: both sides coerce alike).
  (equal (fn-blake3 m)
         (fn-b3-output-root
           (fn-b3-window-tree *fn-b3-iv* 0
             (fn-b3-window-outs *fn-b3-iv* k 0 m 0))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-b3-node-is-window-tree
                          (key *fn-b3-iv*) (counter 0) (flags 0)
                          (octets m)))
                  :do-not-induct t
                  :in-theory (e/d (fn-blake3 fn-b3-hash)
                                  (fn-b3-node fn-b3-window-outs fn-b3-window-tree
                                   fn-b3-fix-octets)))))

; -----------------------------------------------------------------------------
; PAIRING, the held state: the binary-counter stack over a run of window
; outputs, walked with one more output on its right, is the window tree over
; the run and that output (fn-b3-spine-of-push-all).

(local
 (defthm fn-b3-true-listp-len-0
   (implies (and (true-listp os) (equal (len os) 0)) (equal os nil))
   :rule-classes nil))

(defun fn-b3-tail-ind (u os)
  ; Strong induction on the half-count: peel the left subtree's pairs.
  (declare (xargs :measure (nfix u) :verify-guards nil))
  (if (zp u)
      (list u os)
    (fn-b3-tail-ind (- u (fn-b3-left-windows 1 (+ 1 u)))
                    (fn-b3-nthcdrx (* 2 (fn-b3-left-windows 1 (+ 1 u))) os))))

(local
 (defthm fn-b3-len-of-append-single
   (equal (len (append xs (list a))) (+ 1 (len xs)))))

(defthm fn-b3-window-tree-of-pair-tail-step
  ; One peel: the left subtrees agree by the even prefix, the right ones are
  ; the same statement on the shorter run.
  (implies (and (natp u) (<= 1 u) (true-listp os) (equal (len os) (* 2 u))
                (equal (fn-b3-window-tree key flags
                         (append (fn-b3-nthcdrx (* 2 (fn-b3-left-windows 1 (+ 1 u))) os)
                                 (list x)))
                       (fn-b3-window-tree key flags
                         (append (fn-b3-pair-outs key flags
                                   (fn-b3-nthcdrx (* 2 (fn-b3-left-windows 1 (+ 1 u))) os))
                                 (list x)))))
           (equal (fn-b3-window-tree key flags (append os (list x)))
                  (fn-b3-window-tree key flags
                    (append (fn-b3-pair-outs key flags os) (list x)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-window-tree-split (outs (append os (list x))))
                 (:instance fn-b3-window-tree-split
                   (outs (append (fn-b3-pair-outs key flags os) (list x))))
                 (:instance fn-b3-left-windows-1-of-2u+1)
                 (:instance fn-b3-left-windows-below (p 1) (j (+ 1 u)))
                 (:instance fn-b3-left-windows-posp (p 1) (j (+ 1 u)))
                 (:instance fn-b3-window-tree-of-even-prefix
                   (i (fn-b3-left-windows 1 (+ 1 u))) (outs os))
                 (:instance fn-b3-pair-outs-of-nthcdrx
                   (i (fn-b3-left-windows 1 (+ 1 u))) (outs os))
                 (:instance fn-b3-firstn-of-append-le
                   (a (* 2 (fn-b3-left-windows 1 (+ 1 u)))) (x os) (y (list x)))
                 (:instance fn-b3-nthcdrx-of-append-le
                   (a (* 2 (fn-b3-left-windows 1 (+ 1 u)))) (x os) (y (list x)))
                 (:instance fn-b3-firstn-of-append-le
                   (a (fn-b3-left-windows 1 (+ 1 u)))
                   (x (fn-b3-pair-outs key flags os)) (y (list x)))
                 (:instance fn-b3-nthcdrx-of-append-le
                   (a (fn-b3-left-windows 1 (+ 1 u)))
                   (x (fn-b3-pair-outs key flags os)) (y (list x))))
           :in-theory (e/d (fn-b3-len-of-cdr fn-b3-consp-of-len-pos)
                           (binary-append fn-b3-firstn fn-b3-nthcdrx fn-b3-nthcdrx-all-when-len
                            fn-b3-firstn-all-when-len
                            fn-b3-window-tree fn-b3-pair-outs fn-b3-left-windows
                               fn-b3-window-tree-split fn-b3-left-windows-1-of-2u+1
                               fn-b3-left-windows-below fn-b3-left-windows-posp
                               fn-b3-window-tree-of-even-prefix
                               fn-b3-pair-outs-of-nthcdrx
                               fn-b3-firstn-of-append-le fn-b3-nthcdrx-of-append-le
                               fn-b3-left-windows-plus fn-b3-left-windows-1-plus
                               fn-b3-left-windows-double fn-b3-left-windows-double-minus
                               fn-b3-left-windows-1-double fn-b3-lw-of-double-len
                               fn-b3-window-tree-of-pairs))
           :nonlinearp t)))

(local
 (defthm fn-b3-len-of-append-two
   (equal (len (append xs (list a b))) (+ 2 (len xs)))))

(defthm fn-b3-window-tree-of-pair-tail
  ; The tree over an even run and one more output is the tree over the run's
  ; pairs and that output: the extra single stays last at every level.
  (implies (and (natp u) (true-listp os) (equal (len os) (* 2 u)))
           (equal (fn-b3-window-tree key flags (append os (list x)))
                  (fn-b3-window-tree key flags
                    (append (fn-b3-pair-outs key flags os) (list x)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-b3-tail-ind u os)
                  :in-theory (disable fn-b3-window-tree fn-b3-pair-outs
                                      fn-b3-left-windows))
          ("Subgoal *1/1" :use ((:instance fn-b3-true-listp-len-0))
                        :in-theory (enable fn-b3-pair-outs))
          ("Subgoal *1/2" :use ((:instance fn-b3-window-tree-of-pair-tail-step)))))

(defun fn-b3-all-non-nil (outs)
  ; Every output of the run is a non-NIL object (NIL names the empty right
  ; side of the held state's spine walk).
  (declare (xargs :guard t))
  (if (atom outs)
      t
    (and (car outs) (fn-b3-all-non-nil (cdr outs)))))

(defthm fn-b3-chunk-consp
  (consp (fn-b3-chunk cv octets counter flags startp))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-b3-chunk cv octets counter flags startp))))

(defthm fn-b3-node-consp
  (consp (fn-b3-node key octets counter flags))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-b3-node key octets counter flags))))

(defthm fn-b3-parent-out-consp
  (consp (fn-b3-parent-out key lout rout flags))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-b3-parent-out))))

(defthm fn-b3-all-non-nil-of-window-outs
  (fn-b3-all-non-nil (fn-b3-window-outs key k base octets flags))
  :hints (("Goal" :induct (fn-b3-window-outs key k base octets flags)
                  :in-theory (disable fn-b3-node))))

(defthm fn-b3-all-non-nil-of-pair-outs
  (fn-b3-all-non-nil (fn-b3-pair-outs key flags outs))
  :hints (("Goal" :induct (fn-b3-pair-outs key flags outs))))

(local
 (defthm fn-b3-all-non-nil-of-append
    (equal (fn-b3-all-non-nil (append xs ys))
           (and (fn-b3-all-non-nil xs) (fn-b3-all-non-nil ys)))))

(defthm fn-b3-cv-push-spine
  ; Absorbing a non-NIL output into a held state does not change what the
  ; state folds to with that output as the right side: the merge cascade
  ; and the spine nest the same parents.
  (implies x
           (equal (fn-b3-stack-spine key flags
                    (fn-b3-cv-push key flags h x st) nil)
                  (fn-b3-stack-spine key flags st x)))
  :hints (("Goal" :induct (fn-b3-cv-push key flags h x st))))

(local
 (defthm fn-b3-snoc-split
    ; A non-empty run is its all-but-last followed by its last.
    (implies (and (true-listp os) (consp os))
             (equal (append (fn-b3-firstn (+ -1 (len os)) os)
                            (list (car (fn-b3-nthcdrx (+ -1 (len os)) os))))
                    os))
    :hints (("Goal" :induct (len os)
                    :expand ((fn-b3-firstn (+ -1 (len os)) os)
                             (fn-b3-nthcdrx (+ -1 (len os)) os))))))

(local
 (defthm fn-b3-snoc-split-two
    ; The snoc split with one more output appended after the last.
    (implies (and (true-listp os) (consp os))
             (equal (append os (list x))
                    (append (fn-b3-firstn (+ -1 (len os)) os)
                            (list (car (fn-b3-nthcdrx (+ -1 (len os)) os)) x))))
    :rule-classes nil
    :hints (("Goal" :use fn-b3-snoc-split
                    :in-theory (disable fn-b3-snoc-split)))))

(local
 (defthm fn-b3-all-non-nil-of-last
    (implies (and (fn-b3-all-non-nil os) (consp os))
             (car (fn-b3-nthcdrx (+ -1 (len os)) os)))
    :hints (("Goal" :induct (len os)
                    :expand ((fn-b3-nthcdrx (+ -1 (len os)) os))))))

(local
 (defthm fn-b3-all-non-nil-of-firstn
    (implies (fn-b3-all-non-nil os)
             (fn-b3-all-non-nil (fn-b3-firstn n os)))))

(local
 (defthm fn-b3-spine-of-push-all-odd-step
    ; The odd step: the held state after os' ++ (y) is y's entry in front of
    ; the state of os''s pairs, so the walk folds to the state of the pairs with
    ; the parent of y and x on the right.
    (implies (and (natp h) (true-listp os) (evenp (len os)) y x
                  (equal (fn-b3-stack-spine key flags
                           (fn-b3-stack-push-all key flags (+ 1 h)
                             (fn-b3-pair-outs key flags os) nil)
                           (fn-b3-parent-out key y x flags))
                         (fn-b3-window-tree key flags
                           (append (fn-b3-pair-outs key flags os)
                                   (list (fn-b3-parent-out key y x flags))))))
             (equal (fn-b3-stack-spine key flags
                      (fn-b3-stack-push-all key flags h
                        (append os (list y)) nil)
                      x)
                    (fn-b3-window-tree key flags
                      (append os (list y x)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance fn-b3-stack-push-all-append-single (os os) (x y))
                   (:instance fn-b3-stack-push-all-of-pairs (outs os) (st nil))
                   (:instance fn-b3-window-tree-of-pairs
                     (u (+ 1 (floor (len os) 2)))
                     (outs (append os (list y x))))
                   (:instance fn-b3-pair-outs-of-append-two
                     (i (floor (len os) 2)) (os os) (x y) (y x)))
             :expand ((fn-b3-stack-above h nil))
             :in-theory (disable fn-b3-stack-push-all-append-single
                                 fn-b3-stack-push-all-of-pairs
                                 fn-b3-window-tree-of-pairs
                                 fn-b3-pair-outs-of-append-two
                                 fn-b3-window-tree fn-b3-pair-outs
                                 fn-b3-stack-push-all fn-b3-left-windows
                                 fn-b3-left-windows-plus fn-b3-left-windows-1-plus
                                 fn-b3-left-windows-double fn-b3-left-windows-double-minus
                                 fn-b3-left-windows-1-double fn-b3-lw-of-double-len
                                 fn-b3-left-windows-1-of-2u+1)))))

(local
 (defthm fn-b3-spine-of-push-all-even-step
    ; The even step: an even run's state is its pairs' state one level up, and
    ; the tree over the run and one more output is the tree over the pairs and
    ; that output.
    (implies (and (natp h) (true-listp os) (evenp (len os))
                  (equal (fn-b3-stack-spine key flags
                           (fn-b3-stack-push-all key flags (+ 1 h)
                             (fn-b3-pair-outs key flags os) nil)
                           x)
                         (fn-b3-window-tree key flags
                           (append (fn-b3-pair-outs key flags os) (list x)))))
             (equal (fn-b3-stack-spine key flags
                      (fn-b3-stack-push-all key flags h os nil) x)
                    (fn-b3-window-tree key flags (append os (list x)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance fn-b3-stack-push-all-of-pairs (outs os) (st nil))
                   (:instance fn-b3-window-tree-of-pair-tail (u (floor (len os) 2))))
             :expand ((fn-b3-stack-above h nil))
             :in-theory (disable fn-b3-stack-push-all-of-pairs
                                 fn-b3-window-tree fn-b3-pair-outs
                                 fn-b3-stack-push-all fn-b3-left-windows)))))

(defun fn-b3-f-ind (key flags h os x)
  ; The pairing induction: an even run steps to its pairs, an odd run to the
  ; pairs of all but its last, with that last parented over x.
  (declare (xargs :measure (len os) :verify-guards nil))
  (cond ((atom os) (list h x))
        ((evenp (len os))
         (fn-b3-f-ind key flags (+ 1 h) (fn-b3-pair-outs key flags os) x))
        (t (fn-b3-f-ind key flags (+ 1 h)
             (fn-b3-pair-outs key flags (fn-b3-firstn (+ -1 (len os)) os))
             (fn-b3-parent-out key (car (fn-b3-nthcdrx (+ -1 (len os)) os)) x flags)))))

(defthm fn-b3-spine-of-push-all
  ; PAIRING: the held state over a run of non-NIL outputs, walked with one
  ; more output on its right, is the window tree over the run and that output.
  (implies (and (natp h) (true-listp os) (fn-b3-all-non-nil os) x)
           (equal (fn-b3-stack-spine key flags
                    (fn-b3-stack-push-all key flags h os nil) x)
                  (fn-b3-window-tree key flags (append os (list x)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-b3-f-ind key flags h os x)
                  :in-theory (disable fn-b3-window-tree fn-b3-pair-outs
                                      fn-b3-stack-push-all fn-b3-left-windows
                                      fn-b3-stack-push-all-of-pairs))
          ("Subgoal *1/3"
           :use ((:instance fn-b3-spine-of-push-all-odd-step
                   (os (fn-b3-firstn (+ -1 (len os)) os))
                   (y (car (fn-b3-nthcdrx (+ -1 (len os)) os))))
                 (:instance fn-b3-snoc-split)
                 (:instance fn-b3-snoc-split-two)))
          ("Subgoal *1/2"
           :use ((:instance fn-b3-spine-of-push-all-even-step)))
          ("Subgoal *1/1" :in-theory (e/d (fn-b3-stack-push-all)
                                         (fn-b3-stack-push-all-of-pairs)))))

; -----------------------------------------------------------------------------
; THE STREAMING STATE: the held state over whole windows folds to the node of
; the input so far, and absorbing one more window extends that input.

(local
 (defthm fn-b3-len-of-append
   (equal (len (append xs ys)) (+ (len xs) (len ys)))))

(defthm fn-b3-window-outs-true-listp
  (true-listp (fn-b3-window-outs key k base octets flags))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-b3-window-outs key k base octets flags)
                  :in-theory (disable fn-b3-node))))

(defun fn-b3-wj-ind (j k base prefix flags)
  ; Window-by-window induction on whole windows: j counts down.
  (declare (xargs :measure (nfix j) :verify-guards nil))
  (if (<= (nfix j) 1)
      (list j k base prefix flags)
    (fn-b3-wj-ind (- j 1) k (+ (nfix base) (expt 2 (nfix k)))
                  (fn-b3-nthcdrx (* 1024 (expt 2 (nfix k))) prefix) flags)))

(defthm fn-b3-window-outs-of-append-window
  ; One more window after j whole windows is one more output at the advanced
  ; counter, the earlier outputs unchanged.
  (implies (and (natp k) (natp base) (posp j) (true-listp prefix)
                (equal (len prefix) (* j (* 1024 (expt 2 k))))
                (posp (len w)) (<= (len w) (* 1024 (expt 2 k))))
           (equal (fn-b3-window-outs key k base (append prefix w) flags)
                  (append (fn-b3-window-outs key k base prefix flags)
                          (list (fn-b3-node key w
                                  (+ base (* j (expt 2 k))) flags)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-b3-wj-ind j k base prefix flags)
                  :in-theory (disable fn-b3-node))))

(defthm fn-b3-stack-fold-of-push-snoc
  ; The state after one more output is folded as the walk with it on the right.
  (implies x
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-cv-push key flags h x
                      (fn-b3-stack-push-all key flags h os nil)))
                  (fn-b3-stack-spine key flags
                    (fn-b3-stack-push-all key flags h os nil) x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-b3-stack-fold))))

(defthm fn-b3-stack-fold-of-run-snoc
  ; A run of non-NIL outputs and one more: the held state folds to the tree.
  (implies (and (natp h) (true-listp os) (fn-b3-all-non-nil os) x)
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-stack-push-all key flags h (append os (list x)) nil))
                  (fn-b3-window-tree key flags (append os (list x)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-spine-of-push-all)
                 (:instance fn-b3-stack-fold-of-push-snoc))
           :in-theory (disable fn-b3-window-tree fn-b3-pair-outs
                               fn-b3-left-windows fn-b3-stack-push-all-of-pairs)
           :expand ((fn-b3-stack-push-all key flags h (list x)
                      (fn-b3-stack-push-all key flags h os nil))))))

(defthm fn-b3-stack-fold-of-run
  ; The held state over a non-empty run of non-NIL outputs folds to the
  ; window tree over the run.
  (implies (and (natp h) (true-listp outs) (consp outs)
                (fn-b3-all-non-nil outs))
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-stack-push-all key flags h outs nil))
                  (fn-b3-window-tree key flags outs)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-stack-fold-of-run-snoc
                   (os (fn-b3-firstn (+ -1 (len outs)) outs))
                   (x (car (fn-b3-nthcdrx (+ -1 (len outs)) outs))))
                 (:instance fn-b3-snoc-split (os outs)))
           :in-theory (disable fn-b3-window-tree fn-b3-pair-outs
                               fn-b3-left-windows fn-b3-stack-push-all-of-pairs
                               fn-b3-stack-push-all))))

(defthm fn-b3-window-outs-consp
  (consp (fn-b3-window-outs key k base octets flags))
  :rule-classes :type-prescription
  :hints (("Goal" :expand ((fn-b3-window-outs key k base octets flags)))))

(local
 (defthm fn-b3-cv-push-of-nfix-h
    ; The height is read through NFIX everywhere.
    (equal (fn-b3-cv-push key flags (nfix h) out st)
           (fn-b3-cv-push key flags h out st))
    :hints (("Goal" :induct (fn-b3-cv-push key flags h out st)))))

(local
 (defthm fn-b3-stack-push-all-of-nfix-h
    (equal (fn-b3-stack-push-all key flags (nfix h) outs st)
           (fn-b3-stack-push-all key flags h outs st))
    :hints (("Goal" :induct (fn-b3-stack-push-all key flags h outs st)
                    :in-theory (disable nfix)))))

(defthm fn-b3-stack-fold-of-windows-core
  (implies (and (natp k) (natp counter))
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-stack-push-all key flags k
                      (fn-b3-window-outs key k counter octets flags) nil))
                  (fn-b3-node key octets counter flags)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-stack-fold-of-run
                   (h k) (outs (fn-b3-window-outs key k counter octets flags)))
                 (:instance fn-b3-node-is-window-tree-core))
           :in-theory (disable fn-b3-window-tree fn-b3-window-outs fn-b3-node
                               fn-b3-stack-push-all fn-b3-stack-fold
                               fn-b3-left-windows fn-b3-stack-push-all-of-pairs
))))

(defthm fn-b3-stack-fold-of-windows
  ; The held state: folding the stack built from the windows' subtree outputs
  ; is the whole input's node.  (natp counter): see fn-b3-node-is-window-tree.
  (implies (natp counter)
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-stack-push-all key flags k
                      (fn-b3-window-outs key k counter octets flags) nil))
                  (fn-b3-node key octets counter flags)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-b3-stack-fold-of-windows-core (k (nfix k)))
                 (:instance fn-b3-window-outs-of-nfix-k (base counter)))
           :in-theory (disable fn-b3-window-outs
                               fn-b3-node fn-b3-stack-push-all fn-b3-stack-fold
                               fn-b3-stack-push-all-of-pairs))))

(local
 (defthm fn-b3-octet-listp-true-listp
   (implies (fn-b3-octet-listp x) (true-listp x))
   :rule-classes :forward-chaining))

(local
 (defthm fn-b3-whole-windows
   ; A multiple of the window size is that many windows.
   (implies (and (natp a) (posp b) (equal (mod a b) 0))
            (equal (* b (floor a b)) a))
   :rule-classes nil))

(local
 (defthm fn-b3-len-pos-of-consp
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear))

(defthm fn-b3-append-window-core
  (implies (and (natp k) (natp counter)
                (fn-b3-octet-listp prefix) (consp prefix)
                (equal (mod (len prefix) (* 1024 (expt 2 k))) 0)
                (fn-b3-octet-listp w) (posp (len w))
                (<= (len w) (* 1024 (expt 2 k))))
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-cv-push key flags k
                      (fn-b3-node key w
                        (+ counter
                           (* (expt 2 k)
                              (floor (len prefix) (* 1024 (expt 2 k)))))
                        flags)
                      (fn-b3-stack-push-all key flags k
                        (fn-b3-window-outs key k counter prefix flags) nil)))
                  (fn-b3-node key (append prefix w) counter flags)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-stack-fold-of-push-snoc
                   (h k)
                   (x (fn-b3-node key w
                        (+ counter
                           (* (expt 2 k)
                              (floor (len prefix) (* 1024 (expt 2 k)))))
                        flags))
                   (os (fn-b3-window-outs key k counter prefix flags)))
                 (:instance fn-b3-spine-of-push-all
                   (h k)
                   (x (fn-b3-node key w
                        (+ counter
                           (* (expt 2 k)
                              (floor (len prefix) (* 1024 (expt 2 k)))))
                        flags))
                   (os (fn-b3-window-outs key k counter prefix flags)))
                 (:instance fn-b3-window-outs-of-append-window
                   (base counter)
                   (j (floor (len prefix) (* 1024 (expt 2 k)))))
                 (:instance fn-b3-node-is-window-tree-core
                   (octets (append prefix w)))
                 (:instance fn-b3-whole-windows
                   (a (len prefix)) (b (* 1024 (expt 2 k)))))
           :in-theory (disable fn-b3-window-tree fn-b3-window-outs fn-b3-node
                               fn-b3-stack-push-all fn-b3-stack-fold
                               fn-b3-left-windows fn-b3-stack-push-all-of-pairs
                               fn-b3-cv-push))))

(defthm fn-b3-append-window
  ; The append extension: absorbing one more window into the state held over
  ; whole windows of PREFIX equals digesting PREFIX ++ that window.
  ; (consp prefix): an empty prefix still holds the one window of the empty
  ; input (window-outs of nil is a singleton), so the stack would merge with
  ; it.  (natp counter): as for fn-b3-node-is-window-tree.  Both
  ; counterexamples are in the test book.
  (implies (and (natp counter)
                (fn-b3-octet-listp prefix) (consp prefix)
                (equal (mod (len prefix) (* 1024 (expt 2 (nfix k)))) 0)
                (fn-b3-octet-listp w) (posp (len w))
                (<= (len w) (* 1024 (expt 2 (nfix k)))))
           (equal (fn-b3-stack-fold key flags
                    (fn-b3-cv-push key flags k
                      (fn-b3-node key w
                        (+ (nfix counter)
                           (* (expt 2 (nfix k))
                              (floor (len prefix) (* 1024 (expt 2 (nfix k))))))
                        flags)
                      (fn-b3-stack-push-all key flags k
                        (fn-b3-window-outs key k counter prefix flags) nil)))
                  (fn-b3-node key (append prefix w) counter flags)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-b3-append-window-core (k (nfix k)))
                 (:instance fn-b3-window-outs-of-nfix-k (base counter) (octets prefix)))
           :in-theory (disable fn-b3-window-outs fn-b3-node fn-b3-stack-push-all
                               fn-b3-stack-fold fn-b3-cv-push
                               fn-b3-stack-push-all-of-pairs))))

(local
 (defthm fn-b3-stack-push-all-of-snoc
   ; One more output on the right is one more push on the state of the run.
   (equal (fn-b3-stack-push-all key flags h (append os (list x)) st)
          (fn-b3-cv-push key flags h x
            (fn-b3-stack-push-all key flags h os st)))
   :hints (("Goal" :induct (fn-b3-stack-push-all key flags h os st)))))

(defthm fn-b3-append-window-state-core
  (implies (and (natp k) (natp counter)
                (fn-b3-octet-listp prefix) (consp prefix)
                (equal (mod (len prefix) (* 1024 (expt 2 k))) 0)
                (fn-b3-octet-listp w) (posp (len w))
                (<= (len w) (* 1024 (expt 2 k))))
           (equal (fn-b3-cv-push key flags k
                    (fn-b3-node key w
                      (+ counter
                         (* (expt 2 k)
                            (floor (len prefix) (* 1024 (expt 2 k)))))
                      flags)
                    (fn-b3-stack-push-all key flags k
                      (fn-b3-window-outs key k counter prefix flags) nil))
                  (fn-b3-stack-push-all key flags k
                    (fn-b3-window-outs key k counter (append prefix w) flags) nil)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-b3-window-outs-of-append-window
                   (base counter)
                   (j (floor (len prefix) (* 1024 (expt 2 k)))))
                 (:instance fn-b3-whole-windows
                   (a (len prefix)) (b (* 1024 (expt 2 k)))))
           :in-theory (disable fn-b3-window-outs fn-b3-node fn-b3-stack-push-all
                               fn-b3-cv-push))))

(local
 (defthm fn-b3-window-outs-of-nfix-base
   ; The base counter is read through NFIX everywhere.
   (equal (fn-b3-window-outs key k (nfix base) octets flags)
          (fn-b3-window-outs key k base octets flags))
   :hints (("Goal" :expand ((fn-b3-window-outs key k (nfix base) octets flags)
                            (fn-b3-window-outs key k base octets flags))))))

(defthm fn-b3-append-window-state
  ; The append extension on the held STATE, not only its fold: absorbing one
  ; more window into the state over whole windows of PREFIX is the state over
  ; the windows of PREFIX ++ that window, so appends iterate.  The hypotheses
  ; of fn-b3-append-window less (natp counter): counter, height and windows all
  ; read their numbers through NFIX, so the state equation holds for any
  ; counter (the fold equation does not: the node side reads it raw).
  (implies (and (fn-b3-octet-listp prefix) (consp prefix)
                (equal (mod (len prefix) (* 1024 (expt 2 (nfix k)))) 0)
                (fn-b3-octet-listp w) (posp (len w))
                (<= (len w) (* 1024 (expt 2 (nfix k)))))
           (equal (fn-b3-cv-push key flags k
                    (fn-b3-node key w
                      (+ (nfix counter)
                         (* (expt 2 (nfix k))
                            (floor (len prefix) (* 1024 (expt 2 (nfix k))))))
                      flags)
                    (fn-b3-stack-push-all key flags k
                      (fn-b3-window-outs key k counter prefix flags) nil))
                  (fn-b3-stack-push-all key flags k
                    (fn-b3-window-outs key k counter (append prefix w) flags) nil)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-b3-append-window-state-core (k (nfix k)) (counter (nfix counter)))
                 (:instance fn-b3-window-outs-of-nfix-k (base counter) (octets prefix))
                 (:instance fn-b3-window-outs-of-nfix-k (base counter)
                            (octets (append prefix w))))
           :in-theory (disable fn-b3-window-outs fn-b3-node fn-b3-stack-push-all
                               fn-b3-cv-push))))

(defthm fn-blake3-keyed-is-window-composition
  ; Keyed mode: the digest is the root of the window composition at the key
  ; words and the keyed-hash flag.  For any key and message objects.
  (equal (fn-blake3-keyed key m)
         (fn-b3-output-root
           (fn-b3-window-tree (fn-b3-words 8 (fn-b3-fix-octets key))
                              *fn-b3-keyed-hash*
             (fn-b3-window-outs (fn-b3-words 8 (fn-b3-fix-octets key)) k 0 m
                                *fn-b3-keyed-hash*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-b3-node-is-window-tree
                          (key (fn-b3-words 8 (fn-b3-fix-octets key)))
                          (counter 0) (flags *fn-b3-keyed-hash*)
                          (octets m)))
                  :do-not-induct t
                  :in-theory (e/d (fn-blake3-keyed fn-b3-hash)
                                  (fn-b3-node fn-b3-window-outs fn-b3-window-tree
                                   fn-b3-fix-octets)))))

(defthm fn-blake3-derive-key-is-window-composition
  ; Derive-key mode: the context's digest under the context flag keys the
  ; material's window composition under the material flag.
  (equal (fn-blake3-derive-key context m)
         (fn-b3-output-root
           (fn-b3-window-tree
             (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                        (fn-b3-fix-octets context)))
             *fn-b3-derive-key-material*
             (fn-b3-window-outs
               (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                          (fn-b3-fix-octets context)))
               k 0 m *fn-b3-derive-key-material*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-b3-node-is-window-tree
                          (key (fn-b3-words 8 (fn-b3-hash *fn-b3-iv* *fn-b3-derive-key-context*
                                                          (fn-b3-fix-octets context))))
                          (counter 0) (flags *fn-b3-derive-key-material*)
                          (octets m)))
                  :do-not-induct t
                  :in-theory (e/d (fn-blake3-derive-key fn-b3-hash)
                                  (fn-b3-node fn-b3-window-outs fn-b3-window-tree
                                   fn-b3-fix-octets)))))
