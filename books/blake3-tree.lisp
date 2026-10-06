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

; -----------------------------------------------------------------------------
; THE DECOMPOSITION (statements; proofs in progress, see the lanedump):

; The whole input's node equals the window tree over the windows' subtree
; outputs — each window hashed only against itself, at its own chunk counter.
;
; PROOF-OWED: fn-b3-node-is-window-tree
;   (equal (fn-b3-node key octets counter flags)
;          (fn-b3-window-tree key flags
;            (fn-b3-window-outs key k counter octets flags)))
;   Strong induction on (len octets): at most one window by definition; more
;   by fn-b3-node-splits-at-left-chunks, lockstep, and the window-alignment
;   lemmas (split-windows/window-outs of firstn/nthcdr at window multiples),
;   with the induction hypotheses on both strictly shorter children.

; The digest of the whole equals the root of that window composition.
;
; PROOF-OWED: fn-blake3-is-window-composition
;   (implies (fn-b3-octet-listp m)
;            (equal (fn-blake3 m)
;                   (fn-b3-output-root
;                     (fn-b3-window-tree *fn-b3-iv* 0
;                       (fn-b3-window-outs *fn-b3-iv* k 0 m 0)))))

; The held state: folding the stack built from the windows' subtree outputs
; is the whole input's node (PAIRING: fold = window-tree, then decomposition).
;
; PROOF-OWED: fn-b3-stack-fold-of-windows
;   (equal (fn-b3-stack-fold key flags
;             (fn-b3-stack-push-all key flags k
;               (fn-b3-window-outs key k counter octets flags) nil))
;          (fn-b3-node key octets counter flags))

; The append extension: absorbing one more window into the state held over
; whole windows of PREFIX equals digesting PREFIX ++ that window.
;
; PROOF-OWED: fn-b3-append-window
;   (implies (and (fn-b3-octet-listp prefix)
;                 (equal (mod (len prefix) (* 1024 (expt 2 (nfix k)))) 0)
;                 (fn-b3-octet-listp w) (posp (len w))
;                 (<= (len w) (* 1024 (expt 2 (nfix k)))))
;            (equal (fn-b3-stack-fold key flags
;                      (fn-b3-cv-push key flags k
;                        (fn-b3-node key w
;                          (+ (nfix counter)
;                             (* (expt 2 (nfix k))
;                                (floor (len prefix) (* 1024 (expt 2 (nfix k))))))
;                          flags)
;                        (fn-b3-stack-push-all key flags k
;                          (fn-b3-window-outs key k counter prefix flags) nil)))
;                   (fn-b3-node key (append prefix w) counter flags)))
