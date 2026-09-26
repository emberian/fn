; fn: fragment reassembly without a family-size ceiling (RFC 9171 section
; 5.9), in work proportional to the material received, refined to the
; index-wise reference of bp-fragment.lisp.
;
; The reference `fn-bpf-reassemble` computes every cell of the canvas as the
; merge over the whole fragment list at that index.  That is the right
; specification and the wrong program: its work is (total x fragments), so it
; carries two data ceilings, `*fn-bpf-max-length*` (65538) and
; `*fn-bpf-max-fragments*` (64), and a 10 MiB family of 4 KiB fragments would
; cost 2.7e10 probes.  D27 forbids a data ceiling standing in for a work
; bound.
;
; This book separates the two:
;
;   fn-bpfw-spec        the reference's own definition with the two caps
;                       removed from its input recognizer (logic only; it is
;                       the meaning, never executed);
;   fn-bpfw-reassemble  the executed reassembler: the fragments sorted by
;                       offset (a merge sort), then one sweep over positions
;                       0..total-1 that keeps, per position, only the extents
;                       that cover it.  Its work is O(n log n) for the sort
;                       plus O(total + the sum of the fragment lengths) for
;                       the sweep and the outcome scan: linear in the octets
;                       received.  It is tail-recursive over positions.
;
; Keystones:
;   fn-bpfw-reassemble-is-spec          the executed reassembler equals the
;                                       uncapped reference, for every input;
;   fn-bpf-reassemble-is-capped-spec    the old capped reference is the
;                                       uncapped one restricted to the caps,
;                                       so every theorem about it is a
;                                       theorem about the spec in its range;
;   fn-bpfw-exact-canvas-reassembles    a family whose canvas is an octet
;                                       list (every index covered, no
;                                       disagreement) reassembles to exactly
;                                       that list, with no cap.
;
; Conflict still takes precedence over a gap, overlapping identical extents
; still merge, and the four outcomes (:invalid, :conflict, :missing, :ok)
; stay distinct: the outcome function is the reference's, applied to an
; equal canvas.
;
; This book performs no I/O, reserves no capacity and releases no
; obligation.  A reassembled ADU is not an accepted article.

(in-package "ACL2")

(include-book "bp-fragment")

(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable mod-x-y-=-x+y-for-rationals)))

; -----------------------------------------------------------------------------
; Fragments without the data ceiling

(defun fn-bpfw-fragmentp (f)
  (declare (xargs :guard t))
  (and (true-listp f)
       (equal (len f) 4)
       (eq (nth 0 f) :fn-bp-fragment)
       (natp (fn-bpf-offset f))
       (fn-cbor-octet-listp (fn-bpf-bytes f))
       (natp (fn-bpf-total f))
       (consp (fn-bpf-bytes f))
       (<= (+ (fn-bpf-offset f) (len (fn-bpf-bytes f))) (fn-bpf-total f))))

(defun fn-bpfw-fragment-listp (fs)
  (declare (xargs :guard t))
  (if (consp fs)
      (and (fn-bpfw-fragmentp (car fs)) (fn-bpfw-fragment-listp (cdr fs)))
    (null fs)))

(defun fn-bpfw-same-total (fs total)
  (declare (xargs :guard (fn-bpfw-fragment-listp fs)))
  (if (consp fs)
      (and (equal (fn-bpf-total (car fs)) total)
           (fn-bpfw-same-total (cdr fs) total))
    t))

(defun fn-bpfw-inputsp (fs total)
  (declare (xargs :guard t))
  (and (fn-bpfw-fragment-listp fs)
       (natp total)
       (< 0 total)
       (consp fs)
       (fn-bpfw-same-total fs total)))

(local
 (defthm fn-bpfw-fragmentp-fields
   (implies (fn-bpfw-fragmentp f)
            (and (true-listp f)
                 (natp (fn-bpf-offset f))
                 (integerp (fn-bpf-offset f))
                 (<= 0 (fn-bpf-offset f))
                 (fn-cbor-octet-listp (fn-bpf-bytes f))
                 (true-listp (fn-bpf-bytes f))
                 (consp (fn-bpf-bytes f))
                 (<= (+ (fn-bpf-offset f) (len (fn-bpf-bytes f)))
                     (fn-bpf-total f))))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm fn-bpfw-fragment-listp-is-a-true-list
   (implies (fn-bpfw-fragment-listp fs) (true-listp fs))
   :rule-classes (:rewrite :forward-chaining)))

(defthm fn-bpfw-same-total-is-the-reference
  (equal (fn-bpfw-same-total fs total) (fn-bpf-same-total fs total)))

; The capped recognizer is the uncapped one with every total under the cap.
(local
 (defthm fn-bpfw-capped-fragment-list
   (implies (fn-bpf-fragment-listp fs) (fn-bpfw-fragment-listp fs))))

(local
 (defthm fn-bpfw-fragment-list-under-the-cap
   (implies (and (fn-bpfw-fragment-listp fs)
                 (fn-bpf-same-total fs total)
                 (<= total *fn-bpf-max-length*))
            (fn-bpf-fragment-listp fs))))

(local
 (defthm fn-bpfw-inputsp-with-caps
   (equal (fn-bpf-inputsp fs total)
          (and (fn-bpfw-inputsp fs total)
               (<= total *fn-bpf-max-length*)
               (<= (len fs) *fn-bpf-max-fragments*)))
   :hints (("Goal" :in-theory (disable fn-bpf-fragment-listp
                                       fn-bpfw-fragment-listp)))))

; From here on a fragment is seen through its accessors.
(local (in-theory (disable fn-bpfw-fragmentp fn-bpf-offset fn-bpf-bytes
                           fn-bpf-total)))

; -----------------------------------------------------------------------------
; The specification: the reference with the caps removed

(defun fn-bpfw-outcome (cells)
  (declare (xargs :guard (true-listp cells)))
  (let ((conflict (fn-bpf-first-index cells 0 :conflict)))
    (if conflict
        (list :conflict conflict)
      (let ((gap (fn-bpf-first-index cells 0 :gap)))
        (if gap
            (list :missing gap (fn-bpf-run-end (nthcdr gap cells) gap :gap))
          (list :ok cells))))))

(defun fn-bpfw-spec (fs total)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpfw-inputsp fs total))
      (list :invalid :bounds)
    (fn-bpfw-outcome (fn-bpf-canvas fs 0 total))))

(defthm fn-bpf-reassemble-is-capped-spec
  (equal (fn-bpf-reassemble fs total)
         (if (and (<= total *fn-bpf-max-length*)
                  (<= (len fs) *fn-bpf-max-fragments*))
             (fn-bpfw-spec fs total)
           (list :invalid :bounds)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bpfw-inputsp fn-bpf-inputsp
                                      fn-bpf-canvas fn-bpf-first-index
                                      fn-bpf-run-end))))

; -----------------------------------------------------------------------------
; The merge of cells is a semilattice: :gap is its unit and :conflict absorbs
; every non-gap cell, so the order in which extents are merged is irrelevant.

(local
 (defthm fn-bpfw-merge-cell-commutes
   (equal (fn-bpf-merge-cell x y) (fn-bpf-merge-cell y x))))

(local
 (defthm fn-bpfw-merge-cell-associates
   (equal (fn-bpf-merge-cell (fn-bpf-merge-cell x y) z)
          (fn-bpf-merge-cell x (fn-bpf-merge-cell y z)))))

(local
 (defthm fn-bpfw-merge-cell-commutes-2
   (equal (fn-bpf-merge-cell x (fn-bpf-merge-cell y z))
          (fn-bpf-merge-cell y (fn-bpf-merge-cell x z)))))

(local
 (defthm fn-bpfw-merge-cell-gap
   (and (equal (fn-bpf-merge-cell :gap x) x)
        (equal (fn-bpf-merge-cell x :gap) x))))

(local (in-theory (disable fn-bpf-merge-cell)))

; -----------------------------------------------------------------------------
; Sorting by offset (a merge sort)

(defun fn-bpfw-evens (xs)
  (declare (xargs :guard (true-listp xs)))
  (if (consp xs)
      (cons (car xs) (fn-bpfw-evens (cddr xs)))
    nil))

(defthm fn-bpfw-len-evens
  (<= (len (fn-bpfw-evens xs)) (len xs))
  :rule-classes :linear)

(defthm fn-bpfw-len-evens-strict
  (implies (consp (cdr xs))
           (< (len (fn-bpfw-evens xs)) (len xs)))
  :hints (("Goal" :expand ((fn-bpfw-evens xs))))
  :rule-classes :linear)

(defun fn-bpfw-merge (a b)
  (declare (xargs :guard (and (fn-bpfw-fragment-listp a)
                              (fn-bpfw-fragment-listp b))
                  :measure (+ (acl2-count a) (acl2-count b))))
  (cond ((atom a) b)
        ((atom b) a)
        ((<= (fn-bpf-offset (car a)) (fn-bpf-offset (car b)))
         (cons (car a) (fn-bpfw-merge (cdr a) b)))
        (t (cons (car b) (fn-bpfw-merge a (cdr b))))))

(defthm fn-bpfw-evens-fragment-list
  (implies (fn-bpfw-fragment-listp xs)
           (fn-bpfw-fragment-listp (fn-bpfw-evens xs)))
  :hints (("Goal" :induct (fn-bpfw-evens xs)
           :in-theory (disable fn-bpfw-fragmentp))))

(defthm fn-bpfw-merge-fragment-list
  (implies (and (fn-bpfw-fragment-listp a) (fn-bpfw-fragment-listp b))
           (fn-bpfw-fragment-listp (fn-bpfw-merge a b)))
  :hints (("Goal" :induct (fn-bpfw-merge a b)
           :in-theory (disable fn-bpfw-fragmentp))))

(defun fn-bpfw-sort (fs)
  (declare (xargs :guard (fn-bpfw-fragment-listp fs)
                  :measure (len fs)
                  :verify-guards nil))
  (if (and (consp fs) (consp (cdr fs)))
      (fn-bpfw-merge (fn-bpfw-sort (fn-bpfw-evens fs))
                     (fn-bpfw-sort (fn-bpfw-evens (cdr fs))))
    fs))

(defthm fn-bpfw-sort-fragment-list
  (implies (fn-bpfw-fragment-listp fs)
           (fn-bpfw-fragment-listp (fn-bpfw-sort fs)))
  :hints (("Goal" :induct (fn-bpfw-sort fs)
           :in-theory (disable fn-bpfw-fragmentp))))

(verify-guards fn-bpfw-sort)

; Sorting keeps every cell.
(defthm fn-bpfw-cell-at-of-merge
  (equal (fn-bpf-cell-at (fn-bpfw-merge a b) i)
         (fn-bpf-merge-cell (fn-bpf-cell-at a i) (fn-bpf-cell-at b i))))

(defthm fn-bpfw-cell-at-of-evens
  (equal (fn-bpf-merge-cell (fn-bpf-cell-at (fn-bpfw-evens xs) i)
                            (fn-bpf-cell-at (fn-bpfw-evens (cdr xs)) i))
         (fn-bpf-cell-at xs i))
  :hints (("Goal" :induct (fn-bpfw-evens xs))))

(defthm fn-bpfw-cell-at-of-sort
  (equal (fn-bpf-cell-at (fn-bpfw-sort fs) i)
         (fn-bpf-cell-at fs i))
  :hints (("Goal" :induct (fn-bpfw-sort fs))))

(defthm fn-bpfw-canvas-of-sort
  (equal (fn-bpf-canvas (fn-bpfw-sort fs) from n)
         (fn-bpf-canvas fs from n))
  :hints (("Goal" :induct (fn-bpf-canvas fs from n))))

; Sortedness, stated as a lower bound on everything after each element.
(defun fn-bpfw-all-at-least (fs k)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (and (<= k (nfix (fn-bpf-offset (car fs))))
           (fn-bpfw-all-at-least (cdr fs) k))
    t))

(defun fn-bpfw-sortedp (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (and (fn-bpfw-all-at-least (cdr fs) (nfix (fn-bpf-offset (car fs))))
           (fn-bpfw-sortedp (cdr fs)))
    t))

(local
 (defthm fn-bpfw-all-at-least-weakens
   (implies (and (fn-bpfw-all-at-least fs k2) (<= k1 k2))
            (fn-bpfw-all-at-least fs k1))))

(defthm fn-bpfw-all-at-least-of-merge
  (equal (fn-bpfw-all-at-least (fn-bpfw-merge a b) k)
         (and (fn-bpfw-all-at-least a k) (fn-bpfw-all-at-least b k)))
  :hints (("Goal" :induct (fn-bpfw-merge a b)
           :in-theory (disable fn-bpfw-fragment-listp fn-bpfw-fragmentp
                               fn-bpfw-all-at-least-weakens))))

(local
 (defthm fn-bpfw-sorted-at-least-its-head
   (implies (and (fn-bpfw-sortedp b) (consp b)
                 (<= k (nfix (fn-bpf-offset (car b)))))
            (fn-bpfw-all-at-least b k))
   :hints (("Goal" :expand ((fn-bpfw-sortedp b) (fn-bpfw-all-at-least b k))
            :do-not-induct t))))

(defthm fn-bpfw-sortedp-of-merge
  (implies (and (fn-bpfw-sortedp a) (fn-bpfw-sortedp b)
                (fn-bpfw-fragment-listp a) (fn-bpfw-fragment-listp b))
           (fn-bpfw-sortedp (fn-bpfw-merge a b)))
  :hints (("Goal" :induct (fn-bpfw-merge a b)
           :do-not '(generalize fertilize)
           :in-theory (disable fn-bpfw-all-at-least-weakens fn-bpfw-fragmentp
                               fn-bpfw-all-at-least-of-merge))
          ("Subgoal *1/3" :expand ((fn-bpfw-merge a b) (fn-bpfw-sortedp a)
                                   (fn-bpfw-sortedp b)))
          ("Subgoal *1/4" :expand ((fn-bpfw-merge a b) (fn-bpfw-sortedp a)
                                   (fn-bpfw-sortedp b)))))

(defthm fn-bpfw-sortedp-of-sort
  (implies (fn-bpfw-fragment-listp fs)
           (fn-bpfw-sortedp (fn-bpfw-sort fs))))

; -----------------------------------------------------------------------------
; The sweep
;
; ACTIVE is a list of byte lists: the unconsumed suffix, at the current
; position, of every extent admitted so far that still covers it.  QUEUE is
; the sorted fragments not yet admitted.  At position I the sweep admits
; every queued fragment starting at or before I, emits the merge of the
; active heads, and advances every active suffix by one octet, dropping the
; exhausted ones.  Each octet of each fragment is touched once.

(defun fn-bpfw-admit (active queue i)
  (declare (xargs :guard (and (true-list-listp active)
                              (fn-bpfw-fragment-listp queue)
                              (natp i))))
  (if (and (consp queue) (<= (fn-bpf-offset (car queue)) i))
      (fn-bpfw-admit (cons (nthcdr (- i (fn-bpf-offset (car queue)))
                                   (fn-bpf-bytes (car queue)))
                           active)
                     (cdr queue) i)
    (mv active queue)))

(defun fn-bpfw-head-cell (active)
  (declare (xargs :guard (true-list-listp active)))
  (if (consp active)
      (fn-bpf-merge-cell (if (consp (car active)) (car (car active)) :gap)
                         (fn-bpfw-head-cell (cdr active)))
    :gap))

(defun fn-bpfw-advance (active)
  (declare (xargs :guard (true-list-listp active)))
  (if (consp active)
      (if (consp (cdr (car active)))
          (cons (cdr (car active)) (fn-bpfw-advance (cdr active)))
        (fn-bpfw-advance (cdr active)))
    nil))

(local
 (defthm fn-bpfw-true-listp-of-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

(defthm fn-bpfw-admit-true-list-list
  (implies (and (true-list-listp active) (fn-bpfw-fragment-listp queue)
                (natp i))
           (and (true-list-listp (mv-nth 0 (fn-bpfw-admit active queue i)))
                (fn-bpfw-fragment-listp
                 (mv-nth 1 (fn-bpfw-admit active queue i)))))
  :hints (("Goal" :induct (fn-bpfw-admit active queue i)
           :in-theory (disable fn-bpfw-fragmentp))))

(defthm fn-bpfw-admit-queue-fragment-list
  (implies (fn-bpfw-fragment-listp queue)
           (fn-bpfw-fragment-listp (mv-nth 1 (fn-bpfw-admit active queue i))))
  :hints (("Goal" :induct (fn-bpfw-admit active queue i))))

(defthm fn-bpfw-advance-true-list-list
  (implies (true-list-listp active)
           (true-list-listp (fn-bpfw-advance active))))

; The logical sweep (the one the proofs walk) and the tail-recursive one the
; executable calls: a 10 MiB canvas must not be a 10 MiB-deep stack.
(defun fn-bpfw-sweep (active queue i n)
  (declare (xargs :guard (and (true-list-listp active)
                              (fn-bpfw-fragment-listp queue)
                              (natp i) (natp n))
                  :measure (nfix n)))
  (if (zp n)
      nil
    (mv-let (active queue) (fn-bpfw-admit active queue i)
      (cons (fn-bpfw-head-cell active)
            (fn-bpfw-sweep (fn-bpfw-advance active) queue (+ 1 i) (- n 1))))))

(defun fn-bpfw-sweep-acc (active queue i n acc)
  (declare (xargs :guard (and (true-list-listp active)
                              (fn-bpfw-fragment-listp queue)
                              (natp i) (natp n) (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      (reverse acc)
    (mv-let (active queue) (fn-bpfw-admit active queue i)
      (fn-bpfw-sweep-acc (fn-bpfw-advance active) queue (+ 1 i) (- n 1)
                         (cons (fn-bpfw-head-cell active) acc)))))

(defthm fn-bpfw-sweep-acc-is-sweep
  (implies (true-listp acc)
           (equal (fn-bpfw-sweep-acc active queue i n acc)
                  (revappend acc (fn-bpfw-sweep active queue i n)))))

; -----------------------------------------------------------------------------
; What the active suffixes mean

; The merge of every active suffix at distance D from the current position.
(defun fn-bpfw-active-cell (active d)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp active)
      (fn-bpf-merge-cell (if (< (nfix d) (len (car active)))
                             (nth d (car active))
                           :gap)
                         (fn-bpfw-active-cell (cdr active) d))
    :gap))

(defthm fn-bpfw-head-cell-is-active-cell
  (equal (fn-bpfw-head-cell active) (fn-bpfw-active-cell active 0)))

(defthm fn-bpfw-active-cell-of-advance
  (implies (natp d)
           (equal (fn-bpfw-active-cell (fn-bpfw-advance active) d)
                  (fn-bpfw-active-cell active (+ 1 d)))))

(local
 (defthm fn-bpfw-nth-of-nthcdr
   (implies (and (natp k) (natp d))
            (equal (nth d (nthcdr k xs)) (nth (+ k d) xs)))))

(local
 (defthm fn-bpfw-nthcdr-of-nil
   (equal (nthcdr n nil) nil)))

(local
 (defthm fn-bpfw-len-of-nthcdr
   (implies (natp k)
            (equal (len (nthcdr k xs))
                   (if (<= k (len xs)) (- (len xs) k) 0)))
   :hints (("Goal" :induct (nthcdr k xs)))))

; An admitted fragment's suffix at position I carries, at distance J - I,
; exactly the fragment's own cell at J.
(local
 (defthm fn-bpfw-admitted-suffix-cell
   (implies (and (fn-bpfw-fragmentp f)
                 (natp i) (natp j) (<= i j)
                 (<= (fn-bpf-offset f) i))
            (equal (if (< (- j i)
                          (len (nthcdr (- i (fn-bpf-offset f)) (fn-bpf-bytes f))))
                       (nth (- j i)
                            (nthcdr (- i (fn-bpf-offset f)) (fn-bpf-bytes f)))
                     :gap)
                   (fn-bpf-cell-of f j)))
   :hints (("Goal" :cases ((<= (- i (fn-bpf-offset f))
                               (len (fn-bpf-bytes f))))))))

; Admission moves an extent from the queue to the active list without
; changing any cell at or after the current position.
(defthm fn-bpfw-admit-keeps-cells
  (implies (and (fn-bpfw-fragment-listp queue)
                (natp i) (natp j) (<= i j))
           (equal (fn-bpf-merge-cell
                   (fn-bpfw-active-cell
                    (mv-nth 0 (fn-bpfw-admit active queue i)) (- j i))
                   (fn-bpf-cell-at
                    (mv-nth 1 (fn-bpfw-admit active queue i)) j))
                  (fn-bpf-merge-cell (fn-bpfw-active-cell active (- j i))
                                     (fn-bpf-cell-at queue j))))
  :hints (("Goal" :induct (fn-bpfw-admit active queue i))
          ("Subgoal *1/1" :use ((:instance fn-bpfw-admitted-suffix-cell
                                           (f (car queue))))
           :in-theory (disable fn-bpfw-admitted-suffix-cell))))

; After admission at I, nothing queued starts at or before I.
(defthm fn-bpfw-admit-leaves-later-queue
  (implies (and (fn-bpfw-sortedp queue) (fn-bpfw-fragment-listp queue)
                (natp i))
           (and (fn-bpfw-sortedp (mv-nth 1 (fn-bpfw-admit active queue i)))
                (fn-bpfw-all-at-least (mv-nth 1 (fn-bpfw-admit active queue i))
                                      (+ 1 i)))))

(defthm fn-bpfw-cell-at-before-every-offset
  (implies (and (fn-bpfw-all-at-least queue (+ 1 i))
                (fn-bpfw-fragment-listp queue)
                (natp i))
           (equal (fn-bpf-cell-at queue i) :gap)))

; The canvas the sweep promises: at each position J from I, the merge of the
; active suffixes (taken at I) and the queue.
(defun fn-bpfw-view (active base queue j n)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp n)
      nil
    (cons (fn-bpf-merge-cell (fn-bpfw-active-cell active (- j base))
                             (fn-bpf-cell-at queue j))
          (fn-bpfw-view active base queue (+ 1 j) (- n 1)))))

(defthm fn-bpfw-view-of-advance
  (implies (and (natp base) (natp j) (< base j))
           (equal (fn-bpfw-view (fn-bpfw-advance active) (+ 1 base) queue j n)
                  (fn-bpfw-view active base queue j n)))
  :hints (("Goal" :induct (fn-bpfw-view active base queue j n))
          ("Subgoal *1/2" :use ((:instance fn-bpfw-active-cell-of-advance
                                           (d (+ -1 (- base) j))))
           :in-theory (disable fn-bpfw-active-cell-of-advance))))

(defthm fn-bpfw-view-of-admit
  (implies (and (fn-bpfw-fragment-listp queue)
                (natp i) (natp j) (<= i j))
           (equal (fn-bpfw-view (mv-nth 0 (fn-bpfw-admit active queue i)) i
                                (mv-nth 1 (fn-bpfw-admit active queue i)) j n)
                  (fn-bpfw-view active i queue j n)))
  :hints (("Goal" :induct (fn-bpfw-view active i queue j n)
           :in-theory (disable fn-bpfw-admit-keeps-cells))
          ("Subgoal *1/2" :use ((:instance fn-bpfw-admit-keeps-cells)))))

(defthm fn-bpfw-sweep-is-view
  (implies (and (fn-bpfw-sortedp queue) (fn-bpfw-fragment-listp queue)
                (natp i))
           (equal (fn-bpfw-sweep active queue i n)
                  (fn-bpfw-view active i queue i n)))
  :hints (("Goal" :induct (fn-bpfw-sweep active queue i n)
           :expand ((fn-bpfw-view active i queue i n)))
          ("Subgoal *1/2"
           :use ((:instance fn-bpfw-admit-keeps-cells (j i))
                 (:instance fn-bpfw-view-of-admit (j (+ 1 i)) (n (- n 1)))
                 (:instance fn-bpfw-view-of-advance
                            (active (mv-nth 0 (fn-bpfw-admit active queue i)))
                            (queue (mv-nth 1 (fn-bpfw-admit active queue i)))
                            (base i) (j (+ 1 i)) (n (- n 1)))
                 (:instance fn-bpfw-cell-at-before-every-offset
                            (queue (mv-nth 1 (fn-bpfw-admit active queue i)))))
           :in-theory (disable fn-bpfw-admit-keeps-cells fn-bpfw-view-of-admit
                               fn-bpfw-view-of-advance
                               fn-bpfw-cell-at-before-every-offset))))

(defthm fn-bpfw-view-from-nothing-is-canvas
  (equal (fn-bpfw-view nil base queue j n)
         (fn-bpf-canvas queue j n)))

; -----------------------------------------------------------------------------
; The executed reassembler

(defun fn-bpfw-reassemble (fs total)
  (declare (xargs :guard t))
  (if (not (fn-bpfw-inputsp fs total))
      (list :invalid :bounds)
    (fn-bpfw-outcome (fn-bpfw-sweep-acc nil (fn-bpfw-sort fs) 0 total nil))))

(defthm fn-bpfw-sweep-of-sort-is-canvas
  (implies (and (fn-bpfw-fragment-listp fs) (natp total))
           (equal (fn-bpfw-sweep nil (fn-bpfw-sort fs) 0 total)
                  (fn-bpf-canvas fs 0 total)))
  :hints (("Goal" :use ((:instance fn-bpfw-sweep-is-view
                                   (active nil) (queue (fn-bpfw-sort fs))
                                   (i 0) (n total)))
           :in-theory (disable fn-bpfw-sweep-is-view fn-bpfw-sweep
                               fn-bpfw-sort))))

; Keystone: the executed reassembler is the uncapped reference, for every
; fragment list and total.
(defthm fn-bpfw-reassemble-is-spec
  (equal (fn-bpfw-reassemble fs total)
         (fn-bpfw-spec fs total))
  :hints (("Goal" :in-theory (disable fn-bpfw-sweep fn-bpfw-sort fn-bpf-canvas
                                      fn-bpfw-outcome fn-bpfw-sweep-acc-is-sweep)
           :use ((:instance fn-bpfw-sweep-acc-is-sweep
                            (active nil) (queue (fn-bpfw-sort fs))
                            (i 0) (n total) (acc nil))))))

(in-theory (disable fn-bpfw-reassemble))

; Keystone: a family whose canvas is an octet list reassembles to exactly
; that list.  The sender's plan (bp-fragment-send,
; fn-bpfs-plan-fragments-reassemble-exactly) establishes that premise for
; every payload length and fragment count.
(local
 (defthm fn-bpfw-no-marker-in-octets
   (implies (and (fn-cbor-octet-listp cells)
                 (or (equal marker :gap) (equal marker :conflict)))
            (equal (fn-bpf-first-index cells from marker) nil))))

(defthm fn-bpfw-exact-canvas-reassembles
  (implies (and (fn-bpfw-inputsp fs total)
                (fn-cbor-octet-listp (fn-bpf-canvas fs 0 total)))
           (equal (fn-bpfw-reassemble fs total)
                  (list :ok (fn-bpf-canvas fs 0 total))))
  :hints (("Goal" :in-theory (disable fn-bpfw-inputsp fn-bpf-canvas
                                      fn-bpfw-reassemble))))

; -----------------------------------------------------------------------------
; The shape of a success, for the node's family plan (bp-node-fragment-family)

(local
 (defthm fn-bpfw-uncovered-cell-is-gap
   (implies (not (fn-bpf-coveredp fs i))
            (equal (fn-bpf-cell-at fs i) :gap))
   :hints (("Goal" :induct (fn-bpf-cell-at fs i)
            :in-theory (enable fn-bpf-merge-cell)))))

(defthm fn-bpfw-spec-is-never-ready
  (not (equal (car (fn-bpfw-spec fs total)) :ready)))

(defthm fn-bpfw-spec-true-listp
  (true-listp (fn-bpfw-spec fs total)))

(defthm fn-bpfw-spec-ok-shape
  (implies (equal (fn-bpf-result-tag (fn-bpfw-spec fs total)) :ok)
           (and (fn-bpfw-inputsp fs total)
                (equal (fn-bpf-result-bytes (fn-bpfw-spec fs total))
                       (fn-bpf-canvas fs 0 total))
                (equal (fn-bpf-first-index (fn-bpf-canvas fs 0 total)
                                           0 :conflict)
                       nil)
                (equal (fn-bpf-first-index (fn-bpf-canvas fs 0 total) 0 :gap)
                       nil))))

(defthm fn-bpfw-spec-ok-covers-zero
  (implies (equal (fn-bpf-result-tag (fn-bpfw-spec fs total)) :ok)
           (and (fn-bpfw-fragment-listp fs)
                (fn-bpf-coveredp fs 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpfw-spec-ok-shape)
                 (:instance fn-bpfw-uncovered-cell-is-gap (i 0)))
           :expand ((fn-bpf-canvas fs 0 total)
                    (fn-bpf-first-index (cons (fn-bpf-cell-at fs 0)
                                              (fn-bpf-canvas fs 1 (+ -1 total)))
                                        0 :gap))
           :in-theory (disable fn-bpfw-spec-ok-shape fn-bpfw-spec
                               fn-bpfw-uncovered-cell-is-gap))))
