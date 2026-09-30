; fn: the catalog's number index -- the constant-time lookup by (group .
; number) and the ordered, clamped range walk OVER needs (wave 5, lane
; index-stobjs, 2026-09-26; the gpt-6 consolidation review section 6:
; "ordered group-number indexes for bounded ranges").
;
; The catalog (books/catalog.lisp) already executes `fn-cat-group-number'
; as one probe of its (group . number) hash table, and `fn-cat-group-next'
; as one probe of its group table.  What a served reader needs is the row a
; number names AT ITS VERSION, and the rows of a number range at its
; version; the specification is the walk of the visible rows
; (`fn-cat-view-number-find', books/catalog-view.lisp: newest first, every
; row visited).  The walk and the column agree only when a number is bound
; by at most one row.  The catalog's commit assigns each group's next
; number (one past the group's high), so no number is ever bound twice,
; but the generic's recognizer (`fn-cat-p' = `fn-cat-rowsp') does not say
; so.  This book states it as an invariant over the logical list,
; `fn-cnx-freshp' (every row's number in a group exceeds every earlier
; row's number there), proves it established by the creator and preserved
; by every export under its guard (commit, withdraw, redecide, clear: the
; four writers), and under it:
;
;   KEYSTONE fn-cnx-view-seq-is-walk: `fn-cnx-view-seq' (one probe of the
;     number table, one row read, one visibility test) equals the walk
;     `fn-cat-view-number-find' from the count;
;   KEYSTONE fn-cnx-view-range-is-walk: `fn-cnx-view-range' (the numbers
;     LOW .. min(HIGH, next - 1), one probe each, ascending) equals the
;     walk's range over LOW .. HIGH unclamped: a number past the group's
;     high names no row, so the clamp drops nothing, and an OVER 1-4294967295
;     costs the group's rows, not four billion probes.
;
; The preservation lemmas are stated over the logical side's list
; functions (`fn-cat$a-commit', ...), with no stobj, so that the invariant
; can move into the catalog's recognizer (fn-cat$ap) should its owner
; choose to (the LANEDUMP request to catalog-slice); then the hypothesis
; disappears from the keystones.  No skip-proofs.

(in-package "ACL2")
(include-book "catalog-view")
(include-book "catalog-number-read")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(local (in-theory (disable fn-held-number-in)))

; -----------------------------------------------------------------------------
; The invariant: a row's number in each of its groups exceeds every number
; the rows after it... stated front to back: every LATER row's number in a
; group this row is numbered in is absent or larger.

; Every row of REST is unnumbered in GROUP or numbered above B.
(defun fn-cnx-above-p (group b rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (and (let ((x (fn-held-number-in group (car rest))))
             (or (null x) (< (nfix b) (nfix x))))
           (fn-cnx-above-p group b (cdr rest)))
    t))

; For each key of KEYS (the row's numbers alist), the row's number there
; is absent or every row of REST is above it.
(defun fn-cnx-row-below-p (keys h rest)
  (declare (xargs :guard t))
  (if (consp keys)
      (and (or (not (consp (car keys)))
               (let ((b (fn-held-number-in (car (car keys)) h)))
                 (or (null b) (fn-cnx-above-p (car (car keys)) b rest))))
           (fn-cnx-row-below-p (cdr keys) h rest))
    t))

(defun fn-cnx-freshp (c)
  (declare (xargs :guard t))
  (if (consp c)
      (and (fn-cnx-row-below-p (fn-held-numbers (car c)) (car c) (cdr c))
           (fn-cnx-freshp (cdr c)))
    t))

; -----------------------------------------------------------------------------
; Uniqueness: under the invariant, a number is bound by at most one row, so
; the first row binding it (the number table's answer) is the only one.

(local
 (defthm fn-cnx-assoc-consp
   (implies (fn-cat-assoc g keys)
            (and (consp (fn-cat-assoc g keys))
                 (equal (car (fn-cat-assoc g keys)) g)))))

(local
 (defthm fn-cnx-row-below-gives-above
   (implies (and (fn-cnx-row-below-p keys h rest)
                 (fn-cat-assoc g keys)
                 (fn-held-number-in g h))
            (fn-cnx-above-p g (fn-held-number-in g h) rest))))

(local
 (defthm fn-cnx-number-in-bound-has-key
   (implies (fn-held-number-in g h)
            (fn-cat-assoc g (fn-held-numbers h)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cnx-above-nth
   (implies (and (fn-cnx-above-p g b rest) (natp j) (< j (len rest))
                 (fn-held-number-in g (nth j rest)))
            (not (equal (fn-held-number-in g (nth j rest)) b)))))

(local
 (defthm fn-cnx-number-seq-shift-gen
   (implies (and (natp i) (natp j))
            (equal (fn-cat-number-seq g n c (+ i j))
                   (let ((r (fn-cat-number-seq g n c j)))
                     (and r (+ i r)))))
   :hints (("Goal" :induct (fn-cat-number-seq g n c j)))))

(local
 (defthm fn-cnx-number-seq-shift
   (implies (and (natp i) (syntaxp (not (equal i ''0))))
            (equal (fn-cat-number-seq g n c i)
                   (let ((r (fn-cat-number-seq g n c 0)))
                     (and r (+ i r)))))
   :hints (("Goal" :use ((:instance fn-cnx-number-seq-shift-gen (j 0)))
            :in-theory (disable fn-cnx-number-seq-shift-gen)))))

(local
 (defthm fn-cnx-number-seq-natp
   (implies (fn-cat-number-seq g n c 0)
            (and (natp (fn-cat-number-seq g n c 0))
                 (< (fn-cat-number-seq g n c 0) (len c))))
   :rule-classes nil))

(local
 (defthm fn-cnx-number-seq-type
   (implies (natp i)
            (or (null (fn-cat-number-seq g n c i))
                (natp (fn-cat-number-seq g n c i))))
   :rule-classes :type-prescription))

(local
 (defthm fn-cnx-nth-of-1+
   (implies (natp r)
            (equal (nth (+ 1 r) c) (nth r (cdr c))))))

(local
 (defthm fn-cnx-number-seq-binds
   (implies (fn-cat-number-seq g n c 0)
            (equal (fn-held-number-in g (nth (fn-cat-number-seq g n c 0) c)) n))
   :rule-classes nil
   :hints (("Goal" :induct (len c) :expand ((fn-cat-number-seq g n c 0))))))

(local
 (defthm fn-cnx-fresh-car-not-rebound
   (implies (and (fn-cnx-freshp c) (consp c) (natp k) (< k (len (cdr c)))
                 (fn-held-number-in g (car c)))
            (not (equal (fn-held-number-in g (nth k (cdr c)))
                        (fn-held-number-in g (car c)))))
   :hints (("Goal" :expand ((fn-cnx-freshp c))
            :use ((:instance fn-cnx-above-nth (b (fn-held-number-in g (car c)))
                             (rest (cdr c)) (j k))
                  (:instance fn-cnx-row-below-gives-above
                             (keys (fn-held-numbers (car c))) (h (car c)) (rest (cdr c)))
                  (:instance fn-cnx-number-in-bound-has-key (h (car c))))
            :in-theory (disable fn-cnx-above-nth fn-cnx-row-below-gives-above
                                fn-cnx-number-in-bound-has-key)))))

(defthm fn-cnx-number-seq-unique
  (implies (and (fn-cnx-freshp c) (natp j) (< j (len c)) n
                (equal (fn-held-number-in g (nth j c)) n))
           (equal (fn-cat-number-seq g n c 0) j))
  :hints (("Goal" :induct (nth j c)
           :expand ((fn-cat-number-seq g n c 0)))))

; -----------------------------------------------------------------------------
; The invariant through the four writers, over the logical side.

(local
 (defthm fn-cnx-high-natp
   (natp (fn-cat-group-high g c))
   :rule-classes :type-prescription))

(local
 (defthm fn-cnx-high-bounds-member
   (implies (member-equal r c)
            (<= (nfix (fn-held-number-in g r)) (fn-cat-group-high g c)))
   :rule-classes :linear))

(local
 (defthm fn-cnx-number-seq-above-high
   (implies (and (natp n) (< (fn-cat-group-high g c) n))
            (equal (fn-cat-number-seq g n c i) nil))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cnx-assoc-of-assign-numbers
   (equal (fn-cat-assoc g (fn-cat-assign-numbers groups c))
          (if (member-equal g groups)
              (cons g (+ 1 (fn-cat-group-high g c)))
            nil))))

(local
 (defthm fn-cnx-number-in-of-assign
   (equal (fn-held-number-in g (fn-cat-assign h c))
          (if (member-equal g (fn-record-groups h))
              (+ 1 (fn-cat-group-high g c))
            nil))
   :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers fn-held-number-in)))))

(local
 (defthm fn-cnx-subsetp-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local
 (defthm fn-cnx-subsetp-refl
   (subsetp-equal x x)))

(local
 (defthm fn-cnx-row-below-of-nil
   (fn-cnx-row-below-p keys h nil)))

(local
 (defthm fn-cnx-above-p-of-append
   (equal (fn-cnx-above-p g b (append rest (list x)))
          (and (fn-cnx-above-p g b rest)
               (let ((y (fn-held-number-in g x)))
                 (or (null y) (< (nfix b) (nfix y))))))))

(local
 (defthm fn-cnx-above-of-append-assign
   (implies (and (member-equal h0 full)
                 (fn-cnx-above-p g (fn-held-number-in g h0) rest))
            (fn-cnx-above-p g (fn-held-number-in g h0)
                            (append rest (list (fn-cat-assign h full)))))
   :hints (("Goal" :use ((:instance fn-cnx-high-bounds-member (r h0) (c full)))
            :in-theory (disable fn-cat-assign fn-cnx-high-bounds-member)))))

(local
 (defthm fn-cnx-row-below-of-append-assign
   (implies (and (member-equal h0 full)
                 (fn-cnx-row-below-p keys h0 rest))
            (fn-cnx-row-below-p keys h0 (append rest (list (fn-cat-assign h full)))))
   :hints (("Goal" :induct (fn-cnx-row-below-p keys h0 rest)
            :in-theory (disable fn-cat-assign fn-cnx-above-p-of-append)))))

(local
 (defthm fn-cnx-freshp-of-append-assign
   (implies (and (subsetp-equal c full) (fn-cnx-freshp c))
            (fn-cnx-freshp (append c (list (fn-cat-assign h full)))))
   :hints (("Goal" :in-theory (disable fn-cat-assign)))))

(defthm fn-cnx-freshp-of-commit
  (implies (fn-cnx-freshp c)
           (fn-cnx-freshp (fn-cat$a-commit h c)))
  :hints (("Goal" :use ((:instance fn-cnx-freshp-of-append-assign (full c)))
           :in-theory (disable fn-cat-assign fn-cnx-freshp-of-append-assign))))

; A row replaced by one with the same numbers.
(local
 (defthm fn-cnx-above-p-of-update-nth
   (implies (and (natp k) (< k (len rest))
                 (equal (fn-held-numbers x) (fn-held-numbers (nth k rest))))
            (equal (fn-cnx-above-p g b (update-nth k x rest))
                   (fn-cnx-above-p g b rest)))
   :hints (("Goal" :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cnx-row-below-of-update-nth
   (implies (and (natp k) (< k (len rest))
                 (equal (fn-held-numbers x) (fn-held-numbers (nth k rest))))
            (equal (fn-cnx-row-below-p keys h (update-nth k x rest))
                   (fn-cnx-row-below-p keys h rest)))))

(local
 (defthm fn-cnx-row-below-same-numbers-gen
   (implies (equal (fn-held-numbers x) (fn-held-numbers h))
            (equal (fn-cnx-row-below-p keys x rest)
                   (fn-cnx-row-below-p keys h rest)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cnx-row-below-p keys x rest)
            :in-theory (enable fn-held-number-in)))))

(local
 (defthm fn-cnx-row-below-same-numbers
   (implies (equal (fn-held-numbers x) (fn-held-numbers h))
            (equal (fn-cnx-row-below-p (fn-held-numbers x) x rest)
                   (fn-cnx-row-below-p (fn-held-numbers h) h rest)))
   :hints (("Goal" :use ((:instance fn-cnx-row-below-same-numbers-gen (keys (fn-held-numbers h))))))))

(local
 (defthm fn-cnx-freshp-of-update-nth
   (implies (and (natp k) (< k (len c))
                 (equal (fn-held-numbers x) (fn-held-numbers (nth k c))))
            (equal (fn-cnx-freshp (update-nth k x c))
                   (fn-cnx-freshp c)))
   :hints (("Goal" :induct (update-nth k x c)))))

(local
 (defthm fn-cnx-numbers-of-with
   (and (equal (fn-held-numbers (fn-held-with-withdrawn h w)) (fn-held-numbers h))
        (equal (fn-held-numbers (fn-held-with-context h ctx)) (fn-held-numbers h)))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-held-with-context)))))

(defthm fn-cnx-freshp-of-withdraw
  (implies (and (fn-cnx-freshp c) (natp target))
           (fn-cnx-freshp (fn-cat$a-withdraw target by c)))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(defthm fn-cnx-freshp-of-redecide
  (implies (and (fn-cnx-freshp c) (natp seq) (< seq (len c)))
           (fn-cnx-freshp (fn-cat$a-redecide seq context c))))

(defthm fn-cnx-freshp-of-create-and-clear
  (and (fn-cnx-freshp (create-fn-cat$a))
       (fn-cnx-freshp (fn-cat$a-clear c))))

; The same over the generic's exports (what a caller threading fn-cat uses).
(defthm fn-cnx-freshp-of-cat-writers
  (and (implies (fn-cnx-freshp fn-cat)
                (fn-cnx-freshp (fn-cat-commit h fn-cat)))
       (implies (and (fn-cnx-freshp fn-cat) (natp target))
                (fn-cnx-freshp (fn-cat-withdraw target by fn-cat)))
       (implies (and (fn-cnx-freshp fn-cat) (natp seq) (< seq (fn-cat-count fn-cat)))
                (fn-cnx-freshp (fn-cat-redecide seq context fn-cat)))
       (fn-cnx-freshp (fn-cat-clear fn-cat)))
  :hints (("Goal" :use ((:instance fn-cnx-freshp-of-commit (c fn-cat))
                        (:instance fn-cnx-freshp-of-withdraw (c fn-cat))
                        (:instance fn-cnx-freshp-of-redecide (c fn-cat)))
           :in-theory (e/d (fn-cat-withdraw-is-mark)
                           (fn-cnx-freshp-of-commit fn-cnx-freshp-of-withdraw
                                                    fn-cnx-freshp-of-redecide)))))

; -----------------------------------------------------------------------------
; The lookup: one probe, one row read, one visibility test.

; The column's answer below I: the row the number table names, when it
; is below I and visible at V.
(defun-nx fn-cnx-col (group n i v c)
  (let ((s (fn-cat-number-seq group n c 0)))
    (if (and s (< s i) (fn-cat-visiblep s v c)) s nil)))

(local
 (defthm fn-cnx-col-step
   (implies (and (fn-cnx-freshp c) n (natp i) (< 0 i) (<= i (len c)))
            (equal (fn-cnx-col group n i v c)
                   (if (and (fn-cat-visiblep (+ -1 i) v c)
                            (equal n (fn-held-number-in group (nth (+ -1 i) c))))
                       (+ -1 i)
                     (fn-cnx-col group n (+ -1 i) v c))))
   :hints (("Goal" :use ((:instance fn-cnx-number-seq-unique (g group) (j (+ -1 i)))
                         (:instance fn-cnx-number-seq-binds (g group))
                         (:instance fn-cnx-number-seq-natp (g group)))
            :in-theory (disable fn-cnx-number-seq-unique)))))

(local
 (defthm fn-cnx-col-zero
   (equal (fn-cnx-col group n 0 v c) nil)))

(local
 (defthm fn-cnx-walk-is-column
   (implies (and (fn-cnx-freshp fn-cat) n (natp i) (<= i (len fn-cat)))
            (equal (fn-cat-view-number-find group n i v fn-cat)
                   (fn-cnx-col group n i v fn-cat)))
   :hints (("Goal" :induct (fn-cat-view-number-find group n i v fn-cat)
            :in-theory (disable fn-cnx-col)))))

; KEYSTONE.
(defthm fn-cnx-view-seq-is-walk
  (implies (and (fn-cnx-freshp fn-cat) n)
           (equal (fn-cnx-view-seq group n v fn-cat)
                  (fn-cat-view-number-find group n (fn-cat-count fn-cat) v fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cnx-col) (fn-cat-view-number-find fn-cnx-freshp)))))

; -----------------------------------------------------------------------------
; The range: numbers LOW .. TOP ascending, the visible rows they name.

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cnx-range-aux-loop (group k top v fn-cat acc)
  (declare (xargs :stobjs fn-cat :measure (nfix (- (+ 1 (nfix top)) (nfix k))) :guard (and (and (natp k) (natp top) (natp v)) (true-listp acc)) :verify-guards nil))
  (if (and (natp k) (natp top) (<= k top))
      (let ((s (fn-cnx-view-seq group k v fn-cat)))
        (if s
            (fn-cnx-range-aux-loop group (+ 1 k) top v fn-cat (cons s acc))
          (fn-cnx-range-aux-loop group (+ 1 k) top v fn-cat acc)))
    (revappend acc nil)))

(defun fn-cnx-range-aux (group k top v fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (mbe :logic
       (if (and (natp k) (natp top) (<= k top))
           (let ((s (fn-cnx-view-seq group k v fn-cat)))
             (if s
                 (cons s (fn-cnx-range-aux group (+ 1 k) top v fn-cat))
               (fn-cnx-range-aux group (+ 1 k) top v fn-cat)))
         nil)
       :exec (fn-cnx-range-aux-loop group k top v fn-cat nil)))

(local
 (defthm fn-cnx-range-aux-loop-is-revappend
   (equal (fn-cnx-range-aux-loop group k top v fn-cat acc)
          (revappend acc (fn-cnx-range-aux group k top v fn-cat)))
   :hints (("Goal" :induct (fn-cnx-range-aux-loop group k top v fn-cat acc)
                   :in-theory (union-theories '(fn-cnx-range-aux-loop fn-cnx-range-aux revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cnx-range-aux-loop)

(verify-guards fn-cnx-range-aux
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cnx-range-aux)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cnx-range-aux-loop-is-revappend (acc nil))))))


; The served range: clamped to the group's high (next - 1).
(defun fn-cnx-view-range (group low high v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp low) (natp high) (natp v))))
  (if (natp high)
      (fn-cnx-range-aux group low (min high (nfix (- (fn-cat-group-next group fn-cat) 1))) v fn-cat)
    nil))

; The specification: the walk per number over LOW .. HIGH, unclamped.
; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of data with no fixed cap.  The :logic is
; the recursion, unchanged; the :exec is the loop, equal by the lemma below.
; (A specification: host/native/io.lisp names it only in its lookup-count
; list.  Its guard is verified so that the loop is what would run.)
(defun fn-cnx-walk-range-loop (group k top v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (let ((s (fn-cat-view-number-find group k (fn-cat-count fn-cat) v fn-cat)))
        (fn-cnx-walk-range-loop group (+ 1 k) top v fn-cat (if s (cons s acc) acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-cnx-walk-range (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (mbe :logic
       (if (and (natp k) (natp top) (<= k top))
           (let ((s (fn-cat-view-number-find group k (fn-cat-count fn-cat) v fn-cat)))
             (if s
                 (cons s (fn-cnx-walk-range group (+ 1 k) top v fn-cat))
               (fn-cnx-walk-range group (+ 1 k) top v fn-cat)))
         nil)
       :exec (fn-cnx-walk-range-loop group k top v fn-cat nil)))

(defthm fn-cnx-walk-range-loop-is-rev-onto
  (equal (fn-cnx-walk-range-loop group k top v fn-cat acc)
         (fn-ag-rev-onto acc (fn-cnx-walk-range group k top v fn-cat)))
  :hints (("Goal" :induct (fn-cnx-walk-range-loop group k top v fn-cat acc)
                  :in-theory (disable fn-cat-view-number-find))))

(verify-guards fn-cnx-walk-range
  :hints (("Goal" :in-theory (disable fn-cat-view-number-find))))

(local
 (defthm fn-cnx-aux-is-walk-range
   (implies (fn-cnx-freshp fn-cat)
            (equal (fn-cnx-range-aux group k top v fn-cat)
                   (fn-cnx-walk-range group k top v fn-cat)))
   :hints (("Goal" :induct (fn-cnx-walk-range group k top v fn-cat)
            :in-theory (disable fn-cnx-view-seq)))))

(local
 (defthm fn-cnx-walk-above-high
   (implies (and (fn-cnx-freshp fn-cat) (natp k) (< (fn-cat-group-high group fn-cat) k))
            (equal (fn-cat-view-number-find group k (len fn-cat) v fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-cnx-col)))))

(local
 (defthm fn-cnx-walk-above-high-nil
   (implies (and (fn-cnx-freshp fn-cat) (natp k) (< (fn-cat-group-high group fn-cat) k))
            (equal (fn-cnx-walk-range group k top v fn-cat) nil))
   :hints (("Goal" :induct (fn-cnx-walk-range group k top v fn-cat)))))

(local
 (defthm fn-cnx-walk-range-clamp
   (implies (and (fn-cnx-freshp fn-cat) (natp k) (natp top) (natp hi)
                 (<= (fn-cat-group-high group fn-cat) top))
            (equal (fn-cnx-walk-range group k (min hi top) v fn-cat)
                   (fn-cnx-walk-range group k hi v fn-cat)))
   :hints (("Goal" :induct (fn-cnx-walk-range group k hi v fn-cat)
            :in-theory (disable fn-cat-view-number-find fn-cnx-freshp fn-cnx-col
                                fn-cnx-col-step fn-cnx-walk-is-column)))))

; KEYSTONE.
(defthm fn-cnx-view-range-is-walk
  (implies (fn-cnx-freshp fn-cat)
           (equal (fn-cnx-view-range group low high v fn-cat)
                  (fn-cnx-walk-range group low high v fn-cat)))
  :hints (("Goal" :use ((:instance fn-cnx-walk-range-clamp
                                   (k low) (hi high)
                                   (top (fn-cat-group-high group fn-cat)))))))
