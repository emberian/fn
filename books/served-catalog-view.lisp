; fn: a group's summary at a reader's view below the catalog's count, from
; the live table plus the rows that differ (lane scale-latency, PKT-870).
;
; The served GROUP, LISTGROUP and LIST ACTIVE read a group's live summary
; (count, least and greatest live number) at the connection's view V
; (books/served-catalog.lisp fn-scat-group-summary, fn-scat-group-low).  The
; catalog keeps the summary at its count (books/catalog.lisp, sca-join-5),
; which answers exactly when V is the count and no withdrawal is at or past
; V.  A reader's view is the durable view: while a batch is in flight the
; catalog already holds the batch's rows (books/owner-reader-view.lisp, the
; reader view), so under posting load a GROUP reads at a view one batch
; below the count, and the summary fell back to the probe pass over every
; number of the group -- the O(store) GROUP of PKT-870 (100,000 articles:
; 70% of the owner's CPU, POST p50 0.4 s under 16 clients, hbox
; 2026-09-28).
;
; What differs between the view and the table is carried or bounded: a
; number whose row is below V and not withdrawn at or after V is served at V
; exactly when the table has it live.  The others are the numbers of the
; rows V .. count-1 and of the rows withdrawn at a version from V to the
; horizon, which the catalog lists per version (fn-cat-withdrawn-at): X
; below.  So
;
;   count at V = the table's count + the sum over X of (served at V) - (live)
;   least at V = the least of: the least table-live number outside X (a scan
;                up from the table's least), and the least served number of X
;   greatest   = likewise downward from the table's greatest.
;
; The work is the size of X (the rows appended since V -- one batch -- and
; the withdrawals since V) plus the scans past numbers of X and withdrawn
; numbers at the group's two ends; nothing walks the group.
;
; KEYSTONES (no hypothesis beyond the catalog's recognizer):
;   fn-scv-count-is-count-p, fn-scv-first-is-first-p, fn-scv-last-is-last-p:
;   the three answers equal the number-wise count, least and greatest of the
;   numbers served at V (fn-scv-keptp: the probe pass's own test,
;   books/served-catalog.lisp fn-scat-range-keep over fn-cnx-range-aux),
;   over 1 .. TOP for any TOP at least the group's high.
(in-package "ACL2")
(include-book "catalog")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(local (in-theory (disable fn-held-number-in fn-scat-msgid-idp)))

; -----------------------------------------------------------------------------
; The two tests, number-wise.

; Served at V: the probe pass's test (the visible row the number table
; names, a served number, a renderable Message-ID).
(defun fn-scv-keptp (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                            fn-cat-group-number-is-number-seq)))))
  (let ((s (fn-cat-group-number group k fn-cat)))
    (and (natp s) (< s (fn-cat-count fn-cat))
         (fn-cat-visible-at s (nfix v) fn-cat)
         (let ((row (fn-cat-at s fn-cat)))
           (and (fn-cat-row-availablep row)
                (posp k) (<= k *fn-nntp-max-article-number*)
                (fn-scat-msgid-idp (fn-record-msgid row))
                t)))))

; Live in the table (books/catalog.lisp fn-cat-live-numberp), read through
; the exports.
(defun fn-scv-liveq (group k fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                            fn-cat-group-number-is-number-seq)))))
  (let ((s (fn-cat-group-number group k fn-cat)))
    (and (natp s) (< s (fn-cat-count fn-cat))
         (fn-cat-live-rowp group k (fn-cat-at s fn-cat)))))

(defthm fn-scv-liveq-is-live-numberp
  (equal (fn-scv-liveq group k fn-cat) (fn-cat-live-numberp group k fn-cat))
  :hints (("Goal" :in-theory (enable fn-cat-live-numberp))))

; -----------------------------------------------------------------------------
; X: the numbers whose answer at V may differ from the table's.
;
; X is built without a pass over itself: it has no duplicates by
; construction (fn-scv-no-dups-x), and a number is in it exactly when the
; row the number table names for it satisfies a constant-time test
; (fn-scv-in-xp-iff-member).  A number counts through its OWN row only -- the
; row the table names (fn-cat-group-number), the row `keptp' and `liveq'
; read -- so a number held by two rows (the recognizer does not forbid it;
; the commit path never makes it) is one element of X, not two.  The rows
; V .. count-1 contribute their numbers; the rows below V contribute only
; when they are withdrawn at a version from V to the horizon.  A row's
; withdrawn field holds one version, so no row is listed twice.

; K is a number of GROUP held by row S, and the number table names row S for it.
(defun fn-scv-ownp (group k s fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (and (posp k) (equal (fn-cat-group-number group k fn-cat) s) t))

; The numbers in GROUP of the rows S .. N-1.  Every walk below executes as
; a loop (an accumulator, reversed at the end: tools/depth_check.py); the
; :logic is the recursion the proofs read.
(defun fn-scv-new-numbers-loop (group s n fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (and (natp s) (natp n) (true-listp acc))
                  :measure (nfix (- (nfix n) (nfix s)))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                            fn-cat-group-number-is-number-seq)))))
  (if (and (natp s) (natp n) (< s n) (< s (fn-cat-count fn-cat)))
      (let ((k (fn-held-number-in group (fn-cat-at s fn-cat))))
        (fn-scv-new-numbers-loop group (+ 1 s) n fn-cat
                                 (if (fn-scv-ownp group k s fn-cat) (cons k acc) acc)))
    (revappend acc nil)))

(defun fn-scv-new-numbers (group s n fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp s) (natp n))
                  :measure (nfix (- (nfix n) (nfix s)))
                  :verify-guards nil))
  (mbe :logic
       (if (and (natp s) (natp n) (< s n) (< s (fn-cat-count fn-cat)))
           (let ((k (fn-held-number-in group (fn-cat-at s fn-cat)))
                 (rest (fn-scv-new-numbers group (+ 1 s) n fn-cat)))
             (if (fn-scv-ownp group k s fn-cat) (cons k rest) rest))
         nil)
       :exec (fn-scv-new-numbers-loop group s n fn-cat nil)))

(local
 (defthm fn-scv-new-numbers-loop-is-revappend
   (equal (fn-scv-new-numbers-loop group s n fn-cat acc)
          (revappend acc (fn-scv-new-numbers group s n fn-cat)))
   :hints (("Goal" :induct (fn-scv-new-numbers-loop group s n fn-cat acc)))))

(verify-guards fn-scv-new-numbers
  :hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                      fn-cat-group-number-is-number-seq))))

; The numbers in GROUP of the rows SEQS names that lie below V.
(defun fn-scv-seq-numbers-loop (group seqs v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (and (natp v) (true-listp acc))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                            fn-cat-group-number-is-number-seq)))))
  (if (consp seqs)
      (let ((s (car seqs)))
        (fn-scv-seq-numbers-loop
         group (cdr seqs) v fn-cat
         (if (and (natp s) (< s v) (< s (fn-cat-count fn-cat)))
             (let ((k (fn-held-number-in group (fn-cat-at s fn-cat))))
               (if (fn-scv-ownp group k s fn-cat) (cons k acc) acc))
           acc)))
    (revappend acc nil)))

(defun fn-scv-seq-numbers (group seqs v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil))
  (mbe :logic
       (if (consp seqs)
           (let ((rest (fn-scv-seq-numbers group (cdr seqs) v fn-cat))
                 (s (car seqs)))
             (if (and (natp s) (< s v) (< s (fn-cat-count fn-cat)))
                 (let ((k (fn-held-number-in group (fn-cat-at s fn-cat))))
                   (if (fn-scv-ownp group k s fn-cat) (cons k rest) rest))
               rest))
         nil)
       :exec (fn-scv-seq-numbers-loop group seqs v fn-cat nil)))

(local
 (defthm fn-scv-seq-numbers-loop-is-revappend
   (equal (fn-scv-seq-numbers-loop group seqs v fn-cat acc)
          (revappend acc (fn-scv-seq-numbers group seqs v fn-cat)))
   :hints (("Goal" :induct (fn-scv-seq-numbers-loop group seqs v fn-cat acc)))))

(verify-guards fn-scv-seq-numbers
  :hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                      fn-cat-group-number-is-number-seq))))

; The numbers in GROUP of the rows below V withdrawn at a version W .. HZ-1.
(defun fn-scv-withdrawn-numbers-loop (group w hz v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (and (natp w) (natp hz) (natp v) (true-listp acc))
                  :measure (nfix (- (nfix hz) (nfix w)))))
  (if (and (natp w) (natp hz) (< w hz))
      (fn-scv-withdrawn-numbers-loop
       group (+ 1 w) hz v fn-cat
       (revappend (fn-scv-seq-numbers group (fn-cat-withdrawn-at w fn-cat) v fn-cat) acc))
    (revappend acc nil)))

(defun fn-scv-withdrawn-numbers (group w hz v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp w) (natp hz) (natp v))
                  :measure (nfix (- (nfix hz) (nfix w)))
                  :verify-guards nil))
  (mbe :logic
       (if (and (natp w) (natp hz) (< w hz))
           (append (fn-scv-seq-numbers group (fn-cat-withdrawn-at w fn-cat) v fn-cat)
                   (fn-scv-withdrawn-numbers group (+ 1 w) hz v fn-cat))
         nil)
       :exec (fn-scv-withdrawn-numbers-loop group w hz v fn-cat nil)))

(local
 (defthm fn-scv-revappend-revappend
   (equal (revappend (revappend a b) c) (revappend b (append a c)))))

(local
 (defthm fn-scv-withdrawn-numbers-loop-is-revappend
   (equal (fn-scv-withdrawn-numbers-loop group w hz v fn-cat acc)
          (revappend acc (fn-scv-withdrawn-numbers group w hz v fn-cat)))
   :hints (("Goal" :induct (fn-scv-withdrawn-numbers-loop group w hz v fn-cat acc)))))

(verify-guards fn-scv-withdrawn-numbers)

(defun fn-scv-x (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (append (fn-scv-new-numbers group (nfix v) (fn-cat-count fn-cat) fn-cat)
          (fn-scv-withdrawn-numbers group (nfix v) (nfix (fn-cat-horizon fn-cat)) (nfix v)
                                    fn-cat)))

; The constant-time test: the row the table names for K is at or past V, or
; is withdrawn at a version at or past V.
(defun fn-scv-in-xp (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                            fn-cat-group-number-is-number-seq)))))
  (let ((s (fn-cat-group-number group k fn-cat)))
    (and (posp k) (natp s) (< s (fn-cat-count fn-cat))
         (or (<= (nfix v) s)
             (let ((w (fn-held-withdrawn (fn-cat-at s fn-cat))))
               (and (consp w) (<= (nfix v) (nfix (car w))))))
         t)))

; -----------------------------------------------------------------------------
; Outside X the two tests agree.

(local
 (defthm fn-scv-number-seq-binds
   (implies (and (natp i) (fn-cat-number-seq g n c i))
            (and (natp (fn-cat-number-seq g n c i))
                 (<= i (fn-cat-number-seq g n c i))
                 (< (fn-cat-number-seq g n c i) (+ i (len c)))
                 (equal (fn-held-number-in g (nth (- (fn-cat-number-seq g n c i) i) c)) n)))
   :hints (("Goal" :induct (fn-cat-number-seq g n c i)))))

(local
 (defthm fn-scv-withdrawn-below-horizon
   (implies (and (fn-cat-rowsp c) (natp s) (< s (len c))
                 (fn-held-withdrawn (nth s c)))
            (< (car (fn-held-withdrawn (nth s c))) (fn-cat-horizon-of c)))
   :rule-classes :linear
   :hints (("Goal" :induct (nth s c)
            :in-theory (e/d (fn-cat-horizon-of fn-held-withdrawnp) (fn-held-withdrawn))
            :expand ((fn-cat-horizon-of c)))
           ("Subgoal *1/2" :use ((:instance fn-cat-rowp-fields (h (car c)))))
           ("Subgoal *1/1" :use ((:instance fn-cat-rowp-fields (h (car c))))))))

(local
 (defthm fn-scv-withdrawn-natp
   (implies (and (fn-cat-rowsp c) (natp s) (< s (len c))
                 (fn-held-withdrawn (nth s c)))
            (and (consp (fn-held-withdrawn (nth s c)))
                 (natp (car (fn-held-withdrawn (nth s c))))))
   :hints (("Goal" :use ((:instance fn-cat-rowp-fields (h (nth s c))))
            :in-theory (e/d (fn-held-withdrawnp) (fn-cat-rowp-fields fn-held-withdrawn))))))

(local
 (defthm fn-scv-member-append
   (iff (member-equal x (append a b))
        (or (member-equal x a) (member-equal x b)))))

; The new rows.
(local
 (defthm fn-scv-member-new-numbers
   (implies (and (natp a) (natp s) (natp n) (<= a s) (< s n) (< s (len c))
                 (posp k) (equal (fn-held-number-in g (nth s c)) k)
                 (equal (fn-cat-number-seq g k c 0) s))
            (member-equal k (fn-scv-new-numbers g a n c)))
   :hints (("Goal" :induct (fn-scv-new-numbers g a n c)))))

(local
 (defthm fn-scv-member-new-numbers-elim
   (implies (member-equal k (fn-scv-new-numbers g a n c))
            (let ((s (fn-cat-number-seq g k c 0)))
              (and (posp k) (natp s) (<= a s) (< s n) (< s (len c))
                   (equal (fn-held-number-in g (nth s c)) k))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-new-numbers g a n c)))))

(local
 (defthm fn-scv-not-member-new-numbers
   (implies (< (fn-cat-number-seq g k c 0) a)
            (not (member-equal k (fn-scv-new-numbers g a n c))))
   :hints (("Goal" :use fn-scv-member-new-numbers-elim))))

(local
 (defthm fn-scv-no-dups-new-numbers
   (no-duplicatesp-equal (fn-scv-new-numbers g a n c))
   :hints (("Goal" :induct (fn-scv-new-numbers g a n c)))))

; The rows a list of sequence numbers names, below V.
(local
 (defthm fn-scv-member-seq-numbers
   (implies (and (member-equal s seqs) (natp s) (< s v) (< s (len c))
                 (posp k) (equal (fn-held-number-in g (nth s c)) k)
                 (equal (fn-cat-number-seq g k c 0) s))
            (member-equal k (fn-scv-seq-numbers g seqs v c)))))

(local
 (defthm fn-scv-member-seq-numbers-elim
   (implies (member-equal k (fn-scv-seq-numbers g seqs v c))
            (let ((s (fn-cat-number-seq g k c 0)))
              (and (posp k) (natp s) (member-equal s seqs) (< s v) (< s (len c))
                   (equal (fn-held-number-in g (nth s c)) k))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-seq-numbers g seqs v c)))))

(local
 (defthm fn-scv-not-member-seq-numbers
   (implies (not (member-equal (fn-cat-number-seq g k c 0) seqs))
            (not (member-equal k (fn-scv-seq-numbers g seqs v c))))
   :hints (("Goal" :use fn-scv-member-seq-numbers-elim))))

(local
 (defthm fn-scv-no-dups-seq-numbers
   (implies (no-duplicatesp-equal seqs)
            (no-duplicatesp-equal (fn-scv-seq-numbers g seqs v c)))
   :hints (("Goal" :induct (fn-scv-seq-numbers g seqs v c)))))

; The rows withdrawn at one version.
(local
 (defthm fn-scv-member-withdrawn-at-from
   (implies (and (natp i) (natp s) (<= i s) (< s (+ i (len c)))
                 (consp (fn-held-withdrawn (nth (- s i) c))))
            (member-equal s (fn-cat-withdrawn-at-from (car (fn-held-withdrawn (nth (- s i) c)))
                                                      c i)))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)
            :in-theory (enable fn-cat-withdrawn-at-from)))))

(local
 (defthm fn-scv-member-withdrawn-at-from-elim
   (implies (and (natp i) (member-equal s (fn-cat-withdrawn-at-from w c i)))
            (and (natp s) (<= i s) (< s (+ i (len c)))
                 (consp (fn-held-withdrawn (nth (- s i) c)))
                 (equal (car (fn-held-withdrawn (nth (- s i) c))) w)))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)
            :in-theory (enable fn-cat-withdrawn-at-from)))))

(local
 (defthm fn-scv-not-member-withdrawn-at-from
   (implies (and (natp i) (< s i))
            (not (member-equal s (fn-cat-withdrawn-at-from w c i))))
   :hints (("Goal" :use fn-scv-member-withdrawn-at-from-elim))))

(local
 (defthm fn-scv-no-dups-withdrawn-at-from
   (implies (natp i) (no-duplicatesp-equal (fn-cat-withdrawn-at-from w c i)))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)
            :in-theory (enable fn-cat-withdrawn-at-from)))))

; The numbers of the rows below V withdrawn at one version.
(local
 (defthm fn-scv-member-version-numbers-elim
   (implies (member-equal k (fn-scv-seq-numbers g (fn-cat-withdrawn-at-from w c 0) v c))
            (let ((s (fn-cat-number-seq g k c 0)))
              (and (posp k) (natp s) (< s v) (< s (len c))
                   (equal (fn-held-number-in g (nth s c)) k)
                   (consp (fn-held-withdrawn (nth s c)))
                   (equal (car (fn-held-withdrawn (nth s c))) w))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-scv-member-seq-numbers-elim
                                    (seqs (fn-cat-withdrawn-at-from w c 0)))
                         (:instance fn-scv-member-withdrawn-at-from-elim (i 0)
                                    (s (fn-cat-number-seq g k c 0))))))))

; Those of the versions W0 .. HZ-1.
(local
 (defthm fn-scv-member-withdrawn-numbers
   (implies (and (natp w0) (natp w) (natp hz) (<= w0 w) (< w hz)
                 (member-equal k (fn-scv-seq-numbers g (fn-cat-withdrawn-at-from w c 0) v c)))
            (member-equal k (fn-scv-withdrawn-numbers g w0 hz v c)))
   :hints (("Goal" :induct (fn-scv-withdrawn-numbers g w0 hz v c))
           ("Subgoal *1/1" :cases ((equal w w0))))))

(local
 (defthm fn-scv-member-withdrawn-numbers-elim
   (implies (member-equal k (fn-scv-withdrawn-numbers g w0 hz v c))
            (let ((s (fn-cat-number-seq g k c 0)))
              (and (posp k) (natp s) (< s v) (< s (len c))
                   (equal (fn-held-number-in g (nth s c)) k)
                   (consp (fn-held-withdrawn (nth s c)))
                   (natp (car (fn-held-withdrawn (nth s c))))
                   (<= w0 (car (fn-held-withdrawn (nth s c))))
                   (< (car (fn-held-withdrawn (nth s c))) hz))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-withdrawn-numbers g w0 hz v c))
           ("Subgoal *1/2" :use ((:instance fn-scv-member-version-numbers-elim (w w0))))
           ("Subgoal *1/1" :use ((:instance fn-scv-member-version-numbers-elim (w w0)))))))

(local
 (defthm fn-scv-not-member-later-versions
   (implies (and (natp w0) (natp hz)
                 (member-equal k (fn-scv-seq-numbers g (fn-cat-withdrawn-at-from w0 c 0) v c)))
            (not (member-equal k (fn-scv-withdrawn-numbers g (+ 1 w0) hz v c))))
   :hints (("Goal" :use ((:instance fn-scv-member-version-numbers-elim (w w0))
                         (:instance fn-scv-member-withdrawn-numbers-elim (w0 (+ 1 w0))))))))

; Two lists with no number in common append to a list without duplicates.
(local
 (defun fn-scv-isect-witness (a b)
   (declare (xargs :verify-guards nil))
   (cond ((atom a) nil)
         ((member-equal (car a) b) (car a))
         (t (fn-scv-isect-witness (cdr a) b)))))

(local
 (defthm fn-scv-isect-witness-works
   (implies (intersectp-equal a b)
            (and (member-equal (fn-scv-isect-witness a b) a)
                 (member-equal (fn-scv-isect-witness a b) b)))))

(local
 (defthm fn-scv-no-dups-append
   (implies (and (no-duplicatesp-equal a) (no-duplicatesp-equal b)
                 (not (intersectp-equal a b)))
            (no-duplicatesp-equal (append a b)))))

(local
 (defthm fn-scv-no-dups-withdrawn-numbers
   (no-duplicatesp-equal (fn-scv-withdrawn-numbers g w0 hz v c))
   :hints (("Goal" :induct (fn-scv-withdrawn-numbers g w0 hz v c))
           ("Subgoal *1/1"
            :use ((:instance fn-scv-isect-witness-works
                             (a (fn-scv-seq-numbers g (fn-cat-withdrawn-at-from w0 c 0) v c))
                             (b (fn-scv-withdrawn-numbers g (+ 1 w0) hz v c)))
                  (:instance fn-scv-not-member-later-versions
                             (k (fn-scv-isect-witness
                                 (fn-scv-seq-numbers g (fn-cat-withdrawn-at-from w0 c 0) v c)
                                 (fn-scv-withdrawn-numbers g (+ 1 w0) hz v c)))))))))

(local
 (defthm fn-scv-no-dups-x
   (no-duplicatesp-equal (fn-scv-x group v fn-cat))
   :hints (("Goal" :in-theory (enable fn-scv-x)
            :use ((:instance fn-scv-isect-witness-works
                             (a (fn-scv-new-numbers group (nfix v) (len fn-cat) fn-cat))
                             (b (fn-scv-withdrawn-numbers group (nfix v)
                                                          (nfix (fn-cat-horizon fn-cat))
                                                          (nfix v) fn-cat)))
                  (:instance fn-scv-member-new-numbers-elim
                             (g group) (c fn-cat) (a (nfix v)) (n (len fn-cat))
                             (k (fn-scv-isect-witness
                                 (fn-scv-new-numbers group (nfix v) (len fn-cat) fn-cat)
                                 (fn-scv-withdrawn-numbers group (nfix v)
                                                           (nfix (fn-cat-horizon fn-cat))
                                                           (nfix v) fn-cat))))
                  (:instance fn-scv-member-withdrawn-numbers-elim
                             (g group) (c fn-cat) (w0 (nfix v)) (v (nfix v))
                             (hz (nfix (fn-cat-horizon fn-cat)))
                             (k (fn-scv-isect-witness
                                 (fn-scv-new-numbers group (nfix v) (len fn-cat) fn-cat)
                                 (fn-scv-withdrawn-numbers group (nfix v)
                                                           (nfix (fn-cat-horizon fn-cat))
                                                           (nfix v) fn-cat)))))))))

; X is the numbers served from rows the constant-time test names.
(local
 (defthm fn-scv-in-xp-when-member
   (implies (and (fn-cat-p fn-cat) (member-equal k (fn-scv-x group v fn-cat)))
            (fn-scv-in-xp group k v fn-cat))
   :hints (("Goal" :in-theory (e/d (fn-scv-x fn-scv-in-xp) (fn-scv-member-new-numbers
                                                              fn-scv-member-withdrawn-numbers))
            :use ((:instance fn-scv-member-new-numbers-elim
                             (g group) (c fn-cat) (a (nfix v)) (n (len fn-cat)))
                  (:instance fn-scv-member-withdrawn-numbers-elim
                             (g group) (c fn-cat) (w0 (nfix v)) (v (nfix v))
                             (hz (nfix (fn-cat-horizon fn-cat)))))))))

(local
 (defthm fn-scv-member-when-in-xp
   (implies (and (fn-cat-p fn-cat) (fn-scv-in-xp group k v fn-cat))
            (member-equal k (fn-scv-x group v fn-cat)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cat-p-is-rowsp fn-scv-x fn-scv-in-xp)
                            (fn-scv-member-new-numbers fn-scv-member-withdrawn-numbers
                             fn-scv-member-seq-numbers fn-scv-member-withdrawn-at-from
                             fn-cat-withdrawn-at-from))
            :use ((:instance fn-scv-number-seq-binds (g group) (n k) (c fn-cat) (i 0))
                  (:instance fn-scv-member-new-numbers (g group) (c fn-cat) (a (nfix v))
                             (n (len fn-cat)) (s (fn-cat-number-seq group k fn-cat 0)))
                  (:instance fn-scv-withdrawn-below-horizon (c fn-cat)
                             (s (fn-cat-number-seq group k fn-cat 0)))
                  (:instance fn-scv-withdrawn-natp (c fn-cat)
                             (s (fn-cat-number-seq group k fn-cat 0)))
                  (:instance fn-scv-member-withdrawn-at-from (c fn-cat) (i 0)
                             (s (fn-cat-number-seq group k fn-cat 0)))
                  (:instance fn-scv-member-seq-numbers (g group) (c fn-cat) (v (nfix v))
                             (s (fn-cat-number-seq group k fn-cat 0))
                             (seqs (fn-cat-withdrawn-at-from
                                    (car (fn-held-withdrawn (nth (fn-cat-number-seq group k fn-cat 0)
                                                                 fn-cat)))
                                    fn-cat 0)))
                  (:instance fn-scv-member-withdrawn-numbers (g group) (c fn-cat)
                             (w0 (nfix v)) (v (nfix v)) (hz (fn-cat-horizon-of fn-cat))
                             (w (car (fn-held-withdrawn (nth (fn-cat-number-seq group k fn-cat 0)
                                                             fn-cat)))))
                  (:instance fn-cat-horizon-is-horizon-of))))))

; The constant-time test is membership in X.
(defthm fn-scv-in-xp-iff-member
  (implies (fn-cat-p fn-cat)
           (iff (fn-scv-in-xp group k v fn-cat)
                (member-equal k (fn-scv-x group v fn-cat))))
  :hints (("Goal" :use (fn-scv-in-xp-when-member fn-scv-member-when-in-xp))))

(local
 (defthm fn-scv-withdrawn-natp-of-seq
   (implies (and (fn-cat-rowsp c) (fn-cat-number-seq g k c 0)
                 (fn-held-withdrawn (nth (fn-cat-number-seq g k c 0) c)))
            (natp (car (fn-held-withdrawn (nth (fn-cat-number-seq g k c 0) c)))))
   :hints (("Goal" :use ((:instance fn-scv-number-seq-binds (g g) (n k) (c c) (i 0))
                         (:instance fn-scv-withdrawn-natp (c c)
                                    (s (fn-cat-number-seq g k c 0))))))))

(local
 (defthm fn-scv-keptp-is-liveq-outside-in-xp
   (implies (and (fn-cat-p fn-cat) (natp v)
                 (not (fn-scv-in-xp group k v fn-cat)))
            (equal (fn-scv-keptp group k v fn-cat) (fn-scv-liveq group k fn-cat)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cat-p-is-rowsp fn-cat-visiblep fn-cat-live-rowp
                             fn-scv-in-xp fn-scv-keptp fn-scv-liveq) (fn-scv-in-xp-iff-member))
            :cases ((fn-cat-number-seq group k fn-cat 0))
            :use ((:instance fn-scv-number-seq-binds (g group) (n k) (c fn-cat) (i 0))
                  (:instance fn-scv-withdrawn-natp-of-seq (g group) (c fn-cat)))))))

(defthm fn-scv-keptp-is-liveq-outside-x
  (implies (and (fn-cat-p fn-cat) (natp v)
                (not (member-equal k (fn-scv-x group v fn-cat))))
           (equal (fn-scv-keptp group k v fn-cat) (fn-scv-liveq group k fn-cat)))
  :hints (("Goal" :use (fn-scv-keptp-is-liveq-outside-in-xp fn-scv-in-xp-iff-member)
           :in-theory (disable fn-scv-keptp-is-liveq-outside-in-xp fn-scv-x
                               fn-scv-in-xp-iff-member))))

(in-theory (disable fn-scv-keptp fn-scv-liveq fn-scv-x fn-scv-in-xp))

(local
 (defthm fn-scv-keptp-posp
   (implies (fn-scv-keptp group k v fn-cat) (posp k))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-scv-keptp)))))

(local
 (defthm fn-scv-liveq-posp
   (implies (fn-scv-liveq group k fn-cat) (posp k))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-scv-liveq fn-cat-live-rowp)))))

; -----------------------------------------------------------------------------
; The specification: the count, least and greatest number served at V over
; K .. TOP (downward from K for the greatest), number-wise.

(defun fn-scv-count-p (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (+ (if (fn-scv-keptp group k v fn-cat) 1 0)
         (fn-scv-count-p group (+ 1 k) top v fn-cat))
    0))

(defun fn-scv-first-p (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-scv-keptp group k v fn-cat)
          k
        (fn-scv-first-p group (+ 1 k) top v fn-cat))
    0))

(defun fn-scv-last-p (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp v))))
  (if (posp k)
      (if (fn-scv-keptp group k v fn-cat)
          k
        (fn-scv-last-p group (- k 1) v fn-cat))
    0))

; -----------------------------------------------------------------------------
; The pieces over X.

(defun fn-scv-tests (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((s (fn-cat-group-number group k fn-cat)))
    (if (and (natp s) (< s (fn-cat-count fn-cat)))
        (let ((row (fn-cat-at s fn-cat)))
          (mv (and (fn-cat-visible-at s (nfix v) fn-cat)
                   (fn-cat-row-availablep row)
                   (posp k) (<= k *fn-nntp-max-article-number*)
                   (fn-scat-msgid-idp (fn-record-msgid row)) t)
              (fn-cat-live-rowp group k row)))
      (mv nil nil))))

(defthm fn-scv-tests-are-the-tests-by-definition
  (and (equal (mv-nth 0 (fn-scv-tests group k v fn-cat))
              (fn-scv-keptp group k v fn-cat))
       (equal (mv-nth 1 (fn-scv-tests group k v fn-cat))
              (fn-scv-liveq group k fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-scv-keptp fn-scv-liveq)
                (fn-scv-liveq-is-live-numberp fn-cat-live-rowp
                 fn-cat-at-is-nth fn-cat-count-is-len
                 fn-cat-group-number-is-number-seq fn-cat-visible-at-is-visiblep)))))

(in-theory (disable fn-scv-tests))

(defun fn-scv-diff (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (mv-let (kept live) (fn-scv-tests group k v fn-cat)
    (- (if kept 1 0) (if live 1 0))))

(defun fn-scv-in-rangep (x lo top)
  (declare (xargs :guard t))
  (and (natp x) (natp lo) (natp top) (<= lo x) (<= x top)))

; The sum of (served) - (live) over the elements of XS within LO .. TOP.

(defun fn-scv-xdiff (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil))
  (if (consp xs)
      (+ (if (fn-scv-in-rangep (car xs) lo top)
             (fn-scv-diff group (car xs) v fn-cat)
           0)
         (fn-scv-xdiff group (cdr xs) lo top v fn-cat))
    0))


(verify-guards fn-scv-xdiff)

; The least (greatest) element of XS within LO .. TOP served at V, else 0.
(defun fn-scv-min* (a b)
  (declare (xargs :guard (and (natp a) (natp b))))
  (cond ((zp a) (nfix b)) ((zp b) a) (t (min a b))))


(defun fn-scv-xmin (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil))
  (if (consp xs)
      (fn-scv-min* (if (and (fn-scv-in-rangep (car xs) lo top)
                            (fn-scv-keptp group (car xs) v fn-cat))
                       (car xs)
                     0)
                   (fn-scv-xmin group (cdr xs) lo top v fn-cat))
    0))

(local
 (defthm fn-scv-min*-natp
   (natp (fn-scv-min* a b))
   :rule-classes :type-prescription))

(local
 (defthm fn-scv-min*-assoc-comm
   (implies (and (natp a) (natp b) (natp c))
            (and (equal (fn-scv-min* (fn-scv-min* a b) c) (fn-scv-min* a (fn-scv-min* b c)))
                 (equal (fn-scv-min* a b) (fn-scv-min* b a))
                 (equal (fn-scv-min* 0 a) a)))))

(local
 (defthm fn-scv-xmin-natp
   (natp (fn-scv-xmin group xs lo top v fn-cat))
   :rule-classes :type-prescription))


(verify-guards fn-scv-xmin
  :hints (("Goal" :in-theory (disable fn-scv-min*))))


(defun fn-scv-xmax (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil))
  (if (consp xs)
      (max (if (and (fn-scv-in-rangep (car xs) lo top)
                    (fn-scv-keptp group (car xs) v fn-cat))
               (car xs)
             0)
           (fn-scv-xmax group (cdr xs) lo top v fn-cat))
    0))

(local
 (defthm fn-scv-xmax-natp
   (natp (fn-scv-xmax group xs lo top v fn-cat))
   :rule-classes :type-prescription))


(verify-guards fn-scv-xmax)

; GEN: def-loop's :fold has no read-only stobj context (def-loop's option
; check). This single accumulator walk has no recursive executable twin.
(defun fn-scv-xfold-loop (group xs lo top v fn-cat count low high)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp v) (integerp count) (natp low) (natp high))))
  (if (consp xs)
      (if (fn-scv-in-rangep (car xs) lo top)
          (mv-let (kept live) (fn-scv-tests group (car xs) v fn-cat)
            (let ((k (if kept (car xs) 0)))
              (fn-scv-xfold-loop group (cdr xs) lo top v fn-cat
                                 (+ count (- (if kept 1 0) (if live 1 0)))
                                 (fn-scv-min* low k) (max high k))))
        (fn-scv-xfold-loop group (cdr xs) lo top v fn-cat count low high))
    (list count low high)))

(local
 (defthm fn-scv-xfold-loop-is-the-three-with-accumulators
   (implies (and (integerp count) (natp low) (natp high))
            (equal (fn-scv-xfold-loop group xs lo top v fn-cat count low high)
                   (list (+ count (fn-scv-xdiff group xs lo top v fn-cat))
                         (fn-scv-min* low (fn-scv-xmin group xs lo top v fn-cat))
                         (max high (fn-scv-xmax group xs lo top v fn-cat)))))
   :hints (("Goal" :induct (fn-scv-xfold-loop group xs lo top v fn-cat count low high)
            :in-theory (disable fn-scv-keptp fn-scv-liveq fn-scv-min*)))))

(defun fn-scv-xfold (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (fn-scv-xfold-loop group xs lo top v fn-cat 0 0 0))

(defthm fn-scv-xfold-is-the-three
  (equal (fn-scv-xfold group xs lo top v fn-cat)
         (list (fn-scv-xdiff group xs lo top v fn-cat)
               (fn-scv-xmin group xs lo top v fn-cat)
               (fn-scv-xmax group xs lo top v fn-cat)))
  :hints (("Goal" :in-theory (disable fn-scv-xfold-loop fn-scv-xdiff
                                      fn-scv-xmin fn-scv-xmax))))

(in-theory (disable fn-scv-xfold fn-scv-xfold-loop))

; The first (last) table-live number outside X from K up to TOP (down to 1).
; A step tests membership in X in constant time (fn-scv-in-xp).
(defun fn-scv-scan-up (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (and (not (fn-scv-in-xp group k v fn-cat)) (fn-scv-liveq group k fn-cat))
          k
        (fn-scv-scan-up group (+ 1 k) top v fn-cat))
    0))

(defun fn-scv-scan-down (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp v))))
  (if (posp k)
      (if (and (not (fn-scv-in-xp group k v fn-cat)) (fn-scv-liveq group k fn-cat))
          k
        (fn-scv-scan-down group (- k 1) v fn-cat))
    0))

; -----------------------------------------------------------------------------
; The count.

(local
 (defthm fn-scv-xdiff-empty-range
   (implies (and (natp lo) (natp top) (< top lo))
            (equal (fn-scv-xdiff group xs lo top v fn-cat) 0))))

(local
 (defthm fn-scv-xdiff-step
   (implies (and (no-duplicatesp-equal xs) (natp k) (natp top) (<= k top))
            (equal (fn-scv-xdiff group xs k top v fn-cat)
                   (+ (if (member-equal k xs) (fn-scv-diff group k v fn-cat) 0)
                      (fn-scv-xdiff group xs (+ 1 k) top v fn-cat))))
   :hints (("Goal" :induct (fn-scv-xdiff group xs k top v fn-cat)
            :in-theory (disable fn-scv-diff)))))

(local
 (defthm fn-scv-diff-outside-x
   (implies (and (fn-cat-p fn-cat) (natp v) (natp k)
                 (not (member-equal k (fn-scv-x group v fn-cat))))
            (equal (fn-scv-diff group k v fn-cat) 0))))

(local
 (defthm fn-scv-count-general
   (implies (and (fn-cat-p fn-cat) (natp v) (natp k) (natp top))
            (equal (fn-scv-count-p group k top v fn-cat)
                   (+ (fn-cat-live-count-from group k top fn-cat)
                      (fn-scv-xdiff group (fn-scv-x group v fn-cat) k top v fn-cat))))
   :hints (("Goal" :induct (fn-scv-count-p group k top v fn-cat)
            :in-theory (disable fn-cat-live-numberp))
           ("Subgoal *1/1" :cases ((member-equal k (fn-scv-x group v fn-cat)))))))

; -----------------------------------------------------------------------------
; The least.

(local
 (defthm fn-scv-scan-up-range
   (let ((j (fn-scv-scan-up group k top v fn-cat)))
     (and (natp j)
          (implies (not (equal j 0)) (and (<= k j) (<= j top)))))
   :rule-classes ((:rewrite) (:linear :corollary
                              (implies (not (equal (fn-scv-scan-up group k top v fn-cat) 0))
                                       (and (<= k (fn-scv-scan-up group k top v fn-cat))
                                            (<= (fn-scv-scan-up group k top v fn-cat) top)))))))

(local
 (defthm fn-scv-xmin-range
   (let ((j (fn-scv-xmin group xs lo top v fn-cat)))
     (and (natp j)
          (implies (not (equal j 0)) (and (<= lo j) (<= j top)))))
   :rule-classes ((:rewrite) (:linear :corollary
                              (implies (not (equal (fn-scv-xmin group xs lo top v fn-cat) 0))
                                       (and (<= lo (fn-scv-xmin group xs lo top v fn-cat))
                                            (<= (fn-scv-xmin group xs lo top v fn-cat) top)))))))

(local
 (defthm fn-scv-xmin-step
   (implies (and (natp k) (natp top) (<= k top))
            (equal (fn-scv-xmin group xs k top v fn-cat)
                   (if (and (member-equal k xs) (fn-scv-keptp group k v fn-cat))
                       k
                     (fn-scv-xmin group xs (+ 1 k) top v fn-cat))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-xmin group xs k top v fn-cat)
            :in-theory (disable fn-scv-keptp)))))

(local
 (defthm fn-scv-xmin-empty-range
   (implies (and (natp lo) (natp top) (< top lo))
            (equal (fn-scv-xmin group xs lo top v fn-cat) 0))))

(local
 (defthm fn-scv-live-numberp-posp
   (implies (fn-cat-live-numberp g k c) (posp k))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cat-live-numberp fn-cat-live-rowp)))))

(local
 (defthm fn-scv-min*-left
   (implies (and (posp k) (natp j) (or (equal j 0) (< k j)))
            (equal (fn-scv-min* k j) k))))

(local
 (defthm fn-scv-min*-right
   (implies (and (posp k) (natp j) (or (equal j 0) (< k j)))
            (equal (fn-scv-min* j k) k))))

(local
 (defthm fn-scv-first-general
   (implies (and (fn-cat-p fn-cat) (natp v) (natp k) (natp top))
            (equal (fn-scv-first-p group k top v fn-cat)
                   (fn-scv-min* (fn-scv-scan-up group k top v fn-cat)
                                (fn-scv-xmin group (fn-scv-x group v fn-cat) k top v fn-cat))))
   :hints (("Goal" :induct (fn-scv-first-p group k top v fn-cat)
            :in-theory (disable fn-scv-xmin fn-scv-min* fn-scv-scan-up fn-scv-x
                                fn-scv-liveq-is-live-numberp)
            :expand ((fn-scv-scan-up group k top v fn-cat)))
           ("Subgoal *1/3" :use ((:instance fn-scv-xmin-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x)))
           ("Subgoal *1/2" :use ((:instance fn-scv-xmin-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x)))
           ("Subgoal *1/1" :use ((:instance fn-scv-xmin-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x))))))

; The scan may start at the table's least.
(local
 (defthm fn-scv-scan-up-from-first
   (implies (and (natp k) (natp top))
            (equal (fn-scv-scan-up group k top v fn-cat)
                   (let ((j (fn-cat-live-first group k top fn-cat)))
                     (if (equal j 0) 0 (fn-scv-scan-up group j top v fn-cat)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-scan-up group k top v fn-cat)
            :in-theory (e/d (fn-scv-liveq-is-live-numberp) (fn-cat-live-numberp))))))

; -----------------------------------------------------------------------------
; The greatest.

(local
 (defthm fn-scv-scan-down-range
   (let ((j (fn-scv-scan-down group k v fn-cat)))
     (and (natp j) (<= j (nfix k))))
   :rule-classes ((:rewrite) (:linear :corollary
                              (<= (fn-scv-scan-down group k v fn-cat) (nfix k))))))

(local
 (defthm fn-scv-xmax-range
   (let ((j (fn-scv-xmax group xs lo top v fn-cat)))
     (and (natp j)
          (implies (not (equal j 0)) (and (<= lo j) (<= j top)))))
   :rule-classes ((:rewrite) (:linear :corollary
                              (implies (not (equal (fn-scv-xmax group xs lo top v fn-cat) 0))
                                       (and (<= lo (fn-scv-xmax group xs lo top v fn-cat))
                                            (<= (fn-scv-xmax group xs lo top v fn-cat) top)))))))

(local
 (defthm fn-scv-xmax-step
   (implies (and (posp k))
            (equal (fn-scv-xmax group xs 1 k v fn-cat)
                   (if (and (member-equal k xs) (fn-scv-keptp group k v fn-cat))
                       k
                     (fn-scv-xmax group xs 1 (- k 1) v fn-cat))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-xmax group xs 1 k v fn-cat)
            :in-theory (disable fn-scv-keptp)))))

(local
 (defthm fn-scv-last-general
   (implies (and (fn-cat-p fn-cat) (natp v) (natp k))
            (equal (fn-scv-last-p group k v fn-cat)
                   (max (fn-scv-scan-down group k v fn-cat)
                        (fn-scv-xmax group (fn-scv-x group v fn-cat) 1 k v fn-cat))))
   :hints (("Goal" :induct (fn-scv-last-p group k v fn-cat)
            :in-theory (disable fn-scv-xmax fn-scv-scan-down fn-scv-x
                                fn-scv-liveq-is-live-numberp)
            :expand ((fn-scv-scan-down group k v fn-cat)))
           ("Subgoal *1/3" :use ((:instance fn-scv-xmax-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x)))
           ("Subgoal *1/2" :use ((:instance fn-scv-xmax-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x)))
           ("Subgoal *1/1" :use ((:instance fn-scv-xmax-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x))))))

(local
 (defthm fn-scv-scan-down-from-last
   (implies (natp k)
            (equal (fn-scv-scan-down group k v fn-cat)
                   (let ((j (fn-cat-live-last group k fn-cat)))
                     (if (equal j 0) 0 (fn-scv-scan-down group j v fn-cat)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-scan-down group k v fn-cat)
            :in-theory (e/d (fn-scv-liveq-is-live-numberp) (fn-cat-live-numberp))))))

; -----------------------------------------------------------------------------
; The walks the summary executes: along the catalog's live list (the
; exports fn-cat-live-next and fn-cat-live-prev, one link read each in the
; paged catalog), stepping only past numbers in X.  A step past a number
; outside X never happens, so a walk takes at most one step more than the
; numbers of X it passes (fn-scv-link-up-steps-bound below), whatever the
; dead runs between the live numbers.  The number-wise scans above stay as
; the logical side (the summary's mbe), and the walks equal them from a live
; start (fn-scv-link-up-is-scan-up, fn-scv-link-down-is-scan-down).

(local
 (defthm fn-scv-live-first-bound
   (implies (and (natp top) (not (equal (fn-cat-live-first g k top c) 0)))
            (and (<= (fn-cat-live-first g k top c) top)
                 (<= (nfix k) (fn-cat-live-first g k top c))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-scv-live-next-bound
   (implies (not (equal (fn-cat-live-next g k fn-cat) 0))
            (and (< (nfix k) (fn-cat-live-next g k fn-cat))
                 (<= (fn-cat-live-next g k fn-cat) (fn-cat-group-high g fn-cat))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-cat-live-numberp)))))

(defun fn-scv-link-up (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :measure (nfix (- (+ 1 (fn-cat-group-high group fn-cat)) (nfix k)))))
  (if (and (posp k) (fn-scv-in-xp group k v fn-cat))
      (let ((n (fn-cat-live-next group k fn-cat)))
        (if (< k n) (fn-scv-link-up group n v fn-cat) 0))
    (nfix k)))

(defun fn-scv-link-down (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :measure (nfix k)))
  (if (and (posp k) (fn-scv-in-xp group k v fn-cat))
      (let ((p (fn-cat-live-prev group k fn-cat)))
        (if (< p k) (fn-scv-link-down group p v fn-cat) 0))
    (nfix k)))

(local
 (defthm fn-scv-number-seq-above-high
   (implies (and (natp n) (< (fn-cat-group-high g c) n))
            (equal (fn-cat-number-seq g n c i) nil))
   :hints (("Goal" :in-theory (enable fn-cat-number-seq fn-cat-group-high)))))

(local
 (defthm fn-scv-live-numberp-below-high
   (implies (fn-cat-live-numberp g k c)
            (<= k (fn-cat-group-high g c)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cat-live-numberp)))))

(local
 (defthm fn-scv-live-first-is-live
   (implies (not (equal (fn-cat-live-first g k top c) 0))
            (fn-cat-live-numberp g (fn-cat-live-first g k top c) c))
   :hints (("Goal" :in-theory (disable fn-cat-live-numberp)))))

(local
 (defthm fn-scv-live-last-is-live
   (implies (not (equal (fn-cat-live-last g k c) 0))
            (fn-cat-live-numberp g (fn-cat-live-last g k c) c))
   :hints (("Goal" :in-theory (disable fn-cat-live-numberp)))))

(defthm fn-scv-link-up-is-scan-up
  (implies (and (fn-cat-p fn-cat) (fn-cat-live-numberp g k fn-cat))
           (equal (fn-scv-link-up g k v fn-cat)
                  (fn-scv-scan-up g k (fn-cat-group-high g fn-cat) v fn-cat)))
  :hints (("Goal" :induct (fn-scv-link-up g k v fn-cat)
           :in-theory (disable fn-cat-live-numberp fn-scv-in-xp fn-cat-live-first))
          ("Subgoal *1/1" :expand ((fn-scv-scan-up g k (fn-cat-group-high g fn-cat) v fn-cat))
           :use ((:instance fn-scv-scan-up-from-first (group g) (k (+ 1 k))
                            (top (fn-cat-group-high g fn-cat)))))
          ("Subgoal *1/2" :expand ((fn-scv-scan-up g k (fn-cat-group-high g fn-cat) v fn-cat))
           :use ((:instance fn-scv-scan-up-from-first (group g) (k (+ 1 k))
                            (top (fn-cat-group-high g fn-cat)))))))

(local
 (defthm fn-scv-live-last-bound
   (<= (fn-cat-live-last g k c) (nfix k))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-cat-live-numberp)))))

(defthm fn-scv-link-down-is-scan-down
  (implies (and (fn-cat-p fn-cat) (fn-cat-live-numberp g k fn-cat))
           (equal (fn-scv-link-down g k v fn-cat)
                  (fn-scv-scan-down g k v fn-cat)))
  :hints (("Goal" :induct (fn-scv-link-down g k v fn-cat)
           :in-theory (disable fn-cat-live-numberp fn-scv-in-xp fn-cat-live-last))
          ("Subgoal *1/1" :expand ((fn-scv-scan-down g k v fn-cat))
           :use ((:instance fn-scv-scan-down-from-last (group g) (k (- k 1)))))
          ("Subgoal *1/2" :expand ((fn-scv-scan-down g k v fn-cat))
           :use ((:instance fn-scv-scan-down-from-last (group g) (k (- k 1)))))))

; -----------------------------------------------------------------------------
; The summary at V, and its keystones.

(defun fn-scv-summary (group v fn-cat)
  "(COUNT LEAST GREATEST) of GROUP's numbers served at view V: the live
table's, corrected over X (the numbers of the rows appended at or after V
and of the rows withdrawn at or after V)."
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-scv-scan-up fn-scv-scan-down fn-scv-link-up
                                                            fn-scv-link-down fn-cat-live-numberp
                                                            fn-cat-live-first fn-cat-live-last)))))
  (let* ((top (nfix (- (fn-cat-group-next group fn-cat) 1)))
         (x (fn-scv-x group v fn-cat))
         (correction (fn-scv-xfold group x 1 top v fn-cat))
         (count (+ (fn-cat-group-live-count group fn-cat)
                   (car correction)))
         (low (fn-cat-group-live-low group fn-cat))
         (first (fn-scv-min* (if (posp low)
                                 (mbe :logic (fn-scv-scan-up group low top v fn-cat)
                                      :exec (fn-scv-link-up group low v fn-cat))
                               0)
                             (cadr correction)))
         (high (fn-cat-group-live-high group fn-cat))
         (last (max (if (posp high)
                        (mbe :logic (fn-scv-scan-down group high v fn-cat)
                             :exec (fn-scv-link-down group high v fn-cat))
                      0)
                    (caddr correction))))
    (list (nfix count) first last)))

(local
 (defthm fn-scv-count-p-natp
   (natp (fn-scv-count-p group k top v fn-cat))
   :rule-classes :type-prescription))

(local
 (defthm fn-scv-live-first-natp
   (natp (fn-cat-live-first g k top c))
   :rule-classes :type-prescription))

(local
 (defthm fn-scv-live-last-natp
   (natp (fn-cat-live-last g k c))
   :rule-classes :type-prescription))

(local
 (defthm fn-scv-count-is-count-p-natp
  (implies (and (fn-cat-p fn-cat) (natp v))
           (equal (car (fn-scv-summary group v fn-cat))
                  (fn-scv-count-p group 1 (fn-cat-group-high group fn-cat) v fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-group-live-count-is-count-from)
                           (fn-scv-xdiff fn-scv-x fn-scv-count-p fn-cat-live-count-from))
           :use ((:instance fn-scv-count-general (k 1)
                            (top (fn-cat-group-high group fn-cat)))
                 (:instance fn-scv-count-p-natp (k 1)
                            (top (fn-cat-group-high group fn-cat))))))))

(local
 (defthm fn-scv-first-is-first-p-natp
  (implies (and (fn-cat-p fn-cat) (natp v))
           (equal (cadr (fn-scv-summary group v fn-cat))
                  (fn-scv-first-p group 1 (fn-cat-group-high group fn-cat) v fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-group-live-low-is-first)
                           (fn-scv-xmin fn-scv-x fn-scv-first-p fn-scv-scan-up fn-scv-min*
                            fn-cat-live-first fn-scv-xdiff))
           :use ((:instance fn-scv-first-general (k 1)
                            (top (fn-cat-group-high group fn-cat)))
                 (:instance fn-scv-scan-up-from-first (k 1)
                            (top (fn-cat-group-high group fn-cat))))))))

(local
 (defthm fn-scv-last-is-last-p-natp
  (implies (and (fn-cat-p fn-cat) (natp v))
           (equal (caddr (fn-scv-summary group v fn-cat))
                  (fn-scv-last-p group (fn-cat-group-high group fn-cat) v fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-group-live-high-is-last)
                           (fn-scv-xmax fn-scv-x fn-scv-last-p fn-scv-scan-down
                            fn-cat-live-last fn-scv-xdiff fn-scv-xmin fn-scv-scan-up))
           :use ((:instance fn-scv-last-general (k (fn-cat-group-high group fn-cat)))
                 (:instance fn-scv-scan-down-from-last (k (fn-cat-group-high group fn-cat))))))))

; v enters only through (nfix v): off the naturals every fold is its value at 0.
(local
 (defthm fn-scv-keptp-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-keptp group k v fn-cat) (fn-scv-keptp group k 0 fn-cat)))
   :hints (("Goal" :in-theory (enable fn-scv-keptp)))))

(local
 (defthm fn-scv-x-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-x group v fn-cat) (fn-scv-x group 0 fn-cat)))
   :hints (("Goal" :in-theory (enable fn-scv-x)))))

(local
 (defthm fn-scv-count-p-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-count-p group k top v fn-cat) (fn-scv-count-p group k top 0 fn-cat)))))

(local
 (defthm fn-scv-first-p-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-first-p group k top v fn-cat) (fn-scv-first-p group k top 0 fn-cat)))))

(local
 (defthm fn-scv-last-p-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-last-p group k v fn-cat) (fn-scv-last-p group k 0 fn-cat)))))

(local
 (defthm fn-scv-in-xp-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-in-xp group k v fn-cat) (fn-scv-in-xp group k 0 fn-cat)))
   :hints (("Goal" :in-theory (enable fn-scv-in-xp)))))

(local
 (defthm fn-scv-scan-up-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-scan-up group k top v fn-cat) (fn-scv-scan-up group k top 0 fn-cat)))
   :hints (("Goal" :induct (fn-scv-scan-up group k top v fn-cat)))))

(local
 (defthm fn-scv-scan-down-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-scan-down group k v fn-cat) (fn-scv-scan-down group k 0 fn-cat)))
   :hints (("Goal" :induct (fn-scv-scan-down group k v fn-cat)))))

(local
 (defthm fn-scv-xdiff-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-xdiff group xs lo top v fn-cat) (fn-scv-xdiff group xs lo top 0 fn-cat)))))

(local
 (defthm fn-scv-xmin-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-xmin group xs lo top v fn-cat) (fn-scv-xmin group xs lo top 0 fn-cat)))))

(local
 (defthm fn-scv-xmax-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-xmax group xs lo top v fn-cat) (fn-scv-xmax group xs lo top 0 fn-cat)))))

(local
 (defthm fn-scv-summary-off-naturals
   (implies (not (natp v))
            (equal (fn-scv-summary group v fn-cat) (fn-scv-summary group 0 fn-cat)))
   :hints (("Goal" :in-theory (disable fn-scv-x fn-scv-xdiff fn-scv-xmin fn-scv-xmax
                                       fn-scv-scan-up fn-scv-scan-down)))))

; KEYSTONE: the count.
(defthm fn-scv-count-is-count-p
  (implies (fn-cat-p fn-cat)
           (equal (car (fn-scv-summary group v fn-cat))
                  (fn-scv-count-p group 1 (fn-cat-group-high group fn-cat) v fn-cat)))
  :hints (("Goal" :cases ((natp v))
           :use ((:instance fn-scv-count-is-count-p-natp)
                 (:instance fn-scv-count-is-count-p-natp (v 0)))
           :in-theory (disable fn-scv-summary fn-scv-count-p fn-scv-count-is-count-p-natp))))

; KEYSTONE: the least.
(defthm fn-scv-first-is-first-p
  (implies (fn-cat-p fn-cat)
           (equal (cadr (fn-scv-summary group v fn-cat))
                  (fn-scv-first-p group 1 (fn-cat-group-high group fn-cat) v fn-cat)))
  :hints (("Goal" :cases ((natp v))
           :use ((:instance fn-scv-first-is-first-p-natp)
                 (:instance fn-scv-first-is-first-p-natp (v 0)))
           :in-theory (disable fn-scv-summary fn-scv-first-p fn-scv-first-is-first-p-natp))))

; KEYSTONE: the greatest.
(defthm fn-scv-last-is-last-p
  (implies (fn-cat-p fn-cat)
           (equal (caddr (fn-scv-summary group v fn-cat))
                  (fn-scv-last-p group (fn-cat-group-high group fn-cat) v fn-cat)))
  :hints (("Goal" :cases ((natp v))
           :use ((:instance fn-scv-last-is-last-p-natp)
                 (:instance fn-scv-last-is-last-p-natp (v 0)))
           :in-theory (disable fn-scv-summary fn-scv-last-p fn-scv-last-is-last-p-natp))))

; -----------------------------------------------------------------------------
; The work: linear in the change since V, plus the scans.
;
; The summary's loop iterations, counted by the same recursions the loops
; run: the rows V .. count-1 (one iteration each), the versions V .. HZ-1
; (one each, and one per withdrawn seq the version lists), six passes over X
; (the three folds, the append that builds X, and the reversals of the
; loops that build it), and the scan steps (each a constant-time test, then
; a constant-time liveness read).  There is no |X|^2 term: X is built
; without a pass over itself and a scan step tests membership in X in
; constant time.
;
; The walks step along the live list, only past numbers of X, so their
; steps are at most two plus two per number of X (fn-scv-scan-steps-bound),
; whatever dead runs lie between live numbers.

(defun fn-scv-new-work (s n fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp s) (natp n))
                  :measure (nfix (- (nfix n) (nfix s)))))
  (if (and (natp s) (natp n) (< s n) (< s (fn-cat-count fn-cat)))
      (+ 1 (fn-scv-new-work (+ 1 s) n fn-cat))
    0))

(defun fn-scv-withdrawn-work (w hz fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp w) (natp hz))
                  :measure (nfix (- (nfix hz) (nfix w)))))
  (if (and (natp w) (natp hz) (< w hz))
      (+ 1 (len (fn-cat-withdrawn-at w fn-cat))
         (fn-scv-withdrawn-work (+ 1 w) hz fn-cat))
    0))

(defun fn-scv-count-in (xs lo hi)
  (declare (xargs :guard t))
  (if (consp xs)
      (+ (if (and (natp (car xs)) (natp lo) (natp hi) (<= lo (car xs)) (<= (car xs) hi)) 1 0)
         (fn-scv-count-in (cdr xs) lo hi))
    0))

(local
 (defthm fn-scv-count-in-len
   (<= (fn-scv-count-in xs lo hi) (len xs))
   :rule-classes :linear))

(local
 (defthm fn-scv-count-in-up
   (implies (and (member-equal k xs) (natp k) (natp n) (natp hi) (< k n) (<= k hi))
            (<= (+ 1 (fn-scv-count-in xs n hi)) (fn-scv-count-in xs k hi)))
   :rule-classes :linear))

(local
 (defthm fn-scv-count-in-down
   (implies (and (member-equal k xs) (natp k) (natp p) (< p k) (posp lo) (<= lo k))
            (<= (+ 1 (fn-scv-count-in xs lo p)) (fn-scv-count-in xs lo k)))
   :rule-classes :linear))

(defun fn-scv-link-up-steps (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :measure (nfix (- (+ 1 (fn-cat-group-high group fn-cat)) (nfix k)))))
  (if (and (posp k) (fn-scv-in-xp group k v fn-cat))
      (let ((n (fn-cat-live-next group k fn-cat)))
        (if (< k n) (+ 1 (fn-scv-link-up-steps group n v fn-cat)) 1))
    1))

(defun fn-scv-link-down-steps (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v) :measure (nfix k)))
  (if (and (posp k) (fn-scv-in-xp group k v fn-cat))
      (let ((p (fn-cat-live-prev group k fn-cat)))
        (if (< p k) (+ 1 (fn-scv-link-down-steps group p v fn-cat)) 1))
    1))

(defthm fn-scv-link-up-steps-bound
  (implies (and (fn-cat-p fn-cat) (natp k))
           (<= (fn-scv-link-up-steps g k v fn-cat)
               (+ 1 (fn-scv-count-in (fn-scv-x g v fn-cat) k (fn-cat-group-high g fn-cat)))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-scv-link-up-steps g k v fn-cat)
           :in-theory (disable fn-cat-live-numberp fn-cat-live-first fn-scv-x fn-cat-live-next-is-first))))

(defthm fn-scv-link-down-steps-bound
  (implies (and (fn-cat-p fn-cat) (natp k))
           (<= (fn-scv-link-down-steps g k v fn-cat)
               (+ 1 (fn-scv-count-in (fn-scv-x g v fn-cat) 1 k))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-scv-link-down-steps g k v fn-cat)
           :in-theory (disable fn-cat-live-numberp fn-cat-live-last fn-scv-x fn-cat-live-prev-is-last))))

; The steps the summary's two walks take.
(defun fn-scv-scan-steps (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let* ((low (fn-cat-group-live-low group fn-cat))
         (high (fn-cat-group-live-high group fn-cat)))
    (+ (if (posp low) (fn-scv-link-up-steps group low v fn-cat) 0)
       (if (posp high) (fn-scv-link-down-steps group high v fn-cat) 0))))

; THE WALKS ARE LINEAR IN X: two steps plus two per number of X.
(defthm fn-scv-scan-steps-bound
  (implies (fn-cat-p fn-cat)
           (<= (fn-scv-scan-steps group v fn-cat)
               (+ 2 (* 2 (len (fn-scv-x group v fn-cat))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-scv-x fn-cat-live-numberp fn-cat-live-first fn-cat-live-last
                                      fn-scv-link-up-steps fn-scv-link-down-steps)
           :use ((:instance fn-scv-link-up-steps-bound (g group) (k (fn-cat-group-live-low group fn-cat)))
                 (:instance fn-scv-link-down-steps-bound (g group) (k (fn-cat-group-live-high group fn-cat)))
                 (:instance fn-scv-count-in-len (xs (fn-scv-x group v fn-cat)) (lo (fn-cat-group-live-low group fn-cat))
                            (hi (fn-cat-group-high group fn-cat)))
                 (:instance fn-scv-count-in-len (xs (fn-scv-x group v fn-cat)) (lo 1)
                            (hi (fn-cat-group-live-high group fn-cat)))))))

(defun fn-scv-summary-work (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (+ 1
     (fn-scv-new-work (nfix v) (fn-cat-count fn-cat) fn-cat)
     (fn-scv-withdrawn-work (nfix v) (nfix (fn-cat-horizon fn-cat)) fn-cat)
     (* 6 (len (fn-scv-x group v fn-cat)))
     (fn-scv-scan-steps group v fn-cat)))

; The change since V: the rows appended, and per version from V to the
; horizon, the version and the rows it withdrew.
(defun fn-scv-versions-change (w hz fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp w) (natp hz))
                  :measure (nfix (- (nfix hz) (nfix w)))))
  (if (and (natp w) (natp hz) (< w hz))
      (+ 1 (len (fn-cat-withdrawn-at w fn-cat))
         (fn-scv-versions-change (+ 1 w) hz fn-cat))
    0))

(defun fn-scv-change-since (v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (+ (nfix (- (fn-cat-count fn-cat) (nfix v)))
     (fn-scv-versions-change (nfix v) (nfix (fn-cat-horizon fn-cat)) fn-cat)))

(local
 (defthm fn-scv-new-work-is-difference
   (implies (and (natp s) (natp n) (<= n (len c)))
            (equal (fn-scv-new-work s n c) (nfix (- n s))))))

(local
 (defthm fn-scv-withdrawn-work-is-versions-change
   (equal (fn-scv-withdrawn-work w hz fn-cat) (fn-scv-versions-change w hz fn-cat))))

(local
 (defthm fn-scv-len-new-numbers
   (<= (len (fn-scv-new-numbers g s n c)) (fn-scv-new-work s n c))
   :rule-classes :linear))

(local
 (defthm fn-scv-len-seq-numbers
   (<= (len (fn-scv-seq-numbers g seqs v c)) (len seqs))
   :rule-classes :linear))

(local
 (defthm fn-scv-len-withdrawn-numbers
   (<= (len (fn-scv-withdrawn-numbers g w hz v c)) (fn-scv-withdrawn-work w hz c))
   :rule-classes :linear))

(local
 (defthm fn-scv-len-x
   (<= (len (fn-scv-x group v fn-cat))
       (+ (fn-scv-new-work (nfix v) (fn-cat-count fn-cat) fn-cat)
          (fn-scv-withdrawn-work (nfix v) (nfix (fn-cat-horizon fn-cat)) fn-cat)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-scv-x)))))

(local
 (defthm fn-scv-linear-arithmetic
   (implies (and (natp a) (natp b) (natp l) (natp r) (<= l (+ a b)))
            (<= (+ 1 a b (* 6 l) r) (+ 1 (* 7 (+ a b)) r)))
   :rule-classes nil))

(local
 (defthm fn-scv-versions-change-natp
   (natp (fn-scv-versions-change w hz fn-cat))
   :rule-classes :type-prescription))

(local
 (defthm fn-scv-scan-steps-natp
   (natp (fn-scv-scan-steps group v fn-cat))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-scv-scan-steps)))))

; LINEARITY: the summary's work is a constant plus seven per unit of change
; since V -- the rows appended and the withdrawals -- plus the scan steps.
(defthm fn-scv-summary-work-linear
  (implies (fn-cat-p fn-cat)
           (<= (fn-scv-summary-work group v fn-cat)
               (+ 1 (* 7 (fn-scv-change-since v fn-cat))
                  (fn-scv-scan-steps group v fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-scv-summary-work fn-scv-change-since)
                                  (fn-scv-x fn-scv-scan-steps))
           :use ((:instance fn-scv-len-x)
                 (:instance fn-scv-new-work-is-difference
                            (s (nfix v)) (n (fn-cat-count fn-cat)) (c fn-cat))
                 (:instance fn-scv-linear-arithmetic
                            (a (nfix (- (fn-cat-count fn-cat) (nfix v))))
                            (b (fn-scv-versions-change (nfix v) (nfix (fn-cat-horizon fn-cat))
                                                       fn-cat))
                            (l (len (fn-scv-x group v fn-cat)))
                            (r (fn-scv-scan-steps group v fn-cat)))))))

(local
 (defthm fn-scv-bounded-arithmetic
   (implies (and (natp a) (natp b) (natp l) (natp r) (<= l (+ a b)) (<= r (+ 2 (* 2 l))))
            (<= (+ 1 (* 7 (+ a b)) r) (+ 3 (* 9 (+ a b)))))
   :rule-classes nil))

; K-DR-4, THE BOUND: a summary at V is a constant plus nine per unit of
; change since V; no term counts the group's numbers or its dead runs.
(defthm fn-scv-summary-work-bounded
  (implies (fn-cat-p fn-cat)
           (<= (fn-scv-summary-work group v fn-cat)
               (+ 3 (* 9 (fn-scv-change-since v fn-cat)))))
  :hints (("Goal" :in-theory (e/d (fn-scv-change-since)
                                  (fn-scv-x fn-scv-scan-steps fn-scv-summary-work))
           :use ((:instance fn-scv-summary-work-linear)
                 (:instance fn-scv-scan-steps-bound)
                 (:instance fn-scv-len-x)
                 (:instance fn-scv-new-work-is-difference
                            (s (nfix v)) (n (fn-cat-count fn-cat)) (c fn-cat))
                 (:instance fn-scv-bounded-arithmetic
                            (a (nfix (- (fn-cat-count fn-cat) (nfix v))))
                            (b (fn-scv-versions-change (nfix v) (nfix (fn-cat-horizon fn-cat)) fn-cat))
                            (l (len (fn-scv-x group v fn-cat)))
                            (r (fn-scv-scan-steps group v fn-cat)))))))
