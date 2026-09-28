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
         (posp k) (<= k *fn-nntp-max-article-number*)
         (fn-scat-msgid-idp (fn-record-msgid (fn-cat-at s fn-cat)))
         t)))

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

; The numbers in GROUP of the rows S .. N-1.
(defun fn-scv-new-numbers (group s n fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp s) (natp n))
                  :measure (nfix (- (nfix n) (nfix s)))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (and (natp s) (natp n) (< s n) (< s (fn-cat-count fn-cat)))
      (let ((k (fn-held-number-in group (fn-cat-at s fn-cat)))
            (rest (fn-scv-new-numbers group (+ 1 s) n fn-cat)))
        (if (posp k) (cons k rest) rest))
    nil))

; The numbers in GROUP of the rows SEQS names.
(defun fn-scv-seq-numbers (group seqs fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (consp seqs)
      (let ((rest (fn-scv-seq-numbers group (cdr seqs) fn-cat))
            (s (car seqs)))
        (if (and (natp s) (< s (fn-cat-count fn-cat)))
            (let ((k (fn-held-number-in group (fn-cat-at s fn-cat))))
              (if (posp k) (cons k rest) rest))
          rest))
    nil))

; The numbers in GROUP of the rows withdrawn at a version W .. HZ-1.
(defun fn-scv-withdrawn-numbers (group w hz fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp w) (natp hz))
                  :measure (nfix (- (nfix hz) (nfix w)))))
  (if (and (natp w) (natp hz) (< w hz))
      (append (fn-scv-seq-numbers group (fn-cat-withdrawn-at w fn-cat) fn-cat)
              (fn-scv-withdrawn-numbers group (+ 1 w) hz fn-cat))
    nil))

(defun fn-scv-x (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (remove-duplicates-equal
   (append (fn-scv-new-numbers group (nfix v) (fn-cat-count fn-cat) fn-cat)
           (fn-scv-withdrawn-numbers group (nfix v) (nfix (fn-cat-horizon fn-cat)) fn-cat))))

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
 (defthm fn-scv-member-new-numbers
   (implies (and (natp a) (natp s) (natp n) (<= a s) (< s n) (< s (len c))
                 (posp (fn-held-number-in g (nth s c))))
            (member-equal (fn-held-number-in g (nth s c)) (fn-scv-new-numbers g a n c)))
   :hints (("Goal" :induct (fn-scv-new-numbers g a n c)))))

(local
 (defthm fn-scv-member-withdrawn-at-from
   (implies (and (natp i) (natp s) (<= i s) (< s (+ i (len c)))
                 (consp (fn-held-withdrawn (nth (- s i) c))))
            (member-equal s (fn-cat-withdrawn-at-from (car (fn-held-withdrawn (nth (- s i) c)))
                                                      c i)))
   :hints (("Goal" :induct (fn-cat-withdrawn-at-from w c i)
            :in-theory (enable fn-cat-withdrawn-at-from)))))

(local
 (defthm fn-scv-member-seq-numbers
   (implies (and (member-equal s seqs) (natp s) (< s (len c))
                 (posp (fn-held-number-in g (nth s c))))
            (member-equal (fn-held-number-in g (nth s c)) (fn-scv-seq-numbers g seqs c)))))

(local
 (defthm fn-scv-member-append
   (iff (member-equal x (append a b))
        (or (member-equal x a) (member-equal x b)))))

(local
 (defthm fn-scv-member-remove-duplicates
   (iff (member-equal x (remove-duplicates-equal l))
        (member-equal x l))))

(local
 (defthm fn-scv-member-withdrawn-numbers
   (implies (and (natp w0) (natp w) (natp hz) (<= w0 w) (< w hz)
                 (member-equal k (fn-scv-seq-numbers g (fn-cat-withdrawn-at-from w c 0) c)))
            (member-equal k (fn-scv-withdrawn-numbers g w0 hz c)))
   :hints (("Goal" :induct (fn-scv-withdrawn-numbers g w0 hz c)))))

(defthm fn-scv-keptp-is-liveq-outside-x
  (implies (and (fn-cat-p fn-cat) (natp v)
                (not (member-equal k (fn-scv-x group v fn-cat))))
           (equal (fn-scv-keptp group k v fn-cat) (fn-scv-liveq group k fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-p-is-rowsp fn-cat-visiblep fn-cat-live-rowp)
                           (fn-scv-new-numbers fn-scv-withdrawn-numbers fn-cat-withdrawn-at-from))
           :cases ((and (natp k) (fn-cat-number-seq group k fn-cat 0)))
           :use ((:instance fn-scv-number-seq-binds (g group) (n k) (c fn-cat) (i 0))
                 (:instance fn-scv-member-new-numbers (g group) (c fn-cat) (a v)
                            (n (len fn-cat)) (s (fn-cat-number-seq group k fn-cat 0)))
                 (:instance fn-scv-withdrawn-below-horizon (c fn-cat)
                            (s (fn-cat-number-seq group k fn-cat 0)))
                 (:instance fn-scv-withdrawn-natp (c fn-cat)
                            (s (fn-cat-number-seq group k fn-cat 0)))
                 (:instance fn-scv-member-withdrawn-at-from (c fn-cat) (i 0)
                            (s (fn-cat-number-seq group k fn-cat 0)))
                 (:instance fn-scv-member-seq-numbers (g group) (c fn-cat)
                            (s (fn-cat-number-seq group k fn-cat 0))
                            (seqs (fn-cat-withdrawn-at-from
                                   (car (fn-held-withdrawn (nth (fn-cat-number-seq group k fn-cat 0)
                                                                fn-cat)))
                                   fn-cat 0)))
                 (:instance fn-scv-member-withdrawn-numbers (g group) (c fn-cat)
                            (w0 v) (hz (fn-cat-horizon-of fn-cat)) (k k)
                            (w (car (fn-held-withdrawn (nth (fn-cat-number-seq group k fn-cat 0)
                                                            fn-cat)))))))))

(in-theory (disable fn-scv-keptp fn-scv-liveq fn-scv-x))

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

(defun fn-scv-diff (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (- (if (fn-scv-keptp group k v fn-cat) 1 0)
     (if (fn-scv-liveq group k fn-cat) 1 0)))

(defun fn-scv-in-rangep (x lo top)
  (declare (xargs :guard t))
  (and (natp x) (natp lo) (natp top) (<= lo x) (<= x top)))

; The sum of (served) - (live) over the elements of XS within LO .. TOP.
(defun fn-scv-xdiff (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (consp xs)
      (+ (if (fn-scv-in-rangep (car xs) lo top) (fn-scv-diff group (car xs) v fn-cat) 0)
         (fn-scv-xdiff group (cdr xs) lo top v fn-cat))
    0))

; The least (greatest) element of XS within LO .. TOP served at V, else 0.
(defun fn-scv-min* (a b)
  (declare (xargs :guard (and (natp a) (natp b))))
  (cond ((zp a) (nfix b)) ((zp b) a) (t (min a b))))

(defun fn-scv-xmin (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (consp xs)
      (fn-scv-min* (if (and (fn-scv-in-rangep (car xs) lo top)
                            (fn-scv-keptp group (car xs) v fn-cat))
                       (car xs)
                     0)
                   (fn-scv-xmin group (cdr xs) lo top v fn-cat))
    0))

(defun fn-scv-xmax (group xs lo top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (consp xs)
      (max (if (and (fn-scv-in-rangep (car xs) lo top)
                    (fn-scv-keptp group (car xs) v fn-cat))
               (car xs)
             0)
           (fn-scv-xmax group (cdr xs) lo top v fn-cat))
    0))

; The first (last) table-live number outside XS from K up to TOP (down to 1).
(defun fn-scv-scan-up (group k top xs fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (true-listp xs))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (and (not (member-equal k xs)) (fn-scv-liveq group k fn-cat))
          k
        (fn-scv-scan-up group (+ 1 k) top xs fn-cat))
    0))

(defun fn-scv-scan-down (group k xs fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (true-listp xs))))
  (if (posp k)
      (if (and (not (member-equal k xs)) (fn-scv-liveq group k fn-cat))
          k
        (fn-scv-scan-down group (- k 1) xs fn-cat))
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
 (defthm fn-scv-no-dups-remove-duplicates
   (no-duplicatesp-equal (remove-duplicates-equal l))))

(local
 (defthm fn-scv-no-dups-x
   (no-duplicatesp-equal (fn-scv-x group v fn-cat))
   :hints (("Goal" :in-theory (e/d (fn-scv-x) (remove-duplicates-equal))))))

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
   (let ((j (fn-scv-scan-up group k top xs fn-cat)))
     (and (natp j)
          (implies (not (equal j 0)) (and (<= k j) (<= j top)))))
   :rule-classes ((:rewrite) (:linear :corollary
                              (implies (not (equal (fn-scv-scan-up group k top xs fn-cat) 0))
                                       (and (<= k (fn-scv-scan-up group k top xs fn-cat))
                                            (<= (fn-scv-scan-up group k top xs fn-cat) top)))))))

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
                   (fn-scv-min* (fn-scv-scan-up group k top (fn-scv-x group v fn-cat) fn-cat)
                                (fn-scv-xmin group (fn-scv-x group v fn-cat) k top v fn-cat))))
   :hints (("Goal" :induct (fn-scv-first-p group k top v fn-cat)
            :in-theory (disable fn-scv-xmin fn-scv-min* fn-scv-scan-up fn-scv-x
                                fn-scv-liveq-is-live-numberp)
            :expand ((fn-scv-scan-up group k top (fn-scv-x group v fn-cat) fn-cat)))
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
            (equal (fn-scv-scan-up group k top xs fn-cat)
                   (let ((j (fn-cat-live-first group k top fn-cat)))
                     (if (equal j 0) 0 (fn-scv-scan-up group j top xs fn-cat)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-scan-up group k top xs fn-cat)
            :in-theory (e/d (fn-scv-liveq-is-live-numberp) (fn-cat-live-numberp))))))

; -----------------------------------------------------------------------------
; The greatest.

(local
 (defthm fn-scv-scan-down-range
   (let ((j (fn-scv-scan-down group k xs fn-cat)))
     (and (natp j) (<= j (nfix k))))
   :rule-classes ((:rewrite) (:linear :corollary
                              (<= (fn-scv-scan-down group k xs fn-cat) (nfix k))))))

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
                   (max (fn-scv-scan-down group k (fn-scv-x group v fn-cat) fn-cat)
                        (fn-scv-xmax group (fn-scv-x group v fn-cat) 1 k v fn-cat))))
   :hints (("Goal" :induct (fn-scv-last-p group k v fn-cat)
            :in-theory (disable fn-scv-xmax fn-scv-scan-down fn-scv-x
                                fn-scv-liveq-is-live-numberp)
            :expand ((fn-scv-scan-down group k (fn-scv-x group v fn-cat) fn-cat)))
           ("Subgoal *1/3" :use ((:instance fn-scv-xmax-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x)))
           ("Subgoal *1/2" :use ((:instance fn-scv-xmax-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x)))
           ("Subgoal *1/1" :use ((:instance fn-scv-xmax-step (xs (fn-scv-x group v fn-cat)))
                                 (:instance fn-scv-keptp-is-liveq-outside-x))))))

(local
 (defthm fn-scv-scan-down-from-last
   (implies (natp k)
            (equal (fn-scv-scan-down group k xs fn-cat)
                   (let ((j (fn-cat-live-last group k fn-cat)))
                     (if (equal j 0) 0 (fn-scv-scan-down group j xs fn-cat)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scv-scan-down group k xs fn-cat)
            :in-theory (e/d (fn-scv-liveq-is-live-numberp) (fn-cat-live-numberp))))))

; -----------------------------------------------------------------------------
; The summary at V, and its keystones.

(defun fn-scv-summary (group v fn-cat)
  "(COUNT LEAST GREATEST) of GROUP's numbers served at view V: the live
table's, corrected over X (the numbers of the rows appended at or after V
and of the rows withdrawn at or after V)."
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let* ((top (nfix (- (fn-cat-group-next group fn-cat) 1)))
         (x (fn-scv-x group v fn-cat))
         (count (+ (fn-cat-group-live-count group fn-cat)
                   (fn-scv-xdiff group x 1 top v fn-cat)))
         (low (fn-cat-group-live-low group fn-cat))
         (first (fn-scv-min* (if (posp low) (fn-scv-scan-up group low top x fn-cat) 0)
                             (fn-scv-xmin group x 1 top v fn-cat)))
         (high (fn-cat-group-live-high group fn-cat))
         (last (max (if (posp high) (fn-scv-scan-down group high x fn-cat) 0)
                    (fn-scv-xmax group x 1 top v fn-cat))))
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
                            (top (fn-cat-group-high group fn-cat))
                            (xs (fn-scv-x group v fn-cat))))))))

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
                 (:instance fn-scv-scan-down-from-last (k (fn-cat-group-high group fn-cat))
                            (xs (fn-scv-x group v fn-cat))))))))

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
