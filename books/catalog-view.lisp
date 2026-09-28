; fn: the pinned archive at a version, as a function of the catalog and the
; arena (wave 5, lane catalog-slice step 7 groundwork, 2026-09-26; D33; the
; consolidation design 1.4 and 1.5; NNT-042).
;
; A reader connection pins a VERSION v (books/owner.lisp fn-own-conn-version =
; fn-own-view-version = the committed count).  What it pins besides today --
; the archive (fn-state-articles, newest first), the Message-ID trie
; (fn-midx-build of it, books/msgid-index.lisp) and the group buckets
; (fn-gidx-build of it, books/group-bucket-index.lisp) -- is a function of
; (v, fn-cat, fn-arena): the rows visible at v, newest first, each
; materialized as the acceptance article (fn-make-article, books/acceptance.lisp)
; from the row's wire positions, its handle and its numbers.  This book
; defines that function, fn-cat-view-articles, and proves that the two served
; lookups the machine runs over the trie and the buckets BUILT FROM IT are
; walks of the visible rows the catalog's columns answer:
;   fn-cat-view-find-article-is-walk: fn-find-article over the view (what
;     fn-midx-lookup of fn-midx-build is: fn-midx-lookup-of-build-is-find-article)
;     is the newest visible row bound to the Message-ID;
;   fn-cat-view-number-entry-is-walk: fn-gidx-find-number-entry over
;     fn-index-build of the view (what the bucket's number index answers:
;     fn-gidx-nidx-number-article-is-walk, fn-gidx-find-number-entry-of-built-bucket)
;     is the entry of the newest visible row binding (GROUP . N), when every
;     visible row's Message-ID is a served index key (fn-cat-view-msgids-okp);
;   fn-cat-view-number-article-is-row: the composed number lookup (entry, then
;     the trie) is that row's article when its Message-ID names no newer
;     visible row;
;   fn-cat-view-find-is-msgid-column: the Message-ID walk over the whole
;     catalog is the newest visible seq of the Message-ID column
;     (fn-cat-msgid-seqs, the hash-table read): the served lookup's exec.
; The served machine still reads the lists (step 7 proper threads fn-cat and
; fn-arena through its read path and pins v; PKT-585); this book is the
; abstraction it will be proved against.  The equation of fn-cat-view-articles
; with the replayed archive (fn-own-prefix-archive at v, fn-ctl-visible-state)
; is the R-side obligation of step 8 and is NOT claimed here.

(in-package "ACL2")
(include-book "catalog-relation")
(include-book "group-bucket-article")

; -----------------------------------------------------------------------------
; A row as the acceptance article; the view at a version.

; The pin is the archive pin of an installed article (fn-article-pin = t).
; The records flip (lane served-readers): the article carries the row's
; HANDLE, as the owner's archive does; a served reader reads the bytes through
; the arena (books/nntp-session.lisp fn-nntp-article-bytes), so no view read
; materializes a payload and the view's articles can equal the archive's.
(defun fn-cat-row-article (seq fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp seq) (< seq (fn-cat-count fn-cat))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable fn-arena))
  (let ((h (fn-cat-at seq fn-cat)))
    (fn-make-article (fn-record-msgid h)
                     (fn-record-payload h)
                     (fn-record-groups h)
                     (fn-held-numbers h)
                     t
                     (fn-record-stamp h))))

(verify-guards fn-cat-row-article
  :hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)
           :use ((:instance fn-cat-handles-inp-at (n (fn-cat-count fn-cat)) (seq seq))))))

; The rows below I visible at V, newest first (the archive's order).
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cat-view-below-loop (i v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (and (natp i) (natp v) (<= i (fn-cat-count fn-cat)) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)) (true-listp acc)) :verify-guards nil))
  (if (zp i)
      (revappend acc nil)
    (let ((seq (- i 1)))
      (if (fn-cat-visible-at seq v fn-cat)
          (fn-cat-view-below-loop seq
                                  v
                                  fn-arena
                                  fn-cat
                                  (cons (fn-cat-row-article seq fn-arena fn-cat) acc))
        (fn-cat-view-below-loop seq v fn-arena fn-cat acc)))))

(defun fn-cat-view-below (i v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (mbe :logic
       (if (zp i)
           nil
         (let ((seq (- i 1)))
           (if (fn-cat-visible-at seq v fn-cat)
               (cons (fn-cat-row-article seq fn-arena fn-cat)
                     (fn-cat-view-below seq v fn-arena fn-cat))
             (fn-cat-view-below seq v fn-arena fn-cat))))
       :exec (fn-cat-view-below-loop i v fn-arena fn-cat nil)))

(local
 (defthm fn-cat-view-below-loop-is-revappend
   (equal (fn-cat-view-below-loop i v fn-arena fn-cat acc)
          (revappend acc (fn-cat-view-below i v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-cat-view-below-loop i v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-cat-view-below-loop fn-cat-view-below revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))


(verify-guards fn-cat-view-below-loop
  :hints (("Goal"
           :in-theory
           (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth))))

(verify-guards fn-cat-view-below
  :hints (("Goal"
           :in-theory
           (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)
           :use
           ((:instance fn-cat-view-below-loop-is-revappend (acc nil))))))

(defun fn-cat-view-articles (v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (fn-cat-view-below (fn-cat-count fn-cat) v fn-arena fn-cat))

; -----------------------------------------------------------------------------
; The two walks over the visible rows (what the columns answer).

; The newest visible row below I bound to MSGID, or nil.
(defun fn-cat-view-find (msgid i v fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat)))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (zp i)
      nil
    (let ((seq (- i 1)))
      (if (and (fn-cat-visible-at seq v fn-cat)
               (equal msgid (fn-record-msgid (fn-cat-at seq fn-cat))))
          seq
        (fn-cat-view-find msgid seq v fn-cat)))))

; The newest visible row below I binding (GROUP . N), or nil.
(defun fn-cat-view-number-find (group n i v fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat)))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (zp i)
      nil
    (let ((seq (- i 1)))
      (if (and (fn-cat-visible-at seq v fn-cat)
               (equal n (fn-held-number-in group (fn-cat-at seq fn-cat))))
          seq
        (fn-cat-view-number-find group n seq v fn-cat)))))

; Every row below I visible at V has a Message-ID that is a served index key
; (fn-nntp-index-msgid-okp, books/nntp-index-runtime.lisp): the test
; fn-nntp-index-entry-available runs per entry today; it is decided once at
; intern after the slice.
(defun fn-cat-view-msgids-okp (i v fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat)))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (zp i)
      t
    (let ((seq (- i 1)))
      (and (or (not (fn-cat-visible-at seq v fn-cat))
               (fn-nntp-index-msgid-okp (fn-record-msgid (fn-cat-at seq fn-cat))))
           (fn-cat-view-msgids-okp seq v fn-cat)))))

; The row article's projections (the fn-defrecord accessors over fn-make-article).
(defthm fn-cat-row-article-msgid
  (equal (fn-article-msgid (fn-cat-row-article seq fn-arena fn-cat))
         (fn-record-msgid (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))

(defthm fn-cat-row-article-memberships
  (equal (fn-article-memberships (fn-cat-row-article seq fn-arena fn-cat))
         (fn-held-numbers (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))

(defthm fn-cat-row-article-payload
  (equal (fn-article-payload (fn-cat-row-article seq fn-arena fn-cat))
         (fn-record-payload (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))

; -----------------------------------------------------------------------------
; KEYSTONE 1: the Message-ID lookup over the view is the walk.

(defthm fn-cat-view-find-article-is-walk
  (equal (fn-find-article msgid (fn-cat-view-below i v fn-arena fn-cat))
         (let ((seq (fn-cat-view-find msgid i v fn-cat)))
           (if seq (fn-cat-row-article seq fn-arena fn-cat) nil)))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-find-article) (fn-cat-row-article fn-cat-visible-at)))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: the number lookup's entry over the view is the walk.

; (GROUP . N) among a row's numbers, tested as the entry walk tests it.
(defun fn-cat-numbers-bind (group n pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (or (and (equal group (fn-ag-car (fn-ag-car pairs)))
               (equal n (fn-ag-cdr (fn-ag-car pairs))))
          (fn-cat-numbers-bind group n (cdr pairs)))
    nil))

; The newest visible row below I whose numbers bind (GROUP . N), or nil.
(defun fn-cat-view-bound-find (group n i v fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat)))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (if (zp i)
      nil
    (let ((seq (- i 1)))
      (if (and (fn-cat-visible-at seq v fn-cat)
               (fn-cat-numbers-bind group n (fn-held-numbers (fn-cat-at seq fn-cat))))
          seq
        (fn-cat-view-bound-find group n seq v fn-cat)))))

; One article's entries: the walk finds (GROUP . N) among its memberships
; when N is a served number and the Message-ID is a served index key.
(defthm fn-cat-find-number-entry-of-membership-entries
  (implies (and (posp n) (<= n *fn-nntp-max-article-number*)
                (fn-nntp-index-msgid-okp msgid))
           (equal (fn-gidx-find-number-entry group n (fn-index-membership-entries msgid pairs))
                  (if (fn-cat-numbers-bind group n pairs)
                      (fn-index-entry group n msgid)
                    nil)))
  :hints (("Goal" :induct (fn-index-membership-entries msgid pairs)
           :in-theory (e/d (fn-index-membership-entries fn-gidx-find-number-entry
                            fn-nntp-index-entry-available fn-index-entry
                            fn-index-entry-group fn-index-entry-number fn-index-entry-msgid)
                           (fn-nntp-index-msgid-okp)))))

(defthm fn-cat-find-number-entry-of-nil
  (equal (fn-gidx-find-number-entry group n nil) nil))

(defthm fn-cat-view-number-entry-is-walk
  (implies (and (posp n) (<= n *fn-nntp-max-article-number*)
                (fn-cat-view-msgids-okp i v fn-cat))
           (equal (fn-gidx-find-number-entry
                   group n (fn-index-build (fn-cat-view-below i v fn-arena fn-cat)))
                  (let ((seq (fn-cat-view-bound-find group n i v fn-cat)))
                    (if seq
                        (fn-index-entry group n (fn-record-msgid (fn-cat-at seq fn-cat)))
                      nil))))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-index-build fn-index-article-entries)
                           (fn-cat-row-article fn-cat-visible-at fn-nntp-index-msgid-okp
                            fn-index-entry fn-gidx-find-number-entry
                            fn-index-membership-entries fn-cat-numbers-bind)))))

; -----------------------------------------------------------------------------
; KEYSTONE 3: the composed number lookup (the entry, then the trie) is the
; bound row's article when its Message-ID names no newer visible row.

; The bound row is visible below I, so its Message-ID is a served index key,
; hence a string (the trie keystone's hypothesis).
(defthm fn-cat-view-bound-find-msgid-okp
  (implies (and (fn-cat-view-msgids-okp i v fn-cat)
                (fn-cat-view-bound-find group n i v fn-cat))
           (fn-nntp-index-msgid-okp
            (fn-record-msgid (fn-cat-at (fn-cat-view-bound-find group n i v fn-cat) fn-cat))))
  :hints (("Goal" :induct (fn-cat-view-bound-find group n i v fn-cat)
           :in-theory (disable fn-nntp-index-msgid-okp fn-cat-visible-at fn-cat-numbers-bind))))

(defthm fn-nntp-index-msgid-okp-stringp
  (implies (fn-nntp-index-msgid-okp x) (stringp x))
  :hints (("Goal" :in-theory (enable fn-nntp-index-msgid-okp)))
  :rule-classes ((:forward-chaining) (:rewrite)))

(defthm fn-cat-view-number-article-is-row
  (implies (and (posp n) (<= n *fn-nntp-max-article-number*)
                (fn-cat-view-msgids-okp i v fn-cat)
                (fn-midx-string-article-listp (fn-cat-view-below i v fn-arena fn-cat))
                (fn-cat-view-bound-find group n i v fn-cat)
                (equal (fn-cat-view-find
                        (fn-record-msgid (fn-cat-at (fn-cat-view-bound-find group n i v fn-cat) fn-cat))
                        i v fn-cat)
                       (fn-cat-view-bound-find group n i v fn-cat)))
           (equal (fn-gidx-entry-number-article
                   group n
                   (fn-index-build (fn-cat-view-below i v fn-arena fn-cat))
                   (fn-midx-build (fn-cat-view-below i v fn-arena fn-cat)))
                  (fn-cat-row-article (fn-cat-view-bound-find group n i v fn-cat) fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-gidx-entry-number-article fn-index-entry fn-index-entry-msgid)
                                  (fn-cat-row-article fn-cat-visible-at fn-nntp-index-msgid-okp
                                   fn-cat-view-below fn-cat-view-find fn-cat-view-bound-find
                                   fn-index-build fn-midx-build fn-find-article
                                   fn-cat-view-msgids-okp fn-midx-string-article-listp))
           :use ((:instance fn-cat-view-bound-find-msgid-okp)
                 (:instance fn-midx-lookup-of-build-is-find-article
                            (msgid (fn-record-msgid (fn-cat-at (fn-cat-view-bound-find group n i v fn-cat) fn-cat)))
                            (articles (fn-cat-view-below i v fn-arena fn-cat)))))))

; -----------------------------------------------------------------------------
; KEYSTONE 4: the Message-ID walk is the column.  The served lookup's exec is
; the Message-ID table's list (fn-cat-msgid-seqs: the hash-table read) walked
; for its newest visible seq, never the rows.

; The newest visible seq of an ascending list of seqs, or nil.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-cat-view-last-visible-loop (rev v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (natp v) :verify-guards nil))
  (if (consp rev)
      (fn-cat-view-last-visible-loop (cdr rev)
                                     v
                                     fn-cat
                                     (let ((rest acc))
                                       (if rest
                                           rest
                                         (let ((seq (car rev)))
                                           (if (and (natp seq)
                                                    (< seq (fn-cat-count fn-cat))
                                                    (fn-cat-visible-at seq v fn-cat))
                                               seq
                                             nil)))))
    acc))

(defun fn-cat-view-last-visible (seqs v fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)))))
  (mbe :logic
       (if (consp seqs)
           (let ((rest (fn-cat-view-last-visible (cdr seqs) v fn-cat)))
             (if rest
                 rest
               (let ((seq (car seqs)))
                 (if (and (natp seq) (< seq (fn-cat-count fn-cat)) (fn-cat-visible-at seq v fn-cat))
                     seq
                   nil))))
         nil)
       :exec (fn-cat-view-last-visible-loop (fn-ag-rev-onto seqs nil) v fn-cat nil)))

(local
 (defthm fn-cat-view-last-visible-loop-of-rev-onto
   (equal (fn-cat-view-last-visible-loop (fn-ag-rev-onto seqs zs) v fn-cat nil)
          (fn-cat-view-last-visible-loop zs v fn-cat (fn-cat-view-last-visible seqs v fn-cat)))
   :hints (("Goal" :induct (fn-ag-rev-onto seqs zs)
                   :in-theory (union-theories '(fn-cat-view-last-visible-loop fn-cat-view-last-visible fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cat-view-last-visible-loop
  :hints (("Goal"
           :in-theory
           (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth))))

(verify-guards fn-cat-view-last-visible
  :hints (("Goal" :in-theory (union-theories '(fn-cat-view-last-visible fn-cat-view-last-visible-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-cat-view-last-visible-loop-of-rev-onto (zs nil))))))


(defthm fn-cat-view-last-visible-of-append
  (equal (fn-cat-view-last-visible (append a b) v fn-cat)
         (or (fn-cat-view-last-visible b v fn-cat) (fn-cat-view-last-visible a v fn-cat))))

; The matching positions in [K, I), ascending: the bridge between the
; descending walk and fn-cat-seqs-for (books/catalog.lisp), which ascends.
(local (defun fn-cvl-range (msgid k i c)
  (declare (xargs :measure (nfix (- i (nfix k)))))
  (if (or (not (natp k)) (not (natp i)) (>= k i))
      nil
    (append (if (equal msgid (fn-record-msgid (nth k c))) (list k) nil)
            (fn-cvl-range msgid (+ 1 k) i c)))))

(local (defthm fn-cvl-append-assoc
  (equal (append (append a b) d) (append a (append b d)))))

(local (defthm fn-cvl-range-empty
  (implies (<= (nfix i) (nfix k))
           (equal (fn-cvl-range msgid k i c) nil))
  :hints (("Goal" :expand ((fn-cvl-range msgid k i c))))))

(local (defthm fn-cvl-range-split-top
  (implies (and (natp k) (natp i) (< k i))
           (equal (fn-cvl-range msgid k i c)
                  (append (fn-cvl-range msgid k (+ -1 i) c)
                          (if (equal msgid (fn-record-msgid (nth (+ -1 i) c))) (list (+ -1 i)) nil))))
  :hints (("Goal" :induct (fn-cvl-range msgid k i c)
           :in-theory (disable floor nonnegative-integer-quotient)))))

(local (defthm fn-cvl-view-find-is-range
  (implies (and (natp i) (<= i (fn-cat-count fn-cat)))
           (equal (fn-cat-view-find msgid i v fn-cat)
                  (fn-cat-view-last-visible (fn-cvl-range msgid 0 i fn-cat) v fn-cat)))
  :hints (("Goal" :induct (fn-cat-view-find msgid i v fn-cat)
           :in-theory (disable fn-cat-visible-at)))))

(local (defthm fn-cvl-nthcdr-open
  (implies (and (natp k) (< k (len c)))
           (equal (nthcdr k c) (cons (nth k c) (nthcdr (+ 1 k) c))))))

(local (defthm fn-cvl-nthcdr-beyond
  (implies (and (natp k) (<= (len c) k))
           (not (consp (nthcdr k c))))))

(local (defthm fn-cvl-range-is-seqs-for
  (implies (natp k)
           (equal (fn-cvl-range msgid k (len c) c)
                  (fn-cat-seqs-for msgid (nthcdr k c) k)))
  :hints (("Goal" :induct (fn-cvl-range msgid k (len c) c)
           :in-theory (disable fn-cvl-range-split-top nthcdr)))))

(defthm fn-cat-view-find-is-msgid-column
  (equal (fn-cat-view-find msgid (fn-cat-count fn-cat) v fn-cat)
         (fn-cat-view-last-visible (fn-cat-msgid-seqs msgid fn-cat) v fn-cat))
  :hints (("Goal" :in-theory (disable fn-cat-view-find fn-cat-view-last-visible fn-cvl-range-split-top)
           :use ((:instance fn-cvl-view-find-is-range (i (fn-cat-count fn-cat)))
                 (:instance fn-cvl-range-is-seqs-for (k 0) (c fn-cat))))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-nntp-index-msgid-okp-stringp)))
