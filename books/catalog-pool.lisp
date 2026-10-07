; fn: catalog reads bounded by a frame pool (lane s-pool, 2026-10-07; Phase 2b
; of build/coordinator/STORAGE-PROGRAM-20261006.md, section 3.4).
;
; The catalog's persisted image is two tapes (books/catalog-pages.lisp,
; books/def-representation-pages.lisp): the fn-crow rows (fn-pck-cat-pages h)
; and their DIRECTORY (fn-crow-dir-pages-of, books/def-representation-pageread
; .lisp), one (word offset, width) record per row, so row I is found by
; reading directory record I and then the row's own words -- two reads
; through the one page pool, never a scan.  The reader answers the page
; store's verdict (:need-page) itself: fill the page, read the same word
; again (adt-pr-read-words); progress is kept, so a row of more pages than the
; pool has frames still completes.
;
; What the library proves once over a schema (def-representation-pageread):
; the indexed read gives row I of the sequence, whatever the pool holds
; (adt-pr-read-indexed-is-nth); it fills at most 3 + the row's pages (the
; directory entry takes 2, the row its pages and the one it may straddle:
; adt-pr-read-indexed-fills); a fill never takes the pool past its frame
; count (adt-pr-read-indexed-residency).  This book is the catalog's part:
; the msgid and number tests, and the composition with the existing indexes.
;
; STATEMENTS.  H a catalog, PAGES = (fn-pck-cat-pages h), DPAGES =
; (fn-crow-dir-pages-of (fn-pck-crow-rows h)), CNT = (len h).  P:
; (fn-cat-rowsp h), (fn-pck-carriedp h), (fn-cpg-tape-ok h) -- the tape is
; below 2^64 words, so every offset is a u64.
;
; 1 fn-cpg-msgid-seqs-of-pages: the candidates are the msgid index's own
;   lookup, (fn-mlh-candidates (fn-mlh-tag-of msgid fn-mlh) fn-mlh), and the
;   mlh is the faithful index of the rows (the invariant the stobj carries):
;   (nth 0 reader) = (fn-cat$a-msgid-seqs msgid h).
; 2 fn-cpg-group-number-of-pages: CAND is the dense map's lookup
;   (fn-cat$p-group-number group n fn-cat$p) under (fn-cat$pcorr fn-cat$p h):
;   (nth 0 reader) = (fn-cat$a-group-number group n h).  The row read through
;   the pool confirms the number; (:index-mismatch CAND) is the corrupt-index
;   verdict and is never the answer under the correspondence.
; 3 fn-cpg-msgid-seqs-fills, fn-cpg-group-number-fills: the pages filled are
;   at most (fn-cpg-bound cands h), the sum over the candidates of
;   3 + (fn-crow-pool-pages-of-row row): no term in (len h).
; 4 fn-cpg-msgid-seqs-residency, fn-cpg-group-number-residency: from a pool
;   within its frames the pool stays within (adt-pr-cap frames).
;
; Owed (not here): CPG-TABLE-FILLS (the page store's :need-table fills, an
; additive constant); CPG-POOL-LEDGER (eviction of a frame the ledger allows);
; CPG-MSGID-SCAN (the degraded all-rows scan when the mlh has unplaced rows);
; CPG-DMAP-PAGED, CPG-MLH-PAGED (the indexes read through the pool too);
; the directory's persistence in the catalog root and its commit delta
; (an append of one record) belong with PCK-ADOPT, and a withdrawal that
; ESCAPES a row shifts the later offsets (PCK-ADOPT-ESCAPED's widening).

(in-package "ACL2")
(include-book "catalog-pages")
(include-book "def-representation-pageread")

(defun fn-cpg-tape-ok (h)
  (declare (xargs :guard t :verify-guards nil))
  (< (len (adt-tp-seq-words *fn-crow-schema* (fn-pck-crow-rows h))) (expt 2 64)))

; The directory tape of the catalog's rows.
(defun fn-cpg-dir-pages (h)
  (declare (xargs :guard t :verify-guards nil))
  (fn-crow-dir-pages-of (fn-pck-crow-rows h)))

; A crow row carries MSGID (the held row it decodes to does).
(defun fn-cpg-hitp (msgid row)
  (declare (xargs :guard t :verify-guards nil))
  (equal msgid (fn-record-msgid (fn-cp-row-held row))))

; The candidates whose row, read through the pool, carries MSGID: the
; (mv seqs res fills) of the old fn-cat$p-confirm, over the pages.
(defun fn-cpg-msgid-loop (msgid cands cnt dpages rpages res frames fills acc)
  (declare (xargs :guard (and (nat-listp cands) (natp cnt)) :verify-guards nil))
  (if (consp cands)
      (if (< (car cands) cnt)
          (mv-let (row res fills) (fn-crow-read-indexed (car cands) dpages rpages res frames fills)
            (if (fn-cpg-hitp msgid row)
                (fn-cpg-msgid-loop msgid (cdr cands) cnt dpages rpages res frames fills (cons (car cands) acc))
              (fn-cpg-msgid-loop msgid (cdr cands) cnt dpages rpages res frames fills acc)))
        (fn-cpg-msgid-loop msgid (cdr cands) cnt dpages rpages res frames fills acc))
    (mv (reverse acc) res fills)))

; (list seqs res fills)
(defun fn-cpg-msgid-seqs (msgid cands cnt dpages rpages res frames)
  (declare (xargs :guard (and (nat-listp cands) (natp cnt)) :verify-guards nil))
  (mv-let (seqs res fills) (fn-cpg-msgid-loop msgid cands cnt dpages rpages res frames nil nil)
    (list seqs res fills)))

; (list answer res fills), CAND the dense map's answer (nil or a seq): CAND,
; nil, or (:index-mismatch CAND).
(defun fn-cpg-group-number (group n cand cnt dpages rpages res frames)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((null cand) (list nil res nil))
        ((not (and (natp cand) (< cand (nfix cnt)))) (list (list :index-mismatch cand) res nil))
        (t (mv-let (row res fills) (fn-crow-read-indexed cand dpages rpages res frames nil)
             (let ((b (fn-held-number-in group (fn-cp-row-held row))))
               (if (and b (equal b n))
                   (list cand res fills)
                 (list (list :index-mismatch cand) res fills)))))))

; The pages-touched bound.
(defun fn-cpg-bound (cands h)
  (declare (xargs :guard (nat-listp cands) :verify-guards nil))
  (if (consp cands)
      (+ (if (< (car cands) (len h))
             (+ 3 (fn-crow-pool-pages-of-row (fn-cp-row-of (nth (car cands) h))))
           0)
         (fn-cpg-bound (cdr cands) h))
    0))

; -----------------------------------------------------------------------------
; The row read through the pool is the catalog's row.

(local
 (defthm fn-cpg-carried-nth
   (implies (and (fn-pck-carriedp h) (natp i) (< i (len h)))
            (not (fn-cp-overflow-of (nth i h))))
   :hints (("Goal" :in-theory (enable nth) :induct (nth i h)))))

(local
 (defthm fn-cpg-held-of-row-of
   (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (natp i) (< i (len h)))
            (equal (fn-cp-row-held (fn-cp-row-of (nth i h))) (nth i h)))
   :hints (("Goal" :use ((:instance fn-pck-row-held-of-carried-row (x (nth i h)))
                         fn-cpg-carried-nth
                         (:instance fn-cat-rowp-of-nth-of-rowsp (xs h)))
            :in-theory (disable fn-pck-row-held-of-carried-row fn-cpg-carried-nth fn-cat-rowp-of-nth-of-rowsp
                                fn-cp-row-of fn-cp-row-held fn-cp-overflow-of fn-cat-rowp)))))

(defthm fn-cpg-read-row-is-nth
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h) (natp i) (< i (len h)))
           (equal (mv-nth 0 (fn-crow-read-indexed i (fn-cpg-dir-pages h) (fn-pck-cat-pages h) res frames fills))
                  (fn-cp-row-of (nth i h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-crow-read-indexed-is-nth (a (fn-pck-crow-rows h)))
                 fn-pck-crow-rows-ap
                 (:instance fn-pck-nth-crow-rows))
           :in-theory (e/d (fn-cpg-tape-ok fn-cpg-dir-pages fn-pck-cat-pages)
                           (fn-crow-read-indexed-is-nth fn-pck-crow-rows-ap fn-pck-nth-crow-rows
                            fn-pck-crow-rows fn-cp-row-of fn-crow-read-indexed fn-crow-dir-pages-of
                            fn-crow-pages-of)))))

(defthm fn-cpg-read-row-held
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h) (natp i) (< i (len h)))
           (equal (fn-cp-row-held (mv-nth 0 (fn-crow-read-indexed i (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                                                  res frames fills)))
                  (nth i h)))
  :hints (("Goal" :in-theory (disable fn-cp-row-of fn-cp-row-held fn-crow-read-indexed fn-cpg-dir-pages
                                      fn-pck-cat-pages fn-cpg-tape-ok))))

; -----------------------------------------------------------------------------
; 1. The Message-ID reader over the pages is the confirmation of its candidates.

(defthm fn-cpg-msgid-loop-is-confirm
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h)
                (nat-listp cands) (fn-mpx-below-p cands (len h)) (true-listp acc))
           (equal (mv-nth 0 (fn-cpg-msgid-loop msgid cands (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                               res frames fills acc))
                  (revappend acc (fn-mpxt-confirm msgid cands h))))
  :hints (("Goal" :induct (fn-cpg-msgid-loop msgid cands (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                             res frames fills acc)
           :in-theory (e/d (fn-mpxt-hitp fn-mpx-below-p fn-cpg-hitp)
                           (fn-cp-row-held fn-cp-row-of fn-cp-escapedp fn-cp-smallp fn-cp-tree-of
                            fn-crow-read-indexed fn-cpg-dir-pages fn-pck-cat-pages fn-cpg-tape-ok
                            mv-nth)))))

(local
 (defthm fn-cpg-tag-of-posp
   (posp (fn-mlh-tag-of msgid fn-mlh))
   :hints (("Goal" :in-theory (enable fn-mlh-tag-of)))
   :rule-classes nil))

(defthm fn-cpg-msgid-seqs-of-pages
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h)
                (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (fn-mlh-faithful h fn-mlh))
           (equal (nth 0 (fn-cpg-msgid-seqs msgid (fn-mlh-candidates (fn-mlh-tag-of msgid fn-mlh) fn-mlh)
                                            (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h) res frames))
                  (fn-cat$a-msgid-seqs msgid h)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpg-msgid-loop-is-confirm (acc nil) (fills nil)
                            (cands (fn-mlh-candidates (fn-mlh-tag-of msgid fn-mlh) fn-mlh)))
                 (:instance fn-mlh-seqs-is-cat-msgid-seqs (fn-cat$a h))
                 (:instance fn-mlh-candidates-below (tag (fn-mlh-tag-of msgid fn-mlh)) (n (len h)))
                 (:instance fn-mlh-candidates-nat-listp (tag (fn-mlh-tag-of msgid fn-mlh)))
                 (:instance fn-cpg-tag-of-posp))
           :in-theory (union-theories '(fn-cpg-msgid-seqs fn-mlh-seqs fn-mlh-faithful (:definition mv-nth)
                                        (:definition revappend) (:executable-counterpart true-listp)
                                        (:definition nth) (:executable-counterpart zp) (:rewrite car-cons) (:rewrite cdr-cons))
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 3, 4. Pages touched and residency of the Message-ID reader.

(defthm fn-cpg-read-row-fills
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h) (natp i) (< i (len h)))
           (<= (len (mv-nth 2 (fn-crow-read-indexed i (fn-cpg-dir-pages h) (fn-pck-cat-pages h) res frames fills)))
               (+ (len fills) 3 (fn-crow-pool-pages-of-row (fn-cp-row-of (nth i h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-crow-read-indexed-fills (a (fn-pck-crow-rows h)))
                 fn-pck-crow-rows-ap
                 (:instance fn-pck-nth-crow-rows))
           :in-theory (e/d (fn-cpg-tape-ok fn-cpg-dir-pages fn-pck-cat-pages)
                           (fn-crow-read-indexed-fills fn-pck-crow-rows-ap fn-pck-nth-crow-rows
                            fn-pck-crow-rows fn-cp-row-of fn-crow-read-indexed fn-crow-dir-pages-of
                            fn-crow-pages-of)))))

(defthm fn-cpg-msgid-loop-fills
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h) (nat-listp cands))
           (<= (len (mv-nth 2 (fn-cpg-msgid-loop msgid cands (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                                 res frames fills acc)))
               (+ (len fills) (fn-cpg-bound cands h))))
  :hints (("Goal" :induct (fn-cpg-msgid-loop msgid cands (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                             res frames fills acc)
           :in-theory (e/d (fn-cpg-bound)
                           (fn-cp-row-held fn-cp-row-of fn-crow-read-indexed fn-cpg-dir-pages fn-pck-cat-pages
                            fn-cpg-tape-ok mv-nth fn-crow-pool-pages-of-row fn-cpg-hitp)))
          ("Subgoal *1/3" :use ((:instance fn-cpg-read-row-fills (i (car cands)))))
          ("Subgoal *1/2" :use ((:instance fn-cpg-read-row-fills (i (car cands)))))
          ("Subgoal *1/1" :use ((:instance fn-cpg-read-row-fills (i (car cands)))))))

(defthm fn-cpg-msgid-loop-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (mv-nth 1 (fn-cpg-msgid-loop msgid cands cnt dpages rpages res frames fills acc)))
               (adt-pr-cap frames)))
  :hints (("Goal" :induct (fn-cpg-msgid-loop msgid cands cnt dpages rpages res frames fills acc)
           :in-theory (e/d () (fn-cp-row-held fn-crow-read-indexed mv-nth adt-pr-cap)))))

(defthm fn-cpg-msgid-seqs-fills
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h) (nat-listp cands))
           (<= (len (nth 2 (fn-cpg-msgid-seqs msgid cands (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h) res frames)))
               (fn-cpg-bound cands h)))
  :hints (("Goal" :use ((:instance fn-cpg-msgid-loop-fills (fills nil) (acc nil)))
           :in-theory (union-theories '(fn-cpg-msgid-seqs (:definition mv-nth) (:definition nth) (:executable-counterpart zp)
                                        (:rewrite car-cons) (:rewrite cdr-cons) (:executable-counterpart len)
                                        (:definition len))
                                      (theory 'minimal-theory)))))

(defthm fn-cpg-msgid-seqs-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (nth 1 (fn-cpg-msgid-seqs msgid cands cnt dpages rpages res frames)))
               (adt-pr-cap frames)))
  :hints (("Goal" :use ((:instance fn-cpg-msgid-loop-residency (fills nil) (acc nil)))
           :in-theory (union-theories '(fn-cpg-msgid-seqs (:definition mv-nth) (:definition nth) (:executable-counterpart zp)
                                        (:rewrite car-cons) (:rewrite cdr-cons))
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 2. The (group . number) reader over the pages.

(local
 (defthm fn-cpg-number-seq-sound
   (implies (and (natp i) (equal k (fn-cat-number-seq g n c i)) k)
            (and (natp k) (<= i k) (< k (+ i (len c)))
                 (fn-held-number-in g (nth (- k i) c))
                 (equal (fn-held-number-in g (nth (- k i) c)) n)))
   :hints (("Goal" :induct (fn-cat-number-seq g n c i)
            :in-theory (enable fn-cat-number-seq)))))

(defthm fn-cpg-group-number-core
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h)
                (equal cand (fn-cat$a-group-number group n h)))
           (equal (nth 0 (fn-cpg-group-number group n cand (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                              res frames))
                  (fn-cat$a-group-number group n h)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpg-number-seq-sound (i 0) (k cand) (g group) (c h))
                 (:instance fn-cpg-read-row-held (i cand) (fills nil)))
           :in-theory (e/d (fn-cpg-group-number fn-cat$a-group-number)
                           (fn-cpg-number-seq-sound fn-cpg-read-row-held fn-cat-number-seq
                            fn-cp-row-held fn-crow-read-indexed fn-cpg-dir-pages fn-pck-cat-pages
                            fn-cpg-tape-ok mv-nth fn-cp-row-of)))))

; The dense map's own lookup, composed with the stobj correspondence the
; paged catalog already proves (fn-cat-paged-group-number{correspondence}).
(defthm fn-cpg-group-number-of-pages
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h)
                (fn-cat$pcorr fn-cat$p h))
           (equal (nth 0 (fn-cpg-group-number group n (fn-cat$p-group-number group n fn-cat$p)
                                              (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h) res frames))
                  (fn-cat$a-group-number group n h)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-paged-group-number{correspondence} (fn-cat-paged h))
                 (:instance fn-cpg-group-number-core (cand (fn-cat$p-group-number group n fn-cat$p))))
           :in-theory (disable fn-cpg-group-number-core
                               fn-cpg-group-number fn-cpg-dir-pages fn-pck-cat-pages fn-cpg-tape-ok
                               fn-cat$p-group-number fn-cat$a-group-number))))

(defthm fn-cpg-group-number-fills
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (fn-cpg-tape-ok h))
           (<= (len (nth 2 (fn-cpg-group-number group n cand (len h) (fn-cpg-dir-pages h) (fn-pck-cat-pages h)
                                                res frames)))
               (fn-cpg-bound (if cand (list cand) nil) h)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpg-read-row-fills (i cand) (fills nil)))
           :in-theory (e/d (fn-cpg-group-number fn-cpg-bound)
                           (fn-cpg-read-row-fills fn-cp-row-held fn-crow-read-indexed fn-cpg-dir-pages
                            fn-pck-cat-pages fn-cpg-tape-ok mv-nth fn-cp-row-of fn-crow-pool-pages-of-row)))))

(defthm fn-cpg-group-number-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (nth 1 (fn-cpg-group-number group n cand cnt dpages rpages res frames)))
               (adt-pr-cap frames)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-crow-read-indexed-residency (i cand) (fills nil)))
           :in-theory (e/d (fn-cpg-group-number)
                           (fn-crow-read-indexed-residency fn-cp-row-held fn-crow-read-indexed mv-nth adt-pr-cap)))))
