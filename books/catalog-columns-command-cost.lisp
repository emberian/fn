; Execution-derived command costs over dense per-group number runs.
(in-package "ACL2")
(include-book "catalog-columns-command-reads")
(include-book "store-tree-codec")
(include-book "def-cost")

(def-cost fn-lbc-command-row
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((row-fetches (fn-lbc-render-nov))
         (probes (fn-lbc-number-get))
         (number-reads (fn-lbc-number-get))
         (summary-reads (fn-lbc-live-summary))
         (decodes (fn-scc-decode-tree))))

(def-cost fn-lbc-over-loop
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-render-nov fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((row-fetches (fn-lbc-render-nov))
         (probes (fn-lbc-number-get))
         (summary-reads (fn-lbc-live-summary))
         (decodes (fn-scc-decode-tree))))

(def-cost fn-lbc-over
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-render-nov fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((row-fetches (fn-lbc-render-nov))
         (probes (fn-lbc-number-get))
         (summary-reads (fn-lbc-live-summary))
         (decodes (fn-scc-decode-tree))))

(def-cost fn-lbc-list-loop
 :unaccounted ()
 :calls ((row-fetches (fn-lbc-render-nov))
         (probes (fn-lbc-number-get))
         (summary-reads (fn-lbc-live-summary))
         (decodes (fn-scc-decode-tree))))

(def-cost fn-lbc-list
 :unaccounted ()
 :calls ((row-fetches (fn-lbc-render-nov))
         (probes (fn-lbc-number-get))
         (summary-reads (fn-lbc-live-summary))
         (decodes (fn-scc-decode-tree))))

(defthm fn-lbc-command-row-zero-row-fetches
 (equal (fn-lbc-command-row-row-fetches group number v fn-lbc-v) 0)
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-command-row-row-fetches)))))

(defthm fn-lbc-command-row-one-probe
 (equal (fn-lbc-command-row-probes group number v fn-lbc-v) 1)
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-command-row-probes)))))

(defthm fn-lbc-over-loop-fetches-eligible
 (equal (fn-lbc-over-loop-row-fetches group v lo hi fn-lbc-v acc) (len (fn-lbc-over-eligible group v lo hi fn-lbc-v)))
 :hints (("Goal" :induct (fn-lbc-over-loop-row-fetches group v lo hi fn-lbc-v acc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-over-loop-row-fetches fn-lbc-over-eligible fn-lbc-command-row-zero-row-fetches len natp nfix)))))

(defthm fn-lbc-over-fetches-exactly-eligible
 (equal (fn-lbc-over-row-fetches group v lo hi fn-lbc-v) (len (fn-lbc-over-eligible group v lo hi fn-lbc-v)))
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-over-row-fetches fn-lbc-over-loop-fetches-eligible)))))

(defthm fn-lbc-over-loop-probes-exact-range
 (implies (and (natp lo) (natp hi)) (equal (fn-lbc-over-loop-probes group v lo hi fn-lbc-v acc) (nfix (+ 1 (- hi lo)))))
 :hints (("Goal" :induct (fn-lbc-over-loop-probes group v lo hi fn-lbc-v acc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-over-loop-probes fn-lbc-command-row-one-probe natp nfix)))))

(local (defthm fn-lbcc-over-probes-at-most-typed-range
 (implies (and (natp lo) (natp hi) (<= lo hi)) (<= (fn-lbc-over-probes group v lo hi fn-lbc-v) (+ 1 (- hi lo))))
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-over-probes fn-lbc-over-loop-probes-exact-range natp nfix))))))

; Endpoint types are redundant: a non-natural endpoint performs no probes.
(defthm fn-lbc-over-probes-at-most-range
 (implies (<= lo hi)
  (<= (fn-lbc-over-probes group v lo hi fn-lbc-v) (+ 1 (- hi lo))))
 :hints (("Goal" :cases ((and (natp lo) (natp hi)))
  :use fn-lbcc-over-probes-at-most-typed-range
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-over-probes fn-lbc-over-loop-probes natp nfix)))))

(defthm fn-lbc-list-loop-exact-summary-reads
 (equal (fn-lbc-list-loop-summary-reads groups fn-lbc-v acc) (len groups))
 :hints (("Goal" :induct (fn-lbc-list-loop-summary-reads groups fn-lbc-v acc)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-list-loop-summary-reads len)))))

(defthm fn-lbc-list-exact-summary-reads
 (equal (fn-lbc-list-summary-reads groups fn-lbc-v) (len groups))
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-list-summary-reads fn-lbc-list-loop-exact-summary-reads)))))

(defthm fn-lbc-list-zero-decodes
 (equal (fn-lbc-list-decodes groups fn-lbc-v) 0)
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-list-decodes)))))

(defthm fn-lbc-list-zero-row-fetches
 (equal (fn-lbc-list-row-fetches groups fn-lbc-v) 0)
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-list-row-fetches)))))

(defthm fn-lbc-over-zero-decodes
 (equal (fn-lbc-over-decodes group v lo hi fn-lbc-v) 0)
 :hints (("Goal" 
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-over-decodes)))))

(def-cost fn-lbc-group-live
 :calls ((row-fetches (fn-lbc-render-nov)) (decodes (fn-scc-decode-tree))
         (summary-reads (fn-lbc-live-summary))))
(defthm fn-lbc-group-live-zero-row-fetches
 (equal (fn-lbc-group-live-row-fetches group fn-lbc-v) 0)
 :hints (("Goal" :in-theory '(fn-lbc-group-live-row-fetches))))
(defthm fn-lbc-group-live-zero-decodes
 (equal (fn-lbc-group-live-decodes group fn-lbc-v) 0)
 :hints (("Goal" :in-theory '(fn-lbc-group-live-decodes))))
(defthm fn-lbc-group-live-one-summary-read
 (equal (fn-lbc-group-live-summary-reads group fn-lbc-v) 1)
 :hints (("Goal" :in-theory '(fn-lbc-group-live-summary-reads))))

(def-cost-check fn-lbc-command-row)
(def-cost-check fn-lbc-over-loop)
(def-cost-check fn-lbc-over)
(def-cost-check fn-lbc-list-loop)
(def-cost-check fn-lbc-list)
(def-cost-check fn-lbc-group-live)

(def-cost fn-lbc-listgroup-loop
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((number-reads (fn-lbc-number-get))
         (row-fetches (fn-lbc-render-nov)) (decodes (fn-scc-decode-tree))))

(def-cost fn-lbc-listgroup
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((number-reads (fn-lbc-number-get))
         (row-fetches (fn-lbc-render-nov)) (decodes (fn-scc-decode-tree))))

(defthm fn-lbc-command-row-one-number-read
 (equal (fn-lbc-command-row-number-reads group number v fn-lbc-v) 1)
 :hints (("Goal" :in-theory '(fn-lbc-command-row-number-reads))))

(defthm fn-lbc-listgroup-loop-reads-requested-numbers
 (equal (fn-lbc-listgroup-loop-number-reads group v lo hi fn-lbc-v acc)
        (len (fn-lbc-listgroup-numbers group v lo hi fn-lbc-v)))
 :hints (("Goal" :induct (fn-lbc-listgroup-loop-number-reads group v lo hi fn-lbc-v acc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-listgroup-loop-number-reads fn-lbc-listgroup-numbers fn-lbc-listgroup-requested-numbers
     fn-lbc-command-row-one-number-read natp nfix len)))))

; Requested positions include withdrawn rows; fn-lbc-listgroup emits only available numbers.
(defthm fn-lbc-listgroup-number-reads-exact
 (equal (fn-lbc-listgroup-number-reads group v lo hi fn-lbc-v)
        (len (fn-lbc-listgroup-numbers group v lo hi fn-lbc-v)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-listgroup-number-reads fn-lbc-listgroup-loop-reads-requested-numbers)))))

(defthm fn-lbc-listgroup-requested-numbers-view-independent
 (equal (fn-lbc-listgroup-numbers group v lo hi fn-lbc)
        (fn-lbc-listgroup-numbers group live lo hi fn-lbc))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-lbc-listgroup-numbers))))

; The scan performs the V withdrawal check directly. Pinning adds zero number reads,
; so its extra reads are <= |X| for every changed set X, including X=nil.
(defthm fn-lbc-listgroup-pinned-extra-reads-bounded-by-changes
 (<= (- (fn-lbc-listgroup-number-reads group v lo hi fn-lbc-v)
        (fn-lbc-listgroup-number-reads group live lo hi fn-lbc-v)) (len x))
 :hints (("Goal"
  :use ((:instance fn-lbc-listgroup-requested-numbers-view-independent (fn-lbc fn-lbc-v)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-listgroup-number-reads-exact)))))

(defthm fn-lbc-listgroup-zero-row-fetches
 (equal (fn-lbc-listgroup-row-fetches group v lo hi fn-lbc-v) 0)
 :hints (("Goal" :in-theory '(fn-lbc-listgroup-row-fetches))))
(defthm fn-lbc-listgroup-zero-decodes
 (equal (fn-lbc-listgroup-decodes group v lo hi fn-lbc-v) 0)
 :hints (("Goal" :in-theory '(fn-lbc-listgroup-decodes))))
(def-cost-check fn-lbc-listgroup-loop)
(def-cost-check fn-lbc-listgroup)
