; Publishing a sealed leaf or parent extends the same physical page list
; that the range adapter will install, without consuming the pending row.
(in-package "ACL2")
(include-book "range-published-run-contents")
(include-book "runs-builder-page-publication-proof")

(defmacro fn2-range-publishing-page (&rest body)
  `(let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (hrow (+ l (fn2-run-builds-hbase 0 builds)))
          (ctx (fn2-run-seal-context w 0 hrow writers previous-context))
          (page (fn2-run-sealed-address w writers))
          (calls (fn2-run-page-check-calls 70 w writers fc ctx b3 f pool ds))
          (run (fn2-run-sealing-loop calls pages builds writers f fc b3 ds)))
     (declare (ignorable w hrow ctx page calls run))
     ,@body))

(defthmd fn2-range-page-publication-returns-list-and-pool
  (fn2-range-publishing-page
   (implies (and (equal (fn2-run-builds-crow 0 builds) 0)
                 (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                 (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds)
                 (fn2-run-written-page-ready-p w (fn2-run-writers-fields w writers) writers f fc pool))
            (and (posp calls) (<= calls 70) (equal (car run) :fuel)
                 (equal (mv-nth 1 run) (cons page pages)) (equal (mv-nth 9 run) pool)
                 (equal (mv-nth 2 run) (fn2-run-sealed-builds builds))
                 (equal (mv-nth 6 run) (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-builder-publishes-written-page (extra 0)))
           :expand ((:free (pp bb ww ff cc b d ctx)
                           (fn2-run-sealing-loop 0 pp bb ww ff cc b d)))
           :in-theory (union-theories (theory 'minimal-theory)
               '(mv-nth car-cons cdr-cons (:t fn2-run-page-check-calls) commutativity-of-+ unicity-of-0 fix
                 (:e natp) (:e zp) (:e equal) (:e binary-+) (:e mv-nth) (:e consp))))))

(defthmd fn2-range-builder-publishes-represented-rows
  (fn2-range-publishing-page
   (let* ((groups (fn2-range-child-entry-lists children records))
          (covered (if (zp l) rows (append-lst groups)))
          (node (list page rows outer inner covered children)))
     (implies (and (equal (fn2-run-builds-crow 0 builds) 0)
                   (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                   (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds)
                   (fn2-run-written-page-ready-p w (fn2-run-writers-fields w writers) writers f fc pool)
                   (fn2-range-published-run-pages-p records pages pool)
                   (natp l) (< l *fn2-run-max-levels*) (fn2-run-page-addressp page)
                   (consp rows) (true-listp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                   (equal (nth *fn2-format-page-header-field-page-kind* outer) (fn2-run-layout-page-kind 3 l))
                   (fn2-run-encoded-overview-page-p rows l outer inner (nth 3 page) (nth 4 page) 9 0 1 pool)
                   (if (zp l) (null children)
                     (and (fn2-range-published-children-p children (1- l) records)
                          (fn2-range-index-addresses-p rows children) (fn2-range-indexes-children-p rows groups)
                          (fn2-run-sorted-spec *fn2-overview-range-key* covered))))
              (and (posp calls) (<= calls 70)
                   (equal (car (mv-nth 1 run)) page)
                   (fn2-range-published-run-pages-p (cons node records) (mv-nth 1 run) (mv-nth 9 run))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-page-publication-returns-list-and-pool
                 (:instance fn2-range-index-and-subtree-start-together (subtrees (fn2-range-child-entry-lists children records))))
           :expand ((:free (node actual result) (fn2-range-published-run-pages-p (cons node records) actual result)))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-range-published-node-p nth car-cons cdr-cons atom not eq eql (:e zp) (:e equal)
                        (:e car) (:e cdr) (:e consp) (:e binary-+) (:e nth))))))

