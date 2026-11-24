; The actual page publication preserves the builder's complete input.
(in-package "ACL2")
(include-book "range-published-writer-rows-proof")
(include-book "range-builder-published-node-proof")
(local (include-book "columns-observation-frames"))

(local (defcolumns-observation-frame fn2-range-publication-keeps-height fn2-run-builds height pages))
(local (defcolumns-observation-frame fn2-range-publication-keeps-writer-base fn2-run-builds wbase pages))

(local
 (defthmd fn2-range-counted-page-keeps-writer-range
   (let ((after (fn2-run-sealed-builds builds)))
     (and (equal (fn2-run-builds-height 0 after) (fn2-run-builds-height 0 builds))
          (equal (fn2-run-builds-wbase 0 after) (fn2-run-builds-wbase 0 builds))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '(fn2-range-publication-keeps-height fn2-range-publication-keeps-writer-base))))))

(defthmd fn2-range-builder-publishes-page-without-changing-input
  (fn2-range-publishing-page
   (let* ((base (fn2-run-builds-wbase 0 builds)) (height (fn2-run-builds-height 0 builds))
          (level-children (if (zp l) nil (nth l children)))
          (covered (if (zp l) leaves (append-lst (fn2-range-child-entry-lists level-children records))))
          (node (list page rows outer inner covered level-children)) (after (mv-nth 2 run)))
     (implies (and (equal (fn2-run-builds-crow 0 builds) 0) (natp base)
                   (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                   (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds)
                   (fn2-run-written-page-ready-p w (fn2-run-writers-fields w writers) writers f fc pool)
                   (fn2-range-published-run-pages-p records pages pool)
                   (fn2-range-child-lists-exclude-page-p page children)
                   (natp l) (< l *fn2-run-max-levels*) (fn2-run-page-addressp page)
                   (consp rows) (true-listp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                   (equal (nth *fn2-format-page-header-field-page-kind* outer) (fn2-run-layout-page-kind 3 l))
                   (fn2-run-encoded-overview-page-p rows l outer inner (nth 3 page) (nth 4 page) 9 0 1 pool)
                   (if (zp l) (equal rows leaves)
                     (and (fn2-range-published-children-p level-children (1- l) records)
                          (fn2-range-index-addresses-p rows level-children)
                          (fn2-range-indexes-children-p rows (fn2-range-child-entry-lists level-children records))
                          (fn2-run-sorted-spec *fn2-overview-range-key* covered))))
              (and (posp calls) (<= calls 70)
                   (fn2-range-published-run-pages-p (cons node records) (mv-nth 1 run) (mv-nth 9 run))
                   (equal (fn2-range-builder-input (fn2-run-builds-height 0 after) (fn2-run-builds-wbase 0 after)
                                                  leaves children (cons node records) (mv-nth 6 run) entries)
                          (fn2-range-builder-input height base leaves children records writers entries))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-page-publication-returns-list-and-pool fn2-range-counted-page-keeps-writer-range
                 (:instance fn2-range-builder-publishes-represented-rows (children (if (zp l) nil (nth l children))))
                 (:instance fn2-range-publication-preserves-builder-input (base (fn2-run-builds-wbase 0 builds))
                   (height (fn2-run-builds-height 0 builds)) (pending entries)
                   (node (fn2-range-publishing-page
                          (let ((kids (if (zp l) nil (nth l children))))
                            (list page rows outer inner (if (zp l) leaves (append-lst (fn2-range-child-entry-lists kids records))) kids))))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-seal-workspace-p fn2-range-writer-covered-rows
                      fn2-range-writer-page-address nth car-cons cdr-cons commutativity-of-+ (:e equal) (:e nth)
                      (:e zp) (:e binary-+) (:e consp))))))
