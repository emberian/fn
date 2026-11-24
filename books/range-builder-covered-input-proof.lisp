; Read the accepted part of a run from highest writer to lowest. A sealed
; writer refers to its published page until its parent accepts the child.
(in-package "ACL2")
(include-book "range-published-run-pages-proof")
(include-book "runs-build-root-proof")

(defthmd fn2-range-idle-levels-leave-only-pending-input
  (implies (fn2-run-below-idle height base writers)
           (equal (fn2-range-builder-input height base leaves children records writers pending) pending))
  :hints (("Goal" :induct (fn2-run-below-idle height base writers)
           :in-theory (e/d (fn2-run-below-idle fn2-range-builder-input fn2-range-writer-covered-rows)
                           (fn2-run-writers-phase fn2-range-writer-page-address fn2-range-child-entry-lists
                            append-lst nth assoc-equal)))))

(local
 (defthmd fn2-range-finished-builder-names-covered-root
   (let* ((height (fn2-run-builds-height 0 builds)) (level (1- height)) (base (fn2-run-builds-wbase 0 builds))
          (page (fn2-range-writer-page-address level (+ base level) writers))
          (covered (nth 4 (assoc-equal page records))))
     (implies (and (fn2-run-finished-root-p builds writers restarts f fc ctx) (true-listp covered))
              (equal (fn2-range-builder-input height base leaves children records writers nil) covered)))
   :hints (("Goal" :do-not '(preprocess)
            :expand ((fn2-range-builder-input (fn2-run-builds-height 0 builds) (fn2-run-builds-wbase 0 builds)
                                              leaves children records writers nil))
            :in-theory (e/d (fn2-run-finished-root-p fn2-range-writer-covered-rows fn2-range-idle-levels-leave-only-pending-input)
                            (fn2-run-below-idle fn2-run-writers-phase fn2-run-writers-ordinal fn2-run-builds-height
                             fn2-run-builds-wbase fn2-run-builds-crow fn2-run-builds-hbase fn2-run-builds-phase
                             fn2-run-writerp fn2-fc-rows fn2-fc-context-rows fn2-run-writers-rows
                             fn2-range-writer-page-address fn2-range-builder-input fn2-range-child-entry-lists
                             append-lst nth assoc-equal unsigned-byte-p))))))

(local
 (defthmd fn2-range-first-published-page-has-coverage
   (let* ((page (car pages)) (node (assoc-equal page records)))
     (implies (and (consp pages) (fn2-range-published-run-pages-p records pages pool))
              (and (equal node (car records)) (true-listp (nth 4 node))
                   (fn2-run-page-addressp page) (unsigned-byte-p 8 (car page)) (< (car page) *fn2-run-max-levels*))))
   :hints (("Goal" :expand ((fn2-range-published-run-pages-p records pages pool) (assoc-equal (car pages) records))
            :in-theory (e/d (fn2-range-published-node-p unsigned-byte-p)
                     (fn2-range-published-run-pages-p fn2-run-page-addressp fn2-run-sorted-spec fn2-run-layout-page-kind
                      fn2-run-encoded-overview-page-p fn2-range-indexes-children-p fn2-range-index-addresses-p
                      fn2-range-published-children-p fn2-range-child-entry-lists append-lst nth assoc-equal))))))

(defthmd fn2-range-finished-builder-installs-covered-input
  (let* ((height (fn2-run-builds-height 0 builds)) (level (1- height)) (base (fn2-run-builds-wbase 0 builds))
         (source (fn2-range-builder-input height base leaves children records writers nil))
         (result (fn2-run-run-loop fuel layout nil src sg at unit pages builds curs paths cache
                                   writers restarts f pool fc ctx b3 ds))
         (installed (fn2-rga-install-pages 3 k (len source) (mv-nth 1 result) inst (mv-nth 5 result)))
         (catalog (mv-nth 1 installed)) (root (fn2-run-installed-root k catalog)))
    (implies (and (fn2-run-finished-root-p builds writers restarts f fc ctx) (posp fuel)
                  (consp pages) (equal (car pages) (fn2-range-writer-page-address level (+ base level) writers))
                  (fn2-range-published-run-pages-p records pages pool)
                  (natp k) (<= k 5) (< k (fn2-run-installed-rows inst))
                  (equal (fn2-run-installed-state k inst) *fn2-run-installed-state-free*) (<= (len source) 48))
             (and (equal (car result) :root) (equal (car installed) :ok)
                  (fn2-range-published-run-pages-p records (mv-nth 1 result) (mv-nth 9 result))
                  (equal root (car pages)) (equal (nth 4 (assoc-equal root records)) source)
                  (equal (fn2-run-installed-source k catalog)
                         (list *fn2-run-installed-state-live* 3 (1+ k) (len source) 9 0 1)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-finished-builder-names-covered-root fn2-range-first-published-page-has-coverage
                 (:instance fn2-run-build-returns-completed-pages (entries nil) (off at))
                 (:instance fn2-range-installed-pages-supply-root (r k) (sid 3)
                    (count (len (fn2-range-builder-input (fn2-run-builds-height 0 builds) (fn2-run-builds-wbase 0 builds)
                                                        leaves children records writers nil)))))
           :in-theory (e/d (unsigned-byte-p mv-nth) (fn2-run-run-loop fn2-rga-install-pages fn2-run-finished-root-p
                fn2-range-builder-input fn2-range-published-run-pages-p fn2-run-builds-height fn2-run-builds-wbase
                fn2-range-writer-page-address fn2-run-installed-root fn2-run-installed-source fn2-run-installed-rows
                fn2-run-installed-state fn2-run-builds-set-phase fn2-run-page-addressp nth assoc-equal len)))))
