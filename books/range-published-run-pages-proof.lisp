; The builder publishes children before their parent. The page list and its
; row descriptions have the same order, with the last published page first.
(in-package "ACL2")
(include-book "range-encoded-page-search-proof")
(include-book "range-index-address-proof")
(include-book "range-run-cache-window-proof")
(include-book "range-installed-pages-proof")

; Each description holds the published address, encoded rows, both header
; value lists, represented leaf rows, and child addresses in key order.
(defun-nx fn2-range-child-entry-lists (children records)
  (if (atom children) nil
    (cons (nth 4 (assoc-equal (car children) records))
          (fn2-range-child-entry-lists (cdr children) records))))

(defun-nx fn2-range-published-children-p (children level records)
  (if (atom children) (null children)
    (and (assoc-equal (car children) records) (equal (caar children) level)
         (fn2-range-published-children-p (cdr children) level records))))

(defun-nx fn2-range-published-node-p (node earlier pool)
  (let* ((page (car node)) (level (car page)) (rows (nth 1 node))
         (outer (nth 2 node)) (inner (nth 3 node)) (entries (nth 4 node))
         (children (nth 5 node)) (groups (fn2-range-child-entry-lists children earlier)))
    (and (fn2-run-page-addressp page) (natp level) (< level *fn2-run-max-levels*)
         (consp rows) (true-listp rows) (consp entries) (true-listp entries)
         (fn2-run-sorted-spec *fn2-overview-range-key* rows)
         (fn2-run-sorted-spec *fn2-overview-range-key* entries)
         (equal (nth *fn2-format-page-header-field-page-kind* outer) (fn2-run-layout-page-kind 3 level))
         (fn2-run-encoded-overview-page-p rows level outer inner (nth 3 page) (nth 4 page) 9 0 1 pool)
         (if (zp level)
             (and (null children) (equal entries rows))
           (and (fn2-range-published-children-p children (1- level) earlier)
                (fn2-range-index-addresses-p rows children) (fn2-range-indexes-children-p rows groups)
                (equal entries (append-lst groups)))))))

(defun-nx fn2-range-published-run-pages-p (records pages pool)
  (if (atom records) (and (null records) (null pages))
    (and (consp pages) (equal (caar records) (car pages))
         (fn2-range-published-node-p (car records) (cdr records) pool)
         (fn2-range-published-run-pages-p (cdr records) (cdr pages) pool))))

(defthmd fn2-range-published-page-has-readable-rows
  (let* ((node (assoc-equal page records)) (level (car page)))
    (implies (and (fn2-range-published-run-pages-p records pages pool) node)
             (and (member-equal page pages) (fn2-run-page-addressp page) (natp level) (< level *fn2-run-max-levels*)
                  (fn2-run-encoded-overview-page-p (nth 1 node) level (nth 2 node) (nth 3 node) (nth 3 page) (nth 4 page) 9 0 1 pool)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (nth 1 node))
                  (consp (nth 1 node)))))
  :hints (("Goal" :induct (fn2-range-published-run-pages-p records pages pool)
           :in-theory (e/d (fn2-range-published-run-pages-p fn2-range-published-node-p assoc-equal member-equal)
                          (fn2-run-encoded-overview-page-p fn2-run-page-addressp fn2-run-sorted-spec fn2-run-layout-page-kind
                           fn2-range-published-children-p fn2-range-child-entry-lists fn2-range-index-addresses-p
                           fn2-range-indexes-children-p append-lst nth)))))

(defthmd fn2-range-installed-published-page-search
  (let* ((node (assoc-equal page records)) (level (car page)) (slot (nth 3 page)) (gen (nth 4 page))
         (read (fn2-run-read-header slot gen rb 9 0 1 f pool)) (rf (mv-nth 1 read))
         (seek (fn2-run-seek 3 level fuel 0 (fn2-run-page-restart-count rb rf) 0 0 qbase rb slot gen 9 0 1 qk qs qg rf pool))
         (write (fn2-rga-install-pages 3 k count pages inst cache)))
    (implies (and (fn2-range-published-run-pages-p records pages pool) node (fn2-range-run-pages-p pages k)
                  (equal (fn2-run-cache-rows cache) 4096)
                  (fn2-fieldsp f) (fn2-run-readerp rb f) (natp qbase) (< (1+ qbase) rb)
                  (natp fuel) (< (+ (integer-length (len (fn2-run-overview-page-offsets level (nth 1 node))))
                                   *fn2-run-restart-interval* 1) fuel))
             (and (equal (fn2-run-cache-lookup (nth 1 page) (nth 2 page) (mv-nth 2 write)) (list :ok slot gen))
                  (equal (car read) :ok)
                  (equal (list (car seek) (mv-nth 3 seek))
                         (fn2-run-lower-bound-spec *fn2-overview-range-key* (nth 1 node) (fn2-overview-range-key-at qbase f) 0)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-published-page-has-readable-rows fn2-range-run-cache-finds-listed-page
                 (:instance fn2-range-installed-pages-supply-child (sid 3))
                 (:instance fn2-run-searches-encoded-overview-page (rows (nth 1 (assoc-equal page records))) (level (car page))
                      (bvals (nth 2 (assoc-equal page records))) (cvals (nth 3 (assoc-equal page records)))
                      (slot (nth 3 page)) (gen (nth 4 page)) (pk 9) (ps 0) (pg 1)))
           :in-theory (union-theories (theory 'minimal-theory) '((:e posp) (:e equal))))))
