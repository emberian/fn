; The builder publishes children before their parent. The page list and its
; row descriptions have the same order, with the last published page first.
(in-package "ACL2")
(include-book "range-published-run-contents")
(include-book "range-run-cache-window-proof")
(include-book "range-installed-pages-proof")

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
