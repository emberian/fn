; Installing a run makes each of its pages retrievable and preserves a
; hit on an earlier run, including when the installed run is the seal.
(in-package "ACL2")
(include-book "range-served")
(include-book "range-run-cache-window-proof")

(local
 (defthm fn2-range-installed-cache-is-page-list
   (equal (mv-nth 2 (fn2-rga-install-pages 3 k n pages inst cache)) (fn2-run-run-cache-all pages cache))
   :hints (("Goal" :in-theory (e/d (fn2-rga-install-pages) (fn2-run-install fn2-run-run-cache-all nth))))))

(defthmd fn2-range-installed-cache-supplies-listed-page
  (let* ((after (mv-nth 2 (fn2-rga-install-pages 3 k n pages inst cache))) (u (nth 1 page)) (a (nth 2 page)))
    (implies (and (equal (fn2-run-cache-rows cache) 4096) (fn2-range-run-pages-p pages k) (member-equal page pages))
             (equal (fn2-run-cache-lookup u a after) (list :ok (nth 3 page) (nth 4 page)))))
  :hints (("Goal" :use (fn2-range-run-cache-finds-listed-page fn2-run-built-cache-supplies-page)
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-installed-cache-is-page-list (:e posp) (:e equal))))))

(defthmd fn2-range-installing-next-run-keeps-earlier-hit
  (let* ((after (mv-nth 2 (fn2-rga-install-pages 3 k n pages inst cache))) (u (nth 1 page)) (a (nth 2 page))
         (hit (list :ok (nth 3 page) (nth 4 page))))
    (implies (and (equal (fn2-run-cache-rows cache) 4096) (fn2-range-run-pages-p pages k)
                  (fn2-run-page-addressp page) (fn2-range-run-unit-p u j) (< j k)
                  (equal (fn2-run-cache-lookup u a cache) hit))
             (equal (fn2-run-cache-lookup u a after) hit)))
  :hints (("Goal" :use (fn2-range-cache-keeps-earlier-run-address fn2-run-built-cache-supplies-page)
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-installed-cache-is-page-list (:e posp) (:e equal))))))
