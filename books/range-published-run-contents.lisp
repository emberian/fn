; Each published address records the encoded rows, both header values,
; the represented leaf entries, and its children in key order.
(in-package "ACL2")
(include-book "range-builder-input")
(include-book "range-encoded-page-search-proof")
(include-book "range-index-address-proof")
(include-book "runs-built-cache-proof")

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
