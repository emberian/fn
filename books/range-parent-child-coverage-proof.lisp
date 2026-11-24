; An open index covers the concatenation of the published children named
; by its encoded rows. Appending a sealed child adds its entire subtree.
(in-package "ACL2")
(include-book "range-published-run-pages-proof")
(include-book "runs-child-reference-values-proof")

(defun-nx fn2-range-open-parent-children-p (rows children level records)
  (and (fn2-range-published-children-p children level records)
       (fn2-range-index-addresses-p rows children)
       (fn2-range-indexes-children-p rows (fn2-range-child-entry-lists children records))))

(local
 (defthmd fn2-range-node-key-starts-covered-rows
   (let ((rows (nth 1 node)) (covered (nth 4 node)))
     (implies (fn2-range-published-node-p node earlier pool)
              (and (consp covered) (true-listp covered)
                   (equal (caar rows) (caar covered)) (equal (cadar rows) (cadar covered)))))
   :hints (("Goal" :use ((:instance fn2-range-index-and-subtree-start-together
                             (rows (nth 1 node)) (subtrees (fn2-range-child-entry-lists (nth 5 node) earlier))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-published-node-p))))))

(defthmd fn2-range-published-key-starts-covered-rows
  (let* ((node (assoc-equal page records)) (rows (nth 1 node)) (covered (nth 4 node)))
    (implies (and (fn2-range-published-run-pages-p records pages pool) node)
             (and (consp covered) (true-listp covered)
                  (equal (caar rows) (caar covered)) (equal (cadar rows) (cadar covered)))))
  :hints (("Goal" :induct (fn2-range-published-run-pages-p records pages pool)
           :in-theory (union-theories (theory 'minimal-theory)
                         '((:induction fn2-range-published-run-pages-p) fn2-range-published-run-pages-p
                           fn2-range-node-key-starts-covered-rows assoc-equal atom endp (:e equal))))))

(local
 (defthm fn2-range-child-lists-after-append
   (equal (fn2-range-child-entry-lists (append children (list page)) records)
          (append (fn2-range-child-entry-lists children records) (list (nth 4 (assoc-equal page records)))))
   :hints (("Goal" :induct (len children)
            :in-theory (enable fn2-range-child-entry-lists)))))

(local
 (defthm fn2-range-published-children-after-append
   (implies (and (fn2-range-published-children-p children level records) (assoc-equal page records)
                 (equal (car page) level))
            (fn2-range-published-children-p (append children (list page)) level records))
   :hints (("Goal" :induct (len children)
            :in-theory (enable fn2-range-published-children-p)))))

(local
 (defthm fn2-range-append-child-after-earlier-rows
   (equal (append (append a b) c) (append a (append b c)))
   :hints (("Goal" :induct (len a)))))

(local
 (defthm fn2-range-last-child-extends-covered-rows
   (implies (true-listp child)
            (equal (append-lst (append groups (list child))) (append (append-lst groups) child)))
   :hints (("Goal" :induct (len groups) :in-theory (enable append-lst)))))

(defthmd fn2-range-index-append-covers-published-child
  (let* ((rows (nth 1 (assoc-equal page records)))
         (covered (nth 4 (assoc-equal page records)))
         (row (fn2-run-overview-child-row (list (caar rows) (cadar rows)) level hrow writers ds)))
    (implies (and (fn2-range-published-run-pages-p records pages pool) (assoc-equal page records)
                  (equal (car page) level) (equal (nth 1 page) (fn2-run-writers-unit level writers))
                  (equal (nth 2 page) (fn2-run-writers-counter level writers))
                  (fn2-range-open-parent-children-p parent-rows children level records))
             (and (fn2-range-open-parent-children-p (append parent-rows (list row)) (append children (list page)) level records)
                  (equal (append-lst (fn2-range-child-entry-lists (append children (list page)) records))
                         (append (append-lst (fn2-range-child-entry-lists children records)) covered)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-published-key-starts-covered-rows
                 (:instance fn2-range-append-indexed-child (index parent-rows)
                    (children (fn2-range-child-entry-lists children records)) (pages children)
                    (child (nth 4 (assoc-equal page records)))
                    (row (let ((rows (nth 1 (assoc-equal page records))))
                           (fn2-run-overview-child-row (list (caar rows) (cadar rows)) level hrow writers ds)))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-range-open-parent-children-p fn2-range-child-lists-after-append
                           fn2-range-published-children-after-append fn2-range-last-child-extends-covered-rows
                           fn2-run-overview-child-row nth car-cons cdr-cons (:e nth) (:e zp) (:e consp)
                           (:e binary-+) (:e car) (:e cdr) (:e equal))))))
