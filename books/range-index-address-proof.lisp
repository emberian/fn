; Bind each parent index row to the physical address of its child.
(in-package "ACL2")
(include-book "range-child-row-order-proof")

(defun-nx fn2-range-index-addresses-p (index pages)
  (if (atom index)
      (and (null index) (null pages))
    (let ((row (car index)) (page (car pages)))
      (and (consp pages)
           (equal (nth (+ 2 *fn2-format-ref-field-physical-unit*) row) (nth 1 page))
           (equal (nth (+ 2 *fn2-format-ref-field-allocation*) row) (nth 2 page))
           (fn2-range-index-addresses-p (cdr index) (cdr pages))))))

(local
 (defthm fn2-range-append-child-address
   (implies (and (fn2-range-index-addresses-p index pages)
                 (equal (nth (+ 2 *fn2-format-ref-field-physical-unit*) row) (nth 1 page))
                 (equal (nth (+ 2 *fn2-format-ref-field-allocation*) row) (nth 2 page)))
            (fn2-range-index-addresses-p (append index (list row)) (append pages (list page))))
   :hints (("Goal" :induct (fn2-range-index-addresses-p index pages)
            :in-theory (disable nth)))))

(local
 (defthm fn2-range-append-child-rows
   (implies (and (fn2-range-indexes-children-p index children) (consp child) (true-listp child)
                 (equal (car row) (caar child)) (equal (cadr row) (cadar child)))
            (fn2-range-indexes-children-p (append index (list row)) (append children (list child))))
   :hints (("Goal" :induct (fn2-range-indexes-children-p index children)
            :in-theory (union-theories (theory 'minimal-theory)
                           '(fn2-range-indexes-children-p binary-append atom not car-cons cdr-cons
                             (:e consp) (:e cdr) (:e car) (:e equal)))))))

(defthm fn2-range-index-and-subtree-start-together
   (implies (and (consp rows) (fn2-range-indexes-children-p rows subtrees))
            (let ((rows-of-children (append-lst subtrees)))
              (and (consp rows-of-children) (true-listp rows-of-children)
                   (equal (caar rows) (caar rows-of-children))
                   (equal (cadar rows) (cadar rows-of-children)))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-range-indexes-children-p rows subtrees) (append-lst subtrees) (binary-append (car subtrees) (append-lst (cdr subtrees))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(atom endp binary-append car-cons cdr-cons (:t append-lst) (:t binary-append) true-listp-append true-listp (:e equal) (:e consp))))))


(defthm fn2-range-append-indexed-child
  (implies (and (fn2-range-indexes-children-p index children) (fn2-range-index-addresses-p index pages)
                (consp child) (true-listp child) (equal (car row) (caar child)) (equal (cadr row) (cadar child))
                (equal (nth (+ 2 *fn2-format-ref-field-physical-unit*) row) (nth 1 page))
                (equal (nth (+ 2 *fn2-format-ref-field-allocation*) row) (nth 2 page)))
           (and (fn2-range-indexes-children-p (append index (list row)) (append children (list child)))
                (fn2-range-index-addresses-p (append index (list row)) (append pages (list page)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn2-range-append-child-address fn2-range-append-child-rows)))))

(local
 (defun-nx fn2-range-index-page-walk (i index pages)
   (if (or (zp i) (atom index)) pages (fn2-range-index-page-walk (1- i) (cdr index) (cdr pages)))))

(defthmd fn2-range-index-address-at
  (let ((entry (nth i index)) (page (nth i pages)))
    (implies (and (fn2-range-index-addresses-p index pages) (natp i) (< i (len index)))
             (and (equal (nth (+ 2 *fn2-format-ref-field-physical-unit*) entry) (nth 1 page))
                  (equal (nth (+ 2 *fn2-format-ref-field-allocation*) entry) (nth 2 page)))))
  :hints (("Goal" :induct (fn2-range-index-page-walk i index pages)
           :in-theory (enable fn2-range-index-addresses-p))))
