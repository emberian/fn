; Add the row prepared by promotion to the parent index. Its first key
; represents the child's whole subtree, including when the child is an index.
(in-package "ACL2")
(include-book "range-index-address-proof")
(include-book "runs-promoted-first-key-proof")

(local
 (defthm fn2-range-promoted-row-extends-parent
   (let* ((head (car rows))
          (row (fn2-run-overview-child-row (list (nth 0 head) (nth 1 head)) w hrow writers ds))
          (child (if (zp level) rows (append-lst subtrees)))
          (page (list level (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers)
                            (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers))))
     (implies (and (consp rows) (true-listp rows)
                   (implies (not (zp level)) (fn2-range-indexes-children-p rows subtrees))
                   (fn2-range-indexes-children-p index children) (fn2-range-index-addresses-p index pages))
              (and (fn2-range-indexes-children-p (append index (list row)) (append children (list child)))
                   (fn2-range-index-addresses-p (append index (list row)) (append pages (list page))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-range-index-and-subtree-start-together
                  (:instance fn2-range-append-indexed-child
                    (row (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) w hrow writers ds))
                    (child (if (zp level) rows (append-lst subtrees)))
                    (page (list level (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers)
                                      (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)))))
            :in-theory (e/d (fn2-run-overview-child-row)
                      (fn2-range-indexes-children-p fn2-range-index-addresses-p binary-append append-lst fn2-page-parent-octets
                       fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-entries fn2-run-writers-epoch
                       fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-page-kind fn2-digest-list))))))

(defthm fn2-range-promotion-extends-parent-index
  (let* ((end (fn2-run-writers-cursor w writers))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (ref (fn2-run-promotion-input level w ib end hrow hslot hgen writers f pool ds))
         (row (fn2-run-unload-values *fn2-overview-index* ib (mv-nth 1 ref) (mv-nth 2 ref)))
         (child (if (zp level) rows (append-lst subtrees)))
         (page (list level (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers) slot gen)))
    (implies (and (consp rows) (true-listp rows)
                  (implies (not (zp level)) (fn2-range-indexes-children-p rows subtrees))
                  (fn2-range-indexes-children-p index children) (fn2-range-index-addresses-p index pages)
                  (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen 9 0 1 pool)
                  (equal end (fn2-run-overview-directory-offset level rows))
                  (fn2-fieldsp f) (fn2-fields-wfp f)
                  (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers f pool ds))
             (and (equal (car ref) :ok)
                  (fn2-range-indexes-children-p (append index (list row)) (append children (list child)))
                  (fn2-range-index-addresses-p (append index (list row)) (append pages (list page))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-encoded-child-supplies-promotion-input fn2-range-promoted-row-extends-parent)
           :in-theory (theory 'minimal-theory))))
