; Move a published subtree into the open parent's stored row sequence
; exactly once. If the parent is full it keeps its previous coverage.
(in-package "ACL2")
(include-book "range-parent-child-coverage-proof")
(include-book "range-promotion-published-pages-proof")
(include-book "runs-parent-index-contents-proof")

(defun-nx fn2-range-stored-parent-covers-p (index children covered level records w slot gen restarts pool)
  (and (fn2-run-stored-index-rows-p index w slot gen restarts pool)
       (fn2-range-open-parent-children-p index children level records)
       (equal covered (append-lst (fn2-range-child-entry-lists children records)))))

(local
 (defthm fn2-range-first-two-key-fields
   (and (equal (nth 0 row) (car row)) (equal (nth 1 row) (cadr row)))
   :hints (("Goal" :expand ((nth 1 row) (nth 0 row) (nth 0 (cdr row)))))))

(local
 (defthmd fn2-range-attaching-child-keeps-parent-description
   (let* ((row (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) level hrow writers ds))
          (index (if fits (append parent-rows (list row)) parent-rows))
          (next-children (if fits (append children (list page)) children))
          (next-covered (if fits (append covered (nth 4 (assoc-equal page records))) covered)))
     (implies (and (fn2-range-published-run-pages-p records pages pool) (assoc-equal page records)
                   (equal rows (nth 1 (assoc-equal page records))) (equal (car page) level)
                   (equal (nth 1 page) (fn2-run-writers-unit level writers))
                   (equal (nth 2 page) (fn2-run-writers-counter level writers))
                   (fn2-range-stored-parent-covers-p parent-rows children covered level records w dst dg restarts pool)
                   (fn2-run-stored-index-rows-p index w dst dg next-rs next-pool))
              (fn2-range-stored-parent-covers-p index next-children next-covered level records w dst dg next-rs next-pool)))
   :hints (("Goal" :cases (fits) :do-not '(preprocess) :use fn2-range-index-append-covers-published-child
            :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-range-stored-parent-covers-p fn2-range-first-two-key-fields (:e equal)))))))

(local
 (defthm fn2-range-covered-parent-has-stored-rows
   (implies (fn2-range-stored-parent-covers-p index children covered level records w slot gen restarts pool)
            (fn2-run-stored-index-rows-p index w slot gen restarts pool))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-stored-parent-covers-p))))))

(local
 (defthm fn2-range-parent-step-stores-child-index
  (fn2-run-promoting-index-row
   (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
          (step (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache
                                     writers restarts f pool fc ctx b3 ds))
          (row (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) level hrow writers ds)))
     (implies (and (posp height) (<= height *fn2-run-max-levels*)
                   (fn2-run-higher-writers-available-p (1- height) w writers)
                   (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx))
                   (fn2-range-published-run-pages-p records pages pool)
                   (fn2-range-fixed-page-slot-p hslot pool) (fn2-range-published-slots-apart-p pages hslot pool)
                   (implies fits (and (fn2-range-fixed-page-slot-p dst pool) (fn2-range-published-slots-apart-p pages dst pool)))
                   (fn2-run-write-outside-read-p dst *fn2-run-entries-base* (len (fn2-run-parent-octets parent-rows))
                                                 hslot (* 32 level) 32 pool)
                   (fn2-run-stored-index-rows-p parent-rows w dst dg restarts pool))
              (and (fn2-run-parent-promotion-effects) (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) entries)
                   (fn2-range-published-run-pages-p records (mv-nth 5 step) (mv-nth 13 step))
                   (fn2-run-stored-index-rows-p (if fits (append parent-rows (list row)) parent-rows)
                                                w dst dg (mv-nth 11 step) (mv-nth 13 step))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-promoting-parent-keeps-published-pages fn2-run-parent-stores-all-promoted-children)
           :in-theory (union-theories (theory 'minimal-theory)
                       '(mv-nth car-cons cdr-cons (:e mv-nth) (:e equal) (:e zp) (:e binary-+) (:e consp)))))))

(defthm fn2-range-builder-transfers-child-coverage
  (fn2-run-promoting-index-row
   (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
          (step (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache
                                     writers restarts f pool fc ctx b3 ds))
          (node (assoc-equal page records)) (child-entries (nth 4 node))
          (row (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) level hrow writers ds)))
     (implies (and (posp height) (<= height *fn2-run-max-levels*)
                   (fn2-run-higher-writers-available-p (1- height) w writers)
                   (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx))
                   (fn2-range-published-run-pages-p records pages pool)
                   node (equal rows (nth 1 node)) (equal (car page) level)
                   (equal (nth 1 page) (fn2-run-writers-unit level writers))
                   (equal (nth 2 page) (fn2-run-writers-counter level writers))
                   (equal (nth 3 page) (fn2-run-writers-slot level writers))
                   (equal (nth 4 page) (fn2-run-writers-gen level writers))
                   (fn2-range-fixed-page-slot-p hslot pool) (fn2-range-published-slots-apart-p pages hslot pool)
                   (implies fits (and (fn2-range-fixed-page-slot-p dst pool) (fn2-range-published-slots-apart-p pages dst pool)))
                   (fn2-run-write-outside-read-p dst *fn2-run-entries-base* (len (fn2-run-parent-octets parent-rows))
                                                 hslot (* 32 level) 32 pool)
                   (fn2-range-stored-parent-covers-p parent-rows children covered level records w dst dg restarts pool))
              (and (fn2-run-parent-promotion-effects) (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) entries)
                   (fn2-range-published-run-pages-p records (mv-nth 5 step) (mv-nth 13 step))
                   (fn2-range-stored-parent-covers-p
                    (if fits (append parent-rows (list row)) parent-rows)
                    (if fits (append children (list page)) children)
                    (if fits (append covered child-entries) covered)
                    level records w dst dg (mv-nth 11 step) (mv-nth 13 step))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-parent-step-stores-child-index
                 (:instance fn2-range-attaching-child-keeps-parent-description (hrow (+ 136 level))
                   (w (1+ level)) (dst (fn2-run-writers-slot (1+ level) writers)) (dg (fn2-run-writers-gen (1+ level) writers))
                   (fits (fn2-run-index-fits-writer (1+ level) (fn2-run-child-index-bytes rows level (+ 136 level) writers ds) writers))
                   (next-rs (mv-nth 11 (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
                   (next-pool (mv-nth 13 (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-covered-parent-has-stored-rows)))))
