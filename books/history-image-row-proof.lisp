; A placed row appends exactly the canonical five body blocks.
(in-package "ACL2")
(include-book "history-image-content-step")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-rcs-write-appends
 (implies
  (and (fn-his-cellsp cells) (fn-his-cursors-at rcs lens) (nat-listp starts) (natp np)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np)
       (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let ((res (fn-his-rcs-write cells rcs starts pgs-mem)))
   (equal (fn-his-rcs-flush-write (mv-nth 0 res) starts (mv-nth 1 res))
          (fn-hp-x-put-blocks (fn-hp-bb-list starts lens cells)
           (fn-his-rcs-flush-write rcs starts pgs-mem)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-cursors-apart-of-placement fn-his-rcs-write-materializes fn-his-merged-blocks-split)
          :in-theory (disable fn-his-cellsp fn-his-cursors-at fn-his-rcs-fitp
                              fn-his-cursors-apart fn-his-cell-bytes fn-hp-x-add adt-placement-ok
                              fn-his-rcs-write fn-his-rcs-flush-write fn-hp-x-put-blocks fn-hp-bb-list
                              fn-his-merged-blocks fn-his-merged-blocks-split fn-his-rcs-write-materializes
                              fn-his-cursors-apart-of-placement)))
 :rule-classes nil)

(defthm fn-his-bb-list-fits
 (implies (and (fn-hp-wls-okp cells) (fn-his-cursors-at rcs lens) (nat-listp starts)
               (equal (len cells) (len lens)) (equal (len starts) (len lens))
               (natp nw) (natp nd) (fn-his-rcs-fitp cells rcs starts nw nd))
  (fn-hp-blocks-fit (fn-hp-bb-list starts lens cells) nw nd))
 :hints (("Goal" :induct (fn-his-region-ind cells rcs lens starts)
          :in-theory (e/d (fn-hp-wls-okp fn-his-cursors-at fn-hp-bb-list fn-hp-blocks-fit len)
                          (fn-his-rcp fn-his-rc-fitp floor fn-hp-u64-listp)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-cursor-offset (rc (car rcs)) (start (car starts)) (used (car lens)))
                (:instance fn-his-cell-write-ready (rc (car rcs)) (start (car starts)) (ws (car cells)))))))

(defthm fn-his-row-cells-nonempty
 (implies (and (fn-hp-evp ev) (unsigned-byte-p 64 off)
               (unsigned-byte-p 64 (len (fn-hp-pe ev))))
  (fn-hp-wls-okp (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev)))
                       (list off) (list (len (fn-hp-pe ev)))
                       (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-row-cells-facts fn-hp-len-pe-pos fn-hp-pe-mod-8
                (:instance fn-hp-floor-8-exact (x (len (fn-hp-pe ev)))))
          :in-theory (e/d (fn-his-cellsp fn-hp-wls-okp)
                          (fn-hp-pe fn-hp-pe-is-pad8 fn-scc-encode fn-scc-encode-is-program
                           fn-hp-mkey fn-hp-pack8 fn-hp-u64-listp fn-hp-evp floor mod fn-his-row-cells-facts)))))

(defthm fn-his-rcs-write-appends-words
 (implies
  (and (fn-his-cellsp cells) (fn-hp-wls-okp cells)
       (fn-his-cursors-at rcs lens) (nat-listp starts) (natp np)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np)
       (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let ((res (fn-his-rcs-write cells rcs starts pgs-mem)))
   (equal (nth *pgs-wi* (fn-his-rcs-flush-write (mv-nth 0 res) starts (mv-nth 1 res)))
          (fn-hp-wreps (nth *pgs-wi* (fn-his-rcs-flush-write rcs starts pgs-mem))
                       (fn-hp-bb-list starts lens cells)))))
 :hints (("Goal" :do-not-induct t
          :use (fn-his-rcs-write-appends
                (:instance fn-his-bb-list-fits (nw (pgs-w-length pgs-mem)) (nd (pgs-d-length pgs-mem)))
                (:instance fn-his-rcs-fit-implies-flush-fit (nw (pgs-w-length pgs-mem)) (nd (pgs-d-length pgs-mem)))
                fn-his-rcs-flush-write-keeps-lengths
                (:instance fn-hp-x-put-blocks-words (blocks (fn-hp-bb-list starts lens cells))
                  (pgs-mem (fn-his-rcs-flush-write rcs starts pgs-mem))))
          :in-theory (disable fn-his-cellsp fn-hp-wls-okp fn-his-cursors-at fn-his-rcs-fitp
                              fn-his-cell-bytes fn-hp-x-add adt-placement-ok
                              fn-his-rcs-write fn-his-rcs-flush-write fn-hp-x-put-blocks fn-hp-bb-list
                              fn-hp-wreps fn-hp-blocks-fit fn-his-rcs-flush-fitp
                              fn-his-bb-list-fits fn-his-rcs-fit-implies-flush-fit
                              fn-his-rcs-flush-write-keeps-lengths fn-hp-x-put-blocks-words
                              nth adt-nth-1+)))
 :rule-classes nil)

(defthm fn-his-place-row-appends-words
 (implies
  (and (fn-his-pwp pw) (fn-hp-evp ev)
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (unsigned-byte-p 64 (nth 4 (cadr pw)))
       (unsigned-byte-p 64 (len (fn-hp-pe ev)))
       (adt-placement-ok starts (fn-hp-x-add (cadr pw) (list 8 8 8 8 (len (fn-hp-pe ev)))) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np))
  (let ((res (fn-his-place-row ev salt pw starts np pgs-mem)))
   (equal (nth *pgs-wi* (fn-his-rcs-flush-write (caddr (mv-nth 1 res)) starts (mv-nth 2 res)))
          (fn-hp-wreps
           (nth *pgs-wi* (fn-his-rcs-flush-write (caddr pw) starts pgs-mem))
           (fn-hp-bb-list starts (cadr pw) (fn-hp-ds-words (fn-hp-ds ev salt (nth 4 (cadr pw)))))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-row-cells-facts (off (nth 4 (cadr pw))))
                (:instance fn-his-row-cells-nonempty (off (nth 4 (cadr pw))))
                (:instance fn-his-cursors-at-fit-placement
                 (rcs (caddr pw)) (lens (cadr pw))
                 (cells (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev)))
                              (list (nth 4 (cadr pw))) (list (len (fn-hp-pe ev)))
                              (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev)))))
                (:instance fn-his-rcs-write-appends-words
                 (rcs (caddr pw)) (lens (cadr pw))
                 (cells (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev)))
                              (list (nth 4 (cadr pw))) (list (len (fn-hp-pe ev)))
                              (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev)))))
                (:instance fn-hp-ds-words-of-ds (off (nth 4 (cadr pw)))))
          :in-theory (e/d (fn-his-place-row fn-his-rcs-put fn-his-pwp fn-hp-evp)
                          (fn-hp-x-row fn-his-cursors-at fn-hp-pe fn-hp-pe-is-pad8
                           fn-hp-x-add fn-hp-pack8 fn-hp-mkey fn-hp-ds-words fn-hp-ds fn-hp-bb-list fn-hp-wreps
                           fn-his-cellsp fn-his-cell-bytes fn-his-rcs-fitp fn-his-rcs-write fn-his-rcs-flush-write
                           fn-hp-wls-okp fn-his-row-cells-facts fn-his-row-cells-nonempty fn-his-cursors-at-fit-placement
                           fn-hp-ds-words-of-ds fn-his-flush-consp fn-his-flush-cons
                           fn-scc-encode fn-scc-encode-is-program adt-placement-ok floor mod nth adt-nth-1+))))
 :rule-classes nil)
