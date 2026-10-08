; Relate cursor positions to the byte lengths carried by placement.
(in-package "ACL2")
(include-book "history-image-place")
(include-book "history-image-cursor-proof")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-his-cursors-at (rcs lens)
 (declare (xargs :guard t))
 (if (atom lens) (and (null lens) (null rcs))
  (and (consp rcs) (natp (car lens)) (fn-his-rcp (car rcs))
       (fn-hp-u64-listp (caddr (car rcs)))
       (equal (car lens) (* 8 (+ (* 2048 (car (car rcs))) (cadr (car rcs)))))
       (fn-his-cursors-at (cdr rcs) (cdr lens)))))

(def-loop fn-his-cell-bytes (cells)
 :shape :map :elt cell :body (* 8 (len cell)))

(local
 (defun-nx fn-his-rcs-progress-ind (cells rcs lens starts mem)
  (declare (xargs :guard (and (true-listp rcs) (true-listp lens) (true-listp starts))
                  :verify-guards t))
  (if (atom cells) (list rcs lens starts mem)
    (fn-his-rcs-progress-ind (cdr cells) (cdr rcs) (cdr lens) (cdr starts)
     (mv-nth 1 (ec-call (fn-his-rc-write (car cells) (car rcs) (car starts) mem)))))))

(defthm fn-his-rcs-write-advances
 (implies (and (fn-his-cellsp cells) (fn-his-cursors-at rcs lens)
               (equal (len cells) (len lens)))
          (fn-his-cursors-at (mv-nth 0 (fn-his-rcs-write cells rcs starts pgs-mem))
                             (fn-hp-x-add lens (fn-his-cell-bytes cells))))
 :hints (("Goal" :induct (fn-his-rcs-progress-ind cells rcs lens starts pgs-mem)
          :in-theory (e/d (fn-his-cursors-at fn-hp-x-add fn-his-cell-bytes len)
                          (fn-his-rc-write fn-his-rcp)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-write-position (ws (car cells)) (rc (car rcs)) (start (car starts)))
                (:instance fn-his-rc-write-buffer-u64 (ws (car cells)) (rc (car rcs)) (start (car starts)))))))

(defthm fn-his-rc-cap-fits
 (implies (and (fn-his-rcp rc) (natp start) (natp np)
               (equal used (* 8 (+ (* 2048 (car rc)) (cadr rc))))
               (<= (+ start (adt-cap (+ used (* 8 (len ws))))) np))
          (fn-his-rc-fitp (len ws) rc start (* 2048 np) np))
 :hints (("Goal" :use ((:instance adt-cap-covers (u (+ used (* 8 (len ws))))))
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp)
                          (adt-cap adt-cap-covers len)))))

(defun fn-his-region-ind (cells rcs lens starts)
  (declare (xargs :guard (and (true-listp rcs) (true-listp lens) (true-listp starts))))
  (if (atom cells) (list rcs lens starts)
    (fn-his-region-ind (cdr cells) (cdr rcs) (cdr lens) (cdr starts))))

(defthm fn-his-cursors-at-fit-placement
 (implies (and (fn-his-cellsp cells) (fn-his-cursors-at rcs lens)
               (nat-listp starts) (natp np)
               (equal (len cells) (len lens)) (equal (len starts) (len lens))
               (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np))
          (fn-his-rcs-fitp cells rcs starts (* 2048 np) np))
 :hints (("Goal" :induct (fn-his-region-ind cells rcs lens starts)
          :in-theory (e/d (fn-his-cursors-at fn-hp-x-add fn-his-cell-bytes len adt-placement-ok)
                          (fn-his-rcp fn-his-rc-fitp adt-cap adt-apart)))))

(defthm fn-his-encoded-row-spec
 (equal (fn-hp-x-row ev)
        (if (fn-hp-evp ev)
            (list nil (len (fn-scc-encode ev)) (fn-hp-pe ev))
          (list '(:refused :event) 0 nil)))
 :hints (("Goal" :in-theory (e/d (fn-hp-x-row fn-hp-evp fn-hp-pe)
                                (fn-scc-encode fn-scc-encode-is-program fn-hp-pad8
                                 fn-hp-pe-is-pad8 fn-sccb-treep)))))

(defthm fn-his-row-cells-facts
 (implies (and (fn-hp-evp ev) (unsigned-byte-p 64 off)
               (unsigned-byte-p 64 (len (fn-hp-pe ev))))
  (let ((cells (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev)))
                     (list off) (list (len (fn-hp-pe ev)))
                     (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev)))))
   (and (fn-his-cellsp cells)
        (equal (fn-his-cell-bytes cells) (list 8 8 8 8 (len (fn-hp-pe ev)))))))
 :hints (("Goal"
          :use ((:instance fn-hp-floor-8-exact (x (len (fn-hp-pe ev))))
                fn-hp-pe-mod-8 fn-hp-octetsp-pe)
          :in-theory (e/d (fn-his-cellsp fn-his-cell-bytes fn-hp-evp fn-hp-u64-listp)
                          (fn-hp-pe fn-hp-pe-is-pad8 fn-hp-pack8 fn-hp-mkey
                           fn-scc-encode fn-scc-encode-is-program fn-sccb-treep
                           floor mod fn-hp-floor-8-exact fn-hp-pe-mod-8)))))

(defthm fn-his-place-row-accepts-fitting-cursors
 (implies
  (and (fn-his-pwp pw) (fn-hp-evp ev)
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (unsigned-byte-p 64 (nth 4 (cadr pw)))
       (unsigned-byte-p 64 (len (fn-hp-pe ev)))
       (adt-placement-ok starts (fn-hp-x-add (cadr pw) (list 8 8 8 8 (len (fn-hp-pe ev)))) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np))
  (equal (mv-nth 0 (fn-his-place-row ev salt pw starts np pgs-mem)) :ok))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-row-cells-facts (off (nth 4 (cadr pw))))
                (:instance fn-his-cursors-at-fit-placement
                 (rcs (caddr pw)) (lens (cadr pw))
                 (cells (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev)))
                              (list (nth 4 (cadr pw))) (list (len (fn-hp-pe ev)))
                              (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev))))))
          :in-theory (e/d (fn-his-place-row fn-his-rcs-put fn-his-pwp)
                          (fn-hp-x-row fn-his-cursors-at fn-hp-pe fn-hp-pe-is-pad8
                           fn-hp-x-add fn-hp-evp fn-hp-pack8 fn-hp-mkey
                           fn-his-cellsp fn-his-cell-bytes fn-his-rcs-fitp fn-his-rcs-write
                           fn-scc-encode fn-scc-encode-is-program adt-placement-ok floor mod)))))

(defthm fn-his-place-row-preserves-cursors-at
 (implies
  (and (fn-his-pwp pw) (fn-hp-evp ev)
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (unsigned-byte-p 64 (nth 4 (cadr pw)))
       (unsigned-byte-p 64 (len (fn-hp-pe ev)))
       (equal (mv-nth 0 (fn-his-place-row ev salt pw starts np pgs-mem)) :ok))
  (let ((out (mv-nth 1 (fn-his-place-row ev salt pw starts np pgs-mem))))
   (fn-his-cursors-at (caddr out) (cadr out))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-row-cells-facts (off (nth 4 (cadr pw))))
                (:instance fn-his-rcs-write-advances
                 (rcs (caddr pw)) (lens (cadr pw))
                 (cells (list (list (fn-hp-mkey ev salt)) (list (len (fn-scc-encode ev)))
                              (list (nth 4 (cadr pw))) (list (len (fn-hp-pe ev)))
                              (fn-hp-pack8 (floor (len (fn-hp-pe ev)) 8) (fn-hp-pe ev))))))
          :in-theory (e/d (fn-his-place-row fn-his-rcs-put fn-his-pwp)
                          (fn-hp-x-row fn-his-cursors-at fn-hp-pe fn-hp-pe-is-pad8
                           fn-hp-x-add fn-hp-evp fn-hp-pack8 fn-hp-mkey
                           fn-his-cellsp fn-his-cell-bytes fn-his-rcs-fitp fn-his-rcs-write
                           fn-scc-encode fn-scc-encode-is-program adt-placement-ok floor mod)))))

(defthm fn-his-place-row-lengths-and-verified
 (let ((out (mv-nth 2 (fn-his-place-row ev salt pw starts np pgs-mem))))
  (and (equal (pgs-w-length out) (pgs-w-length pgs-mem))
       (equal (pgs-d-length out) (pgs-d-length pgs-mem))
       (equal (pgs-v-length out) (pgs-v-length pgs-mem))
       (equal (nth *pgs-vi* out) (nth *pgs-vi* pgs-mem))))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row)
               (fn-his-pwp fn-hp-x-row fn-his-rcs-put fn-his-cellsp fn-hp-mkey
                fn-hp-pack8 adt-placement-ok floor nth adt-nth-1+)))))

(defthm fn-his-place-row-metadata
 (implies (and (fn-his-pwp pw) (fn-hp-evp ev)
               (equal (mv-nth 0 (fn-his-place-row ev salt pw starts np pgs-mem)) :ok))
  (let ((out (mv-nth 1 (fn-his-place-row ev salt pw starts np pgs-mem))))
   (and (equal (car out) (+ 1 (car pw)))
        (equal (cadr out) (fn-hp-x-add (cadr pw) (list 8 8 8 8 (len (fn-hp-pe ev))))))))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row fn-his-rcs-put)
               (fn-his-pwp fn-hp-x-row fn-hp-x-add fn-hp-pe fn-hp-pe-is-pad8 fn-hp-evp
                fn-his-rcs-fitp fn-his-rcs-write fn-his-cellsp fn-hp-mkey fn-hp-pack8
                fn-scc-encode fn-scc-encode-is-program adt-placement-ok floor)))))

(defthm fn-his-cursors-at-fit-flush
 (implies (and (fn-his-cursors-at rcs lens) (nat-listp starts) (natp np)
               (equal (len starts) (len lens)) (adt-placement-ok starts lens np))
          (fn-his-rcs-flush-fitp rcs starts (* 2048 np) np))
 :hints (("Goal" :induct (fn-his-region-ind lens rcs lens starts)
          :in-theory (e/d (fn-his-cursors-at len adt-placement-ok fn-his-rcs-flush-fitp)
                          (fn-his-rcp fn-his-rc-fitp adt-cap adt-apart)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-cap-fits (rc (car rcs)) (start (car starts))
                           (used (car lens)) (ws nil))))))

(defthm fn-his-cursors-at-shape
 (implies (fn-his-cursors-at rcs lens)
          (and (true-listp rcs) (nat-listp lens) (equal (len rcs) (len lens))))
 :hints (("Goal" :induct (fn-his-cursors-at rcs lens)
          :in-theory (e/d (fn-his-cursors-at len) (fn-his-rcp fn-hp-u64-listp)))))

(defthm fn-his-place-all-lengths-and-verified
 (let ((out (mv-nth 2 (fn-his-place-all h salt pw starts np pgs-mem))))
  (and (equal (pgs-w-length out) (pgs-w-length pgs-mem))
       (equal (pgs-d-length out) (pgs-d-length pgs-mem))
       (equal (pgs-v-length out) (pgs-v-length pgs-mem))
       (equal (nth *pgs-vi* out) (nth *pgs-vi* pgs-mem))))
 :hints (("Goal" :induct (fn-his-place-all h salt pw starts np pgs-mem)
          :in-theory (disable fn-his-place-row nth adt-nth-1+))))
