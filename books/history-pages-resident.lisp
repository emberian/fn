; The resident case of the existing P3 reader. This is a construction
; invariant for an installed page root, not a scan performed by each read.
; Cold roots retain the existing explicit need verdict and require a funded
; fill boundary; the event-only generic history export cannot swallow it.
(in-package "ACL2")
(include-book "history-pages-placed")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-hp-resident-range-subrange
  (implies (and (natp p) (natp hi) (natp lo) (natp end)
                (<= p lo) (<= end hi)
                (equal (fn-hp-x-ready-range p hi pgs-mem) :ok))
           (equal (fn-hp-x-ready-range lo end pgs-mem) :ok))
  :hints (("Goal" :induct (fn-hp-x-ready-range lo end pgs-mem)
           :in-theory (disable fn-hp-x-ready))))

(defthm fn-hp-resident-cell-ready
  (implies (and (natp seq) (natp np)
                (< (+ (* 2048 (nfix (nth r starts))) seq) (* 2048 np))
                (equal (fn-hp-x-ready-range 0 np pgs-mem) :ok))
           (equal (mv-nth 0 (fn-hp-x-cell r seq starts pgs-mem)) :ok))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-floor-in-pages
                            (i (+ (* 2048 (nfix (nth r starts))) seq))
                            (p 0) (h np))
                 (:instance fn-hp-x-ready-range-each (p 0) (hi np)
                            (q (floor (+ (* 2048 (nfix (nth r starts))) seq) 2048)))
                 (:instance fn-hp-x-ready-range-ok (p 0) (hi np)))
           :in-theory (e/d (fn-hp-x-cell)
                          (fn-hp-x-ready fn-hp-x-ready-range floor
                           fn-hp-x-ready-range-each pgs-w-length pgs-wi)))))

(defthm fn-hp-resident-pool-ready
  (implies (and (natp lo) (posp k) (natp np)
                (<= (+ lo k) (* 2048 np))
                (equal (fn-hp-x-ready-range 0 np pgs-mem) :ok))
           (equal (fn-hp-x-pool-ready lo k pgs-mem) :ok))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-floor-in-pages (i lo) (p 0) (h np))
                 (:instance fn-hp-floor-in-pages (i (+ lo k -1)) (p 0) (h np))
                 (:instance fn-hp-resident-range-subrange (p 0) (hi np)
                            (lo (floor lo 2048))
                            (end (+ 1 (floor (+ lo k -1) 2048)))))
           :in-theory (e/d (fn-hp-x-pool-ready)
                          (fn-hp-x-ready-range floor
                           fn-hp-resident-range-subrange)))))

(defthm fn-hp-resident-pool-extent
  (implies (and (natp off) (posp plen) (natp pool-bytes)
                (natp start) (natp np) (equal (mod plen 8) 0)
                (<= (+ off plen) pool-bytes)
                (<= (+ (* 16384 start) pool-bytes) (* 16384 np)))
           (and (posp (floor plen 8))
                (<= (+ (* 2048 start) (floor off 8) (floor plen 8))
                    (* 2048 np))))
  :hints (("Goal" :in-theory (enable mod))))

(defun fn-hp-resident-row-boundsp (seq lens starts np)
  (declare (xargs :guard (and (true-listp lens) (true-listp starts))))
  (and (< (+ (* 2048 (nfix (nth 0 starts))) (nfix seq)) (* 2048 (nfix np)))
       (< (+ (* 2048 (nfix (nth 1 starts))) (nfix seq)) (* 2048 (nfix np)))
       (< (+ (* 2048 (nfix (nth 2 starts))) (nfix seq)) (* 2048 (nfix np)))
       (< (+ (* 2048 (nfix (nth 3 starts))) (nfix seq)) (* 2048 (nfix np)))
       (<= (+ (* 16384 (nfix (nth 4 starts))) (nfix (nth 4 lens)))
           (* 16384 (nfix np)))))

(defthm fn-hp-resident-at-ready
  (implies (and (pgs-memp pgs-mem) (natp seq) (natp n) (natp np)
                (fn-hp-resident-row-boundsp seq lens starts np)
                (equal (fn-hp-x-ready-range 0 np pgs-mem) :ok))
           (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-resident-cell-ready (r 0))
                 (:instance fn-hp-resident-cell-ready (r 1))
                 (:instance fn-hp-resident-cell-ready (r 2))
                 (:instance fn-hp-resident-cell-ready (r 3))
                 (:instance fn-hp-resident-pool-extent
                            (off (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)))
                            (plen (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                            (pool-bytes (nfix (nth 4 lens)))
                            (start (nfix (nth 4 starts))))
                 (:instance fn-hp-resident-pool-ready
                            (lo (fn-hp-pool-lo
                                 (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)) starts))
                            (k (floor (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)) 8)))
                 (:instance fn-hp-x-ready-range-ok (p 0) (hi np)))
           :in-theory (e/d (fn-hp-x-at fn-hp-pool-lo fn-hp-resident-row-boundsp)
                          (fn-hp-x-cell fn-hp-x-pool-ready fn-hp-at-core
                           fn-hp-x-words fn-hp-x-ready-range pgs-w-length
                           fn-hp-resident-cell-ready fn-hp-resident-pool-ready
                           fn-hp-resident-pool-extent floor mod
                           fn-hp-x-words-is-take fn-hp-x-pool-ready-bound
                           mv-nth nfix fix)))))

(defthm fn-hp-resident-column-bound
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (equal (len starts) 5) (natp r) (< r 4)
                (natp seq) (< seq (len h)) (natp np))
           (< (+ (* 2048 (nfix (nth r starts))) seq) (* 2048 np)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-lens-col-sizes)
                 (:instance adt-cap-covers (u (* 8 (len h)))))
           :in-theory (disable fn-hp-okp fn-hp-lens adt-placement-ok adt-cap
                               fn-hp-lens-col-sizes nth nfix))))

(defthm fn-hp-resident-pool-region-bound
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (equal (len starts) 5) (natp np))
           (<= (+ (* 16384 (nfix (nth 4 starts))) (nfix (nth 4 (fn-hp-lens h salt))))
               (* 16384 np)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (r 4) (lens (fn-hp-lens h salt)))
                 (:instance adt-cap-covers (u (nfix (nth 4 (fn-hp-lens h salt))))))
           :in-theory (disable fn-hp-okp fn-hp-lens adt-placement-ok adt-cap
                               nth nfix))))

(defthm fn-hp-resident-placement-row-bounds
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (equal (len starts) 5) (natp seq) (< seq (len h)) (natp np))
           (fn-hp-resident-row-boundsp seq (fn-hp-lens h salt) starts np))
  :hints (("Goal" :use ((:instance fn-hp-resident-column-bound (r 0))
                        (:instance fn-hp-resident-column-bound (r 1))
                        (:instance fn-hp-resident-column-bound (r 2))
                        (:instance fn-hp-resident-column-bound (r 3))
                        (:instance fn-hp-resident-pool-region-bound))
           :in-theory (e/d (fn-hp-resident-row-boundsp)
                          (fn-hp-okp fn-hp-lens adt-placement-ok nth nfix
                           fn-hp-resident-column-bound fn-hp-resident-pool-region-bound)))))

; An event-only read is sound on this resident construction boundary. The
; cold reader still answers its ordinary :need-table/:need-page verdict.
(defthm fn-hp-resident-at-is-nth
  (implies (and (pgs-memp pgs-mem) (fn-hp-okp h salt)
                (natp seq) (< seq (len h)) (natp np)
                (fn-hp-starts-okp starts)
                (adt-placement-ok starts (fn-hp-lens h salt) np)
                (equal (fn-hp-x-ready-range 0 np pgs-mem) :ok)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem
                             (fn-hp-piw h salt starts np)))
           (and (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok)
                (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem))
                       (list :ok (nth seq h)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-resident-placement-row-bounds)
                 (:instance fn-hp-resident-at-ready (n (len h)) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-at-is-nth-placed))
           :in-theory (e/d (fn-hp-starts-okp)
                          (fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold
                           fn-hp-x-at fn-hp-x-ready-range adt-placement-ok
                           fn-hp-resident-placement-row-bounds fn-hp-resident-at-ready
                           fn-hp-resident-row-boundsp fn-hp-x-at-is-nth-placed)))))
