; Starting the overview range puts the active overlay in slot zero and
; opens the remaining slots in descending run order.
(in-package "ACL2")
(include-book "range-built-overlay-proof")
(include-book "range-input-catalog-proof")

(local
 (defthm fn2-range-enumerates-one-overlay
   (let* ((add (fn2-range-add-overlays 1 0 g sid r rs ov)) (after (mv-nth 2 add)))
     (implies (and (natp j) (fn2-range-adapter-source-space-p g r)
                   (equal (fn2-range-sources-rows rs) *fn2-rga-smax*)
                   (equal (fn2-range-overlay-descriptor ov)
                          (list 1 *fn2-overlay-phase-active* sid 0 9 0 1)))
              (and (equal (car add) :ok) (equal (mv-nth 1 add) 1)
                   (equal (fn2-range-sources-rows after) *fn2-rga-smax*)
                   (equal (fn2-range-source-cursor-record j after)
                          (if (zp j) (fn2-range-fresh-cursor-record 0 *fn2-range-kind-overlay* 0 0)
                            (fn2-range-source-cursor-record j rs))))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-range-add-overlays 1 0 g sid r rs ov)
                            (:free (i rs) (fn2-range-add-overlays 0 i g sid r rs ov)))
            :use ((:instance fn2-range-add-assigns-cursor (i 0) (kind *fn2-range-kind-overlay*) (ref 0) (run 0)))
            :in-theory (e/d (fn2-range-overlay-descriptor)
                      (fn2-range-add-source fn2-range-adapter-source-space-p fn2-range-sources-rows
                       fn2-range-source-cursor-record fn2-range-fresh-cursor-record fn2-overlays-phase fn2-overlays-rows
                       fn2-overlays-schema fn2-overlays-seq fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(local
 (defthm fn2-range-saves-source-count
   (let* ((fn2-ranges r)
          (after (fn2-ranges-put g (phase *fn2-range-phase-seek*) (scount count) (vrun version))))
     (implies (natp g)
              (and (equal (fn2-ranges-phase g after) *fn2-range-phase-seek*)
                   (equal (fn2-ranges-scount g after) count)
                   (equal (fn2-ranges-vrun g after) version))))
   :hints (("Goal" :in-theory (e/d (fn2-ranges-phase fn2-ranges-scount fn2-ranges-vrun nth-update-nth)
                                   (nth update-nth))))))

(local
 (defthm fn2-range-enumeration-records-located-sources
   (let* ((overlay (fn2-range-add-overlays 1 0 g sid r rs ov))
          (runs (fn2-range-add-runs 16 1 g sid 0 r (mv-nth 2 overlay) inst))
          (n (mv-nth 1 runs)) (v (fn2-run-version sid 16 inst))
          (res (fn2-range-enumerate g r rs ov inst)) (after (mv-nth 1 res)))
     (implies (and (fn2-range-adapter-source-space-p g r) (equal (fn2-ranges-schema g r) sid)
                   (equal (fn2-range-overlay-descriptor ov) (list 1 *fn2-overlay-phase-active* sid 0 9 0 1))
                   (equal (fn2-run-installed-rows inst) 16)
                   (equal (car overlay) :ok) (equal (mv-nth 1 overlay) 1)
                   (equal (car runs) :ok) (unsigned-byte-p 32 n) (unsigned-byte-p 60 v))
              (and (equal (car res) :ok) (equal (mv-nth 2 res) (mv-nth 2 runs))
                   (equal (fn2-ranges-phase g after) *fn2-range-phase-seek*)
                   (equal (fn2-ranges-scount g after) n) (equal (fn2-ranges-vrun g after) v))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-range-enumerate fn2-range-adapter-source-space-p fn2-range-overlay-descriptor)
                 (fn2-range-add-overlays fn2-range-add-runs fn2-run-version unsigned-byte-p
                  fn2-ranges-schema fn2-ranges-rows fn2-ranges-cbase fn2-ranges-sbase fn2-ranges-rbase fn2-ranges-smax
                  fn2-ranges-phase fn2-ranges-scount fn2-ranges-vrun fn2-run-installed-rows fn2-overlays-phase
                  fn2-overlays-seq fn2-overlays-schema fn2-overlays-rows fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(defthmd fn2-range-enumerates-adapter-cursors
  (let* ((refs (fn2-range-nonempty-run-indices 16 inputs)) (ref (nth (1- j) refs))
         (version (if (consp refs) (1+ (car refs)) 0))
         (add (fn2-range-enumerate g r rs ov inst)) (after (mv-nth 1 add)))
    (implies (and (natp j) (<= (len inputs) 5)
                  (fn2-range-input-descriptors-p 16 sid inputs inst) (equal (fn2-run-installed-rows inst) 16)
                  (fn2-range-adapter-source-space-p g r) (equal (fn2-ranges-schema g r) sid)
                  (equal (fn2-range-sources-rows rs) *fn2-rga-smax*)
                  (equal (fn2-range-overlay-descriptor ov) (list 1 *fn2-overlay-phase-active* sid 0 9 0 1)))
             (and (equal (car add) :ok)
                  (equal (fn2-ranges-phase g after) *fn2-range-phase-seek*)
                  (equal (fn2-ranges-scount g after) (1+ (len refs)))
                  (equal (fn2-ranges-vrun g after) version)
                  (equal (fn2-range-source-cursor-record j (mv-nth 2 add))
                         (cond ((zp j) (fn2-range-fresh-cursor-record 0 *fn2-range-kind-overlay* 0 0))
                               ((<= j (len refs)) (fn2-range-fresh-cursor-record j *fn2-range-kind-run* ref (1+ ref)))
                               (t (fn2-range-source-cursor-record j rs)))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-enumeration-records-located-sources fn2-range-enumerates-one-overlay
                 (:instance fn2-range-run-count-fits-input (n 16))
                 (:instance fn2-range-input-catalog-version (n 16))
                 (:instance fn2-range-enumerates-input-runs (n 16) (i 1)
                            (rs (mv-nth 2 (fn2-range-add-overlays 1 0 g sid r rs ov)))))
           :in-theory (disable fn2-range-enumerate fn2-range-adapter-source-space-p fn2-range-overlay-descriptor
                      fn2-range-add-overlays fn2-range-add-runs fn2-run-version fn2-range-nonempty-run-indices
                      fn2-range-input-descriptors-p fn2-range-source-cursor-record fn2-range-fresh-cursor-record
                      fn2-ranges-schema fn2-ranges-phase fn2-ranges-scount fn2-ranges-vrun
                      fn2-run-installed-rows fn2-range-sources-rows nth len))))

(local
 (defmacro fn2-range-configured-row (g pf limit r)
   `(let ((fn2-ranges ,r))
      (fn2-ranges-put ,g (phase *fn2-range-phase-idle*) (schema 3) (qbase *fn2-rga-lo*) (hbase *fn2-rga-hi*)
        (sbase 0) (smax *fn2-rga-smax*) (scount 0) (cbase 0) (rbase *fn2-rga-heads*) (vrun 0)
        (pfield ,pf) (plimit ,limit) (out 0) (ok 0) (os 0) (og 0) (delivered 0) (qk 10) (qs 0) (qg 1)))))

(local
 (defthm fn2-range-configured-row-has-cursor-space
   (let ((row (fn2-range-configured-row g pf limit r)))
     (implies (and (natp g) (< g (fn2-ranges-rows r)))
              (and (fn2-range-adapter-source-space-p g row) (equal (fn2-ranges-schema g row) 3))))
   :hints (("Goal" :in-theory (e/d (fn2-range-adapter-source-space-p fn2-ranges-rows fn2-ranges-schema
                              fn2-ranges-sbase fn2-ranges-cbase fn2-ranges-rbase fn2-ranges-smax nth-update-nth)
                             (nth update-nth))))))

(defthmd fn2-range-start-locates-built-sources
  (let* ((refs (fn2-range-nonempty-run-indices 16 inputs)) (ref (nth (1- j) refs))
         (start (fn2-range-start 0 3 *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads*
                                 pf limit 10 0 1 r rs ov inst))
         (after (mv-nth 1 start)))
    (implies (and (natp j) (<= (len inputs) 5) (< 0 (fn2-ranges-rows r))
                  (unsigned-byte-p 32 pf) (unsigned-byte-p 60 limit)
                  (fn2-range-input-descriptors-p 16 3 inputs inst) (equal (fn2-run-installed-rows inst) 16)
                  (equal (fn2-range-sources-rows rs) *fn2-rga-smax*)
                  (equal (fn2-range-overlay-descriptor ov) (list 1 *fn2-overlay-phase-active* 3 0 9 0 1)))
             (and (equal (car start) :ok) (equal (fn2-ranges-phase 0 after) *fn2-range-phase-seek*)
                  (equal (fn2-ranges-scount 0 after) (1+ (len refs)))
                  (equal (fn2-ranges-vrun 0 after) (if (consp refs) (1+ (car refs)) 0))
                  (equal (fn2-range-source-cursor-record j (mv-nth 2 start))
                         (cond ((zp j) (fn2-range-fresh-cursor-record 0 *fn2-range-kind-overlay* 0 0))
                               ((<= j (len refs)) (fn2-range-fresh-cursor-record j *fn2-range-kind-run* ref (1+ ref)))
                               (t (fn2-range-source-cursor-record j rs)))))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-enumerates-adapter-cursors (g 0) (sid 3) (r (fn2-range-configured-row 0 pf limit r))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-start fn2-range-configured-row-has-cursor-space
                    (:e unsigned-byte-p) (:e natp) (:e binary-+) (:e equal) not)))))
