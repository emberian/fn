; Each positioned seek probe sets the concrete query bounds and resets
; every source to seek there. A closed interval returns its answer directly.
(in-package "ACL2")
(include-book "range-setup-cursors-proof")
(include-book "range-window-proof")

(defun-nx fn2-range-adapter-query-space-p (r)
  (and (fn2-range-adapter-source-space-p 0 r) (equal (fn2-ranges-schema 0 r) 3)
       (equal (fn2-ranges-qbase 0 r) *fn2-rga-lo*) (equal (fn2-ranges-hbase 0 r) *fn2-rga-hi*)
       (equal (fn2-ranges-qk 0 r) 10) (equal (fn2-ranges-qs 0 r) 0) (equal (fn2-ranges-qg 0 r) 1)))

(local
 (defthm fn2-range-probe-writes-bounds
   (let* ((low (fn2-fields-set-value (1+ *fn2-rga-lo*) mid f))
          (both (fn2-fields-set-value (1+ *fn2-rga-hi*) (1- hi) low)))
     (and (equal (fn2-overview-range-key-at *fn2-rga-lo* both) (list (fn2-fields-value *fn2-rga-lo* f) mid))
          (equal (fn2-overview-range-key-at *fn2-rga-hi* both) (list (fn2-fields-value *fn2-rga-hi* f) (1- hi)))))
   :hints (("Goal" :in-theory (e/d (fn2-overview-range-key-at fn2-fields-set-value fn2-fields-value
                                    update-fn2-fields-value$ai nth-update-nth) (nth update-nth))))))

(local
 (defthm fn2-range-probe-saves-midpoint
   (let* ((fn2-seeks s) (after (fn2-seeks-put 0 (phase *fn2-seek-phase-read*) (mid mid) (probes probes))))
     (and (equal (fn2-seeks-mid 0 after) mid) (equal (fn2-seeks-probes 0 after) probes)
          (equal (fn2-seeks-phase 0 after) *fn2-seek-phase-read*)
          (equal (fn2-seeks-lo 0 after) (fn2-seeks-lo 0 s)) (equal (fn2-seeks-hi 0 after) (fn2-seeks-hi 0 s))))
   :hints (("Goal" :in-theory (e/d (fn2-seeks-phase fn2-seeks-mid fn2-seeks-probes fn2-seeks-lo fn2-seeks-hi
                fn2-seeks-set-phase fn2-seeks-set-mid fn2-seeks-set-probes update-fn2-seeks-phase$ai
                update-fn2-seeks-mid$ai update-fn2-seeks-probes$ai nth-update-nth) (nth update-nth))))))

(local
 (defthm fn2-range-open-probe-midpoint-fits
   (implies (and (natp lo) (unsigned-byte-p 59 hi) (< lo hi))
            (and (unsigned-byte-p 60 (floor (+ lo hi) 2)) (posp hi)))
   :rule-classes nil))

(local
 (defthmd fn2-range-probe-opens-window
   (let* ((mid (floor (+ (fn2-seeks-lo 0 s) (fn2-seeks-hi 0 s)) 2)) (hi (fn2-seeks-hi 0 s))
          (probes (1+ (fn2-seeks-probes 0 s)))
          (step (fn2-seek-step 0 budget s r rs ov ix inst curs paths cache f pool))
          (start (fn2-range-start 0 3 *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads*
                                 *fn2-range-no-position* 0 10 0 1 r rs ov inst)))
     (implies (and (< 0 (fn2-seeks-rows s)) (equal (fn2-seeks-phase 0 s) *fn2-seek-phase-probe*)
                   (equal (fn2-seeks-g 0 s) 0) (fn2-range-adapter-query-space-p r)
                   (< (1+ *fn2-rga-hi*) (fn2-fields-rows f))
                   (natp (fn2-seeks-lo 0 s)) (unsigned-byte-p 59 hi) (< (fn2-seeks-lo 0 s) hi)
                   (unsigned-byte-p 32 probes) (equal (car start) :ok))
              (and (equal (car step) :more) (equal (mv-nth 2 step) (mv-nth 1 start))
                   (equal (mv-nth 3 step) (mv-nth 2 start))
                   (equal (fn2-seeks-phase 0 (mv-nth 1 step)) *fn2-seek-phase-read*)
                   (equal (fn2-seeks-mid 0 (mv-nth 1 step)) mid)
                   (equal (fn2-seeks-probes 0 (mv-nth 1 step)) probes)
                   (equal (fn2-seeks-lo 0 (mv-nth 1 step)) (fn2-seeks-lo 0 s))
                   (equal (fn2-seeks-hi 0 (mv-nth 1 step)) hi)
                   (equal (fn2-overview-range-key-at *fn2-rga-lo* (mv-nth 6 step))
                          (list (fn2-fields-value *fn2-rga-lo* f) mid))
                   (equal (fn2-overview-range-key-at *fn2-rga-hi* (mv-nth 6 step))
                          (list (fn2-fields-value *fn2-rga-hi* f) (1- hi))))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-open-probe-midpoint-fits (lo (fn2-seeks-lo 0 s)) (hi (fn2-seeks-hi 0 s))))
            :in-theory (e/d (fn2-range-adapter-query-space-p fn2-range-adapter-source-space-p fn2-seek-step fn2-seek-probe)
                    (fn2-range-start fn2-seek-narrow fn2-range-step fn2-run-layout-keys fn2-fields-rows fn2-overview-range-key-at
                     fn2-fields-value fn2-fields-set-value fn2-seeks-phase fn2-seeks-g fn2-seeks-rows fn2-seeks-probes
                     fn2-seeks-lo fn2-seeks-hi fn2-seeks-mid fn2-seeks-set-phase fn2-seeks-set-mid fn2-seeks-set-probes
                     fn2-ranges-schema fn2-ranges-qbase fn2-ranges-hbase fn2-ranges-sbase fn2-ranges-smax
                     fn2-ranges-cbase fn2-ranges-rbase fn2-ranges-qk fn2-ranges-qs fn2-ranges-qg fn2-ranges-rows
                     floor natp posp unsigned-byte-p))))))

(defthm fn2-range-seek-probe-locates-input-cursors
  (let* ((lo (fn2-seeks-lo 0 s)) (hi (fn2-seeks-hi 0 s)) (mid (floor (+ lo hi) 2))
         (step (fn2-seek-step 0 budget s r rs ov ix inst curs paths cache f pool)))
    (implies (and (natp j) (<= (len inputs) 5) (fn2-range-input-descriptors-p 16 3 inputs inst)
                  (equal (fn2-run-installed-rows inst) 16) (equal (fn2-range-sources-rows rs) *fn2-rga-smax*)
                  (equal (fn2-range-overlay-descriptor ov) (list 1 *fn2-overlay-phase-active* 3 0 9 0 1))
                  (< 0 (fn2-seeks-rows s)) (equal (fn2-seeks-phase 0 s) *fn2-seek-phase-probe*)
                  (equal (fn2-seeks-g 0 s) 0) (fn2-range-adapter-query-space-p r)
                  (< (1+ *fn2-rga-hi*) (fn2-fields-rows f)) (natp lo) (unsigned-byte-p 59 hi) (< lo hi)
                  (unsigned-byte-p 32 (1+ (fn2-seeks-probes 0 s)))
                  (equal (fn2-fields-value *fn2-rga-lo* f) group) (equal (fn2-fields-value *fn2-rga-hi* f) group))
             (and (equal (car step) :more) (equal (fn2-seeks-phase 0 (mv-nth 1 step)) *fn2-seek-phase-read*)
                  (equal (fn2-seeks-mid 0 (mv-nth 1 step)) mid)
                  (equal (fn2-seeks-probes 0 (mv-nth 1 step)) (1+ (fn2-seeks-probes 0 s)))
                  (equal (fn2-seeks-lo 0 (mv-nth 1 step)) lo) (equal (fn2-seeks-hi 0 (mv-nth 1 step)) hi)
                  (equal (fn2-overview-range-key-at *fn2-rga-lo* (mv-nth 6 step)) (list group mid))
                  (equal (fn2-overview-range-key-at *fn2-rga-hi* (mv-nth 6 step)) (list group (1- hi)))
                  (fn2-range-initial-cursors-p (list :ok (mv-nth 2 step) (mv-nth 3 step)) inputs j rs))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-probe-opens-window
                 (:instance fn2-range-start-locates-built-sources (pf *fn2-range-no-position*) (limit 0)))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-range-adapter-query-space-p fn2-range-adapter-source-space-p fn2-range-initial-cursors-p
                        (:e len) (:t fn2-range-nonempty-run-indices) (:t fn2-range-start) (:t fn2-seek-step)
                        mv-nth car-cons cdr-cons (:e mv-nth) (:e unsigned-byte-p) (:e zp) (:e equal)
                        (:e unary--) (:e binary-+) (:e consp) (:e natp))))))

(defthm fn2-range-seek-driver-returns-closed-interval
  (let ((run (fn2-rgs-drive fuel budget s r rs ov ix inst builds curs paths cache writers restarts f pool fc ctx b3 ds)))
    (implies (and (posp fuel) (< 0 (fn2-seeks-rows s)) (equal (fn2-seeks-phase 0 s) *fn2-seek-phase-probe*)
                  (equal (fn2-seeks-g 0 s) 0) (< 0 (fn2-ranges-rows r))
                  (<= (fn2-seeks-hi 0 s) (fn2-seeks-lo 0 s)))
             (and (equal (car run) :done) (equal (fn2-seeks-lo 0 (mv-nth 1 run)) (fn2-seeks-lo 0 s)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn2-rgs-drive fuel budget s r rs ov ix inst builds curs paths cache writers restarts f pool fc ctx b3 ds))
           :in-theory (e/d (fn2-seek-step fn2-seek-probe fn2-seeks-lo fn2-seeks-set-phase update-fn2-seeks-phase$ai nth-update-nth)
                      (fn2-seeks-phase fn2-seeks-hi fn2-seeks-g fn2-seeks-rows fn2-ranges-rows fn2-range-start fn2-rgs-drive
                       fn2-range-step fn2-seek-narrow fn2-fields-set-value fn2-run-layout-keys nth update-nth)))))
