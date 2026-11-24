; Follow the setup, run builds, and overlay load shared by the read and seek
; adapters up to their call of range-start.
(in-package "ACL2")
(include-book "range-started-sources-proof")

(local
 (defthm fn2-range-build-preserves-reader-tables
   (let ((build (fn2-rga-call fn2-rga-build sid layout entries k)))
     (and (equal (mv-nth 1 build) fn2-ranges) (equal (mv-nth 2 build) fn2-range-sources)
          (equal (mv-nth 3 build) fn2-overlays)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-rga-build eq atom mv-nth car-cons cdr-cons (:e mv-nth) (:e equal)
                         (:e binary-+) (:e unary--) (:e zp) (:e consp)))))))

(local
 (defthm fn2-range-building-runs-preserves-reader-tables
   (let ((build (fn2-rga-call fn2-rga-builds sid layout entries k)))
     (and (equal (mv-nth 2 build) fn2-ranges) (equal (mv-nth 3 build) fn2-range-sources)
          (equal (mv-nth 4 build) fn2-overlays)))
   :hints (("Goal" :induct (fn2-rga-call fn2-rga-builds sid layout entries k)
            :in-theory (disable fn2-rga-build)))))

(local
 (defthm fn2-range-initial-reader-tables
   (let ((setup (fn2-rga-call fn2-rga-setup)))
     (and (equal (fn2-ranges-rows (mv-nth 1 setup)) 1)
          (equal (fn2-range-sources-rows (mv-nth 2 setup)) *fn2-rga-smax*)
          (equal (fn2-overlays-rows (mv-nth 3 setup)) 1)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-rga-setup fn2-ranges-init-rows fn2-range-sources-init-rows fn2-overlays-init-rows
                          mv-nth car-cons cdr-cons (:e mv-nth) (:e equal) (:e binary-+)
                          (:e unary--) (:e zp) (:e consp)))))))

(defmacro fn2-range-load-after-builds (sid layout inputs overlay)
  `(b* (((mv & & ,@*fn2-rga-stobjs*) (fn2-range-build-from-setup ,sid ,layout ,inputs)))
     (fn2-rga-call fn2-rga-overlay ,sid ,layout ,overlay)))

(local
 (defthm fn2-range-overlay-keeps-query-tables
   (let ((load (fn2-rga-call fn2-rga-overlay sid layout entries)))
     (and (equal (mv-nth 1 load) fn2-ranges) (equal (mv-nth 2 load) fn2-range-sources)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-rga-overlay eq mv-nth car-cons cdr-cons
                           (:e mv-nth) (:e equal) (:e binary-+) (:e unary--) (:e zp) (:e consp)))))))

(defun-nx fn2-range-initial-cursors-p (start inputs j rs)
  (let* ((refs (fn2-range-nonempty-run-indices 16 inputs)) (ref (nth (1- j) refs))
         (after (mv-nth 1 start)))
    (and (equal (car start) :ok) (equal (fn2-ranges-phase 0 after) *fn2-range-phase-seek*)
         (equal (fn2-ranges-scount 0 after) (1+ (len refs)))
         (equal (fn2-ranges-vrun 0 after) (if (consp refs) (1+ (car refs)) 0))
         (equal (fn2-range-source-cursor-record j (mv-nth 2 start))
                (cond ((zp j) (fn2-range-fresh-cursor-record 0 *fn2-range-kind-overlay* 0 0))
                      ((<= j (len refs)) (fn2-range-fresh-cursor-record j *fn2-range-kind-run* ref (1+ ref)))
                      (t (fn2-range-source-cursor-record j rs)))))))

(local
 (defthmd fn2-range-loaded-input-cursors
   (let* ((load (fn2-rga-call fn2-rga-overlay 3 *fn2-overview-entry* overlay))
          (start (fn2-range-start 0 3 *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads*
                    pf limit 10 0 1 (mv-nth 1 load) (mv-nth 2 load) (mv-nth 3 load) (mv-nth 5 load))))
     (implies (and (equal (car load) :ok) (natp j) (<= (len inputs) 5)
                   (unsigned-byte-p 32 pf) (unsigned-byte-p 60 limit)
                   (equal (fn2-ranges-rows fn2-ranges) 1) (equal (fn2-overlays-rows fn2-overlays) 1)
                   (equal (fn2-range-sources-rows fn2-range-sources) *fn2-rga-smax*)
                   (equal (fn2-run-installed-rows fn2-run-installed) 16)
                   (fn2-range-input-descriptors-p 16 3 inputs fn2-run-installed))
              (fn2-range-initial-cursors-p start inputs j fn2-range-sources)))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-start-locates-built-sources
                   (r fn2-ranges) (rs fn2-range-sources) (inst fn2-run-installed)
                   (ov (mv-nth 3 (fn2-rga-call fn2-rga-overlay 3 *fn2-overview-entry* overlay)))))
            :in-theory (union-theories (theory 'minimal-theory)
                          '(fn2-range-loaded-overlay-source fn2-range-overlay-keeps-query-tables
                            fn2-range-initial-cursors-p (:e len) (:t fn2-range-nonempty-run-indices) (:e <) (:e equal) (:e not)))))))

(defthmd fn2-range-setup-locates-input-cursors
  (let* ((build (fn2-range-build-from-setup 3 *fn2-overview-entry* inputs))
         (load (fn2-range-load-after-builds 3 *fn2-overview-entry* inputs overlay))
         (start (fn2-range-start 0 3 *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads*
                   pf limit 10 0 1 (mv-nth 1 load) (mv-nth 2 load) (mv-nth 3 load) (mv-nth 5 load))))
    (implies (and (equal (car build) :ok) (equal (car load) :ok)
                  (natp j) (<= (len inputs) 5) (unsigned-byte-p 32 pf) (unsigned-byte-p 60 limit))
             (fn2-range-initial-cursors-p start inputs j (mv-nth 3 build))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-built-source-at-input-index (sid 3) (layout *fn2-overview-entry*) (r 0) (runs inputs))
                 (:instance fn2-range-setup-build-catalog (sid 3) (layout *fn2-overview-entry*) (n 16)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-range-loaded-input-cursors fn2-range-building-runs-preserves-reader-tables
                          fn2-range-initial-reader-tables (:e natp) (:e equal) (:e <) (:e not))))))
