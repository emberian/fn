; From a free overlay and two available reservations, the actual adapter
; accepts a single arbitrary admitted overview and records its exact bytes.
(in-package "ACL2")
(include-book "range-overlay-start-workspace-proof")

(defmacro fn2-ov-input-start ()
  '(let* ((a (fn2-pool-reserve 0 9 0 1 fn2-pool))
          (s (fn2-pool-reserve 0 9 0 1 (mv-nth 3 a))))
     (fn2-ov-start 0 3 (mv-nth 1 a) (mv-nth 2 a) 0 256 9 0 1 0 fn2-overlays fn2-overlay-index (mv-nth 3 s))))

(local
 (defthmd fn2-ov-one-input-load
   (let* ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-adapter-entry* src sg 0 9 0 1 f pool))
          (ins (fn2-ov-insert 0 *fn2-run-adapter-entry* *fn2-run-adapter-reader* ov ix (mv-nth 2 load) (mv-nth 3 load)))
          (run (fn2-ov-adapter-load 3 *fn2-overview-entry* (list row) src sg 0 ov ix f pool)))
     (implies (and (equal (car load) :ok) (equal (car ins) :ok))
              (equal run (list '(:ok) (mv-nth 1 ins) (mv-nth 2 ins) (mv-nth 3 ins) (mv-nth 4 ins)))))
   :hints (("Goal" :expand ((fn2-ov-adapter-load 3 *fn2-overview-entry* (list row) src sg 0 ov ix f pool)
                            (:free (a b c d e) (fn2-ov-adapter-load 3 *fn2-overview-entry* nil src sg a b c d e)))
            :in-theory (disable fn2-run-load-values fn2-ov-insert fn2-ov-adapter-load)))))

(defthmd fn2-ov-adapter-loads-first-row
  (let* ((bytes (fn2-layout-octets *fn2-overview-entry* row)) (size (len bytes))
         (run (fn2-ov-adapter-load 3 *fn2-overview-entry* (list row) src sg 0 ov ix f pool)))
    (implies (and (fn2-ov-load-workspaces-p nil src sg ov ix f pool) (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (equal (fn2-overlays-fill 0 ov) 0) (equal (fn2-overlays-ibase 0 ov) 0))
             (and (equal (car run) '(:ok)) (equal (fn2-overlays-count 0 (mv-nth 1 run)) 1)
                  (equal (fn2-overlays-fill 0 (mv-nth 1 run)) size) (equal (fn2-overlay-index-off 0 (mv-nth 2 run)) 0)
                  (equal (fn2-run-read-bytes size (fn2-overlays-slot 0 ov) (fn2-overlays-gen 0 ov) 0 9 0 1 (mv-nth 4 run)) bytes))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-inserts-next-prefix-row (rows nil) (j 0)) fn2-ov-one-input-load)
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-run-sorted-spec (:e fn2-run-entries-layoutp) (:e fn2-range-line-bytes) (:e len) (:e append)
                         binary-append car-cons cdr-cons (:e consp) (:e natp) (:e <) (:e equal)
                         (:e binary-+) unicity-of-0 fix (:t len) mv-nth (:e mv-nth))))))

(local
 (defthmd fn2-ov-input-start-addresses
   (let ((res (fn2-ov-start 0 3 dst dg 0 256 9 0 1 0 ov ix p)))
     (implies (equal (car res) :ok)
              (and (equal (fn2-overlays-fill 0 (mv-nth 1 res)) 0) (equal (fn2-overlays-ibase 0 (mv-nth 1 res)) 0)
                   (equal (fn2-overlays-slot 0 (mv-nth 1 res)) dst) (equal (fn2-overlays-gen 0 (mv-nth 1 res)) dg))))
   :hints (("Goal" :in-theory (e/d (fn2-ov-start fn2-overlays-slot fn2-overlays-gen fn2-overlays-ibase fn2-overlays-fill)
                        (fn2-pool-reset fn2-pool-slot-cap fn2-overlays-rows fn2-pool-rows fn2-overlay-index-rows
                         fn2-overlays-phase unsigned-byte-p nth update-nth))))))

(local
 (defthmd fn2-ov-single-accepted-status
   (equal (subsetp-eq '(:ok) '(:ok)) t)))

(defthm fn2-range-overlay-loads-single-input
  (let* ((bytes (fn2-layout-octets *fn2-overview-entry* row)) (size (len bytes))
         (run (fn2-rga-call fn2-rga-overlay 3 *fn2-overview-entry* (list row))))
    (implies (and (natp n) (<= 2 n) (fn2-range-pool-available-p n fn2-pool)
                  (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-overlays-wfp fn2-overlays)
                  (< 0 (fn2-overlays-rows fn2-overlays)) (equal (fn2-overlays-phase 0 fn2-overlays) *fn2-overlay-phase-free*)
                  (fn2-overlay-index-wfp fn2-overlay-index) (<= 256 (fn2-overlay-index-rows fn2-overlay-index))
                  (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (<= (+ *fn2-run-adapter-reader* *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))
                  (fn2-run-values-layoutp *fn2-overview-entry* row))
             (and (equal (car run) :ok) (equal (fn2-overlays-count 0 (mv-nth 3 run)) 1)
                  (equal (fn2-overlays-fill 0 (mv-nth 3 run)) size) (equal (fn2-overlay-index-off 0 (mv-nth 4 run)) 0)
                  (equal (fn2-run-read-bytes size (- 327 n) 1 0 9 0 1 (mv-nth 13 run)) bytes))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-reserved-start-prepares-empty-prefix (p fn2-pool) (ov fn2-overlays) (ix fn2-overlay-index) (f fn2-fields))
                 (:instance fn2-range-build-reserves-workspaces (p fn2-pool))
                 (:instance fn2-ov-adapter-loads-first-row
                    (src (mv-nth 1 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool)))))
                    (sg (mv-nth 2 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool)))))
                    (ov (mv-nth 1 (fn2-ov-input-start))) (ix fn2-overlay-index) (f fn2-fields) (pool (mv-nth 2 (fn2-ov-input-start)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-rga-overlay fn2-ov-input-start-addresses fn2-ov-single-accepted-status eq
                       (:t fn2-ov-adapter-load) (:t fn2-pool-reserve) (:t fn2-ov-start)
                       mv-nth car-cons cdr-cons (:e equal) (:e mv-nth) (:e zp) (:e not)
                       (:e unary--) (:e binary-+) (:e consp))))))
