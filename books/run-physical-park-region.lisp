; CLOSE preflights every job before dropping any catalog obligation. Private
; windows remain owned; the actual caller releases its observer only on :ok.
(in-package "ACL2")
(include-book "run-physical-region")
(fn2-book-layer :c)
(defun fn2-run-load-region-park-check (i b0 n0 b1 n1 b2 n2 kind owner generation
 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :measure (nfix (- (fn2-run-load-region-count n0 n1 n2) (nfix i)))
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* (((when (>= (nfix i) (fn2-run-load-region-count n0 n1 n2))) (mv :ok 0))
      (c (fn2-run-load-region-cursor i b0 n0 b1 n1 b2 n2))
      ((unless (and (< c (fn2-run-loads-rows fn2-run-loads))
                    (< c (fn2-run-cursors-rows fn2-run-cursors))
                    (< c (fn2-checkpoint-summary-leases-rows fn2-checkpoint-summary-leases)))) (mv :bounds 0))
      (idle (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-idle*))
      (live (equal (fn2-checkpoint-summary-leases-live c fn2-checkpoint-summary-leases) 1))
      ((unless (if idle (and (not live) (equal (fn2-run-loads-windows c fn2-run-loads) 0)
                             (equal (fn2-run-loads-pending c fn2-run-loads) 0))
                 (and (fn2-run-load-parkable-p c kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool)
                      (or (not live) (fn2-checkpoint-summary-releaseable-p c kind owner generation fn2-checkpoint-summary fn2-checkpoint-summary-leases)))))
       (mv :source 0))
      ((mv code rest) (fn2-run-load-region-park-check (+ (nfix i) 1) b0 n0 b1 n1 b2 n2 kind owner generation
                       fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
  (mv code (+ (if live 1 0) rest))))

(defun fn2-run-load-region-park-apply (i b0 n0 b1 n1 b2 n2 kind owner generation
 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :measure (nfix (- (fn2-run-load-region-count n0 n1 n2) (nfix i)))
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* (((when (>= (nfix i) (fn2-run-load-region-count n0 n1 n2)))
       (mv :ok fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      (c (fn2-run-load-region-cursor i b0 n0 b1 n1 b2 n2))
      ((unless (< c (fn2-run-loads-rows fn2-run-loads)))
       (mv :bounds fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      ((mv code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (if (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-idle*)
        (mv :ok fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)
        (fn2-run-load-park-source c kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
      ((unless (eq code :ok))
       (mv :recovery-required fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
  (fn2-run-load-region-park-apply (+ (nfix i) 1) b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))

(defun fn2-run-load-region-park (b0 n0 b1 n1 b2 n2 kind owner generation
 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (fn2-run-load-regionp b0 n0 b1 n1 b2 n2 (fn2-run-loads-rows fn2-run-loads)
                (fn2-run-cursors-rows fn2-run-cursors) (fn2-checkpoint-summary-leases-rows fn2-checkpoint-summary-leases)))
       (mv :bounds fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      ((mv code count) (fn2-run-load-region-park-check 0 b0 n0 b1 n1 b2 n2 kind owner generation
                       fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((unless (and (eq code :ok) (or (equal count 0)
                    (and (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                         (<= count (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary))))))
       (mv :source fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
  (fn2-run-load-region-park-apply 0 b0 n0 b1 n1 b2 n2 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))

(fn2-run-load-frames fn2-run-load-region-park
 (b0 n0 b1 n1 b2 n2 kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-checkpoint-summary 3) (fn2-checkpoint-summary-leases 4)))
