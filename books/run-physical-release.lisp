; Request close drains private cursor resources and then its catalog lease.
; No in-flight operation or borrowed workspace may be reclaimed here.
(in-package "ACL2")
(include-book "run-physical-source")
(fn2-book-layer :c)
(defun fn2-run-load-release (c kind owner generation fn2-run-loads fn2-run-cursors
 fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp c) (< c (fn2-run-loads-rows fn2-run-loads))
                    (< c (fn2-run-cursors-rows fn2-run-cursors)) (< c (fn2-checkpoint-summary-leases-rows fn2-checkpoint-summary-leases))))
       (mv :bounds fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((when (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-idle*))
       (mv (if (equal (fn2-checkpoint-summary-leases-live c fn2-checkpoint-summary-leases) 0) :ok :source)
        fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((unless (equal (fn2-run-loads-lease-mode c fn2-run-loads) *fn2-run-load-lease-mode-owned*))
       (mv :borrowed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((unless (and (fn2-run-load-ownerp c kind owner generation fn2-run-loads)
                    (equal (fn2-run-loads-pending c fn2-run-loads) 0)))
       (mv :pending fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      (page (fn2-run-loads-page c fn2-run-loads)) (pgen (fn2-run-loads-page-gen c fn2-run-loads))
      (scratch (fn2-run-loads-scratch c fn2-run-loads)) (sgen (fn2-run-loads-scratch-gen c fn2-run-loads))
      (two (equal (fn2-run-loads-windows c fn2-run-loads) 2))
      ((unless (and (member (fn2-run-loads-windows c fn2-run-loads) '(1 2)) (not (equal page scratch))
                    (eq (fn2-pool-workspace-code page pgen kind owner generation fn2-pool) :ok)
                    (or (not two) (eq (fn2-pool-workspace-code scratch sgen kind owner generation fn2-pool) :ok))
                    (fn2-pool-release-countp page fn2-pool) (or (not two) (fn2-pool-release-countp scratch fn2-pool))))
       (mv :pending fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((mv code fn2-pool) (fn2-pool-release page pgen kind owner generation fn2-pool))
      ((unless (member-eq code '(:ok :retired))) (mv code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((unless (or (not two) (fn2-pool-release-countp scratch fn2-pool)))
       (mv :recovery-required fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((mv code fn2-pool) (if two (fn2-pool-release scratch sgen kind owner generation fn2-pool) (mv :ok fn2-pool)))
      ((unless (member-eq code '(:ok :retired))) (mv code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((mv code fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (if (equal (fn2-checkpoint-summary-leases-live c fn2-checkpoint-summary-leases) 1)
        (fn2-checkpoint-summary-release c kind owner generation fn2-checkpoint-summary fn2-checkpoint-summary-leases)
        (mv :ok fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
      ((unless (eq code :ok)) (mv :recovery-required fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      (fn2-run-cursors (fn2-run-cursors-put c (phase *fn2-run-cursor-phase-idle*) (physical 0)))
      (fn2-run-loads (fn2-run-loads-put c (phase *fn2-run-load-phase-idle*) (tag 0) (windows 0)
       (kind 0) (owner 0) (generation 0))))
  (mv :ok fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))

(fn2-run-load-frames fn2-run-load-release
 (c kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-checkpoint-summary 3) (fn2-checkpoint-summary-leases 4) (fn2-pool 5)))

; Resolved C operations may retain the private bytes through stage retries,
; but must drop old catalog obligations before waiting for a base writer.
; The actual caller proves its resolve/version boundary; this leaf grants
; no permission to stage stale RES fields and never releases pool windows.
; Exact precondition of the canonical park operation. Region CLOSE may
; preflight all jobs before releasing any lease; this predicate confers no
; actual-machine authority and is not a readiness certificate.
(defun fn2-run-load-parkable-p (c kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (and (fn2-run-load-ownerp c kind owner generation fn2-run-loads)
                    (< c (fn2-run-cursors-rows fn2-run-cursors)) (< c (fn2-checkpoint-summary-leases-rows fn2-checkpoint-summary-leases))
                    (equal (fn2-run-loads-lease-mode c fn2-run-loads) *fn2-run-load-lease-mode-owned*)
                    (member (fn2-run-loads-phase c fn2-run-loads) (list *fn2-run-load-phase-reserved* *fn2-run-load-phase-ready*))
                    (equal (fn2-run-loads-windows c fn2-run-loads) 2) (equal (fn2-run-loads-pending c fn2-run-loads) 0)
                    (eq (fn2-pool-workspace-code (fn2-run-loads-page c fn2-run-loads) (fn2-run-loads-page-gen c fn2-run-loads) kind owner generation fn2-pool) :ok)
                    (eq (fn2-pool-workspace-code (fn2-run-loads-scratch c fn2-run-loads) (fn2-run-loads-scratch-gen c fn2-run-loads) kind owner generation fn2-pool) :ok)))

; Shared static mutations, after each actual owner proves its own
; terminal source-view/pending/workspace boundary. No pool lease is freed.
(defmacro fn2-run-load-park-source-mutations ()
 `(b* (((mv code fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (if (equal (fn2-checkpoint-summary-leases-live c fn2-checkpoint-summary-leases) 1)
        (fn2-checkpoint-summary-release c kind owner generation fn2-checkpoint-summary fn2-checkpoint-summary-leases)
        (mv :ok fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
      ((unless (eq code :ok)) (mv code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      (fn2-run-cursors (fn2-run-cursors-put c (phase *fn2-run-cursor-phase-idle*) (physical 0)))
      (fn2-run-loads (fn2-run-loads-put c (phase *fn2-run-load-phase-reserved*) (source *fn2-none*) (tag 0))))
  (mv :ok fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)))

(defun fn2-run-load-park-source (c kind owner generation fn2-run-loads fn2-run-cursors
 fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (fn2-run-load-parkable-p c kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool))
       (mv :source fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
  (fn2-run-load-park-source-mutations)))
(fn2-run-load-frames fn2-run-load-park-source
 (c kind owner generation fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-checkpoint-summary 3) (fn2-checkpoint-summary-leases 4)))
