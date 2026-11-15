; Prepared controller controls. Seal/range/promise identity is explicitly a
; SYNTHETIC internal admission premise. Actual pool reserve/release and actual
; callback guards run below; this is not a persisted sealer merge witness or
; a proof that the promised carrier's B edges were acquired.
(in-package "ACL2")
(include-book "../books/sealer-physical-loader")
(defconst *fn2-spl-stobjs*
 '(fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
   fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed))
(defmacro fn2-spl-local (names form)
 (if (atom names) form `(with-local-stobj ,(car names) (fn2-spl-local ,(cdr names) ,form))))
(defun fn2-sealer-physical-admission-unit (fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
 fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
 fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed) :verify-guards nil))
 (b* ((n *fn2-b-seal-source-cursors*)
      (fn2-seals (fn2-seals-init 1 fn2-seals)) (fn2-csnapshot (fn2-csnapshot-init 1 fn2-csnapshot))
      (fn2-ranges (fn2-ranges-init 1 fn2-ranges)) (fn2-range-sources (fn2-range-sources-init n fn2-range-sources))
      (fn2-run-cursors (fn2-run-cursors-init n fn2-run-cursors)) (fn2-run-loads (fn2-run-loads-init n fn2-run-loads))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 1 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init n fn2-checkpoint-summary-leases))
      (fn2-overlays (fn2-overlays-init 1 fn2-overlays)) (fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      (fn2-pool (fn2-pool-init (list (cons n 4096) (cons n 65536)) 1 100 fn2-pool))
      (fn2-seals (fn2-seals-put 0 (phase *fn2-seal-phase-idle*) (ogen 1) (cbase 0) (rg 0) (sbase 0) (rbase 64) (sid 3)))
      ((mv admitted complete fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
       (fn2-sealer-load-reserve *fn2-idc-owner-kind* 11 1 fn2-seals fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ; With exactly one region's capacity, admission consumed the free pool.
      ; It must still start the pending source rather than demand a second set.
      (fn2-overlays (fn2-overlays-put 0 (phase *fn2-overlay-phase-frozen*) (schema 3) (seq 1) (count 1)))
      (start-status (fn2-sealer-load-status fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-csnapshot))
      (fn2-seals (fn2-seals-put 0 (phase *fn2-seal-phase-build*) (k 1)))
      (fn2-ranges (fn2-ranges-put 0 (phase *fn2-range-phase-seek*) (schema 3) (cbase 0) (sbase 0) (rbase 64) (smax n) (scount 1)))
      (fn2-range-sources (fn2-range-sources-put 0 (kind *fn2-range-kind-run*) (src 0) (cursor 0)))
      (fn2-run-cursors (fn2-run-cursors-put 0 (phase *fn2-run-cursor-phase-miss*) (physical 1) (schema 3) (source-row 0)))
      ((mv foreign & & fn2-run-cursors) (fn2-sealer-load-owner *fn2-idc-owner-kind* 12 1 fn2-seals fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      ((mv owned c load-phase fn2-run-cursors) (fn2-sealer-load-owner *fn2-idc-owner-kind* 11 1 fn2-seals fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      ((mv active-drain &) (fn2-sealer-load-drain 0 *fn2-idc-owner-kind* 11 1 fn2-seals fn2-run-loads))
      (fn2-ranges (fn2-ranges-set-cbase 0 1 fn2-ranges))
      ((mv bad-geometry & & fn2-run-cursors) (fn2-sealer-load-owner *fn2-idc-owner-kind* 11 1 fn2-seals fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-release* fn2-seals))
      ; Pending is synthetic here; real exact event completion is covered by
      ; run-physical-loader-unit, not manufactured by this controller test.
      (fn2-run-loads (fn2-run-loads-put 0 (pending 1) (phase *fn2-run-load-phase-wait*)))
      ((mv pending &) (fn2-sealer-load-drain 0 *fn2-idc-owner-kind* 11 1 fn2-seals fn2-run-loads))
      (fn2-run-loads (fn2-run-loads-put 0 (pending 0) (phase *fn2-run-load-phase-reserved*)))
      ((mv cleaned fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
       (fn2-run-load-region-clean 0 0 n 0 0 0 0 *fn2-idc-owner-kind* 11 1 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      (good (and (eq admitted :ok) (equal complete 1) (eq start-status :admit)
       (eq foreign :source) (eq owned :ok) (equal c 0) (equal load-phase *fn2-run-load-phase-reserved*)
       (eq active-drain :owner) (eq bad-geometry :source) (eq pending :wait) (eq cleaned :ok)
       (equal (fn2-pool-class-countsi 0 fn2-pool) n) (equal (fn2-pool-class-countsi 1 fn2-pool) n)
       (fn2-run-load-region-freep 0 0 n 0 0 0 0 fn2-run-loads fn2-checkpoint-summary-leases))))
  (mv good fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
   fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed)))
(assert-event
 (fn2-spl-local (fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
                fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed)
  (mv-let (good fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
           fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed)
   (fn2-sealer-physical-admission-unit fn2-seals fn2-csnapshot fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads
    fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-overlays fn2-run-installed) good)))

; The catalog/promise carrier is synthetic admission, not edge acquisition.
; This witnesses only the actual RELEASE callback's identity/C-cut boundary
; and preservation of an independent query lease across mutable row reuse.
(defun fn2-sealer-physical-retire-unit (fn2-seals fn2-csnapshot fn2-checkpoint-summary fn2-checkpoint-summary-sources
 fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoint-summary-leases)
 (declare (xargs :stobjs (fn2-seals fn2-csnapshot fn2-checkpoint-summary fn2-checkpoint-summary-sources
 fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoint-summary-leases) :verify-guards nil))
 (b* ((fn2-seals (fn2-seals-init 1 fn2-seals)) (fn2-csnapshot (fn2-csnapshot-init 1 fn2-csnapshot))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 1 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-sources (fn2-checkpoint-summary-sources-init 2 fn2-checkpoint-summary-sources))
      (fn2-checkpoint-cbase-holds (fn2-checkpoint-cbase-holds-init 1 fn2-checkpoint-cbase-holds))
      (fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init 1 fn2-checkpoint-summary-leases))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-release* fn2-seals))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-put 0 (phase *fn2-checkpoint-summary-phase-applied*) (candidate 0)
       (tag 17) (checkpoint 1) (generation 3) (history 1) (incarnation 1) (owner-kind *fn2-idc-owner-kind*) (owner-slot 11) (owner-gen 1)
       (count 1) (installed 1) (lease-count 1)))
      (fn2-checkpoint-cbase-holds (fn2-checkpoint-cbase-holds-put 0 (phase *fn2-checkpoint-cbase-phase-held*)
       (tag 17) (checkpoint 1) (generation 3) (history 1) (incarnation 1) (owner-kind *fn2-idc-owner-kind*) (owner-slot 11) (owner-gen 1)
       (limit 1) (cursor 1) (seen 1)))
      (fn2-checkpoint-summary-sources (fn2-checkpoint-summary-sources-put 1 (tag 17) (schema 3) (rank 7) (top 0) (entries 0)
       (unit *fn2-storage-extent-units*) (epoch 4) (allocation 5)))
      (fn2-run-installed (fn2-run-installed-put 0 (state *fn2-run-installed-state-retired*) (physical 1) (catalog-tag 17)
       (schema 3) (run 7) (top 0) (entries 0) (unit *fn2-storage-extent-units*) (epoch 4) (counter 5)))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-put 0 (live 1) (tag 17) (extent 1) (run-row 0)
       (owner-kind *fn2-idc-owner-kind*) (owner-slot 11) (owner-gen 1)))
      (whole-premise (and (fn2-checkpoint-cbase-promised-p fn2-checkpoint-summary fn2-checkpoint-cbase-holds)
       (fn2-checkpoint-summary-run-source-p 0 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)))
      (fn2-csnapshot (fn2-csnapshot-set-phase 0 *fn2-csnapshot-phase-held* fn2-csnapshot))
      ((mv held fn2-checkpoint-summary fn2-run-installed) (fn2-sealer-load-retire fn2-seals fn2-csnapshot fn2-checkpoint-summary
       fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed))
      (fn2-csnapshot (fn2-csnapshot-set-phase 0 *fn2-csnapshot-phase-idle* fn2-csnapshot))
      (fn2-checkpoint-cbase-holds (fn2-checkpoint-cbase-holds-set-tag 0 16 fn2-checkpoint-cbase-holds))
      ((mv mismatch fn2-checkpoint-summary fn2-run-installed) (fn2-sealer-load-retire fn2-seals fn2-csnapshot fn2-checkpoint-summary
       fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed))
      (unchanged (and (equal (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 1)
       (equal (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-retired*)))
      (fn2-checkpoint-cbase-holds (fn2-checkpoint-cbase-holds-set-tag 0 17 fn2-checkpoint-cbase-holds))
      ((mv retired fn2-checkpoint-summary fn2-run-installed) (fn2-sealer-load-retire fn2-seals fn2-csnapshot fn2-checkpoint-summary
       fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed))
      (good (and whole-premise (eq held :busy) (eq mismatch :source) unchanged (eq retired :retired)
       (equal (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-free*)
       (equal (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 0)
       (equal (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 1)
       (equal (fn2-checkpoint-cbase-holds-phase 0 fn2-checkpoint-cbase-holds) *fn2-checkpoint-cbase-phase-held*)
       (fn2-checkpoint-summary-lease-current-p 0 *fn2-idc-owner-kind* 11 1 fn2-checkpoint-summary
        fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed))))
  (mv good fn2-seals fn2-csnapshot fn2-checkpoint-summary fn2-checkpoint-summary-sources
   fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoint-summary-leases)))
(assert-event
 (fn2-spl-local (fn2-seals fn2-csnapshot fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoint-summary-leases)
  (mv-let (good fn2-seals fn2-csnapshot fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoint-summary-leases)
   (fn2-sealer-physical-retire-unit fn2-seals fn2-csnapshot fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoint-summary-leases) good)))
