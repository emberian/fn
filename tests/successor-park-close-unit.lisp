; UNEXECUTED CLOSE lifetime control. The applied catalog/installed semantic
; root is an explicit SYNTHETIC opener, not source authentication or adoption.
; Reserve, acquire, immutable HAND/RETURN, canonical park and receipt release
; are actual functions. No READY or pending/completed flag is seeded.
(in-package "ACL2")
(include-book "../books/machines-c-bind")
(defun fn2-spc-body (mode fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-pool) :verify-guards nil))
 (b* ((fn2-succ-txns (fn2-succ-txns-init 1 fn2-succ-txns))
      (fn2-run-cursors (fn2-run-cursors-init 1 fn2-run-cursors))
      (fn2-fields (fn2-fields-init (max 256 *fn2-idc-stride*) fn2-fields))
      (fn2-c-source-control (fn2-c-source-control-init 1 fn2-c-source-control))
      (fn2-c-source-readers (fn2-c-source-readers-init 1 fn2-c-source-readers))
      (fn2-run-loads (fn2-run-loads-init 1 fn2-run-loads))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 2 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-sources (fn2-checkpoint-summary-sources-init 1 fn2-checkpoint-summary-sources))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init 1 fn2-checkpoint-summary-leases))
      (fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      (fn2-pool (fn2-pool-init '((1 . 4096) (1 . 65536)) 1 100 fn2-pool))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-put 0 (phase *fn2-checkpoint-summary-phase-applied*) (tag 7) (count 1) (installed 1)))
      (fn2-checkpoint-summary-sources (fn2-checkpoint-summary-sources-put 0 (tag 7) (schema 8) (rank 1) (top 0) (entries 1) (unit 0) (epoch 4) (allocation 35)))
      ((mv install fn2-run-installed) (fn2-run-install-physical 0 8 1 1 0 1 0 4 35 7 0 0 0 0 0 0 0 0 fn2-run-installed))
      ((mv reserve fn2-run-loads fn2-pool) (fn2-run-load-reserve 0 7 8 1 fn2-run-loads fn2-pool))
      (page (fn2-run-loads-page 0 fn2-run-loads)) (pgen (fn2-run-loads-page-gen 0 fn2-run-loads))
      ((mv write fn2-pool) (fn2-pool-write page pgen 0 77 7 8 1 fn2-pool))
      (row *fn2-idc-rb*)
      (fn2-fields (fn2-fields-put row (value 55) (ref-slot page) (ref-gen pgen) (ref-off 0) (ref-len 1)))
      ((mv observer fn2-succ-txns fn2-c-source-control fn2-c-source-readers) (fn2-succ-source-acquire 0 0 fn2-succ-txns fn2-c-source-control fn2-c-source-readers))
      (receipt (fn2-succ-txns-source-receipt 0 fn2-succ-txns))
      ((mv lease & fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (fn2-checkpoint-summary-acquire 0 0 (if (eq mode :owner) 9 7) (if (eq mode :owner) 10 8) (if (eq mode :owner) 11 1)
        fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed))
      ((mv handed fn2-pool) (if (eq mode :hand) (fn2-pool-hand page pgen 7 8 1 9 10 11 fn2-pool) (mv :ok fn2-pool)))
      (free0 (fn2-pool-free-count 0 fn2-pool)) (free1 (fn2-pool-free-count 1 fn2-pool))
      ((mv first fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (fn2-succ-source-close 0 0 0 fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      (refused (if (member-eq mode '(:owner :hand))
       (and (eq first :state) (equal (fn2-succ-txns-source-receipt 0 fn2-succ-txns) receipt)
            (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 1)
            (equal (fn2-checkpoint-summary-leases-live 0 fn2-checkpoint-summary-leases) 1)
            (equal (fn2-fields-ref-len row fn2-fields) 1)) (eq first :ok)))
      ((mv fixed fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (if (eq mode :owner) (fn2-checkpoint-summary-release 0 9 10 11 fn2-checkpoint-summary fn2-checkpoint-summary-leases)
        (mv :ok fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
      ((mv accepted fn2-pool) (if (eq mode :hand) (fn2-pool-accept-hand page pgen 9 10 11 fn2-pool) (mv :ok fn2-pool)))
      ((mv returned fn2-pool) (if (eq mode :hand) (fn2-pool-hand page pgen 9 10 11 7 8 1 fn2-pool) (mv :ok fn2-pool)))
      ((mv regained fn2-pool) (if (eq mode :hand) (fn2-pool-accept-hand page pgen 7 8 1 fn2-pool) (mv :ok fn2-pool)))
      ((mv done fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (fn2-succ-source-close 0 0 0 fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
  (mv (and (eq install :ok) (eq reserve :ok) (eq write :ok) (eq observer :ok) (posp receipt) (eq lease :ok) (eq handed :ok) refused
           (eq fixed :ok) (eq accepted :ok) (eq returned :ok) (eq regained :ok) (eq done :ok)
           (equal (fn2-succ-txns-source-receipt 0 fn2-succ-txns) 0) (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 0)
           (equal (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0) (equal (fn2-checkpoint-summary-leases-live 0 fn2-checkpoint-summary-leases) 0)
           (equal (fn2-run-loads-windows 0 fn2-run-loads) 2) (equal (fn2-run-loads-phase 0 fn2-run-loads) *fn2-run-load-phase-reserved*)
           (equal (fn2-run-loads-tag 0 fn2-run-loads) 0) (equal (fn2-run-loads-source 0 fn2-run-loads) *fn2-none*)
           (equal (fn2-fields-ref-len row fn2-fields) 0) (equal (fn2-fields-value row fn2-fields) 55)
           (equal (fn2-pool-free-count 0 fn2-pool) free0) (equal (fn2-pool-free-count 1 fn2-pool) free1))
   fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-pool)))
(defun fn2-spc-test (mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-succ-txns
 (with-local-stobj fn2-run-cursors
 (with-local-stobj fn2-fields
 (with-local-stobj fn2-c-source-control
 (with-local-stobj fn2-c-source-readers
 (with-local-stobj fn2-run-loads
 (with-local-stobj fn2-checkpoint-summary
 (with-local-stobj fn2-checkpoint-summary-sources
 (with-local-stobj fn2-checkpoint-summary-leases
 (with-local-stobj fn2-run-installed
 (with-local-stobj fn2-pool
 (mv-let (good fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-pool) (fn2-spc-body mode fn2-succ-txns fn2-run-cursors fn2-fields fn2-c-source-control fn2-c-source-readers fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-pool) good)))))))))))))
(assert-event (fn2-spc-test :ok))
(assert-event (fn2-spc-test :owner))
(assert-event (fn2-spc-test :hand))
