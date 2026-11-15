; Prepared exact-borrow constructor control. The actor/directory and C
; continuations are SYNTHETIC internal premises; pool reservation is actual.
; No physical page authenticity, admitted actor or disk completion is claimed.
(in-package "ACL2")
(include-book "../books/cursor")
(defun fn2-cursor-query-borrow-unit (fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool)
 (declare (xargs :stobjs (fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool) :verify-guards nil))
 (b* ((fn2-cursor (fn2-cursor-init 1 fn2-cursor))
      (fn2-machines (fn2-machines-init 11 fn2-machines))
      (fn2-reads (fn2-reads-init *fn2-b-query-read-rows* fn2-reads))
      (fn2-id-decides (fn2-id-decides-init 1 fn2-id-decides))
      (fn2-succ-txns (fn2-succ-txns-init (+ 1 *fn2-b-query-read-rows*) fn2-succ-txns))
      (rows (+ 1 (* *fn2-b-read-loader-jobs* *fn2-b-query-read-rows*) *fn2-b-seal-source-cursors* 1))
      (fn2-run-loads (fn2-run-loads-init rows fn2-run-loads))
      (fn2-run-cursors (fn2-run-cursors-init rows fn2-run-cursors))
      (fn2-pool (fn2-pool-init '((2 . 65536)) 1 100 fn2-pool))
      (fn2-machines (fn2-machines-put 10 (kind *fn2-cursor-kind*) (slot 0)))
      (fn2-cursor (fn2-cursor-put 0 (phase *fn2-cursor-state-render*) (generation 19) (step 22)
       (query-bundle *fn2-cursor-query-bundle-held*) (load-active 1)))
      ; HDR's distinct range may remain active; the exact XL leg must idle.
      (fn2-reads (fn2-reads-put 0 (op *fn2-read-op-range*) (sid 3)))
      (fn2-succ-txns (fn2-succ-txns-set-lphase 1 *fn2-succ-lookup-idle* fn2-succ-txns))
      ((mv reserved fn2-run-loads fn2-pool) (fn2-run-load-reserve 1 *fn2-cursor-kind* 10 19 fn2-run-loads fn2-pool))
      (page (fn2-run-loads-page 1 fn2-run-loads)) (gen (fn2-run-loads-page-gen 1 fn2-run-loads))
      ((mv wrote fn2-pool) (fn2-pool-write page gen 0 77 *fn2-cursor-kind* 10 19 fn2-pool))
      ((mv active & & fn2-run-loads fn2-run-cursors fn2-pool)
       (fn2-cursor-query-article-page-children 0 10 19 fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool))
      (active-refused (and (eq active :owner) (equal (fn2-pool-fill page fn2-pool) 1)))
      (fn2-cursor (fn2-cursor-set-load-active 0 0 fn2-cursor))
      (fn2-run-loads (fn2-run-loads-set-pending 1 1 fn2-run-loads))
      ((mv pending & & fn2-run-loads fn2-run-cursors fn2-pool)
       (fn2-cursor-query-article-page-children 0 10 19 fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool))
      (pending-refused (and (eq pending :active) (equal (fn2-pool-fill page fn2-pool) 1)))
      (fn2-run-loads (fn2-run-loads-set-pending 1 0 fn2-run-loads))
      (fn2-reads (fn2-reads-set-op 0 *fn2-read-op-lookup* fn2-reads))
      ((mv lookup & & fn2-run-loads fn2-run-cursors fn2-pool)
       (fn2-cursor-query-article-page-children 0 10 19 fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool))
      (lookup-refused (and (eq lookup :active) (equal (fn2-pool-fill page fn2-pool) 1)))
      (fn2-reads (fn2-reads-set-op 0 *fn2-read-op-range* fn2-reads))
      (fn2-succ-txns (fn2-succ-txns-set-lphase 1 *fn2-succ-lookup-scan* fn2-succ-txns))
      ((mv xl & & fn2-run-loads fn2-run-cursors fn2-pool)
       (fn2-cursor-query-article-page-children 0 10 19 fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool))
      (xl-refused (and (eq xl :active) (equal (fn2-pool-fill page fn2-pool) 1)))
      (fn2-succ-txns (fn2-succ-txns-set-lphase 1 *fn2-succ-lookup-idle* fn2-succ-txns))
      (fn2-cursor (fn2-cursor-set-query-bundle 0 *fn2-cursor-query-bundle-none* fn2-cursor))
      ((mv bundle & & fn2-run-loads fn2-run-cursors fn2-pool)
       (fn2-cursor-query-article-page-children 0 10 19 fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool))
      (bundle-refused (and (eq bundle :owner) (equal (fn2-pool-fill page fn2-pool) 1)))
      (fn2-cursor (fn2-cursor-set-query-bundle 0 *fn2-cursor-query-bundle-held* fn2-cursor))
      ; Explicit old page-ready premises make invalidation nonvacuous.
      (fn2-run-loads (fn2-run-loads-set-phase 1 *fn2-run-load-phase-ready* fn2-run-loads))
      (fn2-run-cursors (fn2-run-cursors-put 1 (phase *fn2-run-cursor-phase-found*) (physical 1)))
      (old-ready (and (equal (fn2-run-loads-phase 1 fn2-run-loads) *fn2-run-load-phase-ready*)
                      (equal (fn2-run-cursors-physical 1 fn2-run-cursors) 1)))
      ; Range head rows and the read operation remain untouched by borrowing.
      (fn2-run-cursors (fn2-run-cursors-put 3 (phase *fn2-run-cursor-phase-at*) (physical 1) (unit 777) (counter 17)))
      ((mv borrowed slot generation fn2-run-loads fn2-run-cursors fn2-pool)
       (fn2-cursor-query-article-page-children 0 10 19 fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool))
      (good (and (eq reserved :ok) (eq wrote :ok) active-refused pending-refused lookup-refused xl-refused bundle-refused old-ready
       (eq borrowed :ok) (equal slot page) (equal generation gen) (equal (fn2-pool-fill page fn2-pool) 0)
       (equal (fn2-run-loads-phase 1 fn2-run-loads) *fn2-run-load-phase-reserved*)
       (equal (fn2-run-cursors-phase 1 fn2-run-cursors) *fn2-run-cursor-phase-idle*)
       (equal (fn2-run-cursors-physical 1 fn2-run-cursors) 0)
       (equal (fn2-reads-op 0 fn2-reads) *fn2-read-op-range*)
       (equal (fn2-run-cursors-phase 3 fn2-run-cursors) *fn2-run-cursor-phase-at*)
       (equal (fn2-run-cursors-unit 3 fn2-run-cursors) 777) (equal (fn2-run-cursors-counter 3 fn2-run-cursors) 17))))
  (mv good fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool)))
(assert-event
 (with-local-stobj fn2-cursor
 (with-local-stobj fn2-machines
 (with-local-stobj fn2-reads
 (with-local-stobj fn2-id-decides
 (with-local-stobj fn2-succ-txns
 (with-local-stobj fn2-run-loads
 (with-local-stobj fn2-run-cursors
 (with-local-stobj fn2-pool
 (mv-let (good fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool) (fn2-cursor-query-borrow-unit fn2-cursor fn2-machines fn2-reads fn2-id-decides fn2-succ-txns fn2-run-loads fn2-run-cursors fn2-pool) good))))))))))
