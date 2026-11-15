; Prepared actual actor-birth/resource-constructor control. The physical
; installed directory row below is a SYNTHETIC local admission premise;
; no selected descriptor, disk authentication or authority grant is claimed.
; No source bytes are decoded or exposed by this resource-only control.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-e-auth")
(include-book "std/util/bstar" :dir :system)
(defconst *fn2-c-actor-loader-unit-profile*
 (put-assoc-equal :authority 1
 (put-assoc-equal :cns 1
 (put-assoc-equal :t 8
 (put-assoc-equal :pool-classes '((32 . 4096) (8 . 65536)) *fn2-profile-tiny*)))))
(defun fn2-c-actor-loader-unit (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-c-actor-loader-unit-profile* fn2-core))
      ; Actual take reserves the real authority row and its workspace pair.
      ; Control/frame fields are synthetic and unused by these leaf callbacks.
      ((mv born id gen fn2-core)
       (fn2-machine-take-fn2-auth *fn2-none* *fn2-none* 0 7 0 0 *fn2-none* 0 1 0 1 fn2-core))
      ((unless (eq born :ok)) (mv nil fn2-core))
      ((mv plan kind b0 n0 b1 n1 b2 n2) (fn2-c-actor-loader-plan id gen fn2-core))
      ((mv small0 large0) (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (small large)
       (mv (fn2-pool-class-countsi 0 fn2-pool) (fn2-pool-class-countsi 1 fn2-pool)) (mv small large)))
      ((mv resident complete0 fn2-core) (fn2-c-actor-loader-reserve id gen fn2-core))
      (unchanged (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (unchanged)
       (and (equal small0 (fn2-pool-class-countsi 0 fn2-pool))
            (equal large0 (fn2-pool-class-countsi 1 fn2-pool))) unchanged))
      (fn2-core (stobj-let ((fn2-run-installed (fn2-core-run-installed fn2-core))) (fn2-run-installed)
       (let ((fn2-run-installed (fn2-run-installed-put 0 (state *fn2-run-installed-state-live*)
          (physical 1) (schema *fn2-groups-sid*) (run 1) (top 0) (unit 0) (epoch 1) (counter 1))))
        (update-fn2-run-installed-physical-count 1 fn2-run-installed)) fn2-core))
      ((mv admitted complete1 fn2-core) (fn2-c-actor-loader-reserve id gen fn2-core))
      (owned (stobj-let ((fn2-run-loads (fn2-core-run-loads fn2-core)) (fn2-pool (fn2-core-pool fn2-core))) (owned)
       (and (fn2-run-load-ownerp b0 kind id gen fn2-run-loads)
            (fn2-run-load-ownerp b1 kind id gen fn2-run-loads)
            (equal (fn2-run-loads-windows b0 fn2-run-loads) 2)
            (equal (fn2-run-loads-windows b1 fn2-run-loads) 2)
            (equal (fn2-pool-class-countsi 0 fn2-pool) (- small0 2))
            (equal (fn2-pool-class-countsi 1 fn2-pool) (- large0 2))) owned))
      ((mv stale complete2 fn2-core) (fn2-c-actor-loader-reserve id (+ 1 gen) fn2-core))
      ((mv stale-drain & fn2-core) (fn2-c-actor-loader-drain id (+ 1 gen) 0 fn2-core))
      ((mv first c0 fn2-core) (fn2-c-actor-loader-drain id gen 0 fn2-core))
      ((mv released0 fn2-core) (fn2-c-actor-loader-member-release id gen 0 fn2-core))
      ((mv last c1 fn2-core) (fn2-c-actor-loader-drain id gen 1 fn2-core))
      ((mv released1 fn2-core) (fn2-run-page-release c1 kind id gen fn2-core))
      (restored (stobj-let ((fn2-run-loads (fn2-core-run-loads fn2-core)) (fn2-pool (fn2-core-pool fn2-core))) (restored)
       (and (equal (fn2-run-loads-phase b0 fn2-run-loads) *fn2-run-load-phase-idle*)
            (equal (fn2-run-loads-phase b1 fn2-run-loads) *fn2-run-load-phase-idle*)
            (equal (fn2-pool-class-countsi 0 fn2-pool) small0)
            (equal (fn2-pool-class-countsi 1 fn2-pool) large0)) restored)))
  (mv (and (eq plan :ok) (equal kind *fn2-auth-kind*) (equal n0 1) (equal n1 1) (equal n2 0) (equal b2 0)
           (eq resident :resident) (equal complete0 0) unchanged
           (eq admitted :ok) (equal complete1 1) owned
           (eq stale :owner) (equal complete2 0) (eq stale-drain :owner)
           (eq first :member) (equal c0 b0) (eq released0 :ok)
           (eq last :last) (equal c1 b1) (eq released1 :ok) restored)
      fn2-core)))
(assert-event
 (with-local-stobj fn2-core
  (mv-let (ok fn2-core) (fn2-c-actor-loader-unit fn2-core) ok)))
