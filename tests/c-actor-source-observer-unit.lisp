; Prepared actual AUTH callback control, unexecuted. Actual take/admission,
; resolve, park and observer callbacks are used. The empty OPEN successor
; and physical installed-count row are explicit local premises: no parsed
; grant, disk authentication, stored lookup or durable acceptance is claimed.
(in-package "ACL2")
(include-book "c-actor-loader-unit")
(defun fn2-c-actor-observer-drive (fuel id fn2-core)
 (declare (xargs :stobjs fn2-core :measure (nfix fuel) :verify-guards nil))
 (cond ((equal (fn2-auth-row-source-observation id fn2-core) *fn2-auth-source-observation-released*) (mv t fn2-core))
       ((zp fuel) (mv nil fn2-core))
       (t (mv-let (& & & & fn2-core)
           (fn2-auth-run-ready id *fn2-c-read-callback-bytes* fn2-core)
           (fn2-c-actor-observer-drive (1- fuel) id fn2-core)))))
(defun fn2-c-actor-source-observer-unit (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-c-actor-loader-unit-profile* fn2-core))
      ((mv born id gen fn2-core)
       (fn2-machine-take-fn2-auth *fn2-none* *fn2-none* 0 7 0 0 *fn2-none* 0 1 0 1 fn2-core))
      ((unless (eq born :ok)) (mv nil fn2-core))
      ((mv plan kind tx n0 b1 n1 b2 n2) (fn2-c-actor-loader-plan id gen fn2-core))
      (fn2-core (fn2-auth-put-core id (phase *fn2-auth-state-ready*) (wstep 1) (sx tx)))
      (fn2-core (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core))) (fn2-succ-txns)
       (fn2-succ-txns-put tx (phase *fn2-succ-phase-open*) (ri 0) (rstate *fn2-succ-resolve-fresh*)) fn2-core))
      (fn2-core (stobj-let ((fn2-run-installed (fn2-core-run-installed fn2-core))) (fn2-run-installed)
       (let ((fn2-run-installed (fn2-run-installed-put 0 (state *fn2-run-installed-state-live*)
          (physical 1) (schema *fn2-groups-sid*) (run 1) (wire-run 1) (top 0) (unit 0) (epoch 1) (counter 1))))
        (update-fn2-run-installed-physical-count 1 fn2-run-installed)) fn2-core))
      ; First real generated arm turn acquires the global source observer.
      ((mv & & & & fn2-core) (fn2-auth-run-ready id *fn2-c-read-callback-bytes* fn2-core))
      (held (stobj-let ((fn2-c-source-control (fn2-core-c-source-control fn2-core))
                       (fn2-c-source-observers (fn2-core-c-source-observers fn2-core))) (held)
       (and (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 1)
            (fn2-c-source-observer-ownerp kind id gen fn2-c-source-observers)) held))
      ; No completion flag is seeded: real empty-slot resolve advances RI,
      ; the actual arm changes WSTEP, then one real park job runs per turn.
      ((mv released fn2-core) (fn2-c-actor-observer-drive 40 id fn2-core))
      (parked (stobj-let ((fn2-run-loads (fn2-core-run-loads fn2-core))
                         (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                         (fn2-checkpoint-summary-leases (fn2-core-checkpoint-summary-leases fn2-core))
                         (fn2-pool (fn2-core-pool fn2-core))) (parked)
       (and (equal (fn2-run-loads-windows tx fn2-run-loads) 2)
            (equal (fn2-run-loads-windows b1 fn2-run-loads) 2)
            (fn2-c-actor-loader-parkedp 0 tx n0 b1 n1 b2 n2 kind id gen
             fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool)) parked))
      (unobserved (stobj-let ((fn2-c-source-control (fn2-core-c-source-control fn2-core))
                             (fn2-c-source-observers (fn2-core-c-source-observers fn2-core))) (clear)
       (and (equal (fn2-c-source-control-readers 0 fn2-c-source-control) 0)
            (not (fn2-c-source-observer-ownerp kind id gen fn2-c-source-observers))) clear))
      ; A re-resolve continuation must rearm before its next source step.
      (fn2-core (fn2-auth-put-core id (wstep 1)))
      ((mv & & & & fn2-core) (fn2-auth-run-ready id *fn2-c-read-callback-bytes* fn2-core)))
  (mv (and (eq plan :ok) held released parked unobserved
           (equal (fn2-auth-row-source-observation id fn2-core) *fn2-auth-source-observation-none*)
           (equal (fn2-auth-row-loader id fn2-core) *fn2-auth-loader-held*)) fn2-core)))
(assert-event (with-local-stobj fn2-core
 (mv-let (ok fn2-core) (fn2-c-actor-source-observer-unit fn2-core) ok)))
