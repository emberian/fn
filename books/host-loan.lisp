; Actual live-core physical loan authorization, independent of callbacks.
(in-package "ACL2")
(include-book "assembly-core")
(local (in-theory (enable fn2-core-wfp)))
(local
 (in-theory
  (disable fn2-ops-rows fn2-ops-gen fn2-ops-phase fn2-ops-kind
           fn2-ops-range-slot fn2-ops-range-gen fn2-ops-range-off fn2-ops-range-len
           fn2-ops-owner-kind fn2-ops-owner-slot fn2-ops-owner-gen
           fn2-pool-rows fn2-pool-gen fn2-pool-cap fn2-pool-base
           fn2-pool-data-length fn2-pool-lease-off fn2-pool-lease-len
           fn2-pool-state fn2-pool-out-count fn2-pool-fill
           fn2-pool-ownerp fn2-pool-input-code)))

(defun fn2-host-op-span (op gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))
              (fn2-pool (fn2-core-pool fn2-core)))
    (code address length)
    (cond
     ((not (and (natp op) (< op (fn2-ops-rows fn2-ops)))) (mv :bounds 0 0))
     ((not (equal gen (fn2-ops-gen op fn2-ops))) (mv :stale 0 0))
     ((not (or (equal (fn2-ops-phase op fn2-ops) *fn2-op-phase-queued*)
               (equal (fn2-ops-phase op fn2-ops) *fn2-op-phase-submitted*)))
      (mv :state 0 0))
     (t
      (let* ((kind (fn2-ops-kind op fn2-ops))
             (input (or (equal kind *fn2-action-receive*)
                        (equal kind *fn2-action-read*)
                        (equal kind *fn2-action-entropy*)))
             (output (fn2-op-output-kindp kind))
             (slot (fn2-ops-range-slot op fn2-ops))
             (rgen (fn2-ops-range-gen op fn2-ops))
             (off (fn2-ops-range-off op fn2-ops))
             (len (fn2-ops-range-len op fn2-ops)))
        (cond
         ((not (or input output)) (mv :ok 0 0))
         ((not (< slot (fn2-pool-rows fn2-pool))) (mv :bounds 0 0))
         ((not (equal rgen (fn2-pool-gen slot fn2-pool))) (mv :stale 0 0))
         ((or (> (+ off len) (fn2-pool-cap slot fn2-pool))
              (> (+ (fn2-pool-base slot fn2-pool) off len)
                 (fn2-pool-data-length fn2-pool)))
          (mv :bounds 0 0))
         ((if input
              (not (and (eq (fn2-pool-input-code slot rgen op gen fn2-pool) :ok)
                        (equal off (fn2-pool-lease-off slot fn2-pool))
                        (equal len (fn2-pool-lease-len slot fn2-pool))))
            (not (and (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*)
                      (< 0 (fn2-pool-out-count slot fn2-pool))
                      (<= (+ off len) (fn2-pool-fill slot fn2-pool))
                      (fn2-pool-ownerp slot (fn2-ops-owner-kind op fn2-ops)
                        (fn2-ops-owner-slot op fn2-ops)
                        (fn2-ops-owner-gen op fn2-ops) fn2-pool))))
          (mv :owner 0 0))
         (t (mv :ok (+ (fn2-pool-base slot fn2-pool) off) len))))))
    (mv code address length)))
