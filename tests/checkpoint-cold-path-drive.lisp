; Full cold-path fixture transport. This is NOT a positive witness: its caller
; must first produce a persisted checkpoint using the actual maintenance
; actor, crash the simulator and start the real image boot. No authority row
; is populated here. Fuel bounds only the finite test, never stored data.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../sim/check-recovery")

; Hold exactly boot's final epoch Fence while it is still in the real outbox.
; An installation Fence, an arbitrary pending Fence, or a forged event-ready
; flag cannot satisfy this observation.
(defun fn2-ccp-epoch-fence-p (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((id (fn2-machine-kind-base *fn2-boot-kind* fn2-core))
      ((unless (and (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)
                    (= (fn2-machine-phase id fn2-core) *fn2-boot-state-epoch-result*)
                    (= (fn2-machine-stage id fn2-core) 3)
                    (= (fn2-machine-pending id fn2-core) 1)
                    (= (fn2-machine-event-ready id fn2-core) 0))) nil)
      (generation (fn2-machine-generation id fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (held)
   (mv-let (code slot gen) (fn2-outbox-peek 0 fn2-ops)
    (and (eq code :ok) (= (fn2-ops-gen slot fn2-ops) gen)
         (= (fn2-ops-kind slot fn2-ops) *fn2-action-fence*)
         (= (fn2-ops-owner-kind slot fn2-ops) *fn2-boot-kind*)
         (= (fn2-ops-owner-slot slot fn2-ops) id)
         (= (fn2-ops-owner-gen slot fn2-ops) generation))) held)))

; All physical Write/Fence outcomes go through the simulator's pending/durable
; storage model and the executor's normal harvest. Never post a result by hand.
(defun fn2-ccp-pump (fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :verify-guards nil))
 (cond
  ((and (not (fn2-b-rec-posted fn2-core)) (consp (fn2-b-outbox fn2-core)))
   (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)))
    (mv :more fn2-core fn2-sim fn2-own)))
  ((and (not (fn2-b-rec-posted fn2-core)) (fn2-b-rec-flight (fn2-sim-rows fn2-sim) fn2-sim))
   (b* ((slot (fn2-b-rec-flight (fn2-sim-rows fn2-sim) fn2-sim))
        ((mv & fn2-core fn2-sim fn2-own)
         (fn2-sim-advance-selected nil nil t slot *fn2-fault-none* 1 fn2-core fn2-sim fn2-own)))
    (mv :more fn2-core fn2-sim fn2-own)))
  (t (b* (((mv status & fn2-core) (fn2-b-turn fn2-core)))
       (mv (if (eq status :stop) :failed :more) fn2-core fn2-sim fn2-own)))))

(defun fn2-ccp-drive (fuel hold-epoch fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :verify-guards nil :measure (nfix fuel)))
 (cond
  ((zp fuel) (mv :fuel fn2-core fn2-sim fn2-own))
  ((fn2-core-stopped-p fn2-core) (mv :failed fn2-core fn2-sim fn2-own))
  ((eq (fn2-boot-status fn2-core) :ready) (mv :ready fn2-core fn2-sim fn2-own))
  ((and hold-epoch (fn2-ccp-epoch-fence-p fn2-core)) (mv :epoch-held fn2-core fn2-sim fn2-own))
  (t (b* (((mv status fn2-core fn2-sim fn2-own) (fn2-ccp-pump fn2-core fn2-sim fn2-own)))
       (if (eq status :failed) (mv status fn2-core fn2-sim fn2-own)
        (fn2-ccp-drive (- fuel 1) hold-epoch fn2-core fn2-sim fn2-own))))))

; Restart only the real process/flight state. The simulator crash retains its
; actual durable sectors and discards pending writes according to that model.
; Image boot must rebuild every selected source/map/protection/replay premise.
(defun fn2-ccp-restart (profile image-size fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((mv fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own))
      (fn2-core (fn2-init-executor profile :null nil fn2-core))
      ((mv code fn2-core) (fn2-boot-start nil image-size fn2-core)))
  (mv code fn2-core fn2-sim fn2-own)))

; Complete the exact held operation, with an explicit simulator fault for the
; failure control. Result classification, durable effects and ambiguity are
; still decided by the simulator and the production completion/harvest path.
(defun fn2-ccp-complete-epoch (fault fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((unless (fn2-ccp-epoch-fence-p fn2-core)) (mv :not-held fn2-core fn2-sim fn2-own))
      ((mv slot gen)
       (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (slot gen)
        (mv-let (code slot gen) (fn2-outbox-peek 0 fn2-ops)
         (declare (ignore code)) (mv slot gen)) (mv slot gen)))
      ((mv taken fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own))
      ((unless (and (= taken 1) (< slot (fn2-sim-rows fn2-sim))
                    (= (fn2-sim-active slot fn2-sim) 1)
                    (= (fn2-sim-gen slot fn2-sim) gen)
                    (= (fn2-sim-kind slot fn2-sim) *fn2-action-fence*)))
       (mv :not-submitted fn2-core fn2-sim fn2-own))
      ((mv posted fn2-core fn2-sim fn2-own)
       (fn2-sim-advance-selected nil nil t slot fault 1 fn2-core fn2-sim fn2-own)))
  (mv (if posted :posted :not-posted) fn2-core fn2-sim fn2-own)))
