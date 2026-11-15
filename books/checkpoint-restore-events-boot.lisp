; Boot callbacks over the actual cold event engine. Read-result acceptance
; comes from this owner's real machine receipt, not a supplied success flag.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "boot-kind")
(include-book "checkpoint-restore-events")
(fn2-book-layer :c)
(defcost fn2-boot-checkpoint-events-begin :answers t :bytes 512
 :tables (fn2-core-checkpoint-restore-reader fn2-core-checkpoint-restore-events fn2-core-mk fn2-core-fc fn2-core-pool))
(defcost fn2-boot-checkpoint-events-loaded :answers (:more :state :source)
 :tables (fn2-core-event-read))
(defcost fn2-boot-checkpoint-events-directory-entry :child fn2-checkpoint-restore-events-directory-entry :answers t :bytes *fn2-event-proof-entry-width*
 :tables (fn2-core-checkpoint-restore-reader fn2-core-checkpoint-restore-events fn2-core-checkpoint-restore-events-work fn2-core-checkpoint-restore-reach fn2-core-fields))
(defcost fn2-boot-checkpoint-events-directory-finish :child fn2-checkpoint-restore-events-directory-finish :answers t
 :tables (fn2-core-checkpoint-restore-events))
(defcost fn2-boot-checkpoint-events-journal-bind :child fn2-checkpoint-restore-events-journal-bind :answers t :bytes 64
 :tables (fn2-core-checkpoint-restore-events fn2-core-event-read fn2-core-digests))
(defcost fn2-boot-checkpoint-events-journal-target :child fn2-checkpoint-restore-events-journal-target :answers (:read :state))
(defcost fn2-boot-checkpoint-events-journal-step :child fn2-checkpoint-restore-events-journal-step :answers t :bytes 4096
 :tables (fn2-core-checkpoint-restore-events fn2-core-checkpoint-restore-events-work fn2-core-event-read fn2-core-journal-members fn2-core-mk fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests))
(defcost fn2-boot-checkpoint-events-frontier-begin :child fn2-checkpoint-restore-events-frontier-begin :answers t :bytes 128
 :tables (fn2-core-checkpoint-restore-reader fn2-core-checkpoint-restore-events fn2-core-fc fn2-core-pool))
(defcost fn2-boot-checkpoint-events-frontier-step :child fn2-checkpoint-restore-events-frontier-step :answers t :bytes 4096
 :tables (fn2-core-checkpoint-restore-reader fn2-core-checkpoint-restore-events fn2-core-checkpoint-restore-reach fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests))
(defcost fn2-boot-checkpoint-events-peak-step :child fn2-checkpoint-restore-events-peak-step :answers t :bytes 32
 :tables (fn2-core-checkpoint-restore-reader fn2-core-checkpoint-restore-events))
(defcost fn2-boot-checkpoint-events-frontier-finish :child fn2-checkpoint-restore-events-frontier-finish :answers t
 :tables (fn2-core-checkpoint-restore-reader fn2-core-checkpoint-restore-events fn2-core-pool))

(defmacro fn2-boot-checkpoint-events-operations ()
 '(progn
  (make-event (value (cons 'progn
   (append
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-directory-entry 'fn2-checkpoint-restore-events-directory-entry (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-directory-finish 'fn2-checkpoint-restore-events-directory-finish (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-journal-bind 'fn2-checkpoint-restore-events-journal-bind (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-journal-target 'fn2-checkpoint-restore-events-journal-target (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-journal-step 'fn2-checkpoint-restore-events-journal-step (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-frontier-begin 'fn2-checkpoint-restore-events-frontier-begin (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-frontier-step 'fn2-checkpoint-restore-events-frontier-step (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-peak-step 'fn2-checkpoint-restore-events-peak-step (w state))
    (fn2-arms-op-face-events 'fn2-boot-checkpoint-events-frontier-finish 'fn2-checkpoint-restore-events-frontier-finish (w state))))))

  (defun fn2-boot-checkpoint-events-begin (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (if (not (and (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)
                  (equal (fn2-machine-phase id fn2-core) *fn2-boot-state-checkpoint-events-begin*)
                  (equal (fn2-machine-generation id fn2-core) ogen))) (mv :state fn2-core)
    (let ((c (fn2-machine-checkpoint-index id fn2-core))
          (slot (fn2-machine-root-slot id fn2-core)) (gen (fn2-machine-root-gen id fn2-core))
          (rs (fn2-machine-rx-slot id fn2-core)) (rg (fn2-machine-rx-gen id fn2-core)))
     (stobj-let ((fn2-checkpoints (fn2-core-checkpoints fn2-core)) (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
       (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core)) (fn2-extents (fn2-core-extents fn2-core))
       (fn2-checkpoint-restore-reader (fn2-core-checkpoint-restore-reader fn2-core)) (fn2-checkpoint-restore-map (fn2-core-checkpoint-restore-map fn2-core))
       (fn2-checkpoint-restore-map-control (fn2-core-checkpoint-restore-map-control fn2-core)) (fn2-checkpoint-restore-reach-control (fn2-core-checkpoint-restore-reach-control fn2-core))
       (fn2-checkpoint-restore-events (fn2-core-checkpoint-restore-events fn2-core)) (fn2-checkpoint-restore-events-work (fn2-core-checkpoint-restore-events-work fn2-core))
       (fn2-event-read (fn2-core-event-read fn2-core)) (fn2-mk (fn2-core-mk fn2-core))
       (fn2-fc (fn2-core-fc fn2-core)) (fn2-digests (fn2-core-digests fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
      (code fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-mk fn2-fc fn2-pool)
      (if (not (and (< 0 (fn2-checkpoint-restore-reach-control-rows fn2-checkpoint-restore-reach-control))
                     (equal c (fn2-checkpoint-restore-reach-control-candidate 0 fn2-checkpoint-restore-reach-control))))
          (mv :source fn2-checkpoint-restore-reader fn2-checkpoint-restore-events fn2-mk fn2-fc fn2-pool)
       (fn2-checkpoint-restore-events-begin slot gen rs rg *fn2-boot-kind* id ogen
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-extents fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-event-read fn2-mk fn2-fc fn2-digests fn2-pool))
      (mv code fn2-core)))))
  (fn2-core-preserves fn2-boot-checkpoint-events-begin (id ogen fn2-core) :position 1 :rows nil)

  ; This callback observes the real boot read result. It cannot be used to
  ; stamp a stale buffer: owner/generation, stage, exact target offset and the
  ; completed 4096-byte owned input lease all have to match this retained tuple.
  (defun fn2-boot-checkpoint-events-loaded (id ogen fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (if (not (and (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)
                  (equal (fn2-machine-phase id fn2-core) *fn2-boot-state-checkpoint-events-journal-received*)
                  (equal (fn2-machine-generation id fn2-core) ogen) (equal (fn2-machine-stage id fn2-core) 11)
                  (equal (fn2-machine-event-ready id fn2-core) 1)
                  (equal (fn2-machine-outcome id fn2-core) *fn2-outcome-done*) (equal (fn2-machine-count id fn2-core) 4096))) (mv :state fn2-core)
    (let ((offset (fn2-machine-offset id fn2-core)) (c (fn2-machine-checkpoint-index id fn2-core))
          (slot (fn2-machine-rx-slot id fn2-core)) (gen (fn2-machine-rx-gen id fn2-core)))
     (stobj-let ((fn2-checkpoints (fn2-core-checkpoints fn2-core)) (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
       (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core)) (fn2-checkpoint-restore-map (fn2-core-checkpoint-restore-map fn2-core))
       (fn2-checkpoint-restore-map-control (fn2-core-checkpoint-restore-map-control fn2-core)) (fn2-checkpoint-restore-reach-control (fn2-core-checkpoint-restore-reach-control fn2-core))
       (fn2-checkpoint-restore-events (fn2-core-checkpoint-restore-events fn2-core)) (fn2-checkpoint-restore-events-work (fn2-core-checkpoint-restore-events-work fn2-core))
       (fn2-event-read (fn2-core-event-read fn2-core)) (fn2-pool (fn2-core-pool fn2-core))) (code fn2-event-read)
      (b* (((mv target expected) (fn2-checkpoint-restore-events-journal-target fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-event-read))
           ((unless (and (eq target :read) (equal expected offset)
                          (equal (fn2-checkpoint-restore-events-candidate 0 fn2-checkpoint-restore-events) c)
                          (equal (fn2-checkpoint-restore-events-owner-kind 0 fn2-checkpoint-restore-events) *fn2-boot-kind*)
                          (equal (fn2-checkpoint-restore-events-owner-slot 0 fn2-checkpoint-restore-events) id)
                          (equal (fn2-checkpoint-restore-events-owner-gen 0 fn2-checkpoint-restore-events) ogen)
                          (equal (fn2-checkpoint-restore-events-record-slot 0 fn2-checkpoint-restore-events) slot)
                          (equal (fn2-checkpoint-restore-events-record-gen 0 fn2-checkpoint-restore-events) gen)
                          (eq (fn2-pool-workspace-code slot gen *fn2-boot-kind* id ogen fn2-pool) :ok)
                          (equal (fn2-pool-fill slot fn2-pool) 4096))) (mv :source fn2-event-read))
           (seal (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-read-seal*))
           (fn2-event-read (fn2-event-read-set-phase 0
            (if seal *fn2-event-read-phase-frame-seal* *fn2-event-read-phase-frame-records*) fn2-event-read)))
       (mv :more fn2-event-read))
      (mv code fn2-core)))))
  (fn2-core-preserves fn2-boot-checkpoint-events-loaded (id ogen fn2-core) :position 1 :rows nil)))
