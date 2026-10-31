; Layer C1c: the sealer machine's core events (fn2-sealer-core-events,
; materialized in assembly-callbacks-c.lisp after the core instance): the
; core wrappers over the sealer's tables, C's attachment of the grant
; service's :sealable source, C's engine genesis, and the kind's
; continuations and run. Its own book, so a change here recertifies only the
; callbacks sections above it.
(in-package "ACL2")
(include-book "machines-c-sealer")
(fn2-book-layer :c)

(defmacro fn2-sealer-core-events ()
 '(progn
   (assert-event (equal *fn2-sealer-kind* *fn2-idc-owner-kind*))
   (defun fn2-sealer-step (budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-overlay-index (fn2-core-overlay-index fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-run-builds (fn2-core-run-builds fn2-core)) (fn2-run-writers (fn2-core-run-writers fn2-core))
                (fn2-run-restarts (fn2-core-run-restarts fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-ribbon-builds (fn2-core-ribbon-builds fn2-core)) (fn2-ribbon-band (fn2-core-ribbon-band fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core))
                (fn2-fc-context (fn2-core-fc-context fn2-core)) (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core)))
     (code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts
           fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-seal-step budget fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                    fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                    fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-sealer-step (budget fn2-core) :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   ;; Genesis: the seal row's resources, owned by the sealer's row. With no
   ;; checker row 3 + windows in the profile (C-SEAL-NO-ROW, interim until
   ;; B5-4a sizes the format tables for it in every profile) the answer is
   ;; :no-row and the caller stops the sealer's row: overlays then
   ;; accumulate as before C1c (capacity backpressure at stage).
   (defun fn2-sealer-genesis (profile fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-seals)
     (fn2-seal-genesis profile (fn2-fc-rows fn2-fc) (fn2-id-decides-rows fn2-id-decides) (fn2-fields-rows fn2-fields) fn2-seals)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-sealer-genesis (profile fn2-core) :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   ;; C's attachment of the grant service's :sealable source: the sealer's
   ;; row is parked on :sealable in :sealing, its seal row is idle, and an
   ;; overlay is sealable. The grant clears the wait and wakes the row.
   (defun fn2-sealer-pending-p (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core)))
     (yes) (fn2-seal-pending-p fn2-seals fn2-overlays) yes))
   (defun fn2-sealer-ready (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (let ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core)))
     (and (not (equal id *fn2-none*)) (fn2-machine-idp id fn2-core)
          (eq (fn2-machine-phase-read-code id fn2-core) :ok)
          (equal (fn2-machine-phase id fn2-core) *fn2-sealer-state-sealing*)
          (eq (fn2-machine-wait-reason-read-code id fn2-core) :ok)
          (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-sealable*)
          (fn2-sealer-pending-p fn2-core))))
   (defun fn2-sealer-grant (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (fn2-sealer-ready fn2-core)
        (let* ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core))
               (fn2-core (fn2-machine-write-wait-reason id *fn2-wait-none* fn2-core)))
         (mv id fn2-core))
     (mv *fn2-none* fn2-core)))
   (fn2-core-preserves fn2-sealer-grant (fn2-core) :position 1 :rows nil)
   (defthm fn2-sealer-ready-id
    (implies (fn2-sealer-ready fn2-core)
             (not (equal (fn2-machine-kind-base *fn2-sealer-kind* fn2-core) *fn2-none*)))
    :hints (("Goal" :in-theory (e/d (fn2-sealer-ready) (fn2-machine-kind-base fn2-machine-idp fn2-sealer-pending-p)))))
   (defthm fn2-sealer-grant-live
    (implies (fn2-sealer-ready fn2-core)
             (not (equal (mv-nth 0 (fn2-sealer-grant fn2-core)) *fn2-none*)))
    :hints (("Goal" :in-theory (e/d (fn2-sealer-grant) (fn2-sealer-ready fn2-machine-write-wait-reason fn2-machine-kind-base)))))
   (defthm fn2-sealer-grant-type
    (and (consp (fn2-sealer-grant fn2-core)) (true-listp (fn2-sealer-grant fn2-core)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (e/d (fn2-sealer-grant) (fn2-sealer-ready fn2-machine-write-wait-reason)))))
   (in-theory (disable fn2-sealer-step fn2-sealer-genesis fn2-sealer-pending-p fn2-sealer-ready fn2-sealer-grant))
   ;; The attachment proves the pair's constraints (type, shape, liveness)
   ;; from the three lemmas above and the grant's preserves lemmas.
   (defattach (fn2-sealable-ready-p fn2-sealer-ready) (fn2-sealable-grant-one fn2-sealer-grant))
   (defun fn2-sealer-refuse (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (fn2-core-stop *fn2-stop-reason-sealer* fn2-core))
   (fn2-core-preserves fn2-sealer-refuse (fn2-core) :rows nil)
   (in-theory (disable fn2-sealer-refuse))
   (assert-event (fn2-assert-compliant-p '(fn2-sealer-step fn2-sealer-genesis fn2-sealer-pending-p fn2-sealer-ready
                                           fn2-sealer-grant fn2-sealer-refuse) (w state)))

   ;; The continuations. :sealing: one seal step; more work keeps the row
   ;; runnable; nothing sealable (:idle) or backpressure (:full, :cache)
   ;; parks it on :sealable; any other answer is an invariant: the core
   ;; stops (:sealer) and the row is :stopped.
   (defmachine-callback fn2-sealer-seal fn2-sealer (id budget) 4
    (fn2-machine-with-work 4096 *fn2-work-transition* 0
     (mv-let (code fn2-core) (fn2-sealer-step 4096 fn2-core)
      (case code
       ((:more :retired :done) (fn2-machine-result 4096 *fn2-work-transition* 0 t fn2-core))
       ((:idle :full :cache)
        (let ((fn2-core (fn2-sealer-put-core id (wait-reason *fn2-wait-sealable*))))
         (fn2-machine-result 4096 *fn2-work-transition* 0 nil fn2-core)))
       (otherwise
        (let* ((fn2-core (fn2-sealer-refuse fn2-core))
               (fn2-core (fn2-sealer-put-core id (phase *fn2-sealer-state-stopped*) (stopped 1))))
         (fn2-machine-result 4096 *fn2-work-transition* 0 nil fn2-core)))))))
   ;; Layer C's genesis, called once by the executor's fn2-init-engine:
   ;; the group directory (S-GROUP), then the seal row; with no checker row
   ;; (C-SEAL-NO-ROW) the sealer's row is stopped instead.
   ;; READY: park the row on :sealable (its seal row is set); else stop it.
   (defun fn2-sealer-start-row (ready fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (let ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core)))
     (if (and (not (equal id *fn2-none*)) (fn2-machine-idp id fn2-core))
         (if ready
             (let ((fn2-core (fn2-sealer-put-core id (wait-reason *fn2-wait-sealable*)))) (mv :ok fn2-core))
           (let ((fn2-core (fn2-sealer-put-core id (phase *fn2-sealer-state-stopped*) (stopped 1) (wait-reason *fn2-wait-none*))))
            (mv :ok fn2-core)))
      (mv :bounds fn2-core))))
   (fn2-core-preserves fn2-sealer-start-row (ready fn2-core) :position 1 :rows nil)
   (defun fn2-engine-genesis (profile fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((mv code fn2-core) (fn2-groups-genesis profile fn2-core))
         ((unless (eq code :ok)) (mv code fn2-core))
         ((mv code fn2-core) (fn2-sealer-genesis profile fn2-core)))
     (if (member-eq code '(:ok :no-row)) (fn2-sealer-start-row (eq code :ok) fn2-core) (mv code fn2-core))))
   (fn2-core-preserves fn2-engine-genesis (profile fn2-core) :position 1 :rows nil)
   (in-theory (disable fn2-sealer-start-row fn2-engine-genesis))
   (defmachine-callback fn2-sealer-idle fn2-sealer (id budget) 4
    (fn2-machine-idle id fn2-core))
   (defmachine-run fn2-sealer)))
