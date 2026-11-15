; Layer C1c: the sealer machine's core events (fn2-sealer-core-events,
; materialized in assembly-callbacks-c.lisp after the core instance): the
; core wrappers over the sealer's tables, C's attachment of the grant
; service's :sealable source, C's engine genesis, and the kind's
; continuations and run. Its own book, so a change here recertifies only the
; callbacks sections above it.
(in-package "ACL2")
(include-book "sealer-physical-loader")
(include-book "machine-arms")
(fn2-book-layer :c)

;; The arms. :sealing: one seal step; more work keeps the row runnable;
;; nothing sealable (:idle) parks it on :sealable, which the grant service
;; wakes once an overlay is sealable. A seal that needs a page or a run row
;; merges first (C5, sealer.lisp: it joins the schema's runs whenever one
;; free page or row is left, and its install and release free theirs), so
;; :full is a pool that cannot hold one batch's runs and a merge; with no
;; wake for that, every other answer stops the core by name through fn2-sealer-refuse (:full is
;; :sealer-full, :cache :sealer-cache, any other :sealer) rather than park a
;; row nothing would wake, and moves the row to :stopped.
(defmachine-arms fn2-sealer :declare
 :arms
 ((:sealing :on-refusal ((:stop :machine-phase))
   (:do (status) (fn2-sealer-load-status-op))
   (:cond
    ((eq status :pause) (:park :sealable :steps *fn2-work-transition*))
    ((eq status :park)
     (:if (equal row-bundle *fn2-sealer-bundle-held*)
      ((:set (drain 0) (copy-drained 0)) (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
      ((:set (drain 0)) (:next :source-drain) (:charge :steps *fn2-work-transition* :runnable t))))
    ((eq status :retire)
     (:do (observed) (fn2-c-source-read-acquire id row-generation) :accept () :case
      (((:busy) (:park :sealable :steps *fn2-work-transition*))
       ((:ok) (:do (code) (fn2-sealer-load-retire-op) :accept (:retired :resident :busy))
        (:set (drain 0)) (:next :source-drain) (:charge :steps *fn2-work-transition* :runnable t))
       (:otherwise (:do () (fn2-sealer-refuse observed)) (:set (stopped 1)) (:next :stopped)))))
    (t
     (:do (code) (fn2-sealer-step 4096) :accept () :case
      (((:more) (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition* :runnable t))
       ((:done :retired :idle)
        (:if (equal row-bundle *fn2-sealer-bundle-held*)
         ((:set (drain 0) (copy-drained 0)) (:next :draining) (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition* :runnable t))
         ((:set (drain 0)) (:next :source-drain) (:charge :steps *fn2-work-transition* :runnable t))))
       ((:busy) (:park :sealable :steps *fn2-work-transition*))
    ((:need-loader)
     (:do (code complete) (fn2-sealer-load-reserve-op *fn2-sealer-kind* id row-generation)
      :accept () :case
      (((:ok) (:set (bundle *fn2-sealer-bundle-held*))
        (:if (equal complete 1)
         ((:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition* :runnable t))
         ((:set (drain 0) (copy-drained 0)) (:next :draining) (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition* :runnable t))))
       ((:exhausted) (:set (drain 0)) (:next :source-drain) (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition* :runnable t))
       (:otherwise (:do () (fn2-sealer-refuse code)) (:set (stopped 1)) (:next :stopped)
        (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition*)))))
       ((:miss)
        (:do (selected c phase) (fn2-sealer-load-owner-op *fn2-sealer-kind* id row-generation) :accept (:ok))
        (:set (load-cursor c))
        (:next :binding) (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition* :runnable t))
       (:otherwise (:do () (fn2-sealer-refuse code)) (:set (stopped 1)) (:next :stopped)
        (:charge :bytes (+ *fn2-c-read-callback-bytes* 4096) :steps *fn2-work-transition*)))))))
  (:binding :on-refusal ((:stop :machine-phase))
   (:do (bound) (fn2-run-page-bind row-load-cursor *fn2-sealer-kind* id row-generation) :accept (:need-read))
   (:next :loading) (:charge :bytes 64 :steps *fn2-work-transition* :runnable t))
  (:loading :on-refusal ((:stop :machine-phase))
   (:if (not (and (natp budget) (< 0 budget))) ((:yield))
    ((:do (code) (fn2-run-page-step row-load-cursor (min budget *fn2-commit-unit-bytes*)) :accept () :case
      (((:ready) (:next :sealing) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
       ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
       ((:need-read) (:next :reading) (:charge :steps *fn2-work-transition* :runnable t))
       ((:wait) (:wait :completion :steps *fn2-work-small*))
       ((:yield) (:yield))
       (:otherwise (:do () (fn2-sealer-refuse code)) (:set (stopped 1)) (:next :stopped)
        (:charge :steps *fn2-work-transition*)))))))
  (:reading :on-refusal ((:stop :machine-phase))
   (:if (not (and (natp budget) (< 0 budget))) ((:yield))
    ((:issue (fn2-run-page-read row-load-cursor (min budget *fn2-commit-unit-bytes*))
      :ok ((:next :loading) (:wait :completion :bytes 4096 :steps *fn2-work-small*))))))
  (:draining :on-refusal ((:stop :machine-phase))
   (:if (equal row-copy-drained 0)
    ((:do (released) (fn2-sealer-copy-release-op *fn2-sealer-kind* id row-generation) :accept (:ok))
     (:set (copy-drained 1)) (:charge :steps *fn2-work-transition* :runnable t))
    ((:do (code c) (fn2-sealer-load-drain-op row-drain *fn2-sealer-kind* id row-generation) :accept () :case
    (((:member)
      (:do (released) (fn2-sealer-load-member-release-op row-drain *fn2-sealer-kind* id row-generation) :accept (:ok))
      (:set (drain (+ row-drain 1))) (:charge :steps *fn2-work-transition* :runnable t))
     ((:last) (:do (released) (fn2-run-page-release c *fn2-sealer-kind* id row-generation)
               :effects ((:release (:storage-window))) :accept (:ok))
      (:set (bundle *fn2-sealer-bundle-none*) (drain 0)) (:next :source-drain)
      (:charge :steps *fn2-work-transition* :runnable t))
     ((:absent) (:set (drain (+ row-drain 1))) (:charge :steps *fn2-work-transition* :runnable t))
     ((:wait) (:wait :completion :steps *fn2-work-small*))
     (:otherwise (:do () (fn2-sealer-refuse code)) (:set (stopped 1)) (:next :stopped)
      (:charge :steps *fn2-work-transition*)))))
  ))
  (:source-drain :on-refusal ((:stop :machine-phase))
   (:if (< row-drain *fn2-b-seal-source-cursors*)
    ((:do (cleared) (fn2-sealer-source-clear-op row-drain *fn2-sealer-kind* id row-generation) :accept (:more :done))
     (:set (drain (+ row-drain 1))) (:charge :steps *fn2-work-transition* :runnable t))
    ((:do (status) (fn2-sealer-load-status-op))
     (:if (or (eq status :run) (eq status :retire))
      ((:do (reaped) (fn2-sealer-source-reap-op *fn2-sealer-kind* id row-generation) :accept (:more :done :retired))
       (:charge :steps *fn2-work-transition* :runnable t))
      ((:do (released target targetgen) (fn2-sealer-source-end id row-generation) :accept (:ok :absent))
       (:if (not (equal target *fn2-none*)) ((:wake-row target)) ())
       (:set (drain 0)) (:next :sealing) (:park :sealable :steps *fn2-work-transition*))))))
  (:stopped (:idle)))
 :observes ((:read-result (:wake))))

(defmacro fn2-sealer-core-events ()
 '(progn
   ; The actual kind directory distinguishes an absent non-image boot actor
   ; from a present actor whose snapshot is unreadable or not yet complete.
   (defun fn2-sealer-boot-closed-p (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (let ((boot (fn2-machine-kind-base *fn2-boot-kind* fn2-core)))
     (or (equal boot *fn2-none*)
         (and (eq (fn2-boot-snapshot-read-code boot fn2-core) :ok)
              (equal (fn2-machine-phase boot fn2-core) *fn2-boot-state-ready*)
              (equal (fn2-machine-stopped boot fn2-core) 0)))))
   (defun fn2-sealer-source-open-p (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-c-source-control (fn2-core-c-source-control fn2-core))) (yes)
     (and (< 0 (fn2-c-source-control-rows fn2-c-source-control))
          (equal (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-idle*)) yes))
   (defun fn2-sealer-observed-p (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (let* ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core))
           (generation (if (fn2-machine-idp id fn2-core) (fn2-machine-generation id fn2-core) 0)))
     (and (not (equal id *fn2-none*)) (eq (fn2-sealer-snapshot-read-code id fn2-core) :ok)
      (stobj-let ((fn2-c-source-observers (fn2-core-c-source-observers fn2-core))) (yes)
       (fn2-c-source-observer-ownerp *fn2-sealer-kind* id generation fn2-c-source-observers) yes))))
   (assert-event (equal *fn2-sealer-kind* *fn2-idc-owner-kind*))
   (defun fn2-sealer-step (budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (or (not (fn2-sealer-boot-closed-p fn2-core))
            (equal (mv-nth 0 (fn2-csnapshot-state fn2-core)) *fn2-csnapshot-phase-held*)
            (and (not (equal (mv-nth 0 (fn2-csnapshot-state fn2-core)) *fn2-csnapshot-phase-idle*))
                 (not (fn2-sealer-observed-p fn2-core))))
        (mv :busy fn2-core)
    (b* ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core)))
     (if (or (equal id *fn2-none*) (not (eq (fn2-sealer-snapshot-read-code id fn2-core) :ok))) (mv :busy fn2-core)
      (b* (((mv observed fn2-core) (fn2-c-source-read-acquire id (fn2-machine-generation id fn2-core) fn2-core))
           ((unless (eq observed :ok)) (mv (if (eq observed :busy) :busy observed) fn2-core)))
    (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-overlay-index (fn2-core-overlay-index fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
                (fn2-run-builds (fn2-core-run-builds fn2-core)) (fn2-run-writers (fn2-core-run-writers fn2-core))
                (fn2-run-restarts (fn2-core-run-restarts fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-ribbon-builds (fn2-core-ribbon-builds fn2-core)) (fn2-ribbon-band (fn2-core-ribbon-band fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core))
                (fn2-fc-context (fn2-core-fc-context fn2-core)) (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
                (fn2-ranges (fn2-core-ranges fn2-core)) (fn2-range-sources (fn2-core-range-sources fn2-core))
                (fn2-run-cursors (fn2-core-run-cursors fn2-core)) (fn2-run-paths (fn2-core-run-paths fn2-core)))
     (code fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts
           fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests
           fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
     (fn2-seal-step budget fn2-seals fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers
                    fn2-run-restarts fn2-run-cache fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool
                    fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-paths)
     (mv code fn2-core)))))))
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
    (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-pool (fn2-core-pool fn2-core))
                (fn2-csnapshot (fn2-core-csnapshot fn2-core)))
     (yes)
     (let ((status (fn2-sealer-load-status fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-csnapshot)))
      (or (member-eq status '(:run :retire))
          (eq status :admit)))
     yes))
   (defun fn2-sealer-ready (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (let ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core)))
     (and (fn2-sealer-boot-closed-p fn2-core)
          (not (equal (mv-nth 0 (fn2-csnapshot-state fn2-core)) *fn2-csnapshot-phase-held*))
          (or (equal (mv-nth 0 (fn2-csnapshot-state fn2-core)) *fn2-csnapshot-phase-idle*)
              (fn2-sealer-observed-p fn2-core))
          (or (fn2-sealer-observed-p fn2-core) (fn2-sealer-source-open-p fn2-core))
          (not (equal id *fn2-none*)) (fn2-machine-idp id fn2-core)
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
   ;; from the three lemmas above, the grant's preserves lemmas and its frame
   ;; within the defwait's :tables.
   (fn2-wait-attach :sealable fn2-sealer-grant)
   (defattach (fn2-sealable-ready-p fn2-sealer-ready) (fn2-sealable-grant-one fn2-sealer-grant)
    :hints (("Goal" :use ((:instance fn2-sealer-grant-live) (:instance fn2-sealer-grant-wait-kids) (:instance fn2-sealer-grant-wait-directory)))))
   ;; CODE names the stop: a pool exhausted (:full) or a cache row held by
   ;; another page (:cache) is :sealer-full / :sealer-cache, any other
   ;; refusal :sealer.
   (defun fn2-sealer-refuse (code fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (fn2-core-stop (case code (:full *fn2-stop-reason-sealer-full*) (:cache *fn2-stop-reason-sealer-cache*)
                     (otherwise *fn2-stop-reason-sealer*))
                   fn2-core))
   (fn2-core-preserves fn2-sealer-refuse (code fn2-core) :rows nil)
   (in-theory (disable fn2-sealer-refuse))
   (assert-event (fn2-assert-compliant-p '(fn2-sealer-step fn2-sealer-genesis fn2-sealer-pending-p fn2-sealer-ready
                                           fn2-sealer-grant fn2-sealer-refuse) (w state)))

   ;; Layer C's genesis, called once by the executor's fn2-init-engine:
   ;; the group directory (S-GROUP), the principal directory (fn2-principals'
   ;; anonymous and owner), then the seal row; with no checker row
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
      (defun fn2-engine-sealer-genesis (profile fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (mv-let (code fn2-core) (fn2-sealer-genesis profile fn2-core)
     (if (member-eq code '(:ok :no-row)) (fn2-sealer-start-row (eq code :ok) fn2-core) (mv code fn2-core))))
   (fn2-core-preserves fn2-engine-sealer-genesis (profile fn2-core) :position 1 :rows nil)
   ; Image startup can initialize actors before inspecting anchors without
   ; staging any group/principal NAME overlay or rebinding actors later.
   (defun fn2-engine-genesis-actors (profile fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (mv-let (code ids fn2-core) (fn2-principals-bind-genesis profile fn2-core)
     (declare (ignore ids))
     (if (eq code :ok) (fn2-engine-sealer-genesis profile fn2-core) (mv code fn2-core))))
   (fn2-core-preserves fn2-engine-genesis-actors (profile fn2-core) :position 1 :rows nil)
   (defun fn2-engine-genesis (profile fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((mv code fn2-core) (fn2-groups-genesis profile fn2-core))
         ((unless (eq code :ok)) (mv code fn2-core))
         ((mv code fn2-core) (fn2-principals-genesis profile fn2-core))
         ((unless (eq code :ok)) (mv code fn2-core)))
     (fn2-engine-sealer-genesis profile fn2-core)))
   (fn2-core-preserves fn2-engine-genesis (profile fn2-core) :position 1 :rows nil)
   (in-theory (disable fn2-sealer-start-row fn2-engine-sealer-genesis fn2-engine-genesis-actors fn2-engine-genesis))
   (defun fn2-sealer-source-end (id generation fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (not (and (eq (fn2-sealer-snapshot-read-code id fn2-core) :ok)
                  (equal generation (fn2-machine-generation id fn2-core))
                  (equal (fn2-machine-phase id fn2-core) *fn2-sealer-state-source-drain*)))
        (mv :source *fn2-none* 0 fn2-core)
     (let ((ready (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-ranges (fn2-core-ranges fn2-core))
                              (fn2-range-sources (fn2-core-range-sources fn2-core)) (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                              (fn2-run-loads (fn2-core-run-loads fn2-core)) (fn2-checkpoint-summary-leases (fn2-core-checkpoint-summary-leases fn2-core))) (yes)
                   (and (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-idle*)
                        (fn2-sealer-source-quiescent-p fn2-seals fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases)) yes)))
      (if ready (fn2-c-source-read-release id generation fn2-core) (mv :source *fn2-none* 0 fn2-core)))))
   (fn2-core-preserves fn2-sealer-source-end (id generation fn2-core) :position 3 :rows nil)
   (fn2-sealer-loader-core-faces)
   (defmachine-arms fn2-sealer)
   (defmachine-run fn2-sealer)))
