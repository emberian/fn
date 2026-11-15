; SOURCE-ONLY UNEXECUTED teeth for the actual carried-prefix obligations.
; Inherits actual select/map/project/protect and owned-window construction;
; completed authentication remains an explicit synthetic antecedent.
(in-package "ACL2")
(include-book "recovery-selected-adopt-unit")
(include-book "recovery-replay-prefix-state")
(defun fn2-rspu-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv ready tag fn2-core) (fn2-rsau-prepare :reservation fn2-core))
      ((mv linked fn2-core) (fn2-recovery-link 4 fn2-core))
      ((mv classified fn2-core) (fn2-recovery-cand-put 5 *fn2-rec-status-invalid* 0 0 0 0 0 0 0 fn2-core))
      ((mv claimed & fn2-core) (fn2-recovery-claim 5 37 41 6 103 12 fn2-core))
      (id (fn2-machine-kind-base *fn2-recovery-machine-kind* fn2-core))
      (gen (fn2-machine-generation id fn2-core))
      ((mv authenticated fn2-core) (fn2-rsau-auth id gen tag 4 fn2-core))
      (initial (fn2-recovery-replay-carried-prefix-p id gen 4 12 4 103 tag fn2-core))
      ((mv journal-step fn2-core) (fn2-recovery-replay-adopt id gen fn2-core))
      (journal-prefix (fn2-recovery-replay-carried-prefix-p id gen 4 12 4 103 tag fn2-core))
      (actual-token (fn2-machine-rc-own-token id fn2-core))
      (actual-left (fn2-machine-rc-own-left id fn2-core))
      ; Hypothesis-removal control: manufacture the exact raw-domain omission.
      ; The actual helper says :owned, but the unadopted payload remains FREE;
      ; therefore the carried-prefix hypothesis is necessary, not decorative.
      (fn2-core (fn2-recovery-machine-put-core id (rc-own-token 0) (rc-own-left 0)))
      (removed (not (fn2-recovery-replay-carried-prefix-p id gen 4 12 4 103 tag fn2-core)))
      (unsettled (not (fn2-recovery-replay-position-owned-p 5 37 41 6 103 fn2-core)))
      (before (fn2-test-core-snapshot fn2-core))
      ((mv fabricated fn2-core) (fn2-recovery-replay-adopt id gen fn2-core))
      (removal-control (and removed unsettled (eq fabricated :owned)
                           (equal before (fn2-test-core-snapshot fn2-core))))
      (fn2-core (fn2-recovery-machine-put-core id (rc-own-token actual-token) (rc-own-left actual-left)))
      (restored (fn2-recovery-replay-carried-prefix-p id gen 4 12 4 103 tag fn2-core))
      ((mv finished fn2-core) (fn2-rsau-drive 16 id gen fn2-core))
      ; Assert the WHOLE completion antecedent as well as its actual conclusion.
      (antecedent (and (fn2-corep fn2-core)
         (fn2-recovery-replay-carried-prefix-p id gen 4 12 4 103 tag fn2-core)))
      ((mv owned fn2-core) (fn2-recovery-replay-adopt id gen fn2-core))
      ((mv head-code head count) (fn2-recovery-payload-head 4 12 4 103 fn2-core))
      (conclusion (and (eq head-code :ok)
       (fn2-recovery-replay-journal-owned-p 4 12 4 103 fn2-core)
       (fn2-recovery-replay-consumed-prefix-p count head count 0 0 4 12 4 103 fn2-core))))
  (mv (and ready (eq linked :ok) (eq classified :ok) (eq claimed :ok) authenticated
       initial (eq journal-step :more) journal-prefix (= actual-token 6) (= actual-left 1)
       removal-control restored (eq finished :owned) antecedent (eq owned :owned) conclusion) fn2-core)))
(defun fn2-rspu-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-rspu-body fn2-core) answer)))
(assert-event (fn2-rspu-run))
