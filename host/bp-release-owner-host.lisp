; Workflow projections beside the canonical configured owner.  Store retention
; is mutated only by Store events; workflow replay never replaces owner state.
(in-package "ACL2")
(include-book "../books/bp-release")
(include-book "../books/bp-ion-workflow")

(defun fn-owner-workflow-install-replay (records state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((answer (fn-bpiw-replay-journal (fn-sn-node (fn-owner-store state)) records)))
  (if (not (car answer))
      (value :fault)
    (let* ((workflow (fn-bp-journal-nth 1 answer))
           (state (f-put-global 'fn-workflow-state workflow state))
           (state (f-put-global 'fn-workflow-ion-state
                                (fn-bp-journal-nth 3 answer) state))
               (state (f-put-global 'fn-workflow-effects nil state))
               (state (f-put-global 'fn-workflow-recovered
                                    (fn-bp-work-ids
                                     (fn-bp-state-works workflow)) state)))
      (value :ready)))))

(defun fn-owner-workflow-reset (state)
 (declare (xargs :stobjs state :mode :program))
 (fn-workflow-reset state))

(defun fn-owner-workflow-preflight-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (fn-workflow-preflight-record record state))

(defun fn-owner-workflow-forward-pinnedp (work-id state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((workflow (f-get-global 'fn-workflow-state state))
        (work (fn-bp-find-work work-id (fn-bp-state-works workflow))))
  (value (if (and (consp work) (fn-bprl-work-pinnedp workflow work)) t nil))))

; Exact fields for the canonical Store event.  These projections are authored
; from the workflow state and release decision; the native adapter does not
; reconstruct obligation identities or evidence strings.
(defun fn-owner-workflow-store-undertake (work-id charge state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((workflow (f-get-global 'fn-workflow-state state))
        (work (fn-bp-find-work work-id (fn-bp-state-works workflow))))
  (if (not (fn-bprl-undertake-okp workflow work charge))
      (value nil)
    (value (list :undertake (fn-bp-work-obligation-id work)
                 (fn-bp-work-subject work)
                 (fn-bprl-required-evidence (fn-bp-state-config workflow) work)
                 charge)))))

(defun fn-owner-workflow-store-release (release-record state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((workflow (f-get-global 'fn-workflow-state state))
        (work (fn-bp-find-work (fn-bp-journal-nth 2 release-record)
                               (fn-bp-state-works workflow))))
  (if (or (not (fn-bprl-release-recordp release-record))
          (not (fn-bprl-work-pinnedp workflow work)))
      (value nil)
    (value (list :release (fn-bp-work-obligation-id work)
                 (fn-bp-work-subject work)
                 (fn-bprl-evidence-string
                  (fn-bprl-record-evidence release-record))
                 0)))))

(defun fn-owner-workflow-apply-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((answer (fn-bpiw-apply
                 (f-get-global 'fn-workflow-state state)
                 (f-get-global 'fn-workflow-ion-state state) record)))
  (if (not (car answer))
      (value :fault)
    (let* ((workflow (fn-bp-journal-nth 1 answer))
           (state (f-put-global 'fn-workflow-state workflow state))
               (state (f-put-global 'fn-workflow-effects
                                    (fn-bp-journal-nth 2 answer) state))
               (state (f-put-global 'fn-workflow-ion-state
                                    (fn-bp-journal-nth 3 answer) state)))
      (value :ready)))))

(defun fn-owner-workflow-sync-store-node (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((workflow (f-get-global 'fn-workflow-state state))
        (node (fn-sn-node (fn-owner-store state)))
        (next (fn-bprl-with-node workflow node))
        (state (f-put-global 'fn-workflow-state next state)))
  (value :ready)))
