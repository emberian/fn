; Workflow projections beside the canonical configured owner.  Store retention
; is mutated only by Store events; workflow replay never replaces owner state.
(in-package "ACL2")
(include-book "../books/history-columns")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena")
(include-book "../books/bp-release")
(include-book "../books/bp-ion-workflow")
(include-book "../books/bp-payload-gate")
(include-book "../books/definterface")
(include-book "../books/store-node")
(include-book "workflow-host")
(include-book "../books/owner-state-accessors")

; The entries that replay or apply workflow records read the attempt's
; request through the live payload arena (books/bp-outbound.lisp); they take
; fn-arena before state and only read it (host/native/io.lisp fnn-core-state).
(defun fn-owner-workflow-install-replay (records fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  ; Replay is cold: pass the carry unchanged; install anchors it to the
  ; resulting BP ledger, which may differ from the Store seed.
  (let* ((pin-carry (fn-workflow-pin-carry-of state))
         (answer (fn-bpiw-replay-journal (fn-sn-node (fn-owner-store state)) records pin-carry fn-arena)))
    (if (not (car answer))
        (value :fault)
      (let* ((workflow (fn-bp-journal-nth 1 answer))
             (state (f-put-global 'fn-workflow-state workflow state))
             (state (fn-workflow-pin-carry-put
                     (fn-prc-refresh pin-carry
                       (fn-node-retention (fn-bp-state-node workflow))) state))
             (state (f-put-global 'fn-workflow-ion-state
                                  (fn-bp-journal-nth 3 answer) state))
             (state (f-put-global 'fn-workflow-effects nil state))
             (state (f-put-global 'fn-workflow-recovered
                                  (fn-bp-work-ids (fn-bp-state-works workflow)) state)))
        (value :ready)))))

(definterface fn-owner-workflow-install-replay :class :program)

(defun fn-owner-workflow-reset (state)
 (declare (xargs :stobjs state :mode :program))
 (fn-workflow-reset state))

(definterface fn-owner-workflow-reset :class :program)

(defun fn-owner-workflow-preflight-record (record fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (fn-workflow-preflight-record record fn-arena state))

(definterface fn-owner-workflow-preflight-record :class :program)

;; The generic request on the shared owner (`bp-obligation request'):
;; fn-workflow-request-plan's plan through the payload gate, whose canonical
;; node is the OWNER's Store (books/bp-payload-gate.lisp KEYSTONE
;; fn-bppg-request-gate-sends-only-pinned-live-payload): no ADU leaves
;; without the work's :forward pin live in the Store reclaim honours, and
;; never one carrying a reclaim tombstone.
(defun fn-owner-workflow-request-plan (work-id attempt-id fn-arena state)
 ;; The pin-carry writes preserve the owner/workflow bindings and state shape.
 ;; Keep the BP plan closed while proving that frame in the minimal theory.
 (declare (xargs :stobjs (fn-arena state)
                 :guard (and (boundp-global 'fn-owner state)
                             (boundp-global 'fn-workflow-state state))
                 :guard-hints (("Goal" :in-theory
                                (union-theories '(fn-workflow-request-plan-with-pin-carry state-p boundp-global
                                  boundp-global1 global-table assoc-eq
                                  fn-owner-retain-carry-put-preserves-state-p1
                                  fn-owner-retain-carry-put-frames-global-association
                                  fn-workflow-pin-carry-put-preserves-state-p1
                                  fn-workflow-pin-carry-put-frames-global-association)
                                                (theory 'minimal-theory))))))
 (let* ((pin-carry (fn-prc-refresh (fn-owner-retain-carry state)
                         (fn-node-retention (fn-sn-node (fn-owner-store state)))))
        (state (fn-owner-retain-carry-put pin-carry state)))
  (mv-let (erp plan state)
   (fn-workflow-request-plan-with-pin-carry work-id attempt-id pin-carry fn-arena state)
  (declare (ignore erp))
  (value (fn-bppg-request-gate (fn-sn-node (fn-owner-store state))
                               (f-get-global 'fn-workflow-state state)
                               work-id plan pin-carry)))))

; host/native/bp-obligation.lisp dispatches it (lane reclaim-retention).
(definterface fn-owner-workflow-request-plan
  :class :common-lisp-compliant)

(defun fn-owner-workflow-forward-pinnedp (work-id state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (let* ((workflow (f-get-global 'fn-workflow-state state))
        (work (fn-bp-find-work work-id (fn-bp-state-works workflow))))
  (value (if (and (consp work) (fn-bprl-work-pinnedp workflow work pin-carry)) t nil)))))

(definterface fn-owner-workflow-forward-pinnedp
  :class ::program)

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

(definterface fn-owner-workflow-store-undertake
  :class ::program)

(defun fn-owner-workflow-store-release (release-record state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (let* ((workflow (f-get-global 'fn-workflow-state state))
        (work (fn-bp-find-work (fn-bp-journal-nth 2 release-record)
                               (fn-bp-state-works workflow))))
  (if (or (not (fn-bprl-release-recordp release-record))
          (not (fn-bprl-work-pinnedp workflow work pin-carry)))
      (value nil)
    (value (list :release (fn-bp-work-obligation-id work)
                 (fn-bp-work-subject work)
                 (fn-bprl-evidence-string
                  (fn-bprl-record-evidence release-record))
                 0))))))

(definterface fn-owner-workflow-store-release
  :class ::program)

;; PRF-950: the Store retention event of the operator's waiver of WORK-ID
;; (books/bp-carry-control.lisp fn-bpcc-waiver-release-event: the receipt's
;; event shape, the pin's own id, subject and evidence), or nil when the
;; carry journal holds no waiver of it or its pin is already released.
(defun fn-owner-workflow-store-waive (work-id state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-workflow-state state)))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (value (fn-bpcc-waiver-release-event (f-get-global 'fn-workflow-state state)
                                      (fn-workflow-carry-state-of state)
                                      work-id pin-carry))))

; host/native/bp-obligation.lisp dispatches it (lane carry-abandon).
(definterface fn-owner-workflow-store-waive
  :class :common-lisp-compliant)

;; The waivers durable in the carry journal whose Store event did not land.
(defun fn-owner-workflow-pending-waivers (state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-workflow-state state)))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (value (fn-bpcc-pending-waivers (f-get-global 'fn-workflow-state state)
                                 (fn-workflow-carry-state-of state) pin-carry))))

; host/native/bp-obligation.lisp dispatches it (lane carry-abandon).
(definterface fn-owner-workflow-pending-waivers
  :class :common-lisp-compliant)

(defun fn-owner-workflow-apply-record (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (let* ((answer (fn-bpiw-apply
                 (f-get-global 'fn-workflow-state state)
                 (f-get-global 'fn-workflow-ion-state state) record pin-carry fn-arena)))
  (if (not (car answer))
      (value :fault)
    (let* ((workflow (fn-bp-journal-nth 1 answer))
           (state (f-put-global 'fn-workflow-state workflow state))
               (state (f-put-global 'fn-workflow-effects
                                    (fn-bp-journal-nth 2 answer) state))
               (state (f-put-global 'fn-workflow-ion-state
                                    (fn-bp-journal-nth 3 answer) state)))
      (value :ready))))))

(definterface fn-owner-workflow-apply-record :class :program)

(defun fn-owner-workflow-sync-store-node (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((workflow (f-get-global 'fn-workflow-state state))
        (node (fn-sn-node (fn-owner-store state)))
        (next (fn-bprl-with-node workflow node))
        (state (f-put-global 'fn-workflow-state next state)))
  (value :ready)))

(definterface fn-owner-workflow-sync-store-node
  :class ::program)
