; C source callback declarations for the retained event roots. The composing
; checkpoint owner still owns actor dispatch, abort exclusion and installation.
(in-package "ACL2")
(include-book "checkpoint-kind")
(include-book "checkpoint-page-kind")
(include-book "event-rearm")
(fn2-book-layer :c)
(defcorechild fn2-core-event-build fn2-event-build
 :init (fn2-event-build-init 1 fn2-event-build) :profilep t
 :why "One actual retained-event source cursor owns candidate, source claims and completion-gated directory/frontier pages.")
(defcost fn2-checkpoint-events-begin :child fn2-event-producer-begin :answers (:ok :source :bounds)
 :tables (fn2-core-event-build fn2-core-mk)
 :doc "Bind actual descriptor candidate, held cut and owned source/read workspaces; begin real journal authentication.")
(defcost fn2-checkpoint-events-step :child fn2-event-producer-step :answers t :bytes 4096
 :tables (fn2-core-event-build fn2-core-event-read fn2-core-journal-members fn2-core-mk
          fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-checkpoint-construction
          fn2-core-extents fn2-core-alloc-edges fn2-core-fields fn2-core-pool fn2-core-digests fn2-core-checkpoint-build fn2-core-control fn2-core-csnapshot fn2-core-checkpoints fn2-core-commit-root fn2-core-checkpoint-refs fn2-core-checkpoint-bytes fn2-core-ops fn2-core-checkpoint-page-verified fn2-core-checkpoint-summary-authority fn2-core-checkpoint-restore-events fn2-core-checkpoint-restore-events-work)
 :doc "Advance bounded authentication/source construction without issuing physical IO; pending and pressure are explicit.")
(defcost fn2-checkpoint-events-read :child fn2-event-producer-issue :answers t :bytes 4096 :descriptors 1
 :tables (fn2-core-event-build fn2-core-event-read fn2-core-extents fn2-core-alloc-edges fn2-core-pool fn2-core-ops fn2-core-control fn2-core-csnapshot fn2-core-checkpoints fn2-core-checkpoint-summary-authority fn2-core-checkpoint-refs fn2-core-checkpoint-bytes fn2-core-checkpoint-restore-events fn2-core-checkpoint-restore-events-work fn2-core-commit-root)
 :effects ((:acquire (:operation)))
 :doc "Issue one actual pinned journal read and return its exact operation slot/generation for the master issue arm.")
(defcost fn2-checkpoint-events-bind :child fn2-event-build-bind-page :answers t
 :tables (fn2-core-event-build fn2-core-checkpoint-page)
 :doc "Bind one prepared page before actual HAND/TAKE; no source mutation until verified completion and return.")
(defcost fn2-checkpoint-events-consume :child fn2-event-build-consume-page :answers t :bytes 32
 :tables (fn2-core-event-build fn2-core-checkpoint-refs fn2-core-checkpoint-bytes)
 :doc "Consume exact completed page and returned workspace; pending retains owner and all workspaces.")
(defcost fn2-checkpoint-events-rearm :child fn2-event-producer-rearm :answers (:ok :state :retained)
 :tables (fn2-core-event-build fn2-core-event-read fn2-core-journal-members)
 :doc "Rearm finished source cursors only after exact successful publication, bundle release and actual B thaw; preserve frontier and root provenance.")
