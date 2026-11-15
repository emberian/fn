; Prepared actual working-admission and borrowed-reader ownership control.
; HELD-cut/controller premises are explicitly SYNTHETIC, not an admitted
; master, physical page authentication, checkpoint publication or adoption.
; Pool admission and attempted ordinary loader release call actual functions.
(in-package "ACL2")
(include-book "../books/checkpoint-source-loader")
(include-book "../books/run-physical-release")
(defun fn2-root1-source-borrow-unit (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-summary fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-summary fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest) :verify-guards nil))
 (b* ((fn2-checkpoint-root1 (fn2-checkpoint-root1-init 1 fn2-checkpoint-root1))
      (fn2-checkpoint-windows (fn2-checkpoint-windows-init *fn2-checkpoint-window-count* fn2-checkpoint-windows))
      (fn2-checkpoint-future (fn2-checkpoint-future-init 1 fn2-checkpoint-future))
      (fn2-checkpoint-future-windows (fn2-checkpoint-future-windows-init *fn2-checkpoint-future-window-count* fn2-checkpoint-future-windows))
      (fn2-csnapshot (fn2-csnapshot-init 1 fn2-csnapshot))
      (profile '((:t . 1) (:x . 1) (:reading . t)))
      (rows (fn2-b-run-cursor-rows profile))
      (fn2-run-loads (fn2-run-load-profile-init profile fn2-run-loads))
      (fn2-run-cursors (fn2-run-cursors-init rows fn2-run-cursors))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init rows fn2-checkpoint-summary-leases))
      (fn2-pool (fn2-pool-init (list (cons *fn2-checkpoint-working-window-count* *fn2-format-page-size*)) 1 100 fn2-pool))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 1 fn2-checkpoint-summary))
      (fn2-checkpoint-metadata (fn2-checkpoint-metadata-init 1 fn2-checkpoint-metadata))
      (fn2-checkpoint-source (fn2-checkpoint-source-init 1 fn2-checkpoint-source))
      (fn2-checkpoint-metadata-manifest (fn2-checkpoint-metadata-manifest-init 1 fn2-checkpoint-metadata-manifest))
      (fn2-csnapshot (fn2-csnapshot-put 0 (phase *fn2-csnapshot-phase-held*) (token 31) (owner-kind 7) (owner-slot 13) (owner-gen 19)))
      ((mv reserved fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)
       (fn2-checkpoint-root1-reserve 0 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-pool))
      ; The actual root1 BEGIN establishes this controller phase after its
      ; owned descriptor/source initialization. This control isolates borrow.
      (fn2-checkpoint-root1 (fn2-checkpoint-root1-put 0 (token 31) (phase *fn2-checkpoint-root1-phase-select*)))
      (page (fn2-checkpoint-windows-slot *fn2-checkpoint-source-page-window* fn2-checkpoint-windows))
      (pgen (fn2-checkpoint-windows-generation *fn2-checkpoint-source-page-window* fn2-checkpoint-windows))
      (scratch (fn2-checkpoint-windows-slot 14 fn2-checkpoint-windows))
      (scratch-gen (fn2-checkpoint-windows-generation 14 fn2-checkpoint-windows))
      ; Missing isolation cannot borrow authority merely because both
      ; aliased windows currently have the same actor as their pool owner.
      (fn2-checkpoint-windows (fn2-checkpoint-windows-put 14 (slot page) (generation pgen)))
      ((mv aliased fn2-run-loads) (fn2-checkpoint-source-reader-borrow 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool))
      (alias-refused (and (eq aliased :owner) (equal (fn2-run-loads-admissions fn2-run-loads) 0)))
      (fn2-checkpoint-windows (fn2-checkpoint-windows-put 14 (slot scratch) (generation scratch-gen)))
      (antecedent (and (eq reserved :ok)
       (fn2-checkpoint-source-reader-windowsp 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-pool)
       (fn2-checkpoint-source-reader-isolatedp 0 fn2-checkpoint-windows)))
      ((mv borrowed fn2-run-loads) (fn2-checkpoint-source-reader-borrow 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool))
      (c (fn2-b-checkpoint-source-cursor-from-rows rows))
      (positive (and antecedent (eq borrowed :ok) (equal (fn2-run-loads-admissions fn2-run-loads) 1)
       (fn2-checkpoint-source-reader-attachedp 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors)
       (equal (fn2-run-loads-borrow-token c fn2-run-loads) 31)
       (equal (fn2-run-loads-lease-mode c fn2-run-loads) *fn2-run-load-lease-mode-root1-borrowed*)
       (equal (fn2-run-loads-page c fn2-run-loads) page) (equal (fn2-run-loads-page-gen c fn2-run-loads) pgen)))
      ((mv wrong fn2-run-loads) (fn2-checkpoint-source-reader-borrow 32 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool))
      ((mv duplicate fn2-run-loads) (fn2-checkpoint-source-reader-borrow 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool))
      (free-before (fn2-pool-free-count 0 fn2-pool))
      ((mv ordinary fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
       (fn2-run-load-release c 7 13 19 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      ((mv unfinished fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (fn2-checkpoint-source-reader-finish 31 7 13 19 fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
      (good (and alias-refused positive (eq wrong :owner) (eq duplicate :busy)
       (equal (fn2-run-loads-admissions fn2-run-loads) 1) (eq ordinary :borrowed) (eq unfinished :source)
       (equal (fn2-pool-free-count 0 fn2-pool) free-before)
       (equal (fn2-run-loads-borrow-token c fn2-run-loads) 31)
       (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-reserved*)
       (eq (fn2-pool-workspace-code page pgen 7 13 19 fn2-pool) :ok))))
  (mv good fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-summary fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest)))
(assert-event
 (with-local-stobj fn2-checkpoint-root1
 (with-local-stobj fn2-checkpoint-windows
 (with-local-stobj fn2-checkpoint-future
 (with-local-stobj fn2-checkpoint-future-windows
 (with-local-stobj fn2-csnapshot
 (with-local-stobj fn2-run-loads
 (with-local-stobj fn2-run-cursors
 (with-local-stobj fn2-checkpoint-summary-leases
 (with-local-stobj fn2-pool
 (with-local-stobj fn2-checkpoint-summary
 (with-local-stobj fn2-checkpoint-metadata
 (with-local-stobj fn2-checkpoint-source
 (with-local-stobj fn2-checkpoint-metadata-manifest
 (mv-let (good fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-summary fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest) (fn2-root1-source-borrow-unit fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-summary fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest) good)))))))))))))))
