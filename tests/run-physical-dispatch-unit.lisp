; Prepared actual adapter/hook body control. Read/lookup/lease/op-map rows
; are explicitly SYNTHETIC internal premises: this does not witness an
; admitted D actor, persisted page, physical operation, or durable acceptance.
(in-package "ACL2")
(include-book "../books/machines-c-read-loader")
(defun fn2-run-physical-dispatch-unit (fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases fn2-run-load-ops fn2-run-installed)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases fn2-run-load-ops fn2-run-installed) :verify-guards nil))
 (b* ((fn2-reads (fn2-reads-init *fn2-b-query-read-rows* fn2-reads))
      (fn2-id-decides (fn2-id-decides-init 1 fn2-id-decides))
      (fn2-succ-txns (fn2-succ-txns-init (+ 1 *fn2-b-query-read-rows*) fn2-succ-txns))
      (fn2-ranges (fn2-ranges-init *fn2-b-query-read-rows* fn2-ranges))
      (fn2-range-sources (fn2-range-sources-init (* *fn2-b-query-read-rows* *fn2-b-range-source-cursors*) fn2-range-sources))
      (rows (+ 1 (* *fn2-b-read-loader-jobs* *fn2-b-query-read-rows*) *fn2-b-seal-source-cursors* 1))
      (fn2-run-cursors (fn2-run-cursors-init rows fn2-run-cursors))
      (fn2-run-loads (fn2-run-loads-init rows fn2-run-loads))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init rows fn2-checkpoint-summary-leases))
      (fn2-run-load-ops (fn2-run-load-ops-init 1 fn2-run-load-ops))
      (fn2-run-installed (fn2-run-installed-init 5 fn2-run-installed))
      (fn2-reads (fn2-reads-put 0 (op *fn2-read-op-lookup*) (sid 2)))
      (fn2-succ-txns (fn2-succ-txns-put 1 (lphase *fn2-succ-lookup-scan*) (lrow 4)))
      ((mv installed fn2-run-installed) (fn2-run-install 4 2 9 0 0 0 *fn2-storage-extent-units* 7 1 9 99 2 fn2-run-installed))
      (fn2-run-installed (fn2-run-installed-put 4 (physical 1) (epoch 3) (catalog-tag 17)))
      ((mv root fn2-run-cursors) (fn2-run-cursor-start-installed 1 4 0 9 99 2 fn2-run-installed fn2-run-cursors))
      ((mv selected selected-c) (fn2-read-loader-selected 0 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors))
      ((mv owned c phase fn2-run-cursors) (fn2-read-loader-owner 0 7 13 19 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      (positive (and (eq installed :ok) (eq root :ok) (eq selected :ok) (equal selected-c 1) (eq owned :ok) (equal c 1)
       (equal phase *fn2-run-load-phase-idle*) (equal (fn2-run-cursors-okind c fn2-run-cursors) 7)
       (equal (fn2-run-cursors-oslot c fn2-run-cursors) 13) (equal (fn2-run-cursors-ogen c fn2-run-cursors) 19)))
      ; Removing exact selected-root identity must not grant page ownership.
      (fn2-succ-txns (fn2-succ-txns-set-lrow 1 5 fn2-succ-txns))
      ((mv mismatch & & fn2-run-cursors) (fn2-read-loader-owner 0 8 14 20 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      (root-refused (and (eq mismatch :source) (equal (fn2-run-cursors-okind 1 fn2-run-cursors) 7)))
      (fn2-succ-txns (fn2-succ-txns-set-lrow 1 4 fn2-succ-txns))
      (fn2-run-loads (fn2-run-loads-put 1 (phase *fn2-run-load-phase-reserved*) (kind 8) (owner 14) (generation 20) (windows 2)))
      ((mv foreign & & fn2-run-cursors) (fn2-read-loader-owner 0 7 13 19 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      (foreign-refused (and (eq foreign :source) (equal (fn2-run-cursors-okind 1 fn2-run-cursors) 7)))
      (fn2-run-loads (fn2-run-loads-set-phase 1 *fn2-run-load-phase-idle* fn2-run-loads))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-put 1 (live 1) (owner-kind 8) (owner-slot 14) (owner-gen 20)))
      ((mv lease & & fn2-run-cursors) (fn2-read-loader-owner 0 7 13 19 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      (lease-refused (and (eq lease :source) (equal (fn2-run-cursors-okind 1 fn2-run-cursors) 7)))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-set-live 1 0 fn2-checkpoint-summary-leases))
      ; Exact range geometry, source row and schema are constructor premises.
      (fn2-reads (fn2-reads-set-op 0 *fn2-read-op-range* fn2-reads))
      (fn2-ranges (fn2-ranges-put 0 (phase *fn2-range-phase-seek*) (schema 2) (sbase 0) (cbase 3) (scount 1)))
      (fn2-range-sources (fn2-range-sources-put 0 (kind *fn2-range-kind-run*) (src 4) (cursor 3)))
      (fn2-run-cursors (fn2-run-cursors-put 3 (phase *fn2-run-cursor-phase-miss*) (physical 1) (schema 2) (source-row 4)))
      ((mv range-code range-c & fn2-run-cursors) (fn2-read-loader-owner 0 7 13 19 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      (range-positive (and (eq range-code :ok) (equal range-c 3) (equal (fn2-run-cursors-oslot 3 fn2-run-cursors) 13)))
      (fn2-ranges (fn2-ranges-set-cbase 0 4 fn2-ranges))
      ((mv range-bad & & fn2-run-cursors) (fn2-read-loader-owner 0 8 14 20 fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases))
      ; A pending operation and a later owned member prevent rank teardown.
      (last (fn2-run-query-bundle-cursor 0 (- *fn2-b-query-loader-jobs* 1) 1 *fn2-b-query-read-rows*))
      (fn2-run-loads (fn2-run-loads-put last (phase *fn2-run-load-phase-ready*) (kind 7) (owner 13) (generation 19) (windows 2)))
      (fn2-run-loads (fn2-run-loads-put 1 (phase *fn2-run-load-phase-wait*) (kind 7) (owner 13) (generation 19)
       (windows 2) (pending 1) (op-slot 0) (op-gen 41)))
      (fn2-run-load-ops (fn2-run-load-ops-put 0 (live 1) (generation 41) (cursor 1)))
      ((mv pending pending-c) (fn2-read-loader-drain 0 0 7 13 19 fn2-reads fn2-id-decides fn2-run-loads))
      ((mv & fn2-run-loads fn2-run-load-ops) (fn2-run-load-harvest 0 40 0 *fn2-event-read-result* *fn2-outcome-done* 0 *fn2-commit-unit-bytes* 0 0 fn2-run-loads fn2-run-load-ops))
      (stale-retained (equal (fn2-run-loads-pending 1 fn2-run-loads) 1))
      ((mv & fn2-run-loads fn2-run-load-ops) (fn2-run-load-harvest 0 41 0 *fn2-event-read-result* *fn2-outcome-done* 0 *fn2-commit-unit-bytes* 0 0 fn2-run-loads fn2-run-load-ops))
      ((mv member member-c) (fn2-read-loader-drain 0 0 7 13 19 fn2-reads fn2-id-decides fn2-run-loads))
      (good (and positive root-refused foreign-refused lease-refused range-positive (eq range-bad :source)
       (eq pending :wait) (equal pending-c 1) stale-retained (eq member :member) (equal member-c 1)
       (equal (fn2-run-loads-pending 1 fn2-run-loads) 0)
       (equal (fn2-run-loads-phase 1 fn2-run-loads) *fn2-run-load-phase-copy*)
       (equal (fn2-run-load-ops-live 0 fn2-run-load-ops) 0))))
  (mv good fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases fn2-run-load-ops fn2-run-installed)))
(assert-event
 (with-local-stobj fn2-reads
 (with-local-stobj fn2-id-decides
 (with-local-stobj fn2-succ-txns
 (with-local-stobj fn2-ranges
 (with-local-stobj fn2-range-sources
 (with-local-stobj fn2-run-cursors
 (with-local-stobj fn2-run-loads
 (with-local-stobj fn2-checkpoint-summary-leases
 (with-local-stobj fn2-run-load-ops
 (with-local-stobj fn2-run-installed
 (mv-let (good fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases fn2-run-load-ops fn2-run-installed)
 (fn2-run-physical-dispatch-unit fn2-reads fn2-id-decides fn2-succ-txns fn2-ranges fn2-range-sources fn2-run-cursors fn2-run-loads fn2-checkpoint-summary-leases fn2-run-load-ops fn2-run-installed) good))))))))))))
