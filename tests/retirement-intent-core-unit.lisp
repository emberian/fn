; Actual submit/poll interleaving controls over the bounded A/B core entry.
; Settlements/stopped state in these controls are explicitly synthetic.
; This is not a physical writer/fence/ACK or full checkpoint acceptance test.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "retirement-intent-leaf-unit")
(include-book "retirement-core-instance")
(include-book "../sim/commit-test-profile")
(include-book "retirement-intent-core-controls")
(fn2-retirement-intent-core-controls-events)

; The real generic body decoder used by txn-scan rejects lifecycle kinds.
; This is its actual entry, not a claim that a synthetic caller cut is sealed.
; Keyed ordinary batches encode KEYED_MUTATION; their journal extent is
; allocated by commit-allocate rather than an ALLOCATION transaction member.
(defun fn2-riu-generic-lifecycle-closed-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init (fn2-b-test-profile *fn2-profile-tiny* 0) fn2-core))
      ((mv allocation fn2-core)
       (fn2-commit-txn-body *record-kind-allocation* 0 0 0 0 0 0 0 0 fn2-core))
      ((mv retirement fn2-core)
       (fn2-commit-txn-body *record-kind-retirement* 0 0 0 0 0 0 0 0 fn2-core))
      ((mv installation fn2-core)
       (fn2-commit-txn-body *record-kind-checkpoint-installation* 0 0 0 0 0 0 0 0 fn2-core)))
  (mv (and (eq allocation :kind) (eq retirement :kind) (eq installation :kind)
           (not (fn2-core-stopped-p fn2-core))) fn2-core)))
(defun fn2-riu-generic-lifecycle-closed-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (ok fn2-core) (fn2-riu-generic-lifecycle-closed-body fn2-core) ok)))
(assert-event (fn2-riu-generic-lifecycle-closed-run))
