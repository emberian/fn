; Shared actual control events, emitted in either qualified core world.
; Definitions and assertions are preserved from the original entry verbatim.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(defmacro fn2-retirement-generic-controls-events ()
 '(progn
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
))
