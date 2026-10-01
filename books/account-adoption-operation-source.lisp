; Exact protocol callable for the initial account BODY. The original borrowed
; inputs are separate arguments; constructing a request/cache tuple before
; source admission would itself require a funded source. No complete account
; compiled recipe/domain producer is installed yet. This explicit absence
; cannot be replaced by family shape, object subtotals, or a host numeric bound.
(in-package "ACL2")
(defun fn-cado-begin-operation-source
 (config bindings entropy base-config cp-incarnation next-txid)
 (declare (xargs :guard t))
 (declare (ignore config bindings entropy base-config cp-incarnation next-txid))
 (mv :account-begin-operation-source-unavailable nil nil nil))
