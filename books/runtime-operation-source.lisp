; Actual operation authority readout. The immutable qualified installer row
; is not implemented yet; no family/role shape can confer installation.
(in-package "ACL2")
(include-book "page-read-pool-state")
(defun fn-owner-runtime-operation-source (kind fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
  (declare (ignore kind fn-page-read-pool state))
  (mv :runtime-operation-unavailable nil))
(defun fn-owner-runtime-operation-role-table (kind fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
  (declare (ignore kind fn-page-read-pool state))
  (mv :runtime-operation-unavailable nil))
