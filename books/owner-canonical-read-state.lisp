; Exact readonly projections factored from owner-canonical-state.
(in-package "ACL2")
(include-book "owner-canonical-epoch")
(include-book "snapshot-source-token")

(defun fn-owner-canonical-state (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-canonical-state state)
       (f-get-global 'fn-owner-canonical-state state)))

(defun fn-owner-canonical-availablep (durable-count state)
  (declare (xargs :stobjs state :guard t))
  (let ((c (fn-owner-canonical-state state)))
    (and (fn-omk-widthp c 10) (eq (fn-omk-at 0 c) :ready)
         (natp (fn-owner-canonical-epoch state))
         (equal (fn-omk-at 1 c) (fn-owner-canonical-epoch state))
         (natp durable-count) (equal (fn-omk-at 2 c) durable-count))))
