; The shared three-conjunct owner invariant; no host attachment world.
(in-package "ACL2")
(include-book "reclaim-fold-contexts-live")

(defun fn-owner-retain-livep (state fn-arena)
  (declare (xargs :stobjs (state fn-arena) :guard t :verify-guards nil))
  (and (fn-owner-retain-statep state)
       (fn-osr-retainedp (fn-owner-store state))
       (fn-rfcl-okp (fn-owner-store state) fn-arena)))
