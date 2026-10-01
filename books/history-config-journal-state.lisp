; Read only: a live intent also excludes suspension. No journal authority.
(in-package "ACL2")
(include-book "state-globals")
(defun fn-owner-history-config-journal (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-history-config-journal state)
      (f-get-global 'fn-owner-history-config-journal state)))
