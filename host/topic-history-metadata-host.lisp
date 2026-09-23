; Native bridge for bounded FN-Topic candidate inspection.  No authority decision.
(in-package "ACL2")
(include-book "../books/topic-history-metadata")

(defun fn-th-host-inspect-source (source)
  (declare (xargs :mode :program))
  (fn-th-project-source source))
