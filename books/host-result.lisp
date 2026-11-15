; Actual native scalar result boundary, shared by narrow ABI controls.
(in-package "ACL2")
(include-book "terminal-values")

(defun fn2-host-result (kind code count aux len cancelled)
  (declare (xargs :guard (natp len)))
  (fn2-sim-terminal-values kind code count aux len nil cancelled))
