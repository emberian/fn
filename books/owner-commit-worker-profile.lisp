; Architectural worker roles for the two-batch commit pipeline. The second
; I/O role is charged explicitly; it is never borrowed from rescue capacity.
(in-package "ACL2")
(defun fn-ocp-io-worker-roles ()
  (declare (xargs :guard t)) '(:barrier :append))
(defun fn-ocp-extra-io-workers ()
  (declare (xargs :guard t))
  (- (len (fn-ocp-io-worker-roles)) 1))
(defthm fn-ocp-two-distinct-io-roles
  (and (equal (len (fn-ocp-io-worker-roles)) 2)
       (no-duplicatesp-eq (fn-ocp-io-worker-roles))
       (equal (fn-ocp-extra-io-workers) 1)))
