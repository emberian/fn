; Exact fixed carrier shape. No setup/connection-budget dependency.
(in-package "ACL2")
(include-book "incoming-octet-holder")

; Fixed descriptor=(:input-backing incarnation capacity). The incarnation is
; from the shared protected namespace, not a new host counter.
(defun fn-ibc-descriptor (incarnation capacity)
  (declare (xargs :guard t))
  (list :input-backing incarnation capacity))
(defun fn-ibc-descriptorp (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor) (equal (car descriptor) :input-backing)
       (consp (cdr descriptor)) (natp (cadr descriptor))
       (consp (cddr descriptor)) (natp (caddr descriptor))
       (null (cdddr descriptor))))
(defun fn-ibc-carrier (descriptor row)
  (declare (xargs :guard t))
  (list descriptor row))
(defun fn-ibc-carrier-descriptor (carrier)
  (declare (xargs :guard t))
  (fn-prl-nth 0 carrier))
(defun fn-ibc-carrier-row (carrier)
  (declare (xargs :guard t))
  (fn-prl-nth 1 carrier))
(defun fn-ibc-carrier-with-row (carrier row)
  (declare (xargs :guard t))
  (fn-ibc-carrier (fn-ibc-carrier-descriptor carrier) row))
(defthm fn-ibc-row-update-retains-capacity-descriptor-by-definition
  (equal (fn-ibc-carrier-descriptor (fn-ibc-carrier-with-row carrier row))
         (fn-ibc-carrier-descriptor carrier))
  :hints (("Goal" :in-theory (enable fn-prl-nth))))

