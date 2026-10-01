; Projection of the retained durable row into profile-aware carrier work.
; Definite persistence and prepaid BODY custody remain caller obligations.
(in-package "ACL2")
(include-book "substrate-profile-selection")
(include-book "substrate-committed-row")
(defun fn-stpr-row-start (row profile cfg generation keyring)
 (declare (xargs :guard t))
 (fn-stpr-project (fn-stce-row-start row) profile cfg generation keyring))
(defun fn-stpr-row-start-carried (row profile cfg generation keyring)
 (declare (xargs :guard (or (fn-held-p row) (fn-hstxa-p row))))
 (fn-stpr-project (fn-stce-row-start-carried row) profile cfg generation keyring))
(defthm fn-stpr-carried-row-projection
 (implies (or (fn-held-p row) (fn-hstxa-p row))
  (equal (fn-stpr-row-start-carried row profile cfg generation keyring)
         (fn-stpr-row-start row profile cfg generation keyring)))
 :hints (("Goal" :in-theory
  (e/d (fn-stpr-row-start-carried fn-stpr-row-start)
       (fn-stpr-project fn-stce-row-start-carried fn-stce-row-start)))))
