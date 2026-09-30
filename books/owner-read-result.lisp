; Exact configured-owner read result vocabulary, without the owner machine.
(in-package "ACL2")
(include-book "acceptance-alloc")

; (:fn-own-tls-result consumed effects configured-owner repinned): REPINNED
; is whether the read moved the connection's pin (NNT-042; fn-own-result-repinned).
(defun fn-own-tls-make-result (consumed effects owner repinned)
  (declare (xargs :guard t))
  (list :fn-own-tls-result consumed effects owner repinned))

(defun fn-own-tls-result-repinned (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))

(defun fn-own-tls-result-consumed (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr result)))

(defun fn-own-tls-result-effects (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-own-tls-result-owner (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))

