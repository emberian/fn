; Literal actual owner/Store getters extracted for narrow report/index worlds.
(in-package "ACL2")
(include-book "acceptance-alloc")

(defun fn-own-store (o)
  (declare (xargs :guard t))
  (mbe :logic (car o) :exec (fn-ag-car o)))

(defun fn-own-feeds (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o)))))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o)))))))))))))))

(defun fn-ocfg-owner (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-sn-node (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))

(verify-guards fn-sn-node)
(defun fn-own-view (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr o)) :exec (fn-ag-car (fn-ag-cdr o))))

(defun fn-own-view-version (v)
  (declare (xargs :guard t))
  (mbe :logic (car v) :exec (fn-ag-car v)))

(defun fn-own-view-frontier (v)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr v)) :exec (fn-ag-car (fn-ag-cdr v))))

(defun fn-sn-files (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))

(verify-guards fn-sn-files)

(defun fn-sf-frontier (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))

(verify-guards fn-sf-frontier)
