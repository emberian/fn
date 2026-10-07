(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-cfg-peer-names-loop (peers acc)
  (declare (xargs :guard t))
  (if (consp peers)
      (fn-cfg-peer-names-loop
       (cdr peers)
       (if (equal (fn-cfg-row-b (car peers)) "path-identity")
           (cons (fn-cfg-row-a (car peers)) acc)
         acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-cfg-peer-names (peers)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp peers)
           (if (equal (fn-cfg-row-b (car peers)) "path-identity")
               (cons (fn-cfg-row-a (car peers)) (fn-cfg-peer-names (cdr peers)))
             (fn-cfg-peer-names (cdr peers)))
         nil)
       :exec (fn-cfg-peer-names-loop peers nil)))

(defthm fn-cfg-peer-names-loop-is-rev-onto
  (equal (fn-cfg-peer-names-loop peers acc)
         (fn-ag-rev-onto acc (fn-cfg-peer-names peers)))
  :hints (("Goal" :induct (fn-cfg-peer-names-loop peers acc)
                  :in-theory (union-theories
                              '(fn-cfg-peer-names-loop fn-cfg-peer-names
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-cfg-peer-names
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cfg-peer-names
                                fn-cfg-peer-names-loop-is-rev-onto
                                fn-ag-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

