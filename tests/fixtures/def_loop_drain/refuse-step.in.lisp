(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-bprt-rows-table-loop (rows all acc)
  (declare (xargs :guard t))
  (if (or (atom rows) (atom (cdr rows))) (fn-ag-rev-onto acc nil)
    (if (fn-bprt-rows-pairp (car rows) (cadr rows))
        (fn-bprt-rows-table-loop
         (cddr rows) all
         (let ((route (fn-bprt-rows-route (car rows) (cadr rows) all)))
           (if route (cons route acc) acc)))
      (fn-bprt-rows-table-loop (cdr rows) all acc))))

(defun fn-bprt-rows-table (rows all)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (or (atom rows) (atom (cdr rows))) nil
         (let ((d (car rows)) (h (cadr rows)))
           (if (and (equal (fn-cfg-row-b d) "bp-route-destination")
                    (equal (fn-cfg-row-b h) "bp-route-next-hop")
                    (equal (fn-cfg-row-a d) (fn-cfg-row-a h)))
               (let* ((boundary (fn-cfg-row-c h))
                      (eid (fn-bprt-boundary-eid all boundary))
                      (route (fn-bprt-route (fn-cfg-row-n d) (fn-cfg-row-c d)
                                            boundary eid
                                            (fn-bprt-boundary-port all boundary))))
                 (if (and eid (fn-bprt-routep route))
                     (cons route (fn-bprt-rows-table (cddr rows) all))
                   (fn-bprt-rows-table (cddr rows) all)))
             (fn-bprt-rows-table (cdr rows) all))))
       :exec (fn-bprt-rows-table-loop rows all nil)))

(defthm fn-bprt-rows-table-loop-is-rev-onto
  (equal (fn-bprt-rows-table-loop rows all acc)
         (fn-ag-rev-onto acc (fn-bprt-rows-table rows all)))
  :hints (("Goal" :induct (fn-bprt-rows-table-loop rows all acc)
                  :in-theory (e/d (fn-bprt-rows-route fn-bprt-rows-pairp)
                                  (fn-bprt-boundary-eid fn-bprt-boundary-port
                                   fn-bprt-route fn-bprt-routep)))))

(verify-guards fn-bprt-rows-table
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bprt-rows-table fn-ag-rev-onto
                                fn-bprt-rows-table-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

