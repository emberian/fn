(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-bpn-ready-peers-step (job rest)
  (declare (xargs :guard t))
  (if (and (equal (fn-bpn-job-status job) :queued)
           (not (fn-bpn-member (fn-bpn-job-peer job) rest)))
      (cons (fn-bpn-job-peer job) rest)
    rest))

(defun fn-bpn-ready-peers-loop (rev acc)
  (declare (xargs :guard t))
  (if (atom rev)
      acc
    (fn-bpn-ready-peers-loop (cdr rev) (fn-bpn-ready-peers-step (car rev) acc))))

(defun fn-bpn-ready-peers (jobs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (atom jobs)
           nil
         (let ((rest (fn-bpn-ready-peers (cdr jobs))))
           (if (and (equal (fn-bpn-job-status (car jobs)) :queued)
                    (not (fn-bpn-member (fn-bpn-job-peer (car jobs)) rest)))
               (cons (fn-bpn-job-peer (car jobs)) rest)
             rest)))
       :exec (fn-bpn-ready-peers-loop (fn-ag-rev-onto jobs nil) nil)))

(defthm fn-bpn-ready-peers-loop-of-rev-onto
  (equal (fn-bpn-ready-peers-loop (fn-ag-rev-onto jobs zs) nil)
         (fn-bpn-ready-peers-loop zs (fn-bpn-ready-peers jobs)))
  :hints (("Goal" :induct (fn-ag-rev-onto jobs zs)
                  :in-theory (union-theories
                              '(fn-bpn-ready-peers-loop fn-bpn-ready-peers
                                fn-bpn-ready-peers-step fn-ag-rev-onto atom
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(verify-guards fn-bpn-ready-peers-step)

(verify-guards fn-bpn-ready-peers-loop)

(verify-guards fn-bpn-ready-peers
  :hints (("Goal" :use ((:instance fn-bpn-ready-peers-loop-of-rev-onto (zs nil)))
                  :in-theory (union-theories
                              '(fn-bpn-ready-peers-loop fn-bpn-ready-peers atom)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))
