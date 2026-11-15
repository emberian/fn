; The wrapper contract follows actual result carriers, including reordered ABIs.
(in-package "ACL2")
(include-book "../books/machines-b")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (equal (fn2-issued-wrapper-ops-position 'fn2-block-read-children (w state)) 4)
      (assoc-eq 'fn2-issue-tls-start-children (table-alist 'fn2-issue-child-wrappers (w state)))
      (getpropc 'fn2-issue-tls-start-children-queued-effect 'theorem nil (w state))
      (getpropc 'fn2-issue-tls-start-children-issued-total 'theorem nil (w state))
      (getpropc 'fn2-block-read-children-queued-effect 'theorem nil (w state))
      (getpropc 'fn2-block-read-children-issued-total 'theorem nil (w state))))

(defun fn2-test-shifted-read (offset slot gen len okind oslot ogen principal fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-pool fn2-ops fn2-control)
                 :guard (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))))
 (mv-let (code target generation fn2-pool fn2-ops fn2-control)
  (fn2-issue-read-children offset slot gen len okind oslot ogen principal fn2-pool fn2-ops fn2-control)
  (mv code target generation fn2-ops fn2-pool fn2-control)))
(assert-event
 (and (equal (fn2-issued-wrapper-ops-position 'fn2-test-shifted-read (w state)) 3)
      (equal (getpropc 'fn2-test-shifted-read 'stobjs-out nil (w state))
             '(nil nil nil fn2-ops fn2-pool fn2-control))
      (equal (getpropc 'fn2-test-shifted-read 'guard nil (w state))
             (getpropc 'fn2-issue-read-children 'guard nil (w state)))))
(make-event
 (value (cons 'progn
  (append (fn2-issue-wrapper-effect-events '(fn2-test-shifted-read) (w state))
          (fn2-issued-wrapper-events '(fn2-test-shifted-read) (w state))))))

(defun fn2-test-no-issue-carrier (x) (mv :bounds 0 0 x))
(must-fail
 (make-event (value (cons 'progn
  (fn2-issue-wrapper-effect-events '(fn2-test-no-issue-carrier) (w state))))))
(must-fail
 (make-event (value (cons 'progn
  (fn2-issued-wrapper-events '(fn2-test-no-issue-carrier) (w state))))))
