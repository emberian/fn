; D0 acceptance: per-bundle exhaustion and cancellation verdicts, and the
; printed form of resources.lisp's tables (fn2/docs/d-machines-nntp.md
; section 3 is pasted from this output). Exits 1 when an un-owed :exists
; bundle fails, when an owed bundle unexpectedly passes, or when an :exists
; bundle has no scenario.
;   FN_ACL2_SLOT_DIR=/tmp/fn2-d0-acl2-slots FN_ACL2_SLOTS=4 timeout 1800 \
;     tools/acl2 < fn2/tests/sim-acquisition-driver.lsp
(in-package "ACL2")
:q
(handler-case
    (progn
      (multiple-value-bind (erp value state)
          (let ((*features* (adjoin :acl2-loop-only *features*)))
            (with-suppression
              (ld '((set-cbd "fn2/tests/")
                    (include-book "sim-acquisition")
                    (set-inhibit-output-lst '(proof-tree prove event summary observation))
                    (mutual-recursion
                    (defun fn2-acq-name (x)
                      (declare (xargs :verify-guards nil :measure (+ 1 (* 2 (acl2-count x)))))
                      (cond ((keywordp x) (concatenate 'string ":" (string-downcase (symbol-name x))))
                            ((symbolp x) (string-downcase (symbol-name x)))
                            ((stringp x) x)
                            ((natp x) (coerce (explode-nonnegative-integer x 10 nil) 'string))
                            ((atom x) "?")
                            (t (concatenate 'string "(" (fn2-acq-names x) ")"))))
                    (defun fn2-acq-names (xs)
                      (declare (xargs :verify-guards nil :measure (* 2 (acl2-count xs))))
                      (cond ((atom xs) "")
                            ((atom (cdr xs)) (fn2-acq-name (car xs)))
                            (t (concatenate 'string (fn2-acq-name (car xs)) " " (fn2-acq-names (cdr xs)))))))
                    (defun fn2-acq-print-verdicts (vs)
                      (declare (xargs :verify-guards nil))
                      (if (atom vs) nil
                        (let ((v (car vs)))
                          (prog2$
                           (if (eq (nth 1 v) :pending)
                               (cw "BUNDLE ~s0 pending ~s1~%" (fn2-acq-name (nth 0 v)) (fn2-acq-name (nth 4 v)))
                             (cw "BUNDLE ~s0 ~s1 owed-by=~s2 ~s3 checks=~s4~%"
                                 (fn2-acq-name (nth 0 v)) (fn2-acq-name (nth 1 v))
                                 (if (nth 2 v) (fn2-acq-name (nth 2 v)) "none")
                                 (if (nth 3 v) "OK" "RED") (fn2-acq-name (nth 4 v))))
                           (fn2-acq-print-verdicts (cdr vs))))))
                    (defun fn2-acq-print-order (rows)
                      (declare (xargs :verify-guards nil))
                      (if (atom rows) nil
                        (let ((p (cdar rows)))
                          (prog2$ (cw "| ~s0 | `~s1` | ~s2 | `~s3` | ~s4 | ~s5 |~%"
                                      (fn2-acq-name (fn2-resource-get :rank p)) (fn2-acq-name (caar rows))
                                      (fn2-acq-name (fn2-resource-get :unit p))
                                      (fn2-acq-name (fn2-resource-get :bound p))
                                      (let ((r (fn2-resource-get :reserve p))) (if r (fn2-acq-name r) "none"))
                                      (fn2-resource-get :why p))
                                  (fn2-acq-print-order (cdr rows))))))
                    (defun fn2-acq-print-bundles (rows)
                      (declare (xargs :verify-guards nil))
                      (if (atom rows) nil
                        (let ((p (cdar rows)))
                          (prog2$ (cw "| `~s0` | `~s1` | `~s2` | ~s3 | ~s4 | ~s5 |~%"
                                      (fn2-acq-names (caar rows))
                                      (fn2-acq-names (fn2-resource-get :acquires p))
                                      (fn2-acq-names (fn2-resource-get :holds p))
                                      (let ((r (fn2-resource-get :reserve p))) (if r (fn2-acq-name r) "none"))
                                      (let ((s (fn2-resource-get :status p)))
                                        (if (eq s :exists)
                                            (if (fn2-resource-get :owed-by p)
                                                (concatenate 'string "exists, owed-by "
                                                             (fn2-acq-name (fn2-resource-get :owed-by p)))
                                              "exists")
                                          (concatenate 'string "planned " (fn2-acq-name (cadr s)))))
                                      (fn2-resource-get :why p))
                                  (fn2-acq-print-bundles (cdr rows))))))
                    (defun fn2-acq-print-pairs (rows key)
                      (declare (xargs :verify-guards nil))
                      (if (atom rows) nil
                        (prog2$ (cw "| `~s0` | `~s1` |~%" (fn2-acq-names (if (consp (caar rows)) (caar rows) (list (caar rows))))
                                    (fn2-acq-names (fn2-resource-get key (cdar rows))))
                                (fn2-acq-print-pairs (cdr rows) key))))
                    (defun fn2-acq-print-reserves (rows)
                      (declare (xargs :verify-guards nil))
                      (if (atom rows) nil
                        (prog2$ (cw "| `~s0` | `~s1` | ~s2 | ~s3 |~%" (fn2-acq-name (caar rows))
                                    (fn2-acq-names (fn2-resource-get :covers (cdar rows)))
                                    (if (fn2-resource-get :issue (cdar rows)) "issue" "whole bundle")
                                    (fn2-resource-get :why (cdar rows)))
                                (fn2-acq-print-reserves (cdr rows)))))
                    (defun fn2-acq-print-effects (rows)
                      (declare (xargs :verify-guards nil))
                      (if (atom rows) nil
                        (prog2$ (cw "| `~s0` | `~s1` | `~s2` |~%" (fn2-acq-names (caar rows))
                                    (fn2-acq-names (fn2-resource-get :holds-before (cdar rows)))
                                    (fn2-acq-names (fn2-resource-get :effects (cdar rows))))
                                (fn2-acq-print-effects (cdr rows)))))
                    (set-inhibit-output-lst '(proof-tree))
                    (set-fmt-hard-right-margin 100000 state)
                    (set-fmt-soft-right-margin 100000 state)
                    (value-triple (fn2-acq-print-verdicts *fn2-acq-verdicts*))
                    (value-triple (cw "~%TABLES BEGIN~%~%**(a) The order** (`*fn2-resource-order*`).~%~%| rank | kind | unit | bound | reserve | why |~%|---:|---|---|---|---|---|~%"))
                    (value-triple (fn2-acq-print-order *fn2-resource-order*))
                    (value-triple (cw "~%**(b, c) Bundles and held-while-waiting** (`*fn2-resource-bundles*`).~%~%| transition | acquires (in order) | holds while waiting | reserve | status | why |~%|---|---|---|---|---|---|~%"))
                    (value-triple (fn2-acq-print-bundles *fn2-resource-bundles*))
                    (value-triple (cw "~%**(d) Release, descending** (`*fn2-resource-releases*`).~%~%| holder, cause | releases |~%|---|---|~%"))
                    (value-triple (fn2-acq-print-pairs *fn2-resource-releases* :releases))
                    (value-triple (cw "~%**(e) Protected reserves** (`*fn2-resource-reserves*`).~%~%| reserve | covers | drawn as | why |~%|---|---|---|---|~%"))
                    (value-triple (fn2-acq-print-reserves *fn2-resource-reserves*))
                    (value-triple (cw "~%**(f) Commit-batch phases** (`*fn2-resource-batch-phases*`; per-recipient kinds `~s0`).~%~%| phase | holds |~%|---|---|~%" (fn2-acq-names *fn2-resource-per-recipient*)))
                    (value-triple (fn2-acq-print-pairs *fn2-resource-batch-phases* :holds))
                    (value-triple (cw "~%**Effects across rows** (`*fn2-resource-effects*`).~%~%| operation | holds before | effects |~%|---|---|---|~%"))
                    (value-triple (fn2-acq-print-effects *fn2-resource-effects*))
                    (value-triple (cw "~%TABLES END~%"))
                    (assert-event (fn2-acq-verdicts-ok *fn2-acq-verdicts*))
                    (value-triple (cw "SIM-ACQUISITION PASS~%")))
                  :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof))))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "SIM-ACQUISITION-DRIVER FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
