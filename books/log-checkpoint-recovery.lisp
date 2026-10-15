; Recovery observation: run the actual cold open with all of its requested
; effects completed. No logical history is supplied to execution.
(in-package "ACL2")
(include-book "log-checkpoint-open")
(include-book "log-checkpoint-publication-witnesses")
(include-book "log-checkpoint-independent-guards")

(defun fn-lc-recover-owner (disk r mode configs frontier max-conns segs)
 (declare (xargs :guard t :verify-guards nil))
 (let ((outcome (ec-call (fn-lc-proof-ok-outcomes
                         (len (fn-lc-open-program disk r mode segs))))))
  (with-local-stobj fn-lbc
   (mv-let (answer fn-lbc afterdisk aftersegs trace owner)
    (fn-lc-open disk r mode configs frontier max-conns segs outcome fn-lbc)
    (declare (ignore answer afterdisk aftersegs trace)) owner))))
(verify-guards fn-lc-recover-owner)

(defthm fn-lc-recover-owner-is-the-open-owner-by-definition
 (equal (fn-lc-recover-owner disk r mode configs frontier max-conns segs)
   (mv-nth 5 (fn-lc-open disk r mode configs frontier max-conns segs
    (fn-lc-proof-ok-outcomes (len (fn-lc-open-program disk r mode segs))) (create-fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-recover-owner mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
