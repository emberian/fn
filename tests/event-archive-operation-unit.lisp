; Scalar handles remain ordinary parameters; only declared children are stobjs.
; Runnable generator control, unexecuted under the source-only grant.
(in-package "ACL2")
(include-book "../books/event-archive-producer")
(fn2-event-archive-operation (fn2-eaou-check value)
 (fn2-event-archive) (fn2-event-archive)
 (mv (if (equal value 0) :ok :bounds) fn2-event-archive))
(assert-event (equal (getpropc 'fn2-eaou-check 'formals nil (w state)) '(value fn2-event-archive)))
(assert-event (equal (getpropc 'fn2-eaou-check 'stobjs-in nil (w state)) '(nil fn2-event-archive)))
(defun fn2-eaou-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-event-archive
  (mv-let (answer fn2-event-archive)
   (b* ((fn2-event-archive (fn2-event-archive-init 2 fn2-event-archive))
        ((mv good fn2-event-archive) (fn2-eaou-check 0 fn2-event-archive))
        ((mv bad fn2-event-archive) (fn2-eaou-check 1 fn2-event-archive)))
    (mv (and (eq good :ok) (eq bad :bounds) (= (fn2-event-archive-rows fn2-event-archive) 2)) fn2-event-archive)) answer)))
(assert-event (fn2-eaou-test))
