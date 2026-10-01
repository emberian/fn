; Exact fixed-state/publication helpers, extracted without changing bodies.
; State tags and borrowed values alone confer no source or account authority.
(in-package "ACL2")
(include-book "consumer-position-fields")

(defun fn-capr-state (cn original fields cp metadata preparation publication
                        begin-count withdrawals visible verdicts cs es
                        configs events config-history)
 (declare (xargs :guard t))
 (list :configured-authority-replay cn original fields cp metadata preparation
       publication begin-count withdrawals visible verdicts cs es
       configs events config-history))

(defun fn-capr-fault (s reason)
 (declare (xargs :guard t))
 (list :fault s reason))

(defun fn-capr-publication (old full)
 (declare (xargs :guard t))
 (list :ok (fn-cp-nth 1 full)
       (if (fn-cp-nth 2 full) (fn-cp-nth 2 full) (fn-cp-nth 2 old))
       (if (fn-cp-nth 2 full) (fn-cp-nth 3 full) (fn-cp-nth 3 old))))

(defun fn-capr-install (s cn original fields full preparation begin-count
                          withdrawals visible verdicts cs es configs events)
 (declare (xargs :guard t))
 (list :advanced
   (fn-capr-state cn original fields (fn-cp-nth 1 full) (fn-cp-nth 4 full)
     preparation (fn-capr-publication (fn-cp-nth 7 s) full) begin-count
     withdrawals visible verdicts cs es configs events (fn-cp-nth 16 s))
   full))

(in-theory (disable fn-capr-state fn-capr-fault fn-capr-publication fn-capr-install))
