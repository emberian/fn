; Semantic agreement among retained copies of each resident (sequence, handle).
; This is a proof-only carried invariant, never a served-path revalidation.
(in-package "ACL2")
(include-book "lb-log-model")

(defun-nx fn-lb-log-entries-payload-agreep (sequence handle payload entries)
 (declare (xargs :measure (acl2-count entries)))
 (if (consp entries)
  (and (implies (and (equal sequence (nth 8 (car entries)))
                    (equal handle (nth 5 (car entries))))
                (equal (nth 6 (car entries)) payload))
       (fn-lb-log-entries-payload-agreep sequence handle payload (cdr entries))) t))

(defun-nx fn-lb-log-row-copies-agreep (row payload log)
 (declare (xargs :measure (acl2-count log)))
 (if (consp log)
  (and (fn-lb-log-entries-payload-agreep (fn-record-sequence row) (fn-record-payload row)
         payload (caddar log))
       (fn-lb-log-row-copies-agreep row payload (cdr log))) t))

(defun-nx fn-lb-retained-payloads-agreep (rows log)
 (declare (xargs :measure (acl2-count rows)))
 (if (consp rows)
  (and (fn-lb-log-row-copies-agreep (car rows) (fn-lb-log-payload (car rows) log) log)
       (fn-lb-retained-payloads-agreep (cdr rows) log)) t))

(in-theory (disable fn-lb-log-entries-payload-agreep fn-lb-log-row-copies-agreep
                    fn-lb-retained-payloads-agreep))
