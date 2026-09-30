; Exact old reply framing, including ACTUAL status owed state.
(in-package "ACL2")
(include-book "over-cursor-shape")

(defun fn-ovw-reply (lines legacyp owedp)
  (declare (xargs :guard t :verify-guards nil))
  (if owedp
      (if (consp lines)
          (append (fn-ovw-status (fn-proto-text * :overview))
                  (fn-nntp-stuff-lines lines)
                  '(46 13 10))
        (fn-ovw-status (fn-ovw-empty-text legacyp)))
    (append (fn-nntp-stuff-lines lines) '(46 13 10))))


(verify-guards fn-ovw-reply)
