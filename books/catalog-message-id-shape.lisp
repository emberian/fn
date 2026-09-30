; Exact original catalog MsgID predicate; logical reference for streaming.
(in-package "ACL2")
(include-book "nntp-syntax")

(defun fn-scat-msgid-idp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (<= (length text) *fn-nntp-max-message-id-octets*)
       (fn-nntp-message-id-tokenp (fn-nntp-string-octets text))))

