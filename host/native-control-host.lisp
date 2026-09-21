; ACL2-facing boundary for the native local-control transport.
(in-package "ACL2")
(include-book "../books/native-control")

(defun fn-native-control-host-max-frame ()
  (declare (xargs :mode :program))
  *fn-nctrl-max-frame*)

(defun fn-native-control-host-max-article ()
  (declare (xargs :mode :program))
  *fn-article-max-octets*)

(defun fn-native-control-host-request-encode (msgid groups article)
  (declare (xargs :mode :program))
  (fn-native-control-request-encode msgid groups article))

(defun fn-native-control-host-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-native-control-request-decode octets))

(defun fn-native-control-host-reply-encode (status)
  (declare (xargs :mode :program))
  (fn-native-control-reply-encode status))

(defun fn-native-control-host-reply-decode (octets)
  (declare (xargs :mode :program))
  (fn-native-control-reply-decode octets))

(defun fn-native-control-host-status-class (status)
  (declare (xargs :mode :program))
  (fn-native-control-status-class status))

(defun fn-native-control-host-status-exit-code (status)
  (declare (xargs :mode :program))
  (fn-native-control-status-exit-code status))

(defun fn-native-control-host-transport-outcome (stage)
  (declare (xargs :mode :program))
  (fn-native-control-transport-outcome stage))
