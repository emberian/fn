; ACL2-facing boundary for the native local-control transport.
(in-package "ACL2")
(include-book "../books/native-control")
(include-book "../books/consumer-local-control")

(defun fn-native-control-host-max-frame ()
  (declare (xargs :mode :program))
  *fn-nctrl-max-frame*)

(defun fn-native-control-host-max-article ()
  (declare (xargs :mode :program))
  *fn-article-max-octets*)

(defun fn-native-control-host-max-active-clients ()
  (declare (xargs :mode :program))
  (fn-native-control-max-active-clients))

(defun fn-native-control-host-lease-path (control-path)
  (declare (xargs :mode :program))
  (fn-native-control-lease-path control-path))

(defun fn-native-control-host-request-encode (msgid groups article)
  (declare (xargs :mode :program))
  (fn-native-control-request-encode msgid groups article))

(defun fn-native-control-host-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-native-control-request-decode octets))

(defun fn-native-control-host-admin-encode (argv)
  (declare (xargs :mode :program))
  (fn-native-control-admin-encode argv))

(defun fn-native-control-host-admin-decode (octets)
  (declare (xargs :mode :program))
  (fn-native-control-admin-decode octets))

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

(defun fn-native-control-host-consumer-request-encode (kind first second)
  (declare (xargs :mode :program))
  (fn-ncl-request-encode kind first second))

(defun fn-native-control-host-consumer-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-ncl-request-decode octets))

(defun fn-native-control-host-consumer-reply-encode (status cursor)
  (declare (xargs :mode :program))
  (fn-ncl-reply-encode status cursor))

(defun fn-native-control-host-consumer-reply-decode (octets)
  (declare (xargs :mode :program))
  (fn-ncl-reply-decode octets))

(defun fn-native-control-host-consumer-poll-reply-encode
    (status cursor report)
  (declare (xargs :mode :program))
  (fn-ncl-poll-reply-encode status cursor report))

(defun fn-native-control-host-consumer-poll-max-frame ()
  (declare (xargs :mode :program))
  (+ *fn-frame-overhead-octets* *fn-ncl-poll-max-payload*))

(defun fn-native-control-host-consumer-poll-reply-decode (octets)
  (declare (xargs :mode :program))
  (fn-ncl-poll-reply-decode octets))

(defun fn-native-control-host-consumer-status-reply-encode
    (status ack frontier gap)
  (declare (xargs :mode :program))
  (fn-ncl-status-reply-encode status ack frontier gap))

(defun fn-native-control-host-consumer-status-reply-decode (octets)
  (declare (xargs :mode :program))
  (fn-ncl-status-reply-decode octets))

(defun fn-native-control-host-consumer-status-max-frame ()
  (declare (xargs :mode :program))
  (+ *fn-frame-overhead-octets* *fn-ncl-status-max-payload*))

(defun fn-native-control-host-consumer-cli-plan (command argv)
  (declare (xargs :mode :program))
  (fn-ncl-cli-plan command argv))
