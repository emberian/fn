; ACL2-facing boundary for the native local-control transport.
(in-package "ACL2")
(include-book "../books/native-control")
(include-book "../books/native-control-reason")
(include-book "../books/consumer-local-control")
(include-book "../books/topic-history-local-control")

(defun fn-native-control-host-topic-request-encode (operation sequence quota)
  (declare (xargs :mode :program))
  (fn-thlc-request-encode operation sequence quota))

(defun fn-native-control-host-topic-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-thlc-request-decode octets))

(defun fn-native-control-host-topic-reply-encode (status)
  (declare (xargs :mode :program))
  (fn-thlc-reply-encode status))

(defun fn-native-control-host-topic-reply-decode (octets)
  (declare (xargs :mode :program))
  (fn-thlc-reply-decode octets))

(defun fn-native-control-host-topic-status-exit-code (status)
  (declare (xargs :mode :program))
  (fn-thlc-status-exit-code status))

(defun fn-native-control-host-topic-cli-plan (command argv)
  (declare (xargs :mode :program))
  (fn-thlc-cli-plan command argv))

; The read bound of a control frame that carries no article: every reply a
; client reads, and every request other than an article submission.
(defun fn-native-control-host-max-frame ()
  (declare (xargs :mode :program))
  *fn-nctrl-max-command-frame*)

; The owner's read bound for one control connection under the carried
; profile's article bound A and group bound G (`fn-nctrl-read-bound-for';
; `fn-native-control-request-within-read-bound').
(defun fn-native-control-host-read-bound (a g)
  (declare (xargs :mode :program))
  (fn-nctrl-read-bound-for a g))

; The widest article an FNCT request can carry, its article field's width
; (the record codec's payload ceiling).  The client does not know the store's
; profile; the owner applies it: its read bound, then its injection decision,
; which refuses an article past A as `article-exceeds-profile-bound'.
(defun fn-native-control-host-max-article ()
  (declare (xargs :mode :program))
  *fn-record-max-payload*)

; The control reply vocabulary, ACL2's (`*fn-nctrl-statuses*'): a client
; accepts exactly these words and treats any other reply as no reply.
(defun fn-native-control-host-statuses ()
  (declare (xargs :mode :program))
  *fn-nctrl-statuses*)

; The control word for a refused operator submission, from the owner's
; injection decision reason (`fn-native-control-refusal-status').
(defun fn-native-control-host-refusal-status (reason)
  (declare (xargs :mode :program))
  (fn-native-control-refusal-status reason))

(defun fn-native-control-host-max-active-clients ()
  (declare (xargs :mode :program))
  (fn-native-control-max-active-clients))

;; PKT-344: the offline control verb's path, decided from the socket node and
;; the writer lock (fn-native-control-liveness-decides), and its note line.
(defun fn-native-control-host-liveness (socket-node lock)
  (declare (xargs :mode :program))
  (fn-native-control-liveness socket-node lock))

(defun fn-native-control-host-liveness-note (decision)
  (declare (xargs :mode :program))
  (fn-native-control-liveness-note decision))

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

;; PKT-453 (a): the refusal reason on the wire (books/native-control-reason).
(defun fn-native-control-host-reasoned-request-encode (msgid groups article)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-request-encode msgid groups article))

(defun fn-native-control-host-reasoned-request-decode (octets)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-request-decode octets))

(defun fn-native-control-host-reasoned-admin-encode (argv)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-admin-encode argv))

(defun fn-native-control-host-reasoned-admin-decode (octets)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-admin-decode octets))

(defun fn-native-control-host-reasoned-framep (octets)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-framep octets))

(defun fn-native-control-host-reasoned-reply-encode (status reason)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-reply-encode status reason))

(defun fn-native-control-host-reasoned-client-step (octets)
  ; What the client does with the reply to a reasoned request: (:status
  ; STATUS WORD), (:resend) or (:transport).
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-client-step
   (fn-native-control-reasoned-reply-read octets)))

(defun fn-native-control-host-reply-detail (status word)
  ; The reason word the operator's line carries after the status, or nil.
  (declare (xargs :mode :program))
  (fn-native-control-reply-detail status word))
