; ACL2-facing boundary for the native local-control transport.
(in-package "ACL2")
(include-book "../books/native-control")
;; host-decisions-2 packet B: the control launch decision (fn-ncla-).
(include-book "../books/native-control-launch")
(include-book "../books/native-control-reason")
(include-book "../books/native-control-line")
;; online-reclaim-5: the word an operator request prints (fn-crqw-).
(include-book "../books/control-request-word")
(include-book "../books/consumer-local-control")
(include-book "../books/consumer-wait-codec")
(include-book "../books/consumer-reason")
(include-book "../books/topic-history-local-control")
(include-book "../books/native-live-buffer")
(include-book "../books/native-control-kinds")

(defun fn-native-control-host-topic-request-encode (operation sequence quota)
  (declare (xargs :mode :program))
  (fn-thlc-request-encode operation sequence quota))

(defun fn-native-control-host-topic-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-thlc-request-decode octets))

(defun fn-native-control-host-topic-reply-encode (status)
  (declare (xargs :mode :program))
  (fn-thlc-reply-encode status))

(defun fn-native-control-host-topic-reply-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
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

;; host-decisions-2 packet B: whether an accepted control connection gets a
;; worker (:launch), is answered BUSY (:busy) or is closed (:stopping), from
;; the stop flag and the live worker count the host observes
;; (books/native-control-launch.lisp, KEYSTONE
;; fn-ncla-launch-exactly-below-the-ceiling).
(defun fn-native-control-host-launch-disposition (stoppingp active)
  (declare (xargs :mode :program))
  (fn-ncla-launch-disposition stoppingp active))

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

;; PKT-657, PKT-575: the moderation request, FNCT kind 21
;; (books/native-control-reason.lisp).
(defun fn-native-control-host-moderation-encode (op login id reason)
  (declare (xargs :mode :program))
  (fn-native-control-moderation-encode op login id reason))

(defun fn-native-control-host-moderation-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-control-moderation-decode octets))

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
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
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

;; PRF-252: the wait kinds (codes 9, 10) wrap the consumer codec; every
;; other kind is fn-ncl-request-encode / -decode's, unchanged
;; (books/consumer-wait-codec.lisp).
(defun fn-native-control-host-consumer-request-encode (kind first second)
  (declare (xargs :mode :program))
  (fn-cwait-request-encode kind first second))

(defun fn-native-control-host-consumer-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-cwait-request-decode octets))

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
  ;; PKT-709: `--json COMMAND ...' is (:json PLAN) (books/consumer-reason.lisp).
  (declare (xargs :mode :program))
  (fn-ncr-cli-plan command argv))

;; PRF-234: the password a bound consumer's secret file holds.
(defun fn-native-control-host-consumer-secret-of-file (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-ncl-secret-of-file octets))

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
  ;; PKT-709: a reasoned consumer request (kind 22) is answered, however its
  ;; handling ends, with the reasoned reply too (books/consumer-reason.lisp).
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (or (fn-native-control-reasoned-framep octets)
      (fn-ncr-framep octets)))

(defun fn-native-control-host-reasoned-reply-encode (status reason)
  (declare (xargs :mode :program))
  (fn-native-control-reasoned-reply-encode status reason))

(defun fn-native-control-host-reasoned-client-step (octets)
  ; What the client does with the reply to a reasoned request: (:status
  ; STATUS WORD), (:resend) or (:transport).
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-control-reasoned-client-step
   (fn-native-control-reasoned-reply-read octets)))

;; Row S1 (books/native-control-line.lisp, kind 23): a reasoned reply that
;; carries the owner's printed line; a nil LINE seals the reasoned reply.
(defun fn-native-control-host-lined-reply-encode (status reason line)
  (declare (xargs :mode :program))
  (fn-native-control-lined-reply-encode status reason line))

(defun fn-native-control-host-lined-client-step (octets)
  ; (:status STATUS WORD LINE) for a lined reply, else the reasoned step.
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-control-lined-client-step
   (fn-native-control-lined-reply-read octets)))

(defun fn-native-control-host-lined-detail (step)
  ; What the operator's line carries after the status: the owner's line,
  ; else the refusal's word.
  (declare (xargs :mode :program))
  (fn-native-control-lined-detail step))

(defun fn-native-control-host-reply-detail (status word)
  ; The reason word the operator's line carries after the status, or nil.
  (declare (xargs :mode :program))
  (fn-native-control-reply-detail status word))

(defun fn-native-control-host-transport-word (stage)
  ; The reason word of an exchange no reply ended: no-owner before submission.
  (declare (xargs :mode :program))
  (fn-native-control-transport-word stage))

;; PKT-709, PKT-710 (books/consumer-reason.lisp): the reasoned consumer
;; request (FNCT kind 22), the client's read of the owner's answer, the
;; register retry, the report summary and the JSON lines.
(defun fn-native-control-host-consumer-reasoned-request-encode (kind first second)
  (declare (xargs :mode :program))
  (fn-ncr-request-encode kind first second))

(defun fn-native-control-host-consumer-reasoned-request-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-ncr-request-decode octets))

(defun fn-native-control-host-consumer-client-read (operation octets)
  ;; (:status STATUS WORD), (:reply REPLY), (:resend) or (:transport).
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-ncr-client-read operation octets))

(defun fn-native-control-host-consumer-cli-after (operation status word)
  (declare (xargs :mode :program))
  (fn-ncr-cli-after operation status word))

(defun fn-native-control-host-consumer-report-summary (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-ncr-report-summary octets))

(defun fn-native-control-host-consumer-json-line (operation status word counts summary)
  (declare (xargs :mode :program))
  (fn-ncr-json-line operation status word counts summary))

(defun fn-native-control-host-consumer-article-json (summary)
  (declare (xargs :mode :program))
  (fn-ncr-article-json summary))

;; D27 (PRF-960): the frame decoded in place from the control buffer, the
;; whole dispatch of host/native/control.lisp fnn-control-handle-client in
;; one entry from one digest (fn-frb-site-decode-is-reference: the tuple is
;; fn-frb-site-reference of the octet list: the FNCT decoders, then the FNLS
;; requests as fn-native-live-status-host-requestp and
;; fn-native-live-pages-host-requestp decide them).  Called through fnn-core
;; with the live control buffer (io.lisp fnn-octets-ctl-fill of the frame),
;; under the control buffer lock.  The ninth element is the handler chain's
;; word for the frame (books/native-control-kinds.lisp fn-ctlk-frame-handler,
;; KEYSTONE fn-ctlk-every-handled-frame-is-classified; sweep S029): :store,
;; :read or nil, read from the header in place.
(defun fn-native-control-host-decode-frame (fn-octets-ctl)
  (declare (xargs :stobjs fn-octets-ctl :mode :program))
  (append (fn-frb-site-decode fn-octets-ctl)
          (list (fn-ctlk-frame-handler fn-octets-ctl))))
