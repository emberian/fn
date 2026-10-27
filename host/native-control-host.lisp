; ACL2-facing boundary for the native local-control transport.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena")
(include-book "../books/history-columns")
(include-book "../books/native-control")
(include-book "../books/control-observation")
(include-book "../books/control-receipt-wire")
(include-book "../books/moderation-outcome")
;; host-decisions-2 packet B: the control launch decision (fn-ncla-).
(include-book "../books/native-control-launch")
(include-book "../books/native-control-reason")
(include-book "../books/native-control-line")
;; online-reclaim-5: the word an operator request prints (fn-crqw-).
(include-book "../books/control-request-word")
(include-book "../books/consumer-local-control")
(include-book "../books/consumer-wait-codec")
(include-book "../books/owner-publication-state") ; the carried publication record (fn-nco-owner-publication-word)
(include-book "../books/consumer-reason")
(include-book "../books/topic-history-local-control")
(include-book "../books/native-live-buffer")
(include-book "../books/native-control-kinds")
(include-book "../books/definterface")

(include-book "../books/entries-native-control-host")

(definterface fn-native-control-host-reply-seconds :class :program :kinds ((request-octets natp)))

(definterface fn-native-control-host-withdraw-result :class :program)

(definterface fn-native-control-host-topic-request-encode
  :class ::program)

(definterface fn-native-control-host-topic-reply-encode
  :class ::program)

(definterface fn-native-control-host-topic-reply-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-topic-status-exit-code
  :class ::program)

(definterface fn-native-control-host-topic-cli-plan
  :class ::program)

; The read bound of a control frame that carries no article: every reply a
; client reads, and every request other than an article submission.
(defun fn-native-control-host-max-frame ()
  (declare (xargs :mode :program))
  *fn-nctrl-max-command-frame*)

(definterface fn-native-control-host-max-frame
  :class ::program)

; The owner's read bound for one control connection under the carried
; profile's article bound A and group bound G (`fn-nctrl-read-bound-for';
; `fn-native-control-request-within-read-bound').

(definterface fn-native-control-host-read-bound
  :class ::program)

; The widest article an FNCT request can carry, its article field's width
; (the record codec's payload ceiling).  The client does not know the store's
; profile; the owner applies it: its read bound, then its injection decision,
; which refuses an article past A as `article-exceeds-profile-bound'.
(defun fn-native-control-host-max-article ()
  (declare (xargs :mode :program))
  *fn-record-max-payload*)

(definterface fn-native-control-host-max-article
  :class ::program)

; The control reply vocabulary, ACL2's (`*fn-nctrl-statuses*'): a client
; accepts exactly these words and treats any other reply as no reply.
(defun fn-native-control-host-statuses ()
  (declare (xargs :mode :program))
  *fn-nctrl-statuses*)

(definterface fn-native-control-host-statuses
  :class ::program)

; The control word for a refused operator submission, from the owner's
; injection decision reason (`fn-native-control-refusal-status').

(definterface fn-native-control-host-refusal-status
  :class ::program)

(definterface fn-native-control-host-max-active-clients
  :class ::program)

;; host-decisions-2 packet B: whether an accepted control connection gets a
;; worker (:launch), is answered BUSY (:busy) or is closed (:stopping), from
;; the stop flag and the live worker count the host observes
;; (books/native-control-launch.lisp, KEYSTONE
;; fn-ncla-launch-exactly-below-the-ceiling).

(definterface fn-native-control-host-launch-disposition
  :class ::program)

;; PKT-344: the offline control verb's path, decided from the socket node and
;; the writer lock (fn-native-control-liveness-decides), and its note line.

(definterface fn-native-control-host-liveness
  :class ::program)

(definterface fn-native-control-host-liveness-note
  :class ::program)

;; The socket node a closing run may unlink (fn-native-control-socket-removal-decides).

(definterface fn-native-control-host-socket-removal
  :class ::program)

(definterface fn-native-control-host-lease-path
  :class ::program)

;; PKT-657, PKT-575: the moderation request, FNCT kind 21
;; (books/native-control-reason.lisp).

(definterface fn-native-control-host-moderation-encode
  :class ::program)

(definterface fn-native-control-host-admin-encode
  :class ::program)

(definterface fn-native-control-host-reply-encode
  :class ::program)

(definterface fn-native-control-host-reply-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-status-class
  :class ::program)

(definterface fn-native-control-host-status-exit-code
  :class ::program)

(definterface fn-native-control-host-transport-outcome
  :class ::program)

;; PRF-252: the wait kinds (codes 9, 10) wrap the consumer codec; every
;; other kind is fn-ncl-request-encode / -decode's, unchanged
;; (books/consumer-wait-codec.lisp).

(definterface fn-native-control-host-consumer-request-encode
  :class ::program)

(definterface fn-native-control-host-consumer-reply-encode
  :class ::program)

(definterface fn-native-control-host-consumer-poll-reply-encode
  :class ::program)

(defun fn-native-control-host-consumer-poll-max-frame ()
  (declare (xargs :mode :program))
  (+ *fn-frame-overhead-octets* *fn-ncl-poll-max-payload*))

(definterface fn-native-control-host-consumer-status-reply-encode
  :class ::program)

(defun fn-native-control-host-consumer-status-max-frame ()
  (declare (xargs :mode :program))
  (+ *fn-frame-overhead-octets* *fn-ncl-status-max-payload*))

(defun fn-native-control-host-consumer-cli-plan (command argv)
  ;; PKT-709: `--json COMMAND ...' is (:json PLAN) (books/consumer-reason.lisp).
  (declare (xargs :mode :program))
  (fn-ncr-cli-plan command argv))

(definterface fn-native-control-host-consumer-cli-plan
  :class ::program)

;; PRF-234: the password a bound consumer's secret file holds.

(definterface fn-native-control-host-consumer-secret-of-file
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; PKT-453 (a): the refusal reason on the wire (books/native-control-reason).

(definterface fn-native-control-host-reasoned-admin-encode
  :class ::program)

(defun fn-native-control-host-reasoned-framep (octets)
  ;; PKT-709: a reasoned consumer request (kind 22) is answered, however its
  ;; handling ends, with the reasoned reply too (books/consumer-reason.lisp).
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (or (fn-native-control-reasoned-framep octets)
      (fn-ncr-framep octets)))

(defun fn-native-control-host-reasoned-client-step (octets)
  ; What the client does with the reply to a reasoned request: (:status
  ; STATUS WORD), (:resend) or (:transport).
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-control-reasoned-client-step
   (fn-native-control-reasoned-reply-read octets)))

;; Row S1 (books/native-control-line.lisp, kind 23): a reasoned reply that
;; carries the owner's printed line; a nil LINE seals the reasoned reply.

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-lined-reply-encode
  :class :program)

(defun fn-native-control-host-lined-client-step (octets)
  ; (:status STATUS WORD LINE) for a lined reply, else the reasoned step.
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-control-lined-client-step
   (fn-native-control-lined-reply-read octets)))

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-lined-client-step
  :class :program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-native-control-host-lined-detail (step)
  ; What the operator's line carries after the status: the owner's line,
  ; else the refusal's word.
  (declare (xargs :mode :program))
  (fn-native-control-lined-detail step))

; host/native/operator-live.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-lined-detail
  :class :program)

(defun fn-native-control-host-reply-detail (status word)
  ; The reason word the operator's line carries after the status, or nil.
  (declare (xargs :mode :program))
  (fn-native-control-reply-detail status word))

(definterface fn-native-control-host-reply-detail
  :class ::program)

(defun fn-native-control-host-transport-word (stage)
  ; The reason word of an exchange no reply ended: no-owner before submission.
  (declare (xargs :mode :program))
  (fn-native-control-transport-word stage))

(definterface fn-native-control-host-transport-word
  :class ::program)

;; PKT-709, PKT-710 (books/consumer-reason.lisp): the reasoned consumer
;; request (FNCT kind 22), the client's read of the owner's answer, the
;; register retry, the report summary and the JSON lines.

(definterface fn-native-control-host-consumer-reasoned-request-encode
  :class ::program)

(defun fn-native-control-host-consumer-client-read (operation octets)
  ;; (:status STATUS WORD), (:reply REPLY), (:resend) or (:transport).
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-ncr-client-read operation octets))

(definterface fn-native-control-host-consumer-client-read
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-consumer-cli-after
  :class ::program)

(definterface fn-native-control-host-consumer-report-summary
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-consumer-json-line
  :class ::program)

(definterface fn-native-control-host-consumer-article-json
  :class ::program)

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

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-decode-frame
  :class ::program)

; Scalar publication observation for the receipt worker. All comparisons
; and completion classification remain in ACL2.
(defun fn-nco-owner-publication-word (target state)
  (declare (xargs :stobjs state :guard t))
  (fn-nco-publication-word target
    (fn-opub-get :durable (fn-ost-publication state))
    (fn-opub-get :inflight (fn-ost-publication state))
    (fn-opub-get :requested (fn-ost-publication state))
    (fn-opub-get :deferred (fn-ost-publication state))))

(definterface fn-nco-owner-publication-word :class :common-lisp-compliant)
