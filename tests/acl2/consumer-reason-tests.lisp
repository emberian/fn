; Teeth for books/consumer-reason (PKT-709, PKT-710; lane friend-blockers-2):
; the consumer refusal's reason on the wire, the register retry, the
; withdrawal report and the JSON line.  Per keystone a reachable witness
; asserting the whole antecedent and conclusion; per hypothesis a witness
; that keeps the others, fails the omitted one and fails the conclusion.
(in-package "ACL2")
(include-book "../../books/consumer-reason")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defconst *crt-unknown* (fn-record-string-octets "unknown-consumer"))
(defconst *crt-msgid* (fn-record-string-octets "<q1@alice.invalid>"))

; ---------------------------------------------------------------------------
; The reasoned request (kind 22) carries the kind-4 payload unchanged: the
; owner decides it as the plain request.  Sealed frames call the digest
; attachment, which a defconst may not: macros.
(defmacro crt-plain () '(fn-cwait-request-encode :poll '(98 111 98) nil))
(defmacro crt-reasoned () '(fn-ncr-request-encode :poll '(98 111 98) nil))
(assert-event (fn-cbor-octet-listp (crt-plain)))
(assert-event (fn-cbor-octet-listp (crt-reasoned)))
(assert-event (fn-ncr-framep (crt-reasoned)))
(assert-event (not (fn-ncr-framep (crt-plain))))
(assert-event (equal (fn-ncr-request-decode (crt-reasoned))
                     (fn-cwait-request-decode (crt-plain))))
(assert-event (equal (fn-ncr-request-decode (crt-reasoned))
                     '(:consumer :poll (98 111 98) nil)))
; A bound poll (the longest payload, the password) crosses too.
(assert-event (equal (fn-ncr-request-decode
                      (fn-ncr-request-encode :bound-poll '(98 111 98) '(112 119)))
                     '(:consumer :bound-poll (98 111 98) (112 119))))
; A wait (codes 9 and 10) crosses too.
(assert-event (equal (fn-ncr-request-decode
                      (fn-ncr-request-encode :wait '(98 111 98) 300))
                     '(:consumer :wait (98 111 98) 300)))
; The plain encoder's refusal is the reasoned encoder's.
(assert-event (equal (fn-ncr-request-encode :poll nil nil) :bad))
; A kind-4 frame is not a kind-22 one, so the owner's reasoned decode of it
; refuses by frame (and the owner's plain decode takes it, as before).
(assert-event (equal (fn-ncr-request-decode (crt-plain)) '(:refused :frame)))

; ---------------------------------------------------------------------------
; fn-ncr-printed-reason-is-the-decisions.  Positive, for every consumer
; operation a refusal can answer: the status is a member, its class is
; :refused and the reason is non-nil; the read is the owner's status and
; word and the printed detail is the word.
(defmacro crt-refused () '(fn-native-control-reasoned-reply-encode :refused :unknown-consumer))
(assert-event (member-equal :refused *fn-nctrl-statuses*))
(assert-event (equal (fn-native-control-status-class :refused) :refused))
(assert-event (equal (fn-ncr-client-read :poll (crt-refused))
                     (list :status :refused *crt-unknown*)))
(assert-event (equal (fn-ncr-client-read :status (crt-refused))
                     (list :status :refused *crt-unknown*)))
(assert-event (equal (fn-ncr-client-read :register (crt-refused))
                     (list :status :refused *crt-unknown*)))
(assert-event (equal (fn-ncr-client-read :bound-wait (crt-refused))
                     (list :status :refused *crt-unknown*)))
(assert-event (equal (fn-native-control-reply-detail :refused *crt-unknown*)
                     *crt-unknown*))
; A fault the owner ended in is read as the fault, with no reason printed.
(assert-event (equal (fn-ncr-client-read :ack (fn-native-control-reasoned-reply-encode :fault nil))
                     (list :status :fault *fn-nctrl-no-reason-word*)))
(assert-event (null (fn-native-control-reply-detail :fault *fn-nctrl-no-reason-word*)))
; Hypothesis (member status): a word outside the enumeration is not encoded,
; and the client falls back to the transport outcome.
(assert-event (not (member-equal :no-such-status *fn-nctrl-statuses*)))
(assert-event (equal (fn-ncr-client-read :poll (fn-native-control-reasoned-reply-encode
                                                :no-such-status :x))
                     '(:transport)))
(must-fail-checked
 (defthm crt-without-membership
   (equal (fn-ncr-client-read operation
                              (fn-native-control-reasoned-reply-encode status reason))
          (list :status status (fn-nctrl-reason-word reason)))
   :hints (("Goal" :in-theory (e/d (fn-ncr-client-read) (member-equal))))
   :rule-classes nil))
; Hypothesis (a refusal class) of the detail conjunct: an acceptance's read
; still carries the word, and prints none.
(assert-event (equal (fn-ncr-client-read :poll (fn-native-control-reasoned-reply-encode
                                                :accepted :unknown-consumer))
                     (list :status :accepted *crt-unknown*)))
(assert-event (null (fn-native-control-reply-detail :accepted *crt-unknown*)))
; Hypothesis (reason non-nil) of the detail conjunct: no reason prints none.
(assert-event (equal (fn-ncr-client-read :poll (fn-native-control-reasoned-reply-encode :refused nil))
                     (list :status :refused *fn-nctrl-no-reason-word*)))
(assert-event (null (fn-native-control-reply-detail :refused *fn-nctrl-no-reason-word*)))

; The other two reads.  An accepted consumer reply is the reply the old
; client read; an old owner's plain refusal (kind 2) resends; garbage is the
; transport outcome.
(defmacro crt-accepted-poll ()
  '(fn-ncl-poll-reply-encode :refused nil nil))
(assert-event (equal (fn-ncr-client-read :poll (crt-accepted-poll))
                     (list :reply (fn-ncl-poll-reply-decode (crt-accepted-poll)))))
(assert-event (equal (fn-ncr-client-read :poll (fn-native-control-reply-encode :refused))
                     '(:resend)))
(assert-event (equal (fn-ncr-client-read :poll (fn-native-control-reply-encode :busy))
                     (list :status :busy *fn-nctrl-no-reason-word*)))
(assert-event (equal (fn-ncr-client-read :poll '(1 2 3)) '(:transport)))

; ---------------------------------------------------------------------------
; fn-ncr-cli-after-retries-only-an-unbootstrapped-register.
(assert-event (equal (fn-ncr-cli-after :register :refused *fn-ncr-unbootstrapped-word*)
                     '(:bootstrap :register)))
(assert-event (equal *fn-ncr-unbootstrapped-word* (fn-nctrl-reason-word :unbootstrapped)))
(assert-event (equal (fn-ncr-cli-after :register :refused *fn-nctrl-no-reason-word*)
                     '(:bootstrap :register)))
; Each conjunct fails alone.
(assert-event (null (fn-ncr-cli-after :register :refused (fn-nctrl-reason-word :no-such-group))))
(assert-event (null (fn-ncr-cli-after :register :uncertain *fn-nctrl-no-reason-word*)))
(assert-event (null (fn-ncr-cli-after :poll :refused *fn-ncr-unbootstrapped-word*)))

; ---------------------------------------------------------------------------
; fn-ncr-withdrawal-roundtrip and fn-ncr-withdrawal-report-fits-the-poll-reply.
(assert-event (fn-ncr-withdrawal-report *crt-msgid*))
(assert-event (equal (fn-ncr-withdrawal-decode (fn-ncr-withdrawal-report *crt-msgid*))
                     (list :withdrawn *crt-msgid*)))
(assert-event (fn-ncl-poll-event-bytesp (fn-ncr-withdrawal-report *crt-msgid*)))
; The report holds the Message-ID and the five magic octets, nothing more.
(assert-event (equal (len (fn-ncr-withdrawal-report *crt-msgid*)) (+ 5 (len *crt-msgid*))))
; Hypothesis (a report): an empty Message-ID has none, and decodes nothing.
(assert-event (null (fn-ncr-withdrawal-report nil)))
(assert-event (equal (fn-ncr-withdrawal-decode (fn-ncr-withdrawal-report nil))
                     '(:refused :withdrawal)))
(assert-event (null (fn-ncr-withdrawal-report (make-list 513 :initial-element 65))))

; The report summary: empty, withdrawn, unreadable.
(assert-event (equal (fn-ncr-report-summary nil) '(:empty)))
(assert-event (equal (fn-ncr-report-summary (fn-ncr-withdrawal-report *crt-msgid*))
                     (list :withdrawn *crt-msgid*)))
(assert-event (equal (fn-ncr-report-summary '(1 2 3)) '(:unreadable)))

; ---------------------------------------------------------------------------
; The JSON line: fn-ncr-json-object-is-ascii, and the lines themselves.
(assert-event (equal (fn-ncr-json-line :poll :refused *crt-unknown* nil nil)
                     (fn-record-string-octets
                      "{\"command\":\"poll\",\"outcome\":\"refused\",\"reason\":\"unknown-consumer\"}")))
(assert-event (equal (fn-ncr-json-line :status :accepted *fn-nctrl-no-reason-word* '(3 10 7) nil)
                     (fn-record-string-octets
                      "{\"command\":\"status\",\"outcome\":\"accepted\",\"reason\":null,\"committed_ack\":3,\"journal_frontier\":10,\"journal_event_distance\":7}")))
(assert-event (equal (fn-ncr-json-line :wait :accepted *fn-nctrl-no-reason-word* nil '(:empty))
                     (fn-record-string-octets
                      "{\"command\":\"wait\",\"outcome\":\"accepted\",\"reason\":null,\"report\":\"empty\"}")))
(assert-event (equal (fn-ncr-json-line :bound-wait :accepted *fn-nctrl-no-reason-word* nil
                                       (fn-ncr-report-summary
                                        (fn-ncr-withdrawal-report
                                         (fn-record-string-octets "<a\"b@c>"))))
                     (fn-record-string-octets
                      "{\"command\":\"bound-wait\",\"outcome\":\"accepted\",\"reason\":null,\"report\":\"withdrawn\",\"message_id\":\"<a\\\"b@c>\"}")))
; Control octets and octets past ASCII are escaped, so the line is ASCII.
(assert-event (equal (fn-ncr-json-escape '(10 200 92))
                     (fn-record-string-octets "\\u000a\\u00c8\\\\")))
(assert-event (fn-ncr-asciip (fn-ncr-json-object
                              (list (cons '(107) (cons :str '(0 10 13 255)))))))
(assert-event (equal (fn-ncr-decimal 0) '(48)))
(assert-event (equal (fn-ncr-decimal 4294967295) (fn-record-string-octets "4294967295")))
(assert-event (equal (fn-ncr-article-json (list :article *crt-msgid* '(104 105)))
                     (fn-record-string-octets
                      "{\"report\":\"article\",\"message_id\":\"<q1@alice.invalid>\",\"article_hex\":\"6869\"}")))

; ---------------------------------------------------------------------------
; fn-ncr-cli-plan: --json wraps the command's own plan; without the flag the
; plan is the wait codec's.
(assert-event (equal (fn-ncr-cli-plan *fn-ncr-json-flag* (list '(104 101 108 112)))
                     '(:json (:help))))
(assert-event (equal (fn-ncr-cli-plan *fn-ncr-json-flag*
                                      (list '(115 116 97 116 117 115) '(47 99) '(98 111 98)))
                     '(:json (:run :status (47 99) (98 111 98) nil nil))))
(assert-event (equal (fn-ncr-cli-plan '(115 116 97 116 117 115) (list '(47 99) '(98 111 98)))
                     (fn-cwait-cli-plan '(115 116 97 116 117 115) (list '(47 99) '(98 111 98)))))
(assert-event (equal (fn-ncr-cli-plan *fn-ncr-json-flag* nil) '(:json (:usage :control-path))))

(assert-event (equal (fn-ncr-cli-after :bootstrap :accepted nil) '(:register)))
(assert-event (and (null (fn-ncr-cli-after :bootstrap :uncertain nil))
                   (null (fn-ncr-cli-after :bootstrap :fault nil))
                   (null (fn-ncr-cli-after :bootstrap :refused nil))))
