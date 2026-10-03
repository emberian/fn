; Teeth for books/native-control-reason (PKT-453 (a), PRF-172): the refusal
; reason on the FNCT wire.  Per keystone a reachable witness asserting the
; whole antecedent and conclusion; per hypothesis a witness that keeps the
; others, fails the omitted one and fails the conclusion, then a must-fail of
; the weakened theorem.
(in-package "ACL2")
(include-book "../../books/native-control-reason")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defconst *ncrt-unknown-group* (fn-record-string-octets "unknown-group"))
(defconst *ncrt-no-such-grant* (fn-record-string-octets "no-such-grant"))

; The word is the reason's name, folded to lower case.
(assert-event (equal (fn-nctrl-reason-word :unknown-group) *ncrt-unknown-group*))
(assert-event (equal (fn-nctrl-reason-word :no-such-grant) *ncrt-no-such-grant*))
(assert-event (equal (fn-nctrl-reason-word nil) *fn-nctrl-no-reason-word*))
(assert-event (equal (fn-nctrl-reason-word '(:not . :a-word)) *fn-nctrl-unnamed-reason-word*))
; A symbol named NONE is still a reason, and its word is not the no-reason word.
(assert-event (not (equal (fn-nctrl-reason-word :none) *fn-nctrl-no-reason-word*)))

; ---------------------------------------------------------------------------
; fn-native-control-printed-reason-is-the-decisions.  Positive: a refusal the
; injection decision named :unknown-group; the status is a member, its class
; is :refused and the reason is non-nil; the step reports the owner's status
; and word and the printed detail is the word.
; Sealed frames call the digest attachment, which a defconst may not: macros.
(defmacro ncrt-refused () '(fn-native-control-reasoned-reply-encode :refused :unknown-group))
(assert-event (fn-cbor-octet-listp (ncrt-refused)))
(assert-event (member-equal :refused *fn-nctrl-statuses*))
(assert-event (equal (fn-native-control-status-class :refused) :refused))
(assert-event (equal (fn-native-control-reasoned-client-step
                      (fn-native-control-reasoned-reply-read (ncrt-refused)))
                     (list :status :refused *ncrt-unknown-group*)))
(assert-event (equal (fn-native-control-reply-detail :refused *ncrt-unknown-group*)
                     *ncrt-unknown-group*))
; Partial durable success and owner faults must retain their named reason.
; Each witness checks the literal keystone antecedent and both conclusions.
(defun ncrt-named-nonacceptance-witness (status reason)
  (let* ((word (fn-nctrl-reason-word reason))
         (step (fn-native-control-reasoned-client-step
                (fn-native-control-reasoned-reply-read
                 (fn-native-control-reasoned-reply-encode status reason)))))
    (and (member-equal status *fn-nctrl-statuses*) reason
         (member-equal (fn-native-control-status-class status)
                       '(:refused :uncertain :fault))
         (equal step (list :status status word))
         (equal (fn-native-control-reply-detail (cadr step) (caddr step)) word))))
(assert-event
 (ncrt-named-nonacceptance-witness :uncertain :withdrawal-authorized-cause-refused))
(assert-event
 (ncrt-named-nonacceptance-witness :fault :withdrawal-authorized-cause-fault))
(assert-event (null (fn-native-control-reply-detail :uncertain (fn-nctrl-reason-word nil))))
(assert-event (null (fn-native-control-reply-detail :fault (fn-nctrl-reason-word nil))))
; A named refusal keeps its status and carries the decision's word.
(assert-event (equal (fn-native-control-reasoned-client-step
                      (fn-native-control-reasoned-reply-read
                       (fn-native-control-reasoned-reply-encode
                        :article-exceeds-profile-bound :oversize)))
                     (list :status :article-exceeds-profile-bound
                           (fn-record-string-octets "oversize"))))
; Hypothesis (member status): a word outside the enumeration is not encoded,
; and the client falls back to the transport outcome.
(assert-event (equal (fn-native-control-reasoned-reply-encode :no-such-status :x) :bad))
(assert-event (equal (fn-native-control-reasoned-client-step
                      (fn-native-control-reasoned-reply-read
                       (fn-native-control-reasoned-reply-encode :no-such-status :x)))
                     '(:transport)))
(must-fail-checked
 (defthm ncrt-without-membership
   (equal (fn-native-control-reasoned-client-step
           (fn-native-control-reasoned-reply-read
            (fn-native-control-reasoned-reply-encode status reason)))
          (list :status status (fn-nctrl-reason-word reason)))
   :hints (("Goal" :in-theory (disable member-equal)))
   :rule-classes nil))
; Hypothesis (a nonacceptance class): an acceptance prints no reason.
(assert-event (member-equal :accepted *fn-nctrl-statuses*))
(assert-event (null (fn-native-control-reply-detail :accepted *ncrt-unknown-group*)))
(must-fail-checked
 (defthm ncrt-detail-without-nonacceptance
   (implies (and (member-equal status *fn-nctrl-statuses*) reason)
            (equal (fn-native-control-reply-detail status (fn-nctrl-reason-word reason))
                   (fn-nctrl-reason-word reason)))
   :hints (("Goal" :in-theory (enable fn-native-control-reply-detail)))
   :rule-classes nil))
; Hypothesis (a reason): a refusal with no reason prints none.
(assert-event (null (fn-native-control-reply-detail :refused (fn-nctrl-reason-word nil))))
(must-fail-checked
 (defthm ncrt-detail-without-reason
   (implies (and (member-equal status *fn-nctrl-statuses*)
                 (equal (fn-native-control-status-class status) :refused))
            (equal (fn-native-control-reply-detail status (fn-nctrl-reason-word reason))
                   (fn-nctrl-reason-word reason)))
   :hints (("Goal" :in-theory (enable fn-native-control-reply-detail)))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; Compatibility.  An old owner answers a reasoned request with its plain reply
; (it cannot decode kind 13 and refuses it before acting): the new client
; reads :legacy and resends the plain request once; a plain acceptance is
; reported with no reason.
(defconst *ncrt-msgid* (fn-record-string-octets "<a@example.invalid>"))
(defconst *ncrt-groups* (list (fn-record-string-octets "fn.test")))
(defconst *ncrt-article* (fn-record-string-octets "Subject: x"))
(defmacro ncrt-reasoned-post ()
  '(fn-native-control-reasoned-request-encode *ncrt-msgid* *ncrt-groups* *ncrt-article*))
(assert-event (fn-cbor-octet-listp (ncrt-reasoned-post)))
(assert-event (equal (fn-native-control-request-decode (ncrt-reasoned-post))
                     '(:refused :frame)))
(assert-event (equal (fn-native-control-reasoned-request-decode (ncrt-reasoned-post))
                     (fn-native-control-request-decode
                      (fn-native-control-request-encode
                       *ncrt-msgid* *ncrt-groups* *ncrt-article*))))
(assert-event (equal (car (fn-native-control-reasoned-request-decode (ncrt-reasoned-post)))
                     :request))
(assert-event (fn-native-control-reasoned-framep (ncrt-reasoned-post)))
(assert-event (not (fn-native-control-reasoned-framep
                    (fn-native-control-request-encode
                     *ncrt-msgid* *ncrt-groups* *ncrt-article*))))
(defconst *ncrt-argv* (list (fn-record-string-octets "control")
                            (fn-record-string-octets "list")))
(defmacro ncrt-reasoned-admin () '(fn-native-control-reasoned-admin-encode *ncrt-argv*))
(assert-event (equal (fn-native-control-reasoned-admin-decode (ncrt-reasoned-admin))
                     (list :admin *ncrt-argv*)))
(assert-event (equal (fn-native-control-admin-decode (ncrt-reasoned-admin))
                     '(:refused :frame)))
(assert-event (fn-native-control-reasoned-framep (ncrt-reasoned-admin)))
(assert-event (equal (fn-native-control-reasoned-reply-read
                      (fn-native-control-reply-encode :refused))
                     '(:legacy :refused)))
(assert-event (equal (fn-native-control-reasoned-client-step '(:legacy :refused))
                     '(:resend)))
(assert-event (equal (fn-native-control-reasoned-client-step
                      (fn-native-control-reasoned-reply-read
                       (fn-native-control-reply-encode :accepted)))
                     (list :status :accepted *fn-nctrl-no-reason-word*)))
; An old client never sends kind 13 or 17, so it never reads kind 18; were it
; handed one, its decoder answers :bad (no status), never a false acceptance.
(assert-event (equal (fn-native-control-reply-decode (ncrt-refused)) :bad))

; fn-native-control-transport-word-names-the-refusal: a connect that failed
; (no owner at the control path) is refused and names no-owner; an exchange
; lost after submission is uncertain and names nothing (lane ops-fixes).
(assert-event (equal (fn-native-control-transport-outcome :before-submission) :refused))
(assert-event (equal (fn-native-control-reply-detail
                      (fn-native-control-transport-outcome :before-submission)
                      (fn-native-control-transport-word :before-submission))
                     '(110 111 45 111 119 110 101 114)))  ; no-owner
(assert-event (equal (fn-native-control-transport-outcome :after-submission) :uncertain))
(assert-event (null (fn-native-control-reply-detail
                     (fn-native-control-transport-outcome :after-submission)
                     (fn-native-control-transport-word :after-submission))))

; ---------------------------------------------------------------------------
; PKT-472 (e): fn-native-control-host-refusal-names-its-class.  Witness, per
; class: the reply the host writes for a store/OS/socket error, read by the
; client, prints the class's word, not NONE.
(defun ncrt-host-detail (class)
  (let ((step (fn-native-control-reasoned-client-step
               (fn-native-control-reasoned-reply-read
                (fn-native-control-reasoned-reply-encode
                 :refused (fn-native-control-host-refusal-reason class))))))
    (fn-native-control-reply-detail (cadr step) (caddr step))))
(assert-event
 (and (equal (ncrt-host-detail :store-error) (fn-record-string-octets "store-error"))
      (equal (ncrt-host-detail :os-error) (fn-record-string-octets "os-error"))
      (equal (ncrt-host-detail :socket-error) (fn-record-string-octets "socket-error"))
      (not (equal (ncrt-host-detail :store-error) *fn-nctrl-no-reason-word*))))
; Hypothesis removed (the class is one of the three): any other class names
; no reason, and the reply prints NONE -- the answer before PKT-472 (e).
(assert-event
 (and (not (member-equal :timeout *fn-nctrl-host-refusal-classes*))
      (equal (fn-native-control-host-refusal-reason :timeout) nil)
      (equal (caddr (fn-native-control-reasoned-client-step
                     (fn-native-control-reasoned-reply-read
                      (fn-native-control-reasoned-reply-encode
                       :refused (fn-native-control-host-refusal-reason :timeout)))))
             *fn-nctrl-no-reason-word*)
      (not (equal (ncrt-host-detail :timeout) (fn-nctrl-reason-word :timeout)))))
(must-fail-checked
 (defthm ncrt-host-refusal-without-membership
   (not (equal (fn-nctrl-reason-word (fn-native-control-host-refusal-reason class))
               *fn-nctrl-no-reason-word*))
   :rule-classes nil))

; PKT-867 teeth for fn-native-control-admin-decode-of-encode and its reasoned
; twin.  Positive witnesses: the antecedent (the client can seal the argv)
; and the conclusion (the owner decodes that argv) both hold for 200 words
; and for one word of 70,000 octets, past the narrow codec's 65,535 that the
; words were encoded with before.  Hypothesis-removal witness: an argv the
; client cannot seal (a non-ASCII word) is :bad, and its "decode" is not the
; argv, so the antecedent is what makes the conclusion hold.
(defun fn-nctrl-rt-repeat (word count)
  (if (zp count) nil (cons word (fn-nctrl-rt-repeat word (1- count)))))
(defconst *fn-nctrl-rt-200*
  (fn-nctrl-rt-repeat (fn-record-string-octets "group") 200))
(defconst *fn-nctrl-rt-wide*
  (list (fn-record-string-octets "motd") (fn-record-string-octets "set")
        (make-list 70000 :initial-element 97)))
(assert-event (not (equal (fn-native-control-admin-encode *fn-nctrl-rt-200*) :bad)))
(assert-event (equal (fn-native-control-admin-decode
                      (fn-native-control-admin-encode *fn-nctrl-rt-200*))
                     (list :admin *fn-nctrl-rt-200*)))
(assert-event (not (equal (fn-native-control-reasoned-admin-encode *fn-nctrl-rt-wide*) :bad)))
(assert-event (equal (fn-native-control-reasoned-admin-decode
                      (fn-native-control-reasoned-admin-encode *fn-nctrl-rt-wide*))
                     (list :admin *fn-nctrl-rt-wide*)))
(assert-event (equal (fn-native-control-admin-encode (list '(200))) :bad))
(assert-event (not (equal (fn-native-control-admin-decode
                           (fn-native-control-admin-encode (list '(200))))
                          (list :admin (list '(200))))))
(must-fail-checked
 (defthm ncrt-admin-round-trip-without-sealable
   (equal (fn-native-control-admin-decode (fn-native-control-admin-encode argv))
          (list :admin argv))
   :rule-classes nil))
