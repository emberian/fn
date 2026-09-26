; Teeth for books/native-control-reason (PKT-453 (a), PRF-172): the refusal
; reason on the FNCT wire.  Per keystone a reachable witness asserting the
; whole antecedent and conclusion; per hypothesis a witness that keeps the
; others, fails the omitted one and fails the conclusion, then a must-fail of
; the weakened theorem.
(in-package "ACL2")
(include-book "../../books/native-control-reason")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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
(must-fail
 (defthm ncrt-without-membership
   (equal (fn-native-control-reasoned-client-step
           (fn-native-control-reasoned-reply-read
            (fn-native-control-reasoned-reply-encode status reason)))
          (list :status status (fn-nctrl-reason-word reason)))
   :hints (("Goal" :in-theory (disable member-equal)))
   :rule-classes nil))
; Hypothesis (a refusal class): an acceptance prints no reason.
(assert-event (member-equal :accepted *fn-nctrl-statuses*))
(assert-event (null (fn-native-control-reply-detail :accepted *ncrt-unknown-group*)))
(must-fail
 (defthm ncrt-detail-without-refusal
   (implies (and (member-equal status *fn-nctrl-statuses*) reason)
            (equal (fn-native-control-reply-detail status (fn-nctrl-reason-word reason))
                   (fn-nctrl-reason-word reason)))
   :hints (("Goal" :in-theory (enable fn-native-control-reply-detail)))
   :rule-classes nil))
; Hypothesis (a reason): a refusal with no reason prints none.
(assert-event (null (fn-native-control-reply-detail :refused (fn-nctrl-reason-word nil))))
(must-fail
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
