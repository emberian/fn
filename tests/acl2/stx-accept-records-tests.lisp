; Evaluated binding witnesses for atomic article/verdict acceptance.
(in-package "ACL2")
(include-book "../../books/store-events")
(include-book "../../books/codec-attach")

(defconst *stxa-payload* '(70 78 45 83 116 97 116 101 109 101 110 116 58 32 49 13 10))
(defconst *stxa-msgid* "<atomic@example.invalid>")
(defconst *stxa-profile* '(111 112 97 113 117 101 45 118 49))
(defconst *stxa-subject* "subject-v1-exact-source-binding")
(defconst *stxa-record*
  (fn-record-make 4 9 12 *stxa-msgid* *stxa-payload* '("local.test")
                  "obligation" *stxa-subject* "local" 17 841000000))
(defconst *stxa-verdict*
  (fn-stxe-make 4 9 12 *stxa-msgid* :unverified
                *fn-stx-token-signature* 3 *stxa-profile*))
(defconst *stxa-event*
  (fn-stxa-make 4 9 12 3 *stxa-profile*
                (fn-record-string-octets *stxa-subject*)
                (fn-record-encode-impl *stxa-record*)
                (fn-stxe-encode *stxa-verdict*)))

(assert-event (fn-stxa-p *stxa-event*))
(assert-event (fn-stxa-bindsp *stxa-event*))
(assert-event
 (equal (fn-stmt-value (fn-stxa-decode-exact (fn-stxa-encode *stxa-event*)))
        *stxa-event*))
(assert-event
 (equal (fn-stxa-article-record
         (fn-stmt-value (fn-stxa-decode-exact (fn-stxa-encode *stxa-event*))))
        (fn-record-encode *stxa-record*)))

; A valid composite value with two large opaque children crosses the old
; 65,538-octet decoder ceiling.  The value round-trips exactly; semantic child
; binding remains the separate fn-stxa-bindsp contract exercised below.
(defconst *stxa-large-event*
  (fn-stxa-make 4 9 12 3 '(112)
                '(115)
                (make-list *fn-record-max-octets* :initial-element 1)
                (make-list *fn-stxe-max-octets* :initial-element 2)))
(assert-event (fn-stxa-p *stxa-large-event*))
(assert-event (< *fn-cbor-max-input* (len (fn-stxa-encode *stxa-large-event*))))
(assert-event
 (equal (fn-stmt-value
         (fn-store-event-decode-exact (fn-stxa-encode *stxa-large-event*)))
        *stxa-large-event*))

; Every binding dimension has an evaluated substitution witness.
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 5 9 12 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*)
                     (fn-stxe-encode *stxa-verdict*)))))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 10 12 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*)
                     (fn-stxe-encode *stxa-verdict*)))))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 13 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*)
                     (fn-stxe-encode *stxa-verdict*)))))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 12 4 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*)
                     (fn-stxe-encode *stxa-verdict*)))))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 12 3 '(111 116 104 101 114)
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*)
                     (fn-stxe-encode *stxa-verdict*)))))

(defconst *stxa-other-verdict*
  (fn-stxe-make 4 9 12 "<other@example.invalid>" :unverified
                *fn-stx-token-signature* 3 *stxa-profile*))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 12 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*)
                     (fn-stxe-encode *stxa-other-verdict*)))))

(defconst *stxa-wrong-subject-record*
  (fn-record-make 4 9 12 *stxa-msgid* *stxa-payload* '("local.test")
                  "obligation" "wrong-subject" "local" 17 841000000))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 12 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-wrong-subject-record*)
                     (fn-stxe-encode *stxa-verdict*)))))

; Neither malformed child becomes a partial acceptance.
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 12 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*) '(1 2 3)
                     (fn-stxe-encode *stxa-verdict*)))))
(assert-event
 (not (fn-stxa-bindsp
       (fn-stxa-make 4 9 12 3 *stxa-profile*
                     (fn-record-string-octets *stxa-subject*)
                     (fn-record-encode *stxa-record*) '(1 2 3)))))
