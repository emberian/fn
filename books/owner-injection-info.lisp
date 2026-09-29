; fn: Injection-Info and D25 over the octets the owner stores (PKT-597 with
; SEC-006; prefix `fn-oii-').
;
; The subject is books/owner-served-invariants.lisp fn-own-sub-stored-octets,
; which host/owner-host.lisp fn-owner-take stages for the Store and the
; completion gate compares with the durable record.  For a served submission
; it is the node's generated RFC 8315 lines (books/cancel-lock.lisp) in front
; of the injected octets with the Injection-Info parameters
; (books/injection-info-params.lisp).  Both are injecting-node metadata:
; the D25 comparison subject (books/poster-bytes.lisp fn-pb-subject, what
; fn-pb-same-articlep and so the Store's duplicate test read) of the stored
; octets is the poster's source, whatever the account, login, key epoch or
; complaints address that wrote them.

(in-package "ACL2")
(include-book "owner-served-invariants")
(include-book "injection-info-params-invariants")

; An injected decision is never a transit submission (:injected against
; :transit in the first field).
(local
 (defthm fn-oii-injected-car
   (implies (fn-inj-injectedp d) (equal (car d) :injected))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-inj-injectedp fn-inj-decision-status fn-inj-car)
            :expand ((fn-inj-nth 0 d))))))

(local
 (defthm fn-oii-an-injection-is-not-transit
   (implies (fn-inj-injectedp d) (not (fn-peer-submissionp d)))
   :hints (("Goal" :in-theory (e/d (fn-peer-submissionp fn-ag-car)
                                   (fn-inj-injectedp fn-nntp-printable-tokenp
                                    fn-af-message-idp fn-peer-submission-shapep))
            :use fn-oii-injected-car))))

; KEYSTONE (D25 over the stored octets; gpt-6 wave-5 review section 3).
(defthm fn-oii-stored-octets-keep-the-d25-subject
  (let ((d (fn-own-sub-decision sub)))
    (implies (and (equal d (fn-inj-decide source config obs))
                  (fn-inj-injectedp d))
             (equal (fn-pb-subject (fn-own-sub-stored-octets cfg sub ring)
                                   (fn-inj-config-agent config)
                                   (fn-inj-decision-msgid d))
                    (cons :source source))))
  :hints (("Goal" :in-theory (e/d (fn-pb-subject)
                                  (fn-own-sub-stored-octets fn-ipp-injected-octets
                                   fn-inj-decide fn-inj-injectedp fn-inj-source-of
                                   fn-cll-skip))
           :use ((:instance fn-own-stored-octets-keep-the-injected-octets
                            (secret ring))
                 (:instance fn-ipp-an-injection-does-not-open-with-c
                            (secret ring) (login (fn-own-sub-account sub)))
                 (:instance fn-ipp-injected-octets-keep-the-d25-subject
                            (secret ring) (login (fn-own-sub-account sub)))
                 (:instance fn-oii-an-injection-is-not-transit
                            (d (fn-inj-decide source config obs)))))))
