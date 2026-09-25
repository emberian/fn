; Teeth for PRF-097 (books/peer-invite.lisp and the invitations slot of
; books/config.lisp).  Per keystone: a reachable witness asserting the
; antecedent and the conclusion, and per hypothesis a removal witness that
; shows the conclusion failing where the hypothesis fails (AGENTS.md, "Teeth
; ship with the theorem").  The signatures are fixed-width placeholders:
; whether a carrier verifies enters every plan only as the two primitive
; observations, which the witnesses supply (:verified, or :refused for a
; tampered body).  crypto-attach and codec-attach make the digest SHA-256
; and the statement codec executable, so genesis identities and source
; identities are the image's.  A value computed through an attachment is a
; zero-argument macro, not a `defconst' (ACL2 does not call an attachment
; while evaluating a constant; tests/acl2/auth-secret-tests.lisp).
(in-package "ACL2")
(include-book "../../books/peer-invite")
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; Two key sets and their genesis principals: node A (inviter), node B.
(defconst *pit-a-ed* (make-list 32 :initial-element 1))
(defconst *pit-a-ml* (make-list 1952 :initial-element 2))
(defconst *pit-a-token* '(7 7 7 7))
(defconst *pit-a-keys* (list (cons :ed25519 *pit-a-ed*)
                             (cons :ml-dsa-65 *pit-a-ml*)))
(defmacro pit-a ()
  '(fn-pinv-genesis-principal *pit-a-ed* *pit-a-ml* *pit-a-token*))
(defconst *pit-b-ed* (make-list 32 :initial-element 3))
(defconst *pit-b-ml* (make-list 1952 :initial-element 4))
(defconst *pit-b-token* '(9 9))
(defconst *pit-b-keys* (list (cons :ed25519 *pit-b-ed*)
                             (cons :ml-dsa-65 *pit-b-ml*)))
(defmacro pit-b ()
  '(fn-pinv-genesis-principal *pit-b-ed* *pit-b-ml* *pit-b-token*))
(assert-event (fn-hsig-exact-octets-p (pit-a) 32))
(assert-event (fn-prin-genesis-bindsp (pit-a) (append *pit-a-ed* *pit-a-ml*)
                                      *pit-a-token*))

(defconst *pit-sigs*
  (list (cons :ed25519 (make-list 64 :initial-element 5))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 6))))

(defun pit-sign (source principal keys)
  (fn-hc-render-at-most 1000000 source principal keys *pit-sigs*))

(defconst *pit-date* 812345678000)
(defconst *pit-nonce* (make-list 16 :initial-element 171))
(defconst *pit-nonce2* (make-list 16 :initial-element 172))

(defun pit-invitation-source (nonce principal token keys)
  (fn-pinv-invitation-source *pit-date* nonce principal token keys
                             (fn-pinv-text "nodeB") (fn-pinv-text "a.example")
                             (fn-pinv-text "fn.*") (fn-pinv-text "127.0.0.1")
                             (fn-pinv-text "11190")))

(defmacro pit-inv-source ()
  '(pit-invitation-source *pit-nonce* (pit-a) *pit-a-token* *pit-a-keys*))
(defmacro pit-inv ()
  ' (pit-sign (pit-inv-source) (pit-a) *pit-a-keys*))
(assert-event (consp (pit-inv)))

; -----------------------------------------------------------------------------
; Accept.  Witness: B enrols A with A's key set at generation 1.

(defmacro pit-accept ()
  '(fn-pinv-accept-step 1 2 3 (pit-inv) *pit-a-ml* :verified :verified nil))
(assert-event (equal (car (pit-accept)) :enrol))
(assert-event (fn-pinv-bound-document-p (pit-inv) *pit-a-ml* :verified
                                        :verified *fn-pinv-invitation-kind*))
(assert-event (equal (fn-pinv-at 1 (pit-accept))
                     (fn-hl-enroll-event 1 2 3 1 (pit-a) *pit-a-keys* nil)))
(assert-event (equal (fn-pinv-received-principal (pit-inv)) (pit-a)))
(assert-event (equal (fn-pinv-received-keys (pit-inv)) *pit-a-keys*))

; Tampered body: a byte of the source changed after signing.  The primitive
; observation refuses; the step refuses, and the binding fails.
(defmacro pit-tampered ()
  '(pit-sign (append (take (- (len (pit-inv-source)) 3) (pit-inv-source))
                    (fn-pinv-text "99") (list 13 10))
            (pit-a) *pit-a-keys*))
(assert-event (equal (fn-pinv-accept-step 1 2 3 (pit-tampered) *pit-a-ml*
                                          :verified :refused nil)
                     '(:refused :unverified)))
(must-fail (assert-event (fn-pinv-bound-document-p (pit-tampered) *pit-a-ml*
                                                   :verified :refused
                                                   *fn-pinv-invitation-kind*)))

; A body naming another key than the carrier's: refused by name.
(defmacro pit-claims ()
  '(pit-sign (pit-invitation-source *pit-nonce* (pit-a) *pit-a-token*
                                   *pit-b-keys*)
            (pit-a) *pit-a-keys*))
(assert-event (equal (fn-pinv-accept-step 1 2 3 (pit-claims) *pit-a-ml*
                                          :verified :verified nil)
                     '(:refused :claimed-keys)))
(must-fail (assert-event (fn-pinv-bound-document-p (pit-claims) *pit-a-ml*
                                                   :verified :verified
                                                   *fn-pinv-invitation-kind*)))

; A principal that is not the key set's genesis identity: refused.
(defmacro pit-not-genesis ()
  '(pit-sign (pit-invitation-source *pit-nonce* (pit-b) *pit-a-token*
                                   *pit-a-keys*)
            (pit-b) *pit-a-keys*))
(assert-event (equal (fn-pinv-accept-step 1 2 3 (pit-not-genesis) *pit-a-ml*
                                          :verified :verified nil)
                     '(:refused :genesis)))
(must-fail (assert-event (fn-pinv-bound-document-p (pit-not-genesis)
                                                   *pit-a-ml* :verified
                                                   :verified
                                                   *fn-pinv-invitation-kind*)))

; Already enrolled with exactly these keys: the accept step refuses, and
; the keystone's "not already enrolled" conclusion fails there.
(defmacro pit-a-snapshots ()
  ' (list (fn-pinv-at 1 (pit-accept))))
(assert-event (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* (pit-a-snapshots)))
(assert-event (equal (fn-pinv-accept-step 4 5 3 (pit-inv) *pit-a-ml* :verified
                                          :verified (pit-a-snapshots))
                     '(:refused :already-enrolled)))

; -----------------------------------------------------------------------------
; Issue.  Witness: A records its invitation; a replayed nonce is refused
; by the plan and, independently, by configuration admission.

(defmacro pit-issue ()
  '(fn-pinv-issue-plan (pit-inv) *pit-a-ml* :verified :verified nil))
(assert-event (equal (car (pit-issue)) :issue))
(defconst *pit-v0* (fn-cfg-empty-value))
(assert-event (null (fn-cfg-delta-reason *pit-v0* 1 nil 0 0
                                         (fn-pinv-at 1 (pit-issue)))))
(defmacro pit-v1 ()
  ' (fn-cfg-apply-delta *pit-v0* 1 nil (fn-pinv-at 1 (pit-issue))))
(defmacro pit-inv-rows ()
  ' (fn-cfg-invitations (pit-v1)))
(defconst *pit-nonce-hex* (fn-pinv-hex-string *pit-nonce*))
(assert-event (fn-cfg-invitation-pendingp (pit-inv-rows) *pit-nonce-hex*))
(assert-event (equal (fn-pinv-issue-plan (pit-inv) *pit-a-ml* :verified
                                         :verified (pit-inv-rows))
                     '(:refused :invitation-nonce-reused)))
(assert-event (equal (fn-cfg-delta-reason (pit-v1) 2 nil 0 0
                                          (fn-pinv-at 1 (pit-issue)))
                     :invitation-nonce-reused))

; -----------------------------------------------------------------------------
; Confirm.  B's acceptance of A's invitation.

(defun pit-acceptance (invitation inviter-ml principal token keys)
  (pit-sign (fn-pinv-acceptance-source *pit-date* invitation inviter-ml
                                       :verified :verified principal token
                                       keys (fn-pinv-text "b.example")
                                       (fn-pinv-text "-"))
            principal keys))

(defmacro pit-acc ()
  ' (pit-acceptance (pit-inv) *pit-a-ml* (pit-b) *pit-b-token*
                                    *pit-b-keys*))
(assert-event (consp (pit-acc)))

(defmacro pit-confirm ()
  '(fn-pinv-confirm-plan (pit-acc) *pit-b-ml* :verified :verified
                        (pit-inv-rows) nil))
(assert-event (equal (car (pit-confirm)) :consume))
(assert-event (fn-pinv-acceptance-names-row-p
               (fn-pinv-received-source (pit-acc))
               (fn-cfg-invitation-row (pit-inv-rows) *pit-nonce-hex*)))
(assert-event (fn-pinv-bound-document-p (pit-acc) *pit-b-ml* :verified
                                        :verified *fn-pinv-acceptance-kind*))

; Consumption, then the crash point: the configuration record is durable,
; the kind-3 record is not.  The same acceptance now enrols B.
(defmacro pit-v2 ()
  ' (fn-cfg-apply-delta (pit-v1) 2 nil (fn-pinv-at 1 (pit-confirm))))
(assert-event (null (fn-cfg-delta-reason (pit-v1) 2 nil 0 0
                                         (fn-pinv-at 1 (pit-confirm)))))
(defmacro pit-consumed-rows ()
  ' (fn-cfg-invitations (pit-v2)))
(assert-event (fn-cfg-invitation-consumedp (pit-consumed-rows) *pit-nonce-hex*))
(defmacro pit-confirm-step ()
  '(fn-pinv-confirm-step 7 8 2 (pit-acc) *pit-b-ml* :verified :verified
                        (pit-consumed-rows) nil))
(assert-event (equal (car (pit-confirm-step)) :enrol))
(assert-event (equal (fn-pinv-at 1 (pit-confirm-step))
                     (fn-hl-enroll-event 7 8 2 1 (pit-b) *pit-b-keys* nil)))
; Before the consumption is durable, the confirm step enrols nothing.
(assert-event (equal (car (fn-pinv-confirm-step 7 8 2 (pit-acc) *pit-b-ml*
                                                :verified :verified
                                                (pit-inv-rows) nil))
                     :consume))

; A second consumption of the same nonce: refused by admission, whatever
; the acceptance.
(assert-event (equal (fn-cfg-delta-reason (pit-v2) 3 nil 0 0
                                          (fn-pinv-at 1 (pit-confirm)))
                     :invitation-not-pending))
; Removal witness for "consumed": on the pending value it is admitted.
(must-fail (assert-event (fn-cfg-delta-reason (pit-v1) 3 nil 0 0
                                              (fn-pinv-at 1 (pit-confirm)))))

; A second confirm after the enrolment: refused.
(defmacro pit-b-snapshots ()
  ' (list (fn-pinv-at 1 (pit-confirm-step))))
(assert-event (equal (fn-pinv-confirm-step 9 10 2 (pit-acc) *pit-b-ml*
                                           :verified :verified
                                           (pit-consumed-rows)
                                           (pit-b-snapshots))
                     '(:refused :already-confirmed)))
; Removal witness for the resume keystone's "not enrolled": the resumed
; plan is not an enrolment there.
(must-fail (assert-event
            (equal (car (fn-pinv-confirm-plan (pit-acc) *pit-b-ml* :verified
                                              :verified (pit-consumed-rows)
                                              (pit-b-snapshots)))
                   :enrol)))

; A replayed nonce: a second acceptance (another acceptor, C = B's keys
; under another token) of the consumed invitation is refused.
(defconst *pit-c-token* '(1 2 3))
(defmacro pit-c ()
  '(fn-pinv-genesis-principal *pit-b-ed* *pit-b-ml* *pit-c-token*))
(defmacro pit-acc-c ()
  ' (pit-acceptance (pit-inv) *pit-a-ml* (pit-c) *pit-c-token*
                                      *pit-b-keys*))
(assert-event (equal (fn-pinv-confirm-plan (pit-acc-c) *pit-b-ml* :verified
                                           :verified (pit-consumed-rows) nil)
                     '(:refused :invitation-consumed)))

; An acceptance of another invitation: A issued nonce2 too, and B answers an
; invitation under nonce2 that A did not sign (another source identity).
(defmacro pit-inv2-source ()
  '(pit-invitation-source *pit-nonce2* (pit-a) *pit-a-token* *pit-a-keys*))
(defmacro pit-inv2 ()
  ' (pit-sign (pit-inv2-source) (pit-a) *pit-a-keys*))
(defmacro pit-v3 ()
  '(fn-cfg-apply-delta (pit-v2) 3 nil
                      (fn-pinv-at 1 (fn-pinv-issue-plan (pit-inv2) *pit-a-ml*
                                                        :verified :verified
                                                        (pit-consumed-rows)))))
(defmacro pit-other-inv ()
  '(pit-sign (fn-pinv-invitation-source *pit-date* *pit-nonce2* (pit-a)
                                       *pit-a-token* *pit-a-keys*
                                       (fn-pinv-text "nodeX")
                                       (fn-pinv-text "a.example")
                                       (fn-pinv-text "fn.*")
                                       (fn-pinv-text "127.0.0.1")
                                       (fn-pinv-text "11190"))
            (pit-a) *pit-a-keys*))
(defmacro pit-acc-other ()
  ' (pit-acceptance (pit-other-inv) *pit-a-ml* (pit-b) *pit-b-token*
                                          *pit-b-keys*))
(assert-event (equal (fn-pinv-confirm-plan (pit-acc-other) *pit-b-ml*
                                           :verified :verified
                                           (fn-cfg-invitations (pit-v3)) nil)
                     '(:refused :another-invitation)))
(must-fail (assert-event (fn-pinv-acceptance-names-row-p
                          (fn-pinv-received-source (pit-acc-other))
                          (fn-cfg-invitation-row
                           (fn-cfg-invitations (pit-v3))
                           (fn-pinv-hex-string *pit-nonce2*)))))

; An acceptance of an invitation another inviter signed (B invites under
; A's nonce): the row names A, the acceptance names B as inviter.
(defmacro pit-b-inv ()
  '(pit-sign (pit-invitation-source *pit-nonce* (pit-b) *pit-b-token*
                                   *pit-b-keys*)
            (pit-b) *pit-b-keys*))
(defmacro pit-acc-b-inv ()
  ' (pit-acceptance (pit-b-inv) *pit-b-ml* (pit-a) *pit-a-token*
                                          *pit-a-keys*))
(assert-event (equal (fn-pinv-confirm-plan (pit-acc-b-inv) *pit-a-ml*
                                           :verified :verified (pit-inv-rows)
                                           nil)
                     '(:refused :another-inviter)))

; An acceptance under a nonce this node never issued.
(assert-event (equal (fn-pinv-confirm-plan (pit-acc) *pit-b-ml* :verified
                                           :verified nil nil)
                     '(:refused :no-such-invitation)))

; An invitation presented to confirm is not an acceptance.
(assert-event (equal (fn-pinv-confirm-plan (pit-inv) *pit-a-ml* :verified
                                           :verified (pit-inv-rows) nil)
                     '(:refused :document-kind)))

; The control requests round-trip, and a wrong kind decodes to nothing.
(assert-event (equal (fn-pinv-request-decode
                      *fn-pinv-confirm-kind*
                      (fn-pinv-request-encode *fn-pinv-confirm-kind* (pit-acc)))
                     (pit-acc)))
(assert-event (null (fn-pinv-request-decode
                     *fn-pinv-accept-kind*
                     (fn-pinv-request-encode *fn-pinv-confirm-kind* (pit-acc)))))
