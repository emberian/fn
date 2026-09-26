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
                             (fn-pinv-text "11190") (fn-pinv-text "192.0.2.7")
                             (fn-pinv-text "11191")))

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
                                        :verified *fn-pinv-invitation-kind* nil))
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
                                                   *fn-pinv-invitation-kind* nil)))

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
                                                   *fn-pinv-invitation-kind* nil)))

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
                                                   *fn-pinv-invitation-kind* nil)))

; Already enrolled with exactly these keys: since PKT-473 the accept step
; answers (:current), nothing to enrol (the record plan refuses a replay;
; below), so the keystone's enrolment conclusion does not hold there.
(defmacro pit-a-snapshots ()
  ' (list (fn-pinv-at 1 (pit-accept))))
(assert-event (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* (pit-a-snapshots)))
(assert-event (equal (fn-pinv-accept-step 4 5 3 (pit-inv) *pit-a-ml* :verified
                                          :verified (pit-a-snapshots))
                     '(:current)))

; -----------------------------------------------------------------------------
; Issue.  Witness: A records its invitation; a replayed nonce is refused
; by the plan and, independently, by configuration admission.

(defmacro pit-issue ()
  '(fn-pinv-issue-plan (pit-inv) *pit-a-ml* :verified :verified nil nil))
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
                                         :verified (pit-inv-rows) nil)
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
                                        :verified *fn-pinv-acceptance-kind* nil))

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

; A second confirm after the enrolment: refused by the plans the host asks
; first (the record plan passes the confirm plan's `already-confirmed').
; The step itself answers (:current) there (PKT-211): the host asks it only
; right after a consumption it published, below (PRF-179).
(defmacro pit-b-snapshots ()
  ' (list (fn-pinv-at 1 (pit-confirm-step))))
(assert-event (equal (fn-pinv-confirm-record-plan (pit-acc) (pit-inv) *pit-b-ml*
                                                  :verified :verified
                                                  (pit-consumed-rows)
                                                  (pit-b-snapshots) nil)
                     '(:refused :already-confirmed)))
(assert-event (equal (fn-pinv-confirm-step 9 10 2 (pit-acc) *pit-b-ml*
                                           :verified :verified
                                           (pit-consumed-rows)
                                           (pit-b-snapshots))
                     '(:current)))
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
                                                        (pit-consumed-rows) nil))))
(defmacro pit-other-inv ()
  '(pit-sign (fn-pinv-invitation-source *pit-date* *pit-nonce2* (pit-a)
                                       *pit-a-token* *pit-a-keys*
                                       (fn-pinv-text "nodeX")
                                       (fn-pinv-text "a.example")
                                       (fn-pinv-text "fn.*")
                                       (fn-pinv-text "127.0.0.1")
                                       (fn-pinv-text "11190")
                                       (fn-pinv-text "-") (fn-pinv-text "-"))
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
; Confirm (kind 11) carries the acceptance and the invitation (PRF-124).
(assert-event (equal (fn-pinv-request-decode
                      *fn-pinv-accept-kind*
                      (fn-pinv-request-encode *fn-pinv-accept-kind* (pit-inv)))
                     (pit-inv)))
(assert-event (equal (fn-pinv-confirm-request-decode
                      (fn-pinv-confirm-request-encode (pit-acc) (pit-inv)))
                     (list (pit-acc) (pit-inv))))
(assert-event (null (fn-pinv-request-decode
                     *fn-pinv-accept-kind*
                     (fn-pinv-confirm-request-encode (pit-acc) (pit-inv)))))
(assert-event (null (fn-pinv-confirm-request-decode
                     (fn-pinv-request-encode *fn-pinv-accept-kind* (pit-inv)))))
(assert-event (equal (fn-pinv-request-encode *fn-pinv-confirm-kind* (pit-acc))
                     :bad))

; =============================================================================
; PRF-124: the confirm's one record consumes and configures the peer.

(defmacro pit-record ()
  '(fn-pinv-confirm-record-plan (pit-acc) (pit-inv) *pit-b-ml* :verified
                               :verified (pit-inv-rows) nil nil))
(defmacro pit-peer ()
  '(fn-pinv-confirmed-peer (fn-pinv-received-source (pit-inv))
                          (fn-pinv-received-source (pit-acc)) (pit-b)))

; Reachable witness of fn-pinv-confirm-record-configures-the-issued-
; invitations-peer: the antecedent and every conjunct of the conclusion.
(assert-event (equal (car (pit-record)) :configure))
(assert-event (equal (car (pit-confirm)) :consume))
(assert-event (fn-cfg-invitation-pendingp (pit-inv-rows) *pit-nonce-hex*))
(assert-event (fn-pinv-kindp (fn-pinv-received-source (pit-inv))
                             *fn-pinv-invitation-kind*))
(assert-event (equal (fn-pinv-hex-string
                      (fn-pinv-source-id (fn-pinv-received-source (pit-inv))))
                     (fn-cfg-row-c (fn-cfg-invitation-row (pit-inv-rows)
                                                          *pit-nonce-hex*))))
(assert-event (fn-cfg-peerp (pit-peer)))
(assert-event (equal (fn-cfg-peer-auth (pit-peer))
                     (list :principal (fn-pinv-hex-string (pit-b)))))
(assert-event (not (fn-cfg-peer-find (fn-cfg-peer-name (pit-peer)) nil)))
(assert-event (equal (fn-pinv-at 1 (pit-record))
                     (list (fn-pinv-at 1 (pit-confirm))
                           (fn-cfg-set-peer-delta (pit-peer)))))
; The peer is the invitation's words and the acceptance's.
(assert-event (equal (pit-peer)
                     (fn-cfg-peer-make "nodeB" "b.example"
                                       '(:nntp 1 "127.0.0.1" 11190 (:clear))
                                       (list "fn.*" *fn-record-max-payload* 16)
                                       nil
                                       (list :principal
                                             (fn-pinv-hex-string (pit-b))))))

; Reachable witness of fn-pinv-confirm-record-fold-consumes-and-configures,
; over the fold from the issued value (pit-v1).
(defmacro pit-next ()
  ' (fn-cfg-apply (pit-v1) 2 nil (fn-pinv-at 1 (pit-record))))
(assert-event (equal (fn-cfg-invitation-row (fn-cfg-invitations (pit-next))
                                            *pit-nonce-hex*)
                     (fn-cfg-row-make *pit-nonce-hex*
                                      (fn-pinv-hex-string (pit-b))
                                      (fn-pinv-hex-string
                                       (fn-pinv-source-id
                                        (fn-pinv-received-source (pit-acc))))
                                      1)))
(assert-event (equal (fn-cfg-rows-with-key (fn-cfg-peers (pit-next)) "nodeB")
                     (fn-cfg-peer-rows (pit-peer))))
(assert-event (equal (fn-cfg-peer-find "nodeB" (fn-cfg-peers (pit-next)))
                     (pit-peer)))
(assert-event (not (fn-pinv-enrolled-withp (pit-b) *pit-b-keys* nil)))
(assert-event (equal (car (fn-pinv-confirm-plan (pit-acc) *pit-b-ml* :verified
                                                :verified
                                                (fn-cfg-invitations (pit-next))
                                                nil))
                     :enrol))
; The record is admissible as one configuration record from the issued value.
(assert-event (fn-cfg-admissiblep (pit-v1) 2 nil 0 0 (fn-pinv-at 1 (pit-record))))

; Hypothesis removal (the one hypothesis, a :configure plan), each keeping
; the rest of the witness and failing the conclusion it guards.
; (1) Another invitation of this node (another nonce) presented with the
; acceptance: refused, and the "invitation this node issued" conjunct fails.
(assert-event (equal (fn-pinv-confirm-record-plan (pit-acc) (pit-inv2)
                                                  *pit-b-ml* :verified
                                                  :verified (pit-inv-rows) nil
                                                  nil)
                     '(:refused :another-invitation)))
(must-fail (assert-event
            (equal (fn-pinv-hex-string
                    (fn-pinv-source-id (fn-pinv-received-source (pit-inv2))))
                   (fn-cfg-row-c (fn-cfg-invitation-row (pit-inv-rows)
                                                        *pit-nonce-hex*)))))
; (2) A peer of that name already configured: refused, and "no configured
; peer has the name" fails.
(defconst *pit-taken*
  (fn-cfg-peer-rows (fn-cfg-peer-make "nodeB" "other.example"
                                      '(:nntp 1 "127.0.0.2" 119 (:clear))
                                      nil nil
                                      '(:source-address "127.0.0.2"))))
(assert-event (equal (fn-pinv-confirm-record-plan (pit-acc) (pit-inv)
                                                  *pit-b-ml* :verified
                                                  :verified (pit-inv-rows) nil
                                                  *pit-taken*)
                     '(:refused :peer-name-taken)))
(must-fail (assert-event (not (fn-cfg-peer-find "nodeB" *pit-taken*))))
; (3) The acceptance presented in the invitation's place: refused by kind.
(assert-event (equal (fn-pinv-confirm-record-plan (pit-acc) (pit-acc)
                                                  *pit-b-ml* :verified
                                                  :verified (pit-inv-rows) nil
                                                  nil)
                     '(:refused :invitation-kind)))
(must-fail (assert-event (fn-pinv-kindp (fn-pinv-received-source (pit-acc))
                                        *fn-pinv-invitation-kind*)))
; (4) The fold's inner hypothesis (the acceptor not yet enrolled): with B
; enrolled, the resumed plan after the record is not an enrolment.
(assert-event (fn-pinv-enrolled-withp (pit-b) *pit-b-keys* (pit-b-snapshots)))
(must-fail (assert-event
            (equal (car (fn-pinv-confirm-plan (pit-acc) *pit-b-ml* :verified
                                              :verified
                                              (fn-cfg-invitations (pit-next))
                                              (pit-b-snapshots)))
                   :enrol)))
; Before the record, the peers table has no nodeB: the fold made it.
(must-fail (assert-event (fn-cfg-peer-find "nodeB" (fn-cfg-peers (pit-v1)))))

; =============================================================================
; PRF-160: the accept configures the inviter from the invitation's address.

(defmacro pit-arec ()
  '(fn-pinv-accept-record-plan (pit-inv) *pit-a-ml* :verified :verified nil nil))
(defmacro pit-inviter-peer ()
  '(fn-pinv-inviter-peer (fn-pinv-received-source (pit-inv)) (pit-a)))

; Reachable witness of fn-pinv-accept-record-configures-the-verified-inviter:
; the antecedent and every conjunct of the conclusion.
(assert-event (equal (car (pit-arec)) :configure))
(assert-event (fn-pinv-bound-document-p (pit-inv) *pit-a-ml* :verified
                                        :verified *fn-pinv-invitation-kind* nil))
(assert-event (not (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* nil)))
(assert-event (fn-pinv-inviter-addressedp (fn-pinv-received-source (pit-inv))))
(assert-event (fn-cfg-peerp (pit-inviter-peer)))
(assert-event (equal (fn-cfg-peer-auth (pit-inviter-peer))
                     (list :principal (fn-pinv-hex-string (pit-a)))))
(assert-event (not (consp (fn-cfg-rows-with-key nil "a.example"))))
(assert-event (equal (fn-pinv-at 1 (pit-arec))
                     (list (fn-cfg-set-peer-delta (pit-inviter-peer)))))
; The peer is the invitation's own words: named by its Inviter-Path, at its
; Inviter-Host and Inviter-Port, taking its Groups, bound to its signer.
(assert-event (equal (pit-inviter-peer)
                     (fn-cfg-peer-make "a.example" "a.example"
                                       '(:nntp 1 "192.0.2.7" 11191 (:clear))
                                       (list "fn.*" *fn-record-max-payload* 16)
                                       nil
                                       (list :principal
                                             (fn-pinv-hex-string (pit-a))))))

; Reachable witness of fn-pinv-accept-record-fold-configures-the-inviter,
; over the fold from the empty value.
(defmacro pit-anext ()
  '(fn-cfg-apply *pit-v0* 1 nil (fn-pinv-at 1 (pit-arec))))
(assert-event (equal (fn-cfg-rows-with-key (fn-cfg-peers (pit-anext)) "a.example")
                     (fn-cfg-peer-rows (pit-inviter-peer))))
(assert-event (equal (fn-cfg-peer-find "a.example" (fn-cfg-peers (pit-anext)))
                     (pit-inviter-peer)))
(assert-event (equal (fn-pinv-accept-record-plan (pit-inv) *pit-a-ml* :verified
                                                 :verified nil
                                                 (fn-cfg-peers (pit-anext)))
                     (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                          :verified nil)))
(assert-event (equal (car (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                               :verified nil))
                     :enrol))
; ... and the resumed step is the enrolment of A.
(assert-event (equal (car (fn-pinv-accept-step 1 2 3 (pit-inv) *pit-a-ml*
                                               :verified :verified nil))
                     :enrol))
(assert-event (fn-cfg-admissiblep *pit-v0* 1 nil 0 0 (fn-pinv-at 1 (pit-arec))))
; The fold made the rows: before it the table has none under the name.
(must-fail (assert-event
            (equal (fn-cfg-rows-with-key (fn-cfg-peers *pit-v0*) "a.example")
                   (fn-cfg-peer-rows (pit-inviter-peer)))))

; Hypothesis removal (the one hypothesis, a :configure plan), each keeping
; the rest of the witness and failing the conclusion it guards.
; (1) An invitation that names no address (`-'): the plan is the accept
; plan (enrol only), and "the invitation names an address" fails.
(assert-event (equal (fn-pinv-accept-record-plan (pit-other-inv) *pit-a-ml*
                                                 :verified :verified nil nil)
                     (fn-pinv-accept-plan (pit-other-inv) *pit-a-ml* :verified
                                          :verified nil)))
(assert-event (equal (car (fn-pinv-accept-plan (pit-other-inv) *pit-a-ml*
                                               :verified :verified nil))
                     :enrol))
(must-fail (assert-event (fn-pinv-inviter-addressedp
                          (fn-pinv-received-source (pit-other-inv)))))
; (2) The inviter already enrolled here (PKT-473): its peer is configured
; all the same (fn-pinv-accept-of-a-current-inviter-configures-it, below);
; with the peer's rows already there (a replay) or no address, refused
; `already-enrolled' before any record.
(assert-event (equal (fn-pinv-accept-record-plan (pit-inv) *pit-a-ml* :verified
                                                 :verified (pit-a-snapshots)
                                                 nil)
                     (list :configure (list (fn-cfg-set-peer-delta (pit-inviter-peer))))))
(assert-event (equal (fn-pinv-accept-record-plan (pit-inv) *pit-a-ml* :verified
                                                 :verified (pit-a-snapshots)
                                                 (fn-cfg-peers (pit-anext)))
                     '(:refused :already-enrolled)))
(assert-event (equal (fn-pinv-accept-record-plan (pit-other-inv) *pit-a-ml* :verified
                                                 :verified (pit-a-snapshots)
                                                 nil)
                     '(:refused :already-enrolled)))
; (3) Another peer record under the name: refused, and "no configured peer
; has the name" fails.
(defconst *pit-a-taken*
  (fn-cfg-peer-rows (fn-cfg-peer-make "a.example" "a.example"
                                      '(:nntp 1 "127.0.0.2" 119 (:clear))
                                      nil nil
                                      '(:source-address "127.0.0.2"))))
(assert-event (equal (fn-pinv-accept-record-plan (pit-inv) *pit-a-ml* :verified
                                                 :verified nil *pit-a-taken*)
                     '(:refused :peer-name-taken)))
(must-fail (assert-event (not (consp (fn-cfg-rows-with-key *pit-a-taken*
                                                           "a.example")))))
; (4) A tampered invitation: refused unverified, and the binding fails.
(assert-event (equal (fn-pinv-accept-record-plan (pit-tampered) *pit-a-ml*
                                                 :verified :refused nil nil)
                     '(:refused :unverified)))
(must-fail (assert-event (fn-pinv-bound-document-p (pit-tampered) *pit-a-ml*
                                                   :verified :refused
                                                   *fn-pinv-invitation-kind* nil)))


; PRF-166 (PKT-325): the `keys redecide' request (kind 12) round-trips its
; Message-ID, and is no other request.
(defconst *pinv-redecide-msgid* (fn-record-string-octets "<s@x.invalid>"))
(assert-event
 (equal (fn-pinv-redecide-request-decode
         (fn-pinv-redecide-request-encode *pinv-redecide-msgid*))
        *pinv-redecide-msgid*))
(assert-event
 (not (fn-pinv-request-decode *fn-pinv-issue-kind*
                              (fn-pinv-redecide-request-encode *pinv-redecide-msgid*))))
(assert-event (equal (fn-pinv-redecide-request-encode nil) :bad))
(assert-event
 (equal (fn-pinv-redecide-request-encode (make-list 251 :initial-element 60)) :bad))

; PKT-221: the login-binding reload (kind 14) decodes as itself and as no
; redecide; a redecide frame is no reload.
(assert-event (fn-pinv-bindings-request-decode (fn-pinv-bindings-request-encode)))
(assert-event
 (not (fn-pinv-redecide-request-decode (fn-pinv-bindings-request-encode))))
(assert-event
 (not (fn-pinv-bindings-request-decode
       (fn-pinv-redecide-request-encode *pinv-redecide-msgid*))))


; -----------------------------------------------------------------------------
; PRF-179 (PKT-211): succession-era documents.  B enrolled at A under its
; genesis keys (generation 1), then succeeded to B2 (generation 2, same
; principal): A's keyring.  B's acceptance signed under B2 names B's
; principal and token, so the genesis rule alone refuses it.
(defconst *pit-b2-ed* (make-list 32 :initial-element 13))
(defconst *pit-b2-ml* (make-list 1952 :initial-element 14))
(defconst *pit-b2-keys* (list (cons :ed25519 *pit-b2-ed*)
                              (cons :ml-dsa-65 *pit-b2-ml*)))
(defmacro pit-g1 () '(fn-hl-enroll-event 1 2 3 1 (pit-b) *pit-b-keys* nil))
(defmacro pit-succ ()
  '(list (fn-hl-enroll-event 4 5 6 2 (pit-b) *pit-b2-keys* (list (pit-g1)))
         (pit-g1)))
(assert-event (fn-stxk-p (car (pit-succ))))
(defmacro pit-acc2 ()
  ' (pit-acceptance (pit-inv) *pit-a-ml* (pit-b) *pit-b-token* *pit-b2-keys*))
(defmacro pit-acc2-source () '(fn-pinv-received-source (pit-acc2)))
(assert-event (consp (pit-acc2)))
(assert-event (equal (fn-pinv-received-principal (pit-acc2)) (pit-b)))
(assert-event (equal (fn-pinv-received-keys (pit-acc2)) *pit-b2-keys*))
; Non-degenerate: B2 is not B's genesis key set.
(assert-event (not (fn-pinv-genesis-okp (pit-acc2-source) (pit-b) *pit-b2-keys*)))

; fn-pinv-document-of-a-current-enrolment-is-accepted: every antecedent,
; then the conclusion.
(assert-event (fn-pinv-verifiedp (pit-acc2) *pit-b2-ml* :verified :verified))
(assert-event (fn-pinv-kindp (pit-acc2-source) *fn-pinv-acceptance-kind*))
(assert-event (fn-pinv-names-keysp (pit-acc2-source) (pit-b) *pit-b2-keys*))
(assert-event (fn-pinv-hex-fieldp (fn-pinv-field "Nonce" (pit-acc2-source)) 32))
(assert-event (fn-pinv-enrolled-withp (pit-b) *pit-b2-keys* (pit-succ)))
(assert-event (equal (fn-pinv-document (pit-acc2) *pit-b2-ml* :verified
                                       :verified *fn-pinv-acceptance-kind*
                                       (pit-succ))
                     (list :ok (pit-acc2-source) (pit-b) *pit-b2-keys*)))
; Without the current enrolment (the keyring before the succession): the
; hypothesis fails, and so does the conclusion: `not-current-keys'.
(assert-event (not (fn-pinv-enrolled-withp (pit-b) *pit-b2-keys*
                                           (list (pit-g1)))))
(assert-event (equal (fn-pinv-document (pit-acc2) *pit-b2-ml* :verified
                                       :verified *fn-pinv-acceptance-kind*
                                       (list (pit-g1)))
                     '(:refused :not-current-keys)))
; Without the verification: the ML-DSA observation refuses.
(assert-event (not (fn-pinv-verifiedp (pit-acc2) *pit-b2-ml* :verified :refused)))
(must-fail (assert-event
            (equal (car (fn-pinv-document (pit-acc2) *pit-b2-ml* :verified
                                          :refused *fn-pinv-acceptance-kind*
                                          (pit-succ)))
                   :ok)))
; Without the kind: the same acceptance asked as an invitation.
(assert-event (not (fn-pinv-kindp (pit-acc2-source) *fn-pinv-invitation-kind*)))
(must-fail (assert-event
            (equal (car (fn-pinv-document (pit-acc2) *pit-b2-ml* :verified
                                          :verified *fn-pinv-invitation-kind*
                                          (pit-succ)))
                   :ok)))
; Without the body naming the carrier's keys: the body names B's genesis
; keys, the carrier is B2's.
(defmacro pit-acc2-claims ()
  '(pit-sign (fn-pinv-acceptance-source *pit-date* (pit-inv) *pit-a-ml*
                                        :verified :verified (pit-b)
                                        *pit-b-token* *pit-b-keys*
                                        (fn-pinv-text "b.example")
                                        (fn-pinv-text "-"))
             (pit-b) *pit-b2-keys*))
(assert-event (fn-pinv-enrolled-withp (fn-pinv-received-principal (pit-acc2-claims))
                                      (fn-pinv-received-keys (pit-acc2-claims))
                                      (pit-succ)))
(assert-event (not (fn-pinv-names-keysp (fn-pinv-received-source (pit-acc2-claims))
                                        (pit-b) *pit-b2-keys*)))
(must-fail (assert-event
            (equal (car (fn-pinv-document (pit-acc2-claims) *pit-b2-ml* :verified
                                          :verified *fn-pinv-acceptance-kind*
                                          (pit-succ)))
                   :ok)))
; Without a 32-octet nonce: an acceptance body built with a 3-octet one.
(defmacro pit-acc2-short-nonce ()
  '(pit-sign (fn-pinv-source "fn-acceptance" (fn-pinv-text "<fn-accept-x@fn-peering.invalid>")
                             *pit-date*
                             (fn-pinv-acceptance-fields
                              (fn-pinv-hex '(1 2 3))
                              (fn-pinv-source-id (pit-inv-source)) (pit-a) (pit-b)
                              *pit-b-token* *pit-b2-keys*
                              (fn-pinv-text "b.example") (fn-pinv-text "-")))
             (pit-b) *pit-b2-keys*))
(assert-event (fn-pinv-names-keysp (fn-pinv-received-source (pit-acc2-short-nonce))
                                   (pit-b) *pit-b2-keys*))
(assert-event (not (fn-pinv-hex-fieldp
                    (fn-pinv-field "Nonce" (fn-pinv-received-source
                                            (pit-acc2-short-nonce)))
                    32)))
(must-fail (assert-event
            (equal (car (fn-pinv-document (pit-acc2-short-nonce) *pit-b2-ml*
                                          :verified :verified
                                          *fn-pinv-acceptance-kind* (pit-succ)))
                   :ok)))

; fn-pinv-document-binds-a-known-principal-only-at-its-current-keys:
; witness above (B known, the document ok, B2 current).  Without "known":
; under an empty keyring B's genesis acceptance passes, and B's genesis keys
; are no current enrolment there.
(assert-event (not (fn-pinv-knownp (pit-b) nil)))
(assert-event (equal (car (fn-pinv-document (pit-acc) *pit-b-ml* :verified
                                            :verified *fn-pinv-acceptance-kind*
                                            nil))
                     :ok))
(must-fail (assert-event (fn-pinv-enrolled-withp (pit-b) *pit-b-keys* nil)))
; Without the document passing: B's superseded genesis keys after the
; succession (B known) are refused, and are not B's current enrolment.
(assert-event (fn-pinv-knownp (pit-b) (pit-succ)))
(assert-event (equal (fn-pinv-document (pit-acc) *pit-b-ml* :verified :verified
                                       *fn-pinv-acceptance-kind* (pit-succ))
                     '(:refused :not-current-keys)))
(must-fail (assert-event (fn-pinv-enrolled-withp (pit-b) *pit-b-keys* (pit-succ))))
; A refusal by name: B revoked (generation 3, a tombstone).
(defmacro pit-revoked ()
  '(cons (fn-hl-revoke-event 7 8 9 3 (pit-b) (pit-succ)) (pit-succ)))
(assert-event (fn-stxk-p (car (pit-revoked))))
(assert-event (equal (fn-pinv-document (pit-acc2) *pit-b2-ml* :verified
                                       :verified *fn-pinv-acceptance-kind*
                                       (pit-revoked))
                     '(:refused :revoked)))

; fn-pinv-document-of-an-unknown-principal-is-the-genesis-decision: B
; unknown to a keyring holding only A: the decision is the empty keyring's.
(assert-event (not (fn-pinv-knownp (pit-b) (pit-a-snapshots))))
(assert-event (equal (fn-pinv-document (pit-acc) *pit-b-ml* :verified :verified
                                       *fn-pinv-acceptance-kind*
                                       (pit-a-snapshots))
                     (fn-pinv-document (pit-acc) *pit-b-ml* :verified :verified
                                       *fn-pinv-acceptance-kind* nil)))
; Without "unknown": B known after the succession decides otherwise.
(must-fail (assert-event
            (equal (fn-pinv-document (pit-acc) *pit-b-ml* :verified :verified
                                     *fn-pinv-acceptance-kind* (pit-succ))
                   (fn-pinv-document (pit-acc) *pit-b-ml* :verified :verified
                                     *fn-pinv-acceptance-kind* nil))))

; fn-pinv-an-enrolling-accept-is-the-clis-plan: B accepts A's invitation
; with a keyring that holds B only (A unknown): the step enrols and the
; plans agree.
(assert-event (equal (car (fn-pinv-accept-step 1 2 3 (pit-inv) *pit-a-ml*
                                               :verified :verified (pit-succ)))
                     :enrol))
(assert-event (equal (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                          :verified nil)
                     (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                          :verified (pit-succ))))
; Without the enrolling step: A known here at a key set it has since
; succeeded (B2's, for the fixture): the plans differ, and the step refuses.
(defmacro pit-a-moved ()
  '(list (fn-hl-enroll-event 4 5 6 2 (pit-a) *pit-b2-keys* (pit-a-snapshots))
         (car (pit-a-snapshots))))
(assert-event (equal (fn-pinv-accept-step 1 2 3 (pit-inv) *pit-a-ml* :verified
                                          :verified (pit-a-moved))
                     '(:refused :not-current-keys)))
(must-fail (assert-event
            (equal (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                        :verified nil)
                   (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                        :verified (pit-a-moved)))))

; The confirm of a current acceptor, end to end over the plans the host
; asks: A's record plan consumes and configures; after the record the step
; answers (:current), enrolling nothing.
(defmacro pit-confirm2 ()
  '(fn-pinv-confirm-plan (pit-acc2) *pit-b2-ml* :verified :verified
                         (pit-inv-rows) (pit-succ)))
(assert-event (equal (car (pit-confirm2)) :consume))
(assert-event (equal (car (fn-pinv-confirm-record-plan
                           (pit-acc2) (pit-inv) *pit-b2-ml* :verified :verified
                           (pit-inv-rows) (pit-succ) nil))
                     :configure))
(defmacro pit-v2s ()
  '(fn-cfg-apply-delta (pit-v1) 2 nil (fn-pinv-at 1 (pit-confirm2))))
(assert-event (null (fn-cfg-delta-reason (pit-v1) 2 nil 0 0
                                         (fn-pinv-at 1 (pit-confirm2)))))
(defmacro pit-step2 ()
  '(fn-pinv-confirm-step 7 8 2 (pit-acc2) *pit-b2-ml* :verified :verified
                         (fn-cfg-invitations (pit-v2s)) (pit-succ)))
; fn-pinv-confirm-of-a-current-acceptor-completes-at-its-consumption:
; antecedents (the plan consumes; B2 current), conclusion (:current).
(assert-event (equal (pit-step2) '(:current)))
; Without "current": the genesis acceptor under the empty keyring enrols.
(must-fail (assert-event (equal (pit-confirm-step) '(:current))))
; Without "consumes": a superseded acceptance's plan is a refusal, and the
; step after it is that refusal.
(defmacro pit-confirm-old ()
  '(fn-pinv-confirm-plan (pit-acc) *pit-b-ml* :verified :verified
                         (pit-inv-rows) (pit-succ)))
(assert-event (equal (pit-confirm-old) '(:refused :not-current-keys)))
(must-fail (assert-event
            (equal (fn-pinv-confirm-step
                    7 8 2 (pit-acc) *pit-b-ml* :verified :verified
                    (fn-cfg-invitations
                     (fn-cfg-apply-delta (pit-v1) 2 nil
                                         (fn-pinv-at 1 (pit-confirm-old))))
                    (pit-succ))
                   '(:current))))

; fn-pinv-confirm-step-current-only-for-the-consuming-current-acceptor: the
; antecedent (:current) and each conclusion at the witness.
(defmacro pit-rows2 () '(fn-cfg-invitations (pit-v2s)))
(defmacro pit-row2 ()
  '(fn-cfg-invitation-row (pit-rows2)
                          (fn-record-octets-string
                           (fn-pinv-field "Nonce" (pit-acc2-source)))))
(assert-event (fn-pinv-bound-document-p (pit-acc2) *pit-b2-ml* :verified
                                        :verified *fn-pinv-acceptance-kind*
                                        (pit-succ)))
(assert-event (consp (pit-row2)))
(assert-event (equal (fn-cfg-row-n (pit-row2)) 1))
(assert-event (equal (fn-cfg-row-b (pit-row2)) (fn-pinv-hex-string (pit-b))))
(assert-event (equal (fn-cfg-row-c (pit-row2))
                     (fn-pinv-hex-string (fn-pinv-source-id (pit-acc2-source)))))
; Without the antecedent: the genesis step enrols, and B's genesis keys are
; no current enrolment in its keyring.
(assert-event (equal (car (pit-confirm-step)) :enrol))
(must-fail (assert-event (fn-pinv-enrolled-withp (pit-b) *pit-b-keys* nil)))

; =============================================================================
; PKT-473 (PRF-184): the accept of an inviter already current here.
;
; fn-pinv-accept-of-a-current-inviter-configures-it.  Reachable witness: B's
; keyring holds A at exactly the invitation's keys (pit-a-snapshots, A's
; enrolment, which is its current one whatever its generation: the rule
; reads only fn-pinv-enrolled-withp); every antecedent, then both
; conclusions.
(assert-event (equal (car (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                               :verified (pit-a-snapshots)))
                     :enrol))
(assert-event (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* (pit-a-snapshots)))
(assert-event (equal (fn-pinv-received-keys (pit-inv)) *pit-a-keys*))
(assert-event (fn-pinv-inviter-addressedp (fn-pinv-received-source (pit-inv))))
(assert-event (fn-cfg-peerp (pit-inviter-peer)))
(assert-event (not (consp (fn-cfg-rows-with-key nil (fn-cfg-peer-name (pit-inviter-peer))))))
(defun pit-current-conclusion (received snapshots peers)
  (and (equal (fn-pinv-accept-record-plan received *pit-a-ml* :verified :verified
                                          snapshots peers)
              (list :configure (list (fn-cfg-set-peer-delta (pit-inviter-peer)))))
       (equal (fn-pinv-accept-step 4 5 3 received *pit-a-ml* :verified :verified
                                   snapshots)
              (list :current))))
(assert-event (pit-current-conclusion (pit-inv) (pit-a-snapshots) nil))
; Each hypothesis dropped, the others kept: A unknown here (the step
; enrols); no address (refused already-enrolled, no record); the name
; taken (peer-name-taken); a tampered invitation (unverified).
(assert-event (not (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* nil)))
(assert-event (not (pit-current-conclusion (pit-inv) nil nil)))
(assert-event (not (fn-pinv-inviter-addressedp (fn-pinv-received-source (pit-other-inv)))))
(assert-event (not (pit-current-conclusion (pit-other-inv) (pit-a-snapshots) nil)))
(assert-event (consp (fn-cfg-rows-with-key *pit-a-taken* "a.example")))
(assert-event (not (pit-current-conclusion (pit-inv) (pit-a-snapshots) *pit-a-taken*)))
(assert-event (not (equal (car (fn-pinv-accept-plan (pit-tampered) *pit-a-ml* :verified
                                                    :refused (pit-a-snapshots)))
                          :enrol)))
(assert-event (not (equal (fn-pinv-accept-step 4 5 3 (pit-tampered) *pit-a-ml* :verified
                                               :refused (pit-a-snapshots))
                          (list :current))))

; fn-pinv-accept-step-current-only-for-a-bound-current-inviter: the witness's
; step is (:current) and both conclusions hold; a keyring where A has moved
; on (pit-a-moved) is refused not-current-keys, never (:current).
(assert-event (fn-pinv-bound-document-p (pit-inv) *pit-a-ml* :verified :verified
                                        *fn-pinv-invitation-kind* (pit-a-snapshots)))
(assert-event (not (equal (fn-pinv-accept-step 1 2 3 (pit-inv) *pit-a-ml* :verified
                                               :verified (pit-a-moved))
                          (list :current))))
(assert-event (not (fn-pinv-enrolled-withp (pit-a) *pit-a-keys* (pit-a-moved))))

; fn-pinv-accept-words-are-the-owners-plan: under the keyring where A is
; current, under the empty keyring, and under B's own keyring, the words
; are the plan; with the hypothesis dropped (a keyring where A has moved on,
; the plan refused) the words are not the plan.
(assert-event (equal (fn-pinv-accept-words (pit-inv) *pit-a-ml* :verified :verified)
                     (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified :verified
                                          (pit-a-snapshots))))
(assert-event (equal (fn-pinv-accept-words (pit-inv) *pit-a-ml* :verified :verified)
                     (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified :verified nil)))
(assert-event (not (equal (car (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified
                                                    :verified (pit-a-moved)))
                          :enrol)))
(assert-event (not (equal (fn-pinv-accept-words (pit-inv) *pit-a-ml* :verified :verified)
                          (fn-pinv-accept-plan (pit-inv) *pit-a-ml* :verified :verified
                                               (pit-a-moved)))))
; The acceptance source is built from those words: under every keyring the
; CLI's source is the same document.
(assert-event (consp (fn-pinv-acceptance-source 1790000000000 (pit-inv) *pit-a-ml*
                                                :verified :verified (pit-b)
                                                *pit-b-token* *pit-b-keys*
                                                (fn-pinv-text "b.example")
                                                (fn-pinv-text "-"))))
