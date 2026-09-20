; fn: group policy on inbound transit -- the gate, and authority confinement.
;
; specs/substrate-transport.md section 3, keystone S4-1 (packet S4).
;
; The gate on a peer-transit article is fn-pol-admitp evaluated against THIS
; node's lace and THIS node's keyring.  A peer cannot widen a group's policy:
; a contact batch carrying no statement by the group's authority verified
; under the local keyring leaves the policy in force EQUAL before and after,
; so no admission and no authorization decision changes.  When it does
; change, fn-stx-batch-policy-change-needs-authority-signature names the
; statement that did it, so "which transit article changed our policy" always
; has a signed answer.

(in-package "ACL2")
(include-book "stx-lace")
(include-book "policy-invariants")

(local (in-theory (enable fn-pol-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The gate

(defun fn-stx-transit-authority-ok (node article keyring group authority)
  (declare (xargs :guard (and (fn-article-syntax-p article)
                              (fn-prin-keyringp keyring))))
  (and (fn-stx-verifiedp article keyring)
       (fn-pol-admitp (fn-stx-lace node keyring) keyring group authority
                      (fn-stx-statement-of article))
       t))

; Named honestly (assurance rule "cite keystones, never corollaries"): the
; equation below is the unfolding of the definition, and it is here so that
; the policy keystones can be read as being about the gate.  The substantive
; theorem-subject obligation -- that the function the HOST calls on the
; transit path is this one -- is fn-stx-transit-gate-is-the-gate in
; books/stx-transit.lisp, which names fn-peer-transfer.
(defthm fn-stx-transit-admit-is-fn-pol-admitp-by-definition
  (implies (fn-stx-verifiedp article keyring)
           (equal (fn-stx-transit-authority-ok node article keyring group
                                               authority)
                  (if (fn-pol-admitp (fn-stx-lace node keyring) keyring group
                                     authority (fn-stx-statement-of article))
                      t
                    nil))))

; Also by definition, and also named so: fn-pol-admitp takes a lace, a
; keyring, a group, an authority and a statement.  The peer is not among
; them, and no function of the peer appears in the gate's support.
(defthm fn-stx-admission-is-peer-independent-by-definition
  (equal (fn-stx-transit-authority-ok node article keyring group authority)
         (and (fn-stx-verifiedp article keyring)
              (fn-pol-admitp (fn-stx-lace node keyring) keyring group authority
                             (fn-stx-statement-of article))
              t)))

(in-theory (disable (:d fn-stx-transit-authority-ok)))

; The spine at the authority layer: an article whose statement does not
; verify under the local keyring is stored and served, and admits nothing.
(defthm fn-stx-unverified-transit-admits-nothing
  (implies (not (fn-stx-verifiedp article keyring))
           (not (fn-stx-transit-authority-ok node article keyring group
                                             authority)))
  :hints (("Goal" :in-theory (enable (:d fn-stx-transit-authority-ok)))))

; Corollary of fn-pol-admission-is-grounded: a gate that opens names the
; policy statement in this node's own lace that opened it.
(defthm fn-stx-transit-admission-is-grounded
  (implies (fn-stx-transit-authority-ok node article keyring group authority)
           (let ((p (fn-pol-current (fn-stx-lace node keyring) keyring group
                                    authority))
                 (s (fn-stx-statement-of article)))
             (and (member-equal p (fn-stx-lace node keyring))
                  (equal (fn-stmt-creator p) authority)
                  (equal (fn-stmt-kind p) :policy)
                  (fn-prin-verifiedp p keyring)
                  (member-equal (fn-stmt-creator s) (fn-pol-authorized-set p))
                  (fn-prin-verifiedp s keyring)
                  (equal (fn-stmt-kind s) :article))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pol-admission-is-grounded
                            (lace (fn-stx-lace node keyring))
                            (s (fn-stx-statement-of article))))
           :in-theory (e/d ((:d fn-stx-transit-authority-ok))
                           (fn-pol-admission-is-grounded fn-pol-admitp
                            fn-pol-current fn-pol-authorized-set
                            fn-stx-lace fn-stx-statement-of)))))

; -----------------------------------------------------------------------------
; A contact batch, as the store grows under it
;
; `batch` is the list of article records the peer's contact contributed, in
; offer order.  Accepting them conses each in turn onto the newest-first
; store, so the lace grows by appending each delta in offer order.

(defun fn-stx-accept-batch (store batch)
  (declare (xargs :guard t))
  (if (consp batch)
      (fn-stx-accept-batch (cons (car batch) store) (cdr batch))
    store))

(defun fn-stx-batch-delta (batch keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp batch)
      (append (fn-stx-delta (fn-article-payload (car batch)) keyring)
              (fn-stx-batch-delta (cdr batch) keyring))
    nil))

(defthm fn-stx-batch-delta-is-lace
  (fn-lace-p (fn-stx-batch-delta batch keyring)))

(defthm fn-stx-batch-delta-is-true-list
  (true-listp (fn-stx-batch-delta batch keyring)))

(defthm fn-stx-lace-of-accept-batch
  (equal (fn-stx-lace-of-store (fn-stx-accept-batch store batch) keyring)
         (append (fn-stx-lace-of-store store keyring)
                 (fn-stx-batch-delta batch keyring)))
  :hints (("Goal" :induct (fn-stx-accept-batch store batch)
           :in-theory (disable fn-stx-delta))))

; -----------------------------------------------------------------------------
; Authority confinement, over the batch

(local (defthm fn-stx-pol-candidates-of-append-foreign
         (implies (fn-pol-delta-without-authority-p delta keyring authority)
                  (equal (fn-pol-candidates (append lace delta) keyring group
                                            authority)
                         (fn-pol-candidates lace keyring group authority)))
         :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-pol-candidates-of-append
                                   (a lace) (b delta))
                        (:instance fn-pol-candidates-of-foreign-delta)
                        (:instance fn-pol-candidates-is-true-list
                                   (lace lace)))
                  :in-theory (disable fn-pol-candidates
                                      fn-pol-candidates-of-append
                                      fn-pol-candidates-of-foreign-delta
                                      fn-pol-candidates-is-true-list)))))

(defthm fn-stx-pol-current-of-append-foreign
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-current (append lace delta) keyring group authority)
                  (fn-pol-current lace keyring group authority)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pol-current)
                           (fn-pol-candidates fn-pol-latest
                            fn-pol-same-slot-conflictp)))))

(defthm fn-stx-pol-authorizedp-of-append-foreign
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-authorizedp (append lace delta) keyring group
                                      authority principal action)
                  (fn-pol-authorizedp lace keyring group authority principal
                                      action)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pol-authorizedp)
                           (fn-pol-current fn-pol-authorized-set)))))

(defthm fn-stx-pol-admitp-of-append-foreign
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-admitp (append lace delta) keyring group authority s)
                  (fn-pol-admitp lace keyring group authority s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pol-admitp)
                           (fn-pol-current fn-pol-authorizedp)))))

; S4-1, second row.  Corollary of fn-pol-current-unchanged-by-foreign-delta,
; restated over the batch's lace delta; the new work is
; fn-stx-lace-of-accept-batch above and the append form of the three
; confinement lemmas.
(defthm fn-stx-peer-batch-cannot-change-policy
  (implies (fn-pol-delta-without-authority-p (fn-stx-batch-delta batch keyring)
                                             keyring authority)
           (equal (fn-pol-current
                   (fn-stx-lace-of-store (fn-stx-accept-batch store batch)
                                         keyring)
                   keyring group authority)
                  (fn-pol-current (fn-stx-lace-of-store store keyring)
                                  keyring group authority)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pol-current fn-stx-batch-delta
                               fn-stx-accept-batch fn-stx-lace-of-store))))

(defthm fn-stx-peer-batch-cannot-change-admission
  (implies (fn-pol-delta-without-authority-p (fn-stx-batch-delta batch keyring)
                                             keyring authority)
           (equal (fn-pol-admitp
                   (fn-stx-lace-of-store (fn-stx-accept-batch store batch)
                                         keyring)
                   keyring group authority s)
                  (fn-pol-admitp (fn-stx-lace-of-store store keyring)
                                 keyring group authority s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pol-admitp fn-stx-batch-delta
                               fn-stx-accept-batch fn-stx-lace-of-store))))

; The constructive contrapositive: the operator's question "which transit
; article changed our policy" has an answer, and it is a signed one.
(defthm fn-stx-batch-policy-change-needs-authority-signature
  (implies (not (equal (fn-pol-current
                        (fn-stx-lace-of-store (fn-stx-accept-batch store batch)
                                              keyring)
                        keyring group authority)
                       (fn-pol-current (fn-stx-lace-of-store store keyring)
                                       keyring group authority)))
           (let ((d (fn-pol-first-authority-stmt
                     (fn-stx-batch-delta batch keyring) keyring authority)))
             (and (member-equal d (fn-stx-batch-delta batch keyring))
                  (fn-stmt-p d)
                  (equal (fn-stmt-creator d) authority)
                  (fn-prin-verifiedp d keyring))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-peer-batch-cannot-change-policy)
                 (:instance fn-pol-first-authority-stmt-when-not-foreign
                            (delta (fn-stx-batch-delta batch keyring))))
           :in-theory (disable fn-stx-peer-batch-cannot-change-policy
                               fn-pol-first-authority-stmt-when-not-foreign
                               fn-pol-current fn-pol-first-authority-stmt
                               fn-pol-delta-without-authority-p
                               fn-stx-batch-delta fn-stx-accept-batch
                               fn-stx-lace-of-store))))

; -----------------------------------------------------------------------------
; Policy statements propagate as statements: nothing is pushed, nothing is
; applied, nothing is executed.  A :policy statement carried by a verified
; transit article is an ordinary member of the receiver's lace, and
; fn-pol-current recomputes over it.

(defthm fn-stx-policy-statement-propagates
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring)
                 (fn-stx-delta (fn-article-payload article) keyring))
                (equal (list s) (fn-stx-delta (fn-article-payload article)
                                              keyring))
                (fn-pol-candidatep s keyring group authority))
           (member-equal s (fn-pol-candidates (fn-stx-lace next keyring)
                                              keyring group authority)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-lace-of-accept-is-merge)
                 (:instance fn-stx-merge-of-fresh-short-delta
                            (lace (fn-stx-lace node keyring))
                            (delta (fn-stx-delta (fn-article-payload article)
                                                 keyring)))
                 (:instance fn-pol-member-candidate-is-in-candidates
                            (lace (append (fn-stx-lace node keyring)
                                          (list s)))))
           :in-theory (disable fn-stx-lace-of-accept-is-merge
                               fn-stx-merge-of-fresh-short-delta
                               fn-pol-member-candidate-is-in-candidates
                               fn-pol-candidates fn-pol-candidatep
                               fn-stx-lace fn-stx-acceptedp fn-stx-delta
                               fn-stx-delta-freshp fn-lace-merge))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(in-theory (disable (:d fn-stx-accept-batch) (:d fn-stx-batch-delta)))
