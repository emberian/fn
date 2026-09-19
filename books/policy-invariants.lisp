; Authority confinement and policy-term invariants for books/policy.lisp.
;
; Keystones:
;   fn-pol-current-unchanged-by-foreign-delta
;     merging any statements that are not verified statements by the
;     authority leaves the policy in force unchanged; hence
;   fn-pol-admitp-unchanged-by-foreign-delta
;     such statements cannot admit a cross-post either.  Both are conditional
;     on fn-sig-verify through fn-prin-verifiedp, and on the keyring.
;   fn-pol-policy-change-needs-authority-signature
;     if the policy in force changes, the delta holds a verified statement by
;     the authority (the constructive contrapositive).
;   fn-pol-admission-is-grounded
;     an admitted post is authorized by a verified policy statement that is a
;     member of the lace and names its creator.
;   fn-pol-current-is-not-superseded
;     a candidate with a later slot in the lace means an earlier one is not in
;     force (the stale-policy tooth).
;   fn-pol-receipt-re-verifiable
;     in a canonical lace the receipt's policy id resolves to the policy that
;     authorized it (uses fn-lace-lookup-of-member).
;   fn-pol-signed-receipt-carries-term
;     a receipt statement's payload decodes to the receipt, so the term
;     travels with the signed bytes.

(in-package "ACL2")
(include-book "policy")
(include-book "lace-invariants")
(include-book "principal-invariants")

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals
                          fn-stmt-invariants-vocabulary
                          fn-prin-internals
                          fn-lace-internals
                          fn-pol-internals)))

(local (in-theory (disable fn-stmt-id fn-stmt-p fn-stmt-creator
                           fn-stmt-incarnation fn-stmt-sequence fn-stmt-kind
                           fn-stmt-payload fn-prin-verifiedp
                           fn-pol-statement-policy fn-stmt-sign
                           fn-stmt-encode fn-digest-tagged fn-prin-key-for
                           fn-lace-lookup fn-pol-candidatep
                           fn-pol-evidence-digest fn-pol-evidence)))

; -----------------------------------------------------------------------------
; Statement shape facts used below

(defthm fn-pol-stmt-is-consp
  (implies (fn-stmt-p s) (consp s))
  :hints (("Goal" :in-theory (enable fn-stmt-p))))

(defthm fn-pol-candidatep-implies-authority-stmt
  (implies (fn-pol-candidatep s keyring group authority)
           (and (fn-stmt-p s)
                (equal (fn-stmt-creator s) authority)
                (equal (fn-stmt-kind s) :policy)
                (fn-prin-verifiedp s keyring)))
  :hints (("Goal" :in-theory (enable fn-pol-candidatep))))

; -----------------------------------------------------------------------------
; Candidates under append and merge

(defthm fn-pol-candidates-is-true-list
  (true-listp (fn-pol-candidates lace keyring group authority)))

(defthm fn-pol-candidates-of-append
  (equal (fn-pol-candidates (append a b) keyring group authority)
         (append (fn-pol-candidates a keyring group authority)
                 (fn-pol-candidates b keyring group authority))))

(defthm fn-pol-candidates-of-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-candidates delta keyring group authority) nil))
  :hints (("Goal" :in-theory (enable fn-pol-candidatep))))

(defthm fn-pol-delta-without-authority-p-of-new
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (fn-pol-delta-without-authority-p (fn-lace-new lace delta)
                                              keyring authority)))

(defthm fn-pol-candidates-of-merge-with-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-candidates (fn-lace-merge lace delta)
                                     keyring group authority)
                  (fn-pol-candidates lace keyring group authority)))
  :hints (("Goal" :in-theory (disable fn-lace-new fn-pol-candidates))))

; -----------------------------------------------------------------------------
; Authority confinement

(defthm fn-pol-current-unchanged-by-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-current (fn-lace-merge lace delta)
                                  keyring group authority)
                  (fn-pol-current lace keyring group authority)))
  :hints (("Goal" :in-theory (e/d (fn-pol-current)
                                  (fn-lace-merge fn-pol-candidates
                                   fn-pol-latest
                                   fn-pol-same-slot-conflictp)))))

(defthm fn-pol-authorizedp-unchanged-by-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-authorizedp (fn-lace-merge lace delta)
                                      keyring group authority principal action)
                  (fn-pol-authorizedp lace keyring group authority
                                      principal action)))
  :hints (("Goal" :in-theory (disable fn-lace-merge fn-pol-current
                                      fn-pol-authorized-set))))

(defthm fn-pol-admitp-unchanged-by-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-admitp (fn-lace-merge lace delta)
                                 keyring group authority s)
                  (fn-pol-admitp lace keyring group authority s)))
  :hints (("Goal" :in-theory (disable fn-lace-merge fn-pol-current
                                      fn-pol-authorizedp))))

; The constructive contrapositive: the first verified authority statement
; in the delta.
(defun fn-pol-first-authority-stmt (delta keyring authority)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp delta)
      (if (and (fn-stmt-p (car delta))
               (equal (fn-stmt-creator (car delta)) authority)
               (fn-prin-verifiedp (car delta) keyring))
          (car delta)
        (fn-pol-first-authority-stmt (cdr delta) keyring authority))
    nil))

(defthm fn-pol-first-authority-stmt-when-not-foreign
  (implies (not (fn-pol-delta-without-authority-p delta keyring authority))
           (and (member-equal (fn-pol-first-authority-stmt delta keyring authority)
                              delta)
                (fn-stmt-p (fn-pol-first-authority-stmt delta keyring authority))
                (equal (fn-stmt-creator
                        (fn-pol-first-authority-stmt delta keyring authority))
                       authority)
                (fn-prin-verifiedp
                 (fn-pol-first-authority-stmt delta keyring authority)
                 keyring))))

(defthm fn-pol-policy-change-needs-authority-signature
  (implies (not (equal (fn-pol-current (fn-lace-merge lace delta)
                                       keyring group authority)
                       (fn-pol-current lace keyring group authority)))
           (let ((d (fn-pol-first-authority-stmt delta keyring authority)))
             (and (member-equal d delta)
                  (fn-stmt-p d)
                  (equal (fn-stmt-creator d) authority)
                  (fn-prin-verifiedp d keyring))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pol-current-unchanged-by-foreign-delta)
                 (:instance fn-pol-first-authority-stmt-when-not-foreign))
           :in-theory (disable fn-lace-merge fn-pol-current
                               fn-pol-first-authority-stmt
                               fn-pol-delta-without-authority-p
                               fn-pol-current-unchanged-by-foreign-delta
                               fn-pol-first-authority-stmt-when-not-foreign))))

; -----------------------------------------------------------------------------
; Grounding

(defthm fn-pol-candidates-members-are-candidates
  (implies (member-equal p (fn-pol-candidates lace keyring group authority))
           (and (member-equal p lace)
                (fn-pol-candidatep p keyring group authority))))

(defthm fn-pol-member-candidate-is-in-candidates
  (implies (and (member-equal p lace)
                (fn-pol-candidatep p keyring group authority))
           (member-equal p (fn-pol-candidates lace keyring group authority))))

(defthm fn-pol-current-is-candidate-in-lace
  (implies (fn-pol-current lace keyring group authority)
           (and (member-equal (fn-pol-current lace keyring group authority) lace)
                (fn-pol-candidatep (fn-pol-current lace keyring group authority)
                                   keyring group authority)))
  :hints (("Goal"
           :use ((:instance fn-pol-latest-is-member-or-nil
                            (cands (fn-pol-candidates lace keyring group
                                                      authority)))
                 (:instance fn-pol-candidates-members-are-candidates
                            (p (fn-pol-latest
                                (fn-pol-candidates lace keyring group
                                                   authority)))))
           :in-theory (e/d (fn-pol-current)
                           (fn-pol-latest fn-pol-candidates
                            fn-pol-same-slot-conflictp
                            fn-pol-latest-is-member-or-nil
                            fn-pol-candidates-members-are-candidates)))))

(defthm fn-pol-admission-is-grounded
  (implies (fn-pol-admitp lace keyring group authority s)
           (let ((p (fn-pol-current lace keyring group authority)))
             (and (member-equal p lace)
                  (fn-pol-candidatep p keyring group authority)
                  (equal (fn-stmt-creator p) authority)
                  (equal (fn-stmt-kind p) :policy)
                  (fn-prin-verifiedp p keyring)
                  (member-equal (fn-stmt-creator s) (fn-pol-authorized-set p))
                  (fn-prin-verifiedp s keyring)
                  (equal (fn-stmt-kind s) :article)
                  (fn-stmt-p s))))
  :hints (("Goal"
           :use ((:instance fn-pol-current-is-candidate-in-lace)
                 (:instance fn-pol-candidatep-implies-authority-stmt
                            (s (fn-pol-current lace keyring group authority))))
           :in-theory (disable fn-pol-current fn-pol-authorized-set
                               fn-pol-current-is-candidate-in-lace
                               fn-pol-candidatep-implies-authority-stmt))))

; -----------------------------------------------------------------------------
; Staleness

; fn-pol-slot-lessp is a strict total order on the nfixed (incarnation,
; sequence) keys.  These four order facts are everything the maximality
; induction needs, so the comparison stays closed there and the induction
; never splits over the nfix terms (opening it on every branch was a 94 x 90
; subgoal explosion).

(defthm fn-pol-slot-lessp-irreflexive
  (not (fn-pol-slot-lessp a a)))

(defthm fn-pol-slot-lessp-asymmetric
  (implies (fn-pol-slot-lessp b a)
           (not (fn-pol-slot-lessp a b))))

(defthm fn-pol-slot-lessp-negative-transitive
  (implies (and (not (fn-pol-slot-lessp a b))
                (not (fn-pol-slot-lessp b c)))
           (not (fn-pol-slot-lessp a c)))
  :rule-classes ((:rewrite :match-free :all)))

; An atom sits at key (0, 0); nothing is below it, so anything not above it
; is at (0, 0) too.  (fn-pol-latest returns an atom member only when every
; member is at that key; fn-lace-p is deliberately not assumed.)
(defthm fn-pol-slot-lessp-below-atom
  (implies (and (not (consp b))
                (not (fn-pol-slot-lessp b c)))
           (not (fn-pol-slot-lessp a c)))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (enable fn-stmt-incarnation fn-stmt-sequence))))

(defthm fn-pol-latest-is-maximal
  (implies (member-equal c cands)
           (not (fn-pol-slot-lessp (fn-pol-latest cands) c)))
  :hints (("Goal" :induct (fn-pol-latest cands)
           :in-theory (disable fn-pol-slot-lessp))))

(defthm fn-pol-current-is-not-superseded
  (implies (and (member-equal p1 lace)
                (fn-pol-candidatep p1 keyring group authority)
                (member-equal p2 lace)
                (fn-pol-candidatep p2 keyring group authority)
                (fn-pol-slot-lessp p1 p2))
           (not (equal (fn-pol-current lace keyring group authority) p1)))
  :hints (("Goal"
           :use ((:instance fn-pol-latest-is-maximal
                            (cands (fn-pol-candidates lace keyring group
                                                      authority))
                            (c p2))
                 (:instance fn-pol-member-candidate-is-in-candidates (p p2))
                 (:instance fn-pol-candidatep-implies-authority-stmt (s p1)))
           :in-theory (e/d (fn-pol-current)
                           (fn-pol-latest fn-pol-candidates
                            fn-pol-same-slot-conflictp fn-pol-slot-lessp
                            fn-pol-latest-is-maximal
                            fn-pol-member-candidate-is-in-candidates
                            fn-pol-candidatep-implies-authority-stmt)))))

; -----------------------------------------------------------------------------
; Refusals that hold by definition; named as such.  The executable teeth for
; forged and unauthorized statements are in tests/acl2/policy-tests.lisp.

(defthm fn-pol-unverified-is-not-candidate-by-definition
  (implies (not (fn-prin-verifiedp s keyring))
           (not (fn-pol-candidatep s keyring group authority)))
  :hints (("Goal" :in-theory (enable fn-pol-candidatep))))

(defthm fn-pol-unverified-is-not-admitted-by-definition
  (implies (not (fn-prin-verifiedp s keyring))
           (not (fn-pol-admitp lace keyring group authority s))))

(defthm fn-pol-no-policy-in-force-admits-nothing-by-definition
  (implies (not (fn-pol-current lace keyring group authority))
           (not (fn-pol-admitp lace keyring group authority s)))
  :hints (("Goal" :in-theory (disable fn-pol-current))))

; -----------------------------------------------------------------------------
; The policy term and receipts

(defthm fn-pol-receipt-commits-to-term-by-construction
  (implies (fn-pol-admitp lace keyring group authority s)
           (let ((r (fn-pol-make-receipt lace keyring group authority s
                                         obligation)))
             (and (equal (fn-stmt-receipt-term r)
                         (fn-pol-term lace keyring group authority s))
                  (equal (fn-stmt-receipt-policy-id r)
                         (fn-stmt-id (fn-pol-current lace keyring group
                                                     authority)))
                  (equal (fn-stmt-receipt-evidence r)
                         (fn-pol-evidence-digest keyring authority s))
                  (equal (fn-stmt-receipt-subject r) (fn-stmt-id s))
                  (equal (fn-stmt-receipt-obligation r) obligation))))
  :hints (("Goal" :in-theory (disable fn-pol-current fn-pol-authorizedp))))

(defthm fn-pol-stmt-id-is-digest
  (fn-digest-octetsp (fn-stmt-id s))
  :hints (("Goal" :in-theory (enable fn-stmt-id fn-stmt-content-id
                                      fn-digest-tagged))))

(defthm fn-pol-evidence-digest-is-digest
  (fn-digest-octetsp (fn-pol-evidence-digest keyring authority s))
  :hints (("Goal" :in-theory (enable fn-pol-evidence-digest fn-digest-tagged))))

(defthm fn-pol-receipt-is-receipt
  (implies (and (fn-pol-admitp lace keyring group authority s)
                (fn-stmt-obligationp obligation))
           (fn-stmt-receipt-p
            (fn-pol-make-receipt lace keyring group authority s obligation)))
  :hints (("Goal" :in-theory (disable fn-pol-current fn-pol-authorizedp
                                      fn-digest-octetsp))))

(defthm fn-pol-receipt-re-verifiable
  (implies (and (fn-lace-p lace)
                (fn-lace-canonicalp lace)
                (fn-pol-admitp lace keyring group authority s))
           (let ((r (fn-pol-make-receipt lace keyring group authority s
                                         obligation)))
             (and (equal (fn-lace-lookup lace (fn-stmt-receipt-policy-id r))
                         (fn-pol-current lace keyring group authority))
                  (fn-pol-receipt-groundedp r lace keyring group authority))))
  :hints (("Goal"
           :use ((:instance fn-pol-current-is-candidate-in-lace)
                 (:instance fn-lace-lookup-of-member
                            (s (fn-pol-current lace keyring group authority))))
           :in-theory (disable fn-pol-current fn-pol-authorizedp
                               fn-lace-canonicalp
                               fn-pol-current-is-candidate-in-lace
                               fn-lace-lookup-of-member))))

; The kind travels in the header; fn-lace-sign-fields covers the other
; fields.  Proved on the constructors alone, with the signing preimage and
; the payload ref closed, so no codec opens.
(defthm fn-pol-sign-kind
  (equal (fn-stmt-kind (fn-stmt-sign sk c i n preds k p)) k)
  :hints (("Goal" :in-theory (e/d (fn-stmt-sign fn-stmt-kind fn-stmt-header)
                                  (fn-stmt-payload-ref
                                   fn-stmt-signing-preimage)))))

; The codec stays opaque: the payload of the signed statement is the receipt
; encoding by fn-lace-sign-fields, and fn-stmt-receipt-round-trip decodes it.
(defthm fn-pol-signed-receipt-carries-term
  (implies (fn-stmt-receipt-p receipt)
           (and (equal (fn-stmt-receipt-decode-exact
                        (fn-stmt-payload
                         (fn-pol-sign-receipt sk receiver incarnation sequence
                                              preds receipt)))
                       (fn-stmt-ok receipt))
                (equal (fn-stmt-kind
                        (fn-pol-sign-receipt sk receiver incarnation sequence
                                             preds receipt))
                       :receipt)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lace-sign-fields
                            (c receiver) (i incarnation) (n sequence)
                            (k :receipt)
                            (p (fn-stmt-receipt-encode receipt)))
                 (:instance fn-pol-sign-kind
                            (c receiver) (i incarnation) (n sequence)
                            (k :receipt)
                            (p (fn-stmt-receipt-encode receipt)))
                 (:instance fn-stmt-receipt-round-trip (r receipt)))
           :in-theory (disable fn-lace-sign-fields fn-pol-sign-kind
                               fn-stmt-receipt-round-trip
                               fn-stmt-receipt-encode
                               fn-stmt-receipt-decode-exact
                               fn-stmt-receipt-p fn-stmt-sign fn-stmt-kind
                               fn-stmt-payload fn-stmt-header fn-stmt-ok
                               fn-stmt-okp fn-stmt-value))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The keystones below stay enabled on include; everything else this book
; proves is proof vocabulary and is withdrawn under `fn-pol-invariants-vocabulary',
; which a book inside this cluster enables locally in one line.
;
; * fn-pol-current-unchanged-by-foreign-delta
; * fn-pol-authorizedp-unchanged-by-foreign-delta
; * fn-pol-admitp-unchanged-by-foreign-delta
; * fn-pol-policy-change-needs-authority-signature
; * fn-pol-latest-is-maximal
; * fn-pol-current-is-not-superseded
; * fn-pol-admission-is-grounded
; * fn-pol-receipt-commits-to-term-by-construction
; * fn-pol-receipt-re-verifiable
; * fn-pol-signed-receipt-carries-term
; * fn-pol-current-is-candidate-in-lace

(deftheory fn-pol-invariants-vocabulary
  '(
    fn-pol-stmt-is-consp
    fn-pol-candidatep-implies-authority-stmt
    fn-pol-candidates-is-true-list
    fn-pol-candidates-of-append
    fn-pol-candidates-of-foreign-delta
    fn-pol-delta-without-authority-p-of-new
    fn-pol-candidates-of-merge-with-foreign-delta
    fn-pol-first-authority-stmt-when-not-foreign
    fn-pol-candidates-members-are-candidates
    fn-pol-member-candidate-is-in-candidates
    fn-pol-slot-lessp-irreflexive
    fn-pol-slot-lessp-asymmetric
    fn-pol-slot-lessp-negative-transitive
    fn-pol-slot-lessp-below-atom
    fn-pol-unverified-is-not-candidate-by-definition
    fn-pol-unverified-is-not-admitted-by-definition
    fn-pol-no-policy-in-force-admits-nothing-by-definition
    fn-pol-stmt-id-is-digest
    fn-pol-evidence-digest-is-digest
    fn-pol-receipt-is-receipt
    fn-pol-sign-kind
    (:d fn-pol-first-authority-stmt)))

(in-theory (disable fn-pol-invariants-vocabulary))
