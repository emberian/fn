; Witnesses and teeth for books/policy.lisp: authority confinement with a
; forged policy, an unauthorized principal, a stale policy, an equivocating
; authority, and receipts that commit to the policy term.
(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/policy-invariants")

(defconst *fn-t-seed-alice* (make-list 32 :initial-element 1))
(defconst *fn-t-seed-bob* (make-list 32 :initial-element 2))
(defconst *fn-t-seed-mallory* (make-list 32 :initial-element 9))
(defconst *fn-t-seed-relay* (make-list 32 :initial-element 12))
(defconst *fn-t-token* (fn-record-string-octets "default"))
(defconst *fn-t-group* (fn-record-string-octets "fn.test"))
(defconst *fn-t-terms* (fn-record-string-octets "archive-until-release"))
(defconst *fn-t-obligation* (fn-record-string-octets "archive:fn.test:1"))

(defun fn-t-alice () (fn-prin-id (fn-sig-public-key *fn-t-seed-alice*) *fn-t-token*))
(defun fn-t-bob () (fn-prin-id (fn-sig-public-key *fn-t-seed-bob*) *fn-t-token*))
(defun fn-t-mallory () (fn-prin-id (fn-sig-public-key *fn-t-seed-mallory*) *fn-t-token*))
(defun fn-t-relay () (fn-prin-id (fn-sig-public-key *fn-t-seed-relay*) *fn-t-token*))

(defun fn-t-keyring ()
  (fn-prin-keyring-of-states
   (list (fn-prin-genesis-state (fn-sig-public-key *fn-t-seed-alice*) *fn-t-token* 1)
         (fn-prin-genesis-state (fn-sig-public-key *fn-t-seed-bob*) *fn-t-token* 1)
         (fn-prin-genesis-state (fn-sig-public-key *fn-t-seed-mallory*) *fn-t-token* 1)
         (fn-prin-genesis-state (fn-sig-public-key *fn-t-seed-relay*) *fn-t-token* 1))))
(assert-event (fn-prin-keyringp (fn-t-keyring)))

; -----------------------------------------------------------------------------
; Policy payload codec

(defun fn-t-policy-1 () (fn-pol-make-policy *fn-t-group* (list (fn-t-bob)) *fn-t-terms*))
(assert-event (fn-pol-policy-p (fn-t-policy-1)))
(assert-event (equal (fn-pol-policy-decode-exact (fn-pol-policy-encode (fn-t-policy-1)))
                     (fn-stmt-ok (fn-t-policy-1))))
(assert-event (equal (fn-pol-policy-decode-exact
                      (append (fn-pol-policy-encode (fn-t-policy-1)) '(0)))
                     (fn-stmt-error :trailing)))
(assert-event (not (fn-pol-policy-p
                    (fn-pol-make-policy *fn-t-group* (list (fn-t-bob) (fn-t-bob))
                                        *fn-t-terms*))))
(assert-event (equal (fn-pol-policy-decode-exact
                      (fn-stmt-encode-items
                       (list (cons :bytes *fn-t-group*) '(:uint . 2)
                             (cons :bytes (fn-t-bob)) (cons :bytes (fn-t-bob))
                             (cons :bytes *fn-t-terms*))))
                     (fn-stmt-error :duplicate-member)))
(assert-event (equal (fn-pol-policy-decode-exact
                      (fn-stmt-encode-items
                       (list (cons :bytes *fn-t-group*) '(:uint . 65))))
                     (fn-stmt-error :member-count)))
(assert-event (equal (fn-pol-policy-decode-exact
                      (fn-stmt-encode-items (list (cons :bytes nil))))
                     (fn-stmt-error :group)))

; -----------------------------------------------------------------------------
; The policy in force and admission

(defun fn-t-p1 ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 1 nil :policy
                (fn-pol-policy-encode (fn-t-policy-1))))
(defun fn-t-lace-1 () (list (fn-t-p1)))

(assert-event (fn-pol-candidatep (fn-t-p1) (fn-t-keyring) *fn-t-group* (fn-t-alice)))
(assert-event (equal (fn-pol-current (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice))
                     (fn-t-p1)))
(assert-event (equal (fn-pol-authorized-set (fn-t-p1)) (list (fn-t-alice) (fn-t-bob))))
(assert-event (fn-pol-authorizedp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-bob) :post))
(assert-event (fn-pol-authorizedp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-alice) :post))
(assert-event (not (fn-pol-authorizedp (fn-t-lace-1) (fn-t-keyring) *fn-t-group*
                                       (fn-t-alice) (fn-t-mallory) :post)))
(assert-event (fn-pol-authorizedp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-alice) :policy))
(assert-event (not (fn-pol-authorizedp (fn-t-lace-1) (fn-t-keyring) *fn-t-group*
                                       (fn-t-alice) (fn-t-bob) :policy)))
; no policy in force for another group or another authority
(assert-event (equal (fn-pol-current (fn-t-lace-1) (fn-t-keyring)
                                     (fn-record-string-octets "fn.other") (fn-t-alice))
                     nil))
(assert-event (equal (fn-pol-current (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-bob))
                     nil))

(defun fn-t-bob-post ()
  (fn-stmt-sign *fn-t-seed-bob* (fn-t-bob) 1 1 nil :article
                (fn-record-string-octets "a post by bob")))
(defun fn-t-mallory-post ()
  (fn-stmt-sign *fn-t-seed-mallory* (fn-t-mallory) 1 1 nil :article
                (fn-record-string-octets "a post by mallory")))
; bob's creator id under mallory's key: the forged post
(defun fn-t-forged-bob-post ()
  (fn-stmt-sign *fn-t-seed-mallory* (fn-t-bob) 1 1 nil :article
                (fn-record-string-octets "a post by bob?")))

(assert-event (fn-pol-admitp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                             (fn-t-bob-post)))
; teeth: unauthorized principal; forged signature; wrong kind; empty lace
(assert-event (not (fn-pol-admitp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-mallory-post))))
(assert-event (not (fn-pol-admitp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-forged-bob-post))))
(assert-event (not (fn-prin-verifiedp (fn-t-forged-bob-post) (fn-t-keyring))))
(assert-event (not (fn-pol-admitp (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-p1))))
(assert-event (not (fn-pol-admitp nil (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-bob-post))))

; -----------------------------------------------------------------------------
; Authority confinement under hostile deltas

; A forged policy: alice's id, mallory's key, mallory as member.
(defun fn-t-forged-policy ()
  (fn-stmt-sign *fn-t-seed-mallory* (fn-t-alice) 1 2 nil :policy
                (fn-pol-policy-encode
                 (fn-pol-make-policy *fn-t-group* (list (fn-t-mallory)) *fn-t-terms*))))
; Mallory's own honest policy for the same group, signed by mallory.
(defun fn-t-mallory-policy ()
  (fn-stmt-sign *fn-t-seed-mallory* (fn-t-mallory) 1 2 nil :policy
                (fn-pol-policy-encode
                 (fn-pol-make-policy *fn-t-group* (list (fn-t-mallory)) *fn-t-terms*))))
(defun fn-t-hostile-delta ()
  (list (fn-t-forged-policy) (fn-t-mallory-policy) (fn-t-mallory-post)
        (fn-t-forged-bob-post)))

(assert-event (fn-pol-delta-without-authority-p (fn-t-hostile-delta) (fn-t-keyring)
                                                (fn-t-alice)))
(assert-event (not (fn-pol-candidatep (fn-t-forged-policy) (fn-t-keyring) *fn-t-group*
                                      (fn-t-alice))))
(assert-event (not (fn-pol-candidatep (fn-t-mallory-policy) (fn-t-keyring) *fn-t-group*
                                      (fn-t-alice))))
(defun fn-t-lace-2 () (fn-lace-merge (fn-t-lace-1) (fn-t-hostile-delta)))
(assert-event (equal (len (fn-t-lace-2)) 5))
(assert-event (equal (fn-pol-current (fn-t-lace-2) (fn-t-keyring) *fn-t-group* (fn-t-alice))
                     (fn-t-p1)))
(assert-event (not (fn-pol-admitp (fn-t-lace-2) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-mallory-post))))
(assert-event (fn-pol-admitp (fn-t-lace-2) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                             (fn-t-bob-post)))
; Mallory IS the authority of her own namespace for the group; that does not
; touch alice's.
(assert-event (equal (fn-pol-current (fn-t-lace-2) (fn-t-keyring) *fn-t-group*
                                     (fn-t-mallory))
                     (fn-t-mallory-policy)))

; tooth for the foreign-delta hypothesis: a genuine alice policy DOES change
; the policy in force (and supersedes P1: the stale tooth).
(defun fn-t-p2 ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 2 (list (fn-stmt-id (fn-t-p1)))
                :policy (fn-pol-policy-encode
                         (fn-pol-make-policy *fn-t-group* nil *fn-t-terms*))))
(assert-event (not (fn-pol-delta-without-authority-p (list (fn-t-p2)) (fn-t-keyring)
                                                     (fn-t-alice))))
(assert-event (equal (fn-pol-first-authority-stmt (list (fn-t-forged-policy) (fn-t-p2))
                                                  (fn-t-keyring) (fn-t-alice))
                     (fn-t-p2)))
(defun fn-t-lace-3 () (fn-lace-merge (fn-t-lace-2) (list (fn-t-p2))))
(assert-event (equal (fn-pol-current (fn-t-lace-3) (fn-t-keyring) *fn-t-group* (fn-t-alice))
                     (fn-t-p2)))
(assert-event (fn-pol-slot-lessp (fn-t-p1) (fn-t-p2)))
(assert-event (not (fn-pol-admitp (fn-t-lace-3) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-bob-post))))
; order of arrival does not matter
(assert-event (equal (fn-pol-current (fn-lace-merge (list (fn-t-p2)) (fn-t-lace-2))
                                     (fn-t-keyring) *fn-t-group* (fn-t-alice))
                     (fn-t-p2)))

; An equivocating authority: alice restored from a snapshot reissues slot
; (1, 2) with a different member list.  No policy is in force; both are kept.
(defun fn-t-p2-fork ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 2 (list (fn-stmt-id (fn-t-p1)))
                :policy (fn-pol-policy-encode
                         (fn-pol-make-policy *fn-t-group* (list (fn-t-bob) (fn-t-mallory))
                                             *fn-t-terms*))))
(defun fn-t-lace-4 () (fn-lace-merge (fn-t-lace-3) (list (fn-t-p2-fork))))
(assert-event (equal (len (fn-t-lace-4)) 7))
(assert-event (fn-lace-equivocatorp (fn-t-lace-4) (fn-t-alice) 1))
(assert-event (equal (fn-pol-current (fn-t-lace-4) (fn-t-keyring) *fn-t-group* (fn-t-alice))
                     nil))
(assert-event (not (fn-pol-admitp (fn-t-lace-4) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-bob-post))))
(assert-event (not (fn-pol-admitp (fn-t-lace-4) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-mallory-post))))
; A later unforked policy resolves it.
(defun fn-t-p3 ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 3
                (list (fn-stmt-id (fn-t-p2)) (fn-stmt-id (fn-t-p2-fork)))
                :policy (fn-pol-policy-encode (fn-t-policy-1))))
(assert-event (equal (fn-pol-current (fn-lace-merge (fn-t-lace-4) (list (fn-t-p3)))
                                     (fn-t-keyring) *fn-t-group* (fn-t-alice))
                     (fn-t-p3)))

; -----------------------------------------------------------------------------
; Receipts commit to the policy term

(defun fn-t-receipt ()
  (fn-pol-make-receipt (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                       (fn-t-bob-post) *fn-t-obligation*))
(assert-event (fn-stmt-receipt-p (fn-t-receipt)))
(assert-event (equal (fn-stmt-receipt-policy-id (fn-t-receipt)) (fn-stmt-id (fn-t-p1))))
(assert-event (equal (fn-stmt-receipt-subject (fn-t-receipt)) (fn-stmt-id (fn-t-bob-post))))
(assert-event (equal (fn-stmt-receipt-term (fn-t-receipt))
                     (fn-pol-term (fn-t-lace-1) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                                  (fn-t-bob-post))))
(assert-event (equal (fn-stmt-receipt-evidence (fn-t-receipt))
                     (fn-digest-tagged *fn-pol-evidence-tag*
                                       (fn-pol-evidence (fn-t-keyring) (fn-t-alice)
                                                        (fn-t-bob-post)))))
; No receipt for what is not admitted.
(assert-event (equal (fn-pol-make-receipt (fn-t-lace-1) (fn-t-keyring) *fn-t-group*
                                          (fn-t-alice) (fn-t-mallory-post)
                                          *fn-t-obligation*)
                     nil))
; The term is re-resolvable, and still names P1 after P1 is superseded:
; the receipt says WHICH policy authorized it, not that it is current now.
(assert-event (fn-pol-receipt-groundedp (fn-t-receipt) (fn-t-lace-1) (fn-t-keyring)
                                        *fn-t-group* (fn-t-alice)))
(assert-event (fn-pol-receipt-groundedp (fn-t-receipt) (fn-t-lace-3) (fn-t-keyring)
                                        *fn-t-group* (fn-t-alice)))
(assert-event (equal (fn-lace-lookup (fn-t-lace-3) (fn-stmt-receipt-policy-id (fn-t-receipt)))
                     (fn-t-p1)))
(assert-event (not (equal (fn-stmt-receipt-policy-id (fn-t-receipt))
                          (fn-stmt-id (fn-t-p2)))))
; teeth: a receipt naming a policy the lace does not hold is not grounded;
; a receipt naming mallory's policy is not grounded for alice's authority.
(assert-event (not (fn-pol-receipt-groundedp (fn-t-receipt) nil (fn-t-keyring)
                                             *fn-t-group* (fn-t-alice))))
(assert-event (not (fn-pol-receipt-groundedp
                    (fn-stmt-make-receipt (fn-stmt-id (fn-t-bob-post)) *fn-t-obligation*
                                          (fn-stmt-id (fn-t-mallory-policy))
                                          (fn-stmt-receipt-evidence (fn-t-receipt)))
                    (fn-t-lace-2) (fn-t-keyring) *fn-t-group* (fn-t-alice))))
; The evidence digest changes when the evidence (here the keyring) changes.
(assert-event (not (equal (fn-pol-evidence-digest (fn-t-keyring) (fn-t-alice) (fn-t-bob-post))
                          (fn-pol-evidence-digest (cdr (fn-t-keyring)) (fn-t-alice)
                                                  (fn-t-bob-post)))))

; The receipt travels as a signed statement by the relay.
(defun fn-t-receipt-stmt ()
  (fn-pol-sign-receipt *fn-t-seed-relay* (fn-t-relay) 1 1
                       (list (fn-stmt-id (fn-t-bob-post))) (fn-t-receipt)))
(assert-event (fn-prin-verifiedp (fn-t-receipt-stmt) (fn-t-keyring)))
(assert-event (equal (fn-stmt-receipt-decode-exact (fn-stmt-payload (fn-t-receipt-stmt)))
                     (fn-stmt-ok (fn-t-receipt))))
(assert-event (equal (fn-stmt-receipt-term
                      (fn-stmt-value
                       (fn-stmt-receipt-decode-exact (fn-stmt-payload (fn-t-receipt-stmt)))))
                     (fn-stmt-receipt-term (fn-t-receipt))))

; tooth for fn-pol-receipt-re-verifiable's canonicity hypothesis: under a
; colliding digest an article by alice shares the policy's id, sits first in
; the lace, and the receipt's policy id resolves to the article.  Under this
; realiser every principal id collides too, so alice posts to her own group;
; the keyring resolves the shared id to her key.
(defattach fn-digest fn-toy-length-digest)
(defun fn-t-alice-article ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 3 nil :article
                (fn-record-string-octets "not a policy")))
(defun fn-t-p1-c ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 1 nil :policy
                (fn-pol-policy-encode (fn-t-policy-1))))
(defun fn-t-alice-post-c ()
  (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice) 1 5 nil :article
                (fn-record-string-octets "a post")))
(assert-event (equal (fn-stmt-id (fn-t-alice-article)) (fn-stmt-id (fn-t-p1-c))))
(defun fn-t-lace-c () (list (fn-t-alice-article) (fn-t-p1-c)))
(assert-event (not (fn-lace-canonicalp (fn-t-lace-c))))
(assert-event (fn-pol-admitp (fn-t-lace-c) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                             (fn-t-alice-post-c)))
(defun fn-t-receipt-c ()
  (fn-pol-make-receipt (fn-t-lace-c) (fn-t-keyring) *fn-t-group* (fn-t-alice)
                       (fn-t-alice-post-c) *fn-t-obligation*))
(assert-event (fn-stmt-receipt-p (fn-t-receipt-c)))
(assert-event (equal (fn-lace-lookup (fn-t-lace-c) (fn-stmt-receipt-policy-id (fn-t-receipt-c)))
                     (fn-t-alice-article)))
(assert-event (not (fn-pol-receipt-groundedp (fn-t-receipt-c) (fn-t-lace-c) (fn-t-keyring)
                                             *fn-t-group* (fn-t-alice))))
(defattach fn-digest fn-toy-mix-digest)
