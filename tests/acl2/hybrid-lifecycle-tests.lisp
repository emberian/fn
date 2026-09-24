(in-package "ACL2")
(include-book "../../books/hybrid-lifecycle")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "../../books/codec-attach")

(defconst *hl-a* (make-list 32 :initial-element 1))
(defconst *hl-b* (make-list 32 :initial-element 2))
(defconst *hl-a-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 3))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 4))))
(defconst *hl-a-new-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 5))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 6))))
(defconst *hl-b-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 7))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 8))))

(make-event `(defconst *hl-a1*
               ',(fn-hl-enroll-event 0 0 0 1 *hl-a* *hl-a-keys* nil)))
(make-event `(defconst *hl-b2*
               ',(fn-hl-enroll-event 1 1 1 2 *hl-b* *hl-b-keys*
                                     (list *hl-a1*))))
(make-event `(defconst *hl-a3*
               ',(fn-hl-enroll-event 3 3 3 3 *hl-a* *hl-a-new-keys*
                                     (list *hl-b2* *hl-a1*))))
(make-event `(defconst *hl-a4-revoked*
               ',(fn-hl-revoke-event 4 4 4 4 *hl-a*
                                     (list *hl-a3* *hl-b2* *hl-a1*))))

(assert-equal (fn-stxk-p *hl-a1*) t)
(assert-equal (fn-stxk-p *hl-b2*) t)
(assert-equal (fn-stxk-p *hl-a3*) t)
(assert-equal (fn-stxk-p *hl-a4-revoked*) t)
(assert-equal (fn-stxk-decode-exact (fn-stxk-encode *hl-a4-revoked*))
              (fn-stmt-ok *hl-a4-revoked*))
(assert-equal (fn-stxk-profile *hl-a4-revoked*) *fn-hl-revoked-profile*)
(assert-equal (fn-stxk-snapshot *hl-a4-revoked*) *hl-a*)
(assert-equal (fn-hsig-keyring-snapshot-value *hl-a4-revoked*) nil)
(assert-equal
 (fn-hl-snapshot-principal
  (fn-stxk-make 5 5 5 5 *fn-hl-revoked-profile* '(1)))
 nil)
(assert-equal
 (fn-hl-snapshot-principal
  (fn-stxk-make 5 5 5 5 '(1 2 3) *hl-a*))
 nil)
(assert-equal
 (fn-hl-snapshot-principal
  (fn-stmt-value (fn-stxk-decode-exact (fn-stxk-encode *hl-a1*))))
 *hl-a*)

; Enrolling B does not silently retire A. Rotation and revocation target A
; alone, and old snapshot bytes remain available for historical verdicts.
(assert-equal (fn-hl-current-enrollment 1 (list *hl-b2* *hl-a1*))
              (list *hl-a1* *hl-a* *hl-a-keys*))
(assert-equal (fn-hl-current-enrollment 2 (list *hl-b2* *hl-a1*))
              (list *hl-b2* *hl-b* *hl-b-keys*))
(assert-equal (fn-hl-current-enrollment 1 (list *hl-a3* *hl-b2* *hl-a1*)) nil)
(assert-equal (fn-hl-current-enrollment 3 (list *hl-a3* *hl-b2* *hl-a1*))
              (list *hl-a3* *hl-a* *hl-a-new-keys*))
(assert-equal (fn-hl-current-enrollment 2 (list *hl-a3* *hl-b2* *hl-a1*))
              (list *hl-b2* *hl-b* *hl-b-keys*))
(assert-equal (fn-hl-current-enrollment 3
                                        (list *hl-a4-revoked* *hl-a3*
                                              *hl-b2* *hl-a1*)) nil)
(assert-equal (fn-hl-current-enrollment 2
                                        (list *hl-a4-revoked* *hl-a3*
                                              *hl-b2* *hl-a1*))
              (list *hl-b2* *hl-b* *hl-b-keys*))
(assert-equal
 (fn-hl-history-rows
  (list *hl-a4-revoked* *hl-a3* *hl-b2* *hl-a1*)
  (list *hl-a4-revoked* *hl-a3* *hl-b2* *hl-a1*))
 (list (list 4 :revoked *hl-a*) (list 3 :retired *hl-a*)
       (list 2 :active *hl-b*) (list 1 :retired *hl-a*)))

(assert-equal (fn-hl-enroll-event 5 5 5 3 *hl-b* *hl-b-keys*
                                  (list *hl-a4-revoked* *hl-a3* *hl-b2* *hl-a1*))
              nil)
(assert-equal (fn-hl-revoke-event 5 5 5 5 *hl-a*
                                  (list *hl-a4-revoked* *hl-a3* *hl-b2* *hl-a1*))
              nil)
(assert-equal (fn-hl-revoke-event 5 5 5 5 (make-list 32 :initial-element 9)
                                  (list *hl-a4-revoked* *hl-a3* *hl-b2* *hl-a1*))
              nil)

; The Store identity replay interpreter retains the old verdict and both old
; enrollments across later mutation of A's *current* local authority.
(defconst *hl-old-verdict*
  (fn-stxe-make 2 2 2 "<old-a@example.invalid>" :verified *hl-a* 1
                *fn-hsig-profile-tag*))
(defconst *hl-context-1*
  (fn-stxk-apply-snapshot (fn-stxk-initial-context 0) *hl-a1*))
(defconst *hl-context-2*
  (fn-stxk-apply-snapshot *hl-context-1* *hl-b2*))
(defconst *hl-context-3*
  (fn-stxk-apply-verdict *hl-context-2* *hl-old-verdict*))
(defconst *hl-context-4*
  (fn-stxk-apply-snapshot *hl-context-3* *hl-a3*))
(defconst *hl-context-5*
  (fn-stxk-apply-snapshot *hl-context-4* *hl-a4-revoked*))
(assert-equal (fn-stxk-context-kind *hl-context-5*) :ok)
(assert-equal (fn-stxk-context-verdicts *hl-context-5*)
              (fn-stxk-context-verdicts *hl-context-3*))
(assert-equal (fn-stxk-find 1 (fn-stxk-context-snapshots *hl-context-5*))
              *hl-a1*)
