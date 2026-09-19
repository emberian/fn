; General invariants for authorized logical retention release.  Evidence is
; already authenticated/committed input; no disk or cryptographic claim follows.
;
; The retention recognizers and transitions are opened locally; nothing here
; opens a record.  The export theory keeps the three keystones.
(in-package "ACL2")
(include-book "retention")

(local (in-theory (enable fn-retain-obligationp fn-retain-releasep
                          fn-retain-statep fn-retain-initial-state
                          fn-retain-admissiblep fn-retain-admit
                          fn-retain-release)))

(defthm fn-retain-release-find-is-obligation
  (implies (and (fn-retain-obligation-listp pins)
                (consp (fn-retain-find-id id pins)))
           (fn-retain-obligationp (fn-retain-find-id id pins))))

(defthm fn-retain-release-find-id-is-member
  (implies (consp (fn-retain-find-id id pins))
           (member-equal id (fn-retain-obligation-ids pins))))

(defthm fn-retain-release-remove-preserves-obligations
  (implies (fn-retain-obligation-listp pins)
           (fn-retain-obligation-listp (fn-retain-remove-id id pins))))

(defthm fn-retain-release-sum-is-natural
  (implies (fn-retain-obligation-listp pins)
           (natp (fn-retain-sum pins))))

(defthm fn-retain-release-remove-sum
  (implies (and (fn-retain-obligation-listp pins)
                (consp (fn-retain-find-id id pins)))
           (equal (fn-retain-sum (fn-retain-remove-id id pins))
                  (- (fn-retain-sum pins)
                     (fn-retain-obligation-charge (fn-retain-find-id id pins)))))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-retain-release-remove-id-members
  (implies (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
           (iff (member-equal other (fn-retain-obligation-ids
                                    (fn-retain-remove-id id pins)))
                (and (not (equal other id))
                     (member-equal other (fn-retain-obligation-ids pins)))))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-retain-release-remove-preserves-unique-ids
  (implies (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
           (fn-retain-no-duplicatesp
            (fn-retain-obligation-ids (fn-retain-remove-id id pins))))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-retain-release-disjoint-member
  (implies (and (not (intersection-equal xs ys))
                (member-equal x xs))
           (not (member-equal x ys))))

(defthm fn-retain-release-remove-preserves-disjointness
  (implies (and (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
                (not (intersection-equal (fn-retain-obligation-ids pins) history)))
           (not (intersection-equal
                 (fn-retain-obligation-ids (fn-retain-remove-id id pins))
                 (cons id history))))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-retain-release-sum-nonnegative
  (implies (fn-retain-obligation-listp pins)
           (<= 0 (fn-retain-sum pins)))
  :rule-classes :linear
  :hints (("Goal" :use fn-retain-release-sum-is-natural)))

(defthm fn-retain-release-charge-bounded-by-sum
  (implies (and (fn-retain-obligation-listp pins)
                (consp (fn-retain-find-id id pins)))
           (<= (fn-retain-obligation-charge (fn-retain-find-id id pins))
               (fn-retain-sum pins)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-retain-find-id id pins))))

(defthm fn-retain-release-preserves-statep
  (implies (fn-retain-statep s)
           (fn-retain-statep (fn-retain-release s id subject kind evidence)))
  :hints (("Goal"
           :use ((:instance fn-retain-release-charge-bounded-by-sum
                  (pins (fn-retain-pins s)))
                 (:instance fn-retain-release-find-is-obligation
                  (pins (fn-retain-pins s)))
                 (:instance fn-retain-release-sum-is-natural
                  (pins (fn-retain-remove-id id (fn-retain-pins s))))))))

; Releasing one obligation cannot discharge a distinct archive/forward pin,
; even when both pins protect the same immutable content subject.
(defthm fn-retain-release-remove-keeps-other-pin
  (implies (not (equal other id))
           (equal (fn-retain-find-id other (fn-retain-remove-id id pins))
                  (fn-retain-find-id other pins)))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-retain-release-preserves-independent-pin
  (implies (not (equal other id))
           (equal (fn-retain-find-id
                   other (fn-retain-pins (fn-retain-release s id subject kind evidence)))
                  (fn-retain-find-id other (fn-retain-pins s))))
  :hints (("Goal" :in-theory (disable fn-retain-statep fn-retain-find-id
                                      fn-retain-remove-id))))

; Once an identity is known it stays known, including when it moves from an
; active pin into permanent release history.  Admission therefore cannot reuse
; it after successful release.
(defthm fn-retain-release-remove-keeps-other-members
  (implies (and (not (equal other id))
                (member-equal other (fn-retain-obligation-ids pins)))
           (member-equal other
                         (fn-retain-obligation-ids (fn-retain-remove-id id pins))))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-retain-release-preserves-known-identity
  (implies (fn-retain-known-idp known-id (fn-retain-pins s)
                                        (fn-retain-releases s))
           (fn-retain-known-idp
            known-id (fn-retain-pins (fn-retain-release s id subject kind evidence))
            (fn-retain-releases (fn-retain-release s id subject kind evidence))))
  :hints (("Goal" :in-theory (disable fn-retain-statep fn-retain-find-id
                                      fn-retain-remove-id))))

; -----------------------------------------------------------------------------
; Export.  Keystones stay enabled: `fn-retain-release-preserves-statep',
; `fn-retain-release-preserves-independent-pin' and
; `fn-retain-release-preserves-known-identity'.  The remove/find/sum lemmas
; are proof vocabulary and are withdrawn.
(deftheory fn-retention-invariants-vocabulary
  '(fn-retain-release-find-is-obligation
    fn-retain-release-find-id-is-member
    fn-retain-release-remove-preserves-obligations
    fn-retain-release-sum-is-natural
    fn-retain-release-remove-sum
    fn-retain-release-remove-id-members
    fn-retain-release-remove-preserves-unique-ids
    fn-retain-release-disjoint-member
    fn-retain-release-remove-preserves-disjointness
    fn-retain-release-sum-nonnegative
    fn-retain-release-charge-bounded-by-sum
    fn-retain-release-remove-keeps-other-pin
    fn-retain-release-remove-keeps-other-members))
(in-theory (disable fn-retention-invariants-vocabulary))
