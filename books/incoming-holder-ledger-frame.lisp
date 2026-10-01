; Counter-only frame required by the status-aware shared-pool commit.
; These source facts do not authorize JOINED/ALIASES-CLEAR observations.
(in-package "ACL2")
(include-book "incoming-octet-holder")
(include-book "incoming-buffer-carrier")

(defthm fn-ioh-admit-preserves-actual-binding-root
 (equal (fn-prl-nth 3 (mv-nth 2 (fn-ioh-admit ledger slot demand)))
        (fn-prl-nth 3 ledger))
 :hints (("Goal" :in-theory
          (e/d (fn-ioh-admit fn-prl-build fn-prl-nth)
               (fn-prs-issue fn-prs-vectorp fn-prl-baseline))))
 :rule-classes nil)

(defthm fn-ioh-release-preserves-actual-binding-root
 (equal (fn-prl-nth 3
          (mv-nth 1 (fn-ioh-release ledger slot token joined aliases-clear)))
        (fn-prl-nth 3 ledger))
 :hints (("Goal" :in-theory
          (e/d (fn-ioh-release fn-prl-build fn-prl-nth)
               (fn-ioh-matches fn-prs-release-reusable))))
 :rule-classes nil)

; Uses the existing SAME-pool C->U helper, not a parallel promotion rule.
(defthm fn-ibc-publish-backing-preserves-actual-binding-root
 (equal (fn-prl-nth 3
          (mv-nth 1 (fn-ibc-publish-backing ledger carrier token outcome)))
        (fn-prl-nth 3 ledger))
 :hints (("Goal" :in-theory
          (e/d (fn-ibc-publish-backing fn-iqr-promoted-ledger
                fn-prl-build fn-prl-nth)
               (fn-ioh-matches fn-prs-vectorp fn-prs-below
                fn-prs-release-reusable fn-prs-plus fn-prl-baseline))))
 :rule-classes nil)
