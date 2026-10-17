; Recovery and reclaim preserve the authority fields, including on refusal.
(in-package "ACL2")
(include-book "owner-authority-state")
(include-book "owner-recovery-retain")

(local
 (defthm fn-oauth-recovery-writers-frame
   (and
    (equal (fn-ost-authority (fn-owner-authority-proposal-clear state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-owner-install-open-ocfg oc state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-owner-install-ocfg oc state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-owner-retain-carry-put r state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-ost-install-publication r state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-orc-writer-enter state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-orc-writer-leave state)) (fn-ost-authority state))
    (equal (fn-ost-authority (fn-owner-put-credits r state)) (fn-ost-authority state)))
   :hints (("Goal" :in-theory
            (e/d (fn-ost-install-authority fn-owner-authority-proposal-clear fn-owner-canonical-reset
                  fn-owner-install-open-ocfg fn-owner-install-ocfg fn-owner-retain-carry-put
                  fn-ost-install-publication fn-orc-writer-enter fn-orc-writer-leave fn-owner-put-credits)
                 (fn-ost-authority put-global))))))

(defthm fn-owner-install-extended-preserves-authority
  (equal (fn-ost-authority
          (mv-nth 5 (fn-owner-install-extended
                     oc extended key fn-arena fn-cat fn-hist state)))
         (fn-ost-authority state))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended fn-oauth-recovery-writers-frame
              fn-ost-authority-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-owner-orcp-swap-authority-effect
  (equal (fn-ost-authority (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-oauth-put :canonical nil (fn-ost-authority state)))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-oauth-recovery-writers-frame
              fn-owner-canonical-reset-authority-effect
              fn-ost-authority-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

