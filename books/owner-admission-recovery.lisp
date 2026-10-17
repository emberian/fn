; Recovery and reclaim preserve the launch-time opt-in, including on refusal.
(in-package "ACL2")
(include-book "owner-admission-state")
(include-book "owner-recovery-retain")

(local
 (defthm fn-oadm-recovery-writers-frame
   (and
    (equal (fn-ost-admission (fn-owner-authority-proposal-clear state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-owner-canonical-reset state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-owner-install-open-ocfg oc state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-owner-install-ocfg oc state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-owner-retain-carry-put r state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-ost-install-publication r state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-orc-writer-enter state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-orc-writer-leave state)) (fn-ost-admission state))
    (equal (fn-ost-admission (fn-owner-put-credits r state)) (fn-ost-admission state)))
   :hints (("Goal" :in-theory
            (e/d (fn-ost-install-authority fn-owner-authority-proposal-clear fn-owner-canonical-reset
                  fn-owner-install-open-ocfg fn-owner-install-ocfg fn-owner-retain-carry-put
                  fn-ost-install-publication fn-orc-writer-enter fn-orc-writer-leave fn-owner-put-credits)
                 (fn-ost-admission put-global))))))

(defthm fn-owner-install-extended-preserves-admission
  (equal (fn-ost-admission
          (mv-nth 5 (fn-owner-install-extended
                     oc extended key fn-arena fn-cat fn-hist state)))
         (fn-ost-admission state))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended fn-oadm-recovery-writers-frame
              fn-ost-admission-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-owner-orcp-swap-preserves-admission
  (equal (fn-ost-admission (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-ost-admission state))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-oadm-recovery-writers-frame
              fn-ost-admission-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

; The actual request selector consumes this observation without a new policy.
(defthm fn-oadm-configured-request-composition-by-definition
  (equal (fn-orcp-request-word mode
                              (fn-oadm-reclaim-live (fn-oadm-configure-reclaim live)) word)
         (fn-orcp-request-word mode (and live t) word)))
