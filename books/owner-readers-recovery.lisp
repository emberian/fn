; Recovery RESETS reader views and cache on valid install (refusal leaves them); reclaim preserves them.
(in-package "ACL2")
(include-book "owner-readers-state")
(include-book "owner-recovery-retain")

(local
 (defthm fn-ordr-recovery-writers-frame
   (and
    (equal (fn-ost-readers (fn-owner-authority-proposal-clear state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-owner-canonical-reset state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-owner-install-open-ocfg oc state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-owner-install-ocfg oc state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-owner-retain-carry-put r state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-ost-install-publication r state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-orc-writer-enter state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-orc-writer-leave state)) (fn-ost-readers state))
    (equal (fn-ost-readers (fn-owner-put-credits r state)) (fn-ost-readers state)))
   :hints (("Goal" :in-theory
            (e/d (fn-ost-install-authority fn-owner-authority-proposal-clear fn-owner-canonical-reset
                  fn-owner-install-open-ocfg fn-owner-install-ocfg fn-owner-retain-carry-put
                  fn-ost-install-publication fn-orc-writer-enter fn-orc-writer-leave fn-owner-put-credits)
                 (fn-ost-readers put-global))))))

(defthm fn-owner-install-extended-resets-readers
  (equal (fn-ost-readers
          (mv-nth 5 (fn-owner-install-extended
                     oc extended key fn-arena fn-cat fn-hist state)))
         (if (or (equal oc :fault) (not (fn-onb-open-okp (fn-ocfg-owner oc))))
             (fn-ost-readers state)
           (fn-ordr-initial)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended fn-ordr-recovery-writers-frame
              fn-ost-readers-of-other-global-put fn-ost-readers-of-install
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory)))))

(defthm fn-owner-orcp-swap-preserves-readers
  (equal (fn-ost-readers (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-ost-readers state))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-ordr-recovery-writers-frame
              fn-ost-readers-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

