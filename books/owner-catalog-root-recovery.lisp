; The actual recovery and reclaim installers preserve allocation identity.
(in-package "ACL2")
(include-book "owner-catalog-root-state")
(include-book "owner-recovery-retain")

; Keep recovery proofs about state effects; store rebuilding is an opaque value.
(local
 (defthm fn-ocr-recovery-writers-frame
   (and
    (equal (fn-ost-catalog-root (fn-owner-authority-proposal-clear state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-owner-canonical-reset state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-owner-install-open-ocfg oc state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-owner-install-ocfg oc state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-owner-retain-carry-put r state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-ost-install-publication r state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-orc-writer-enter state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-orc-writer-leave state)) (fn-ost-catalog-root state))
    (equal (fn-ost-catalog-root (fn-owner-put-credits r state)) (fn-ost-catalog-root state)))
   :hints (("Goal" :in-theory
            (e/d (fn-ost-install-authority fn-owner-authority-proposal-clear fn-owner-canonical-reset
                  fn-owner-install-open-ocfg fn-owner-install-ocfg fn-owner-retain-carry-put
                  fn-ost-install-publication fn-orc-writer-enter fn-orc-writer-leave fn-owner-put-credits)
                 (fn-ost-catalog-root put-global))))))

(defthm fn-owner-install-extended-preserves-catalog-root
  (equal (fn-ost-catalog-root
          (mv-nth 5 (fn-owner-install-extended
                     oc extended key fn-arena fn-cat fn-hist state)))
         (fn-ost-catalog-root state))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended fn-ocr-recovery-writers-frame
              fn-ost-catalog-root-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-owner-orcp-swap-preserves-catalog-root
  (equal (fn-ost-catalog-root (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-ost-catalog-root state))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-ocr-recovery-writers-frame
              fn-ost-catalog-root-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory))))
  :rule-classes nil)

(local
 (defthm fn-opub-recovery-writers-frame
   (and
    (equal (fn-ost-publication (fn-owner-authority-proposal-clear state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-owner-canonical-reset state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-owner-install-open-ocfg oc state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-owner-install-ocfg oc state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-owner-retain-carry-put r state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-orc-writer-enter state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-orc-writer-leave state)) (fn-ost-publication state))
    (equal (fn-ost-publication (fn-owner-put-credits r state)) (fn-ost-publication state)))
   :hints (("Goal" :in-theory
            (e/d (fn-ost-install-authority fn-owner-authority-proposal-clear fn-owner-canonical-reset
                  fn-owner-install-open-ocfg fn-owner-install-ocfg fn-owner-retain-carry-put
                  fn-ost-install-publication fn-orc-writer-enter fn-orc-writer-leave fn-owner-put-credits)
                 (fn-ost-publication put-global))))))

; Effects of the actual host-called installers on the publication family.
(defthm fn-owner-install-extended-publication-effect
  (equal (fn-ost-publication
          (mv-nth 5 (fn-owner-install-extended
                     oc extended key fn-arena fn-cat fn-hist state)))
         (if (or (equal oc :fault) (not (fn-onb-open-okp (fn-ocfg-owner oc))))
             (fn-ost-publication state)
           (fn-opub-install (fn-ost-publication state) (fn-scka-strip-base extended))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended fn-opub-recovery-writers-frame
              fn-ost-publication-of-other-global-put fn-ost-publication-of-install
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory)))))

(defthm fn-owner-orcp-swap-publication-effect
  (equal (fn-ost-publication (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-opub-reclaim-install (fn-ost-publication state)
                                 (fn-scka-strip-base (nth 0 rebuilt))
                                 (mv-nth 1 (fn-owner-orcp-swap rebuilt state))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-opub-recovery-writers-frame
              fn-ost-publication-of-other-global-put fn-ost-publication-of-install
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))
            (theory 'minimal-theory)))))
