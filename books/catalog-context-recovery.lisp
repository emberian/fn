; The live snapshot carry supplies the catalog's recovery-context premise.
; This is proof vocabulary; no served entry evaluates the history predicates.
(in-package "ACL2")
(include-book "catalog-commit")
(include-book "owner-snapshot-recovery")

(defthm fn-osr-ready-establishes-catalog-recovery-context
  (implies (and (fn-osr-retainedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (fn-snh-recovery-context-coherentp s))
  :hints (("Goal"
           :use fn-osr-ready-identity-exact-view
           :in-theory
           (e/d (fn-osr-retainedp fn-osr-livep fn-sti-livep
                 fn-skp-resolvedp fn-snh-recovery-context-coherentp
                 fn-osr-context-view fn-sn-identity-context)
                (fn-osr-ready-identity-exact-view fn-osr-identity-prefixp
                 fn-csi-livep fn-cst-relation fn-sn-files fn-sf-phase
                 fn-sn-keyring fn-sn-keyring-generation fn-sn-keyring-snapshots
                 fn-sn-identity-next fn-replay-identity fn-sf-records
                 fn-ssk-keyring-of-snapshots fn-ssk-generation)))))
