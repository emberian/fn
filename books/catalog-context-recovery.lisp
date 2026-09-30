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

; At ready, every admissible process-death choice observes the same durable
; records.  The crash discards live projections but retains their context.
(local
 (defthm fn-ccr-ready-crash-keeps-durable-records
   (implies (equal (fn-sf-phase files) :ready)
            (equal (fn-sf-records (fn-sf-crash files fc rc))
                   (fn-sf-records files)))
   :hints (("Goal"
            :in-theory
            (e/d (fn-sf-crash fn-sf-frontier-new-visiblep
                  fn-sf-record-present-visiblep)
                 (fn-sf-statep fn-sf-crash-choicep fn-sf-make
                  fn-sf-phase fn-sf-records fn-sf-frontier
                  fn-sf-frontier-candidate fn-sf-record-candidate
                  fn-sf-successes))))))

(local
 (defthm fn-ccr-ready-crash-keeps-coherent-context
   (implies (and (fn-snh-recovery-context-coherentp s)
                 (equal (fn-sf-phase (fn-sn-files s)) :ready))
            (and (fn-snh-recovery-context-coherentp (fn-sn-crash s fc rc))
                 (equal (fn-sn-keyring (fn-sn-crash s fc rc))
                        (fn-sn-keyring s))
                 (equal (fn-sn-keyring-generation (fn-sn-crash s fc rc))
                        (fn-sn-keyring-generation s))))
   :hints (("Goal"
            :in-theory
            (e/d (fn-sn-crash fn-sn-update-indexed
                  fn-snh-recovery-context-coherentp)
                 (fn-sn-statep fn-sf-crash-choicep fn-sf-crash
                  fn-sn-with-topic fn-sn-with-consumer fn-sn-with-event-index
                  fn-sn-make-v6 fn-sn-keyring fn-sn-keyring-generation
                  fn-sn-keyring-snapshots fn-sn-files fn-sf-phase fn-sf-records
                  fn-replay-identity fn-stxk-context-snapshots
                  fn-ssk-keyring-of-snapshots fn-ssk-generation))))))

(defthm fn-osr-ready-crash-recovery-keeps-catalog-context
  (implies (and (fn-osr-retainedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (and (fn-snh-recovery-context-coherentp (fn-sn-crash s fc rc))
                (equal (fn-sn-keyring (fn-sn-recover (fn-sn-crash s fc rc)))
                       (fn-sn-keyring s))
                (equal (fn-sn-keyring-generation
                        (fn-sn-recover (fn-sn-crash s fc rc)))
                       (fn-sn-keyring-generation s))))
  :hints (("Goal"
           :use ((:instance fn-osr-ready-establishes-catalog-recovery-context)
                 (:instance fn-ccr-ready-crash-keeps-coherent-context)
                 (:instance fn-sn-recover-keeps-coherent-context
                            (s (fn-sn-crash s fc rc))))
           :in-theory
           (disable fn-osr-retainedp fn-snh-recovery-context-coherentp
                    fn-sn-crash fn-sn-recover fn-sn-keyring
                    fn-sn-keyring-generation fn-sn-files fn-sf-phase
                    fn-osr-ready-establishes-catalog-recovery-context
                    fn-ccr-ready-crash-keeps-coherent-context
                    fn-sn-recover-keeps-coherent-context))))
