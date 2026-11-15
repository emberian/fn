; Transport the actual draining arm's complete independent result through
; the public selected implementation. This is NOT attachment/stub equality.
(in-package "ACL2")
(include-book "cns-draining-contract")

(defthm fn2-cns-draining-public-selection
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core)
                (fn2-cns-draining-reservedp core)
                (fn2-pool-semanticp (fn2-core-pool core)))
    (and (equal (fn2-cns-snapshot-read-code id core) :ok)
         (equal (fn2-cns-row-phase id core) *fn2-cns-state-draining*)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-cns-draining-domainp fn2-cns-snapshot-read-code
                 fn2-cns-row-phase fn2-machine-phase-read-code fn2-machine-idp
                 fn2-machine-kind fn2-machine-kind-read-code
                 fn2-machine-slot fn2-machine-slot-read-code
                 fn2-machines-kind fn2-machines-slot fn2-machines-rows
                 fn2-cns-phase fn2-cns-rows fn2-core-machines fn2-cns-table
                 fn2-cns-drain-child fn2-cns-drain-child-index
                 fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index)
                (fn2-corep fn2-core-wfp fn2-pool-semanticp
                 fn2-cns-draining-reservedp fn2-cns-drain-releasablep)))))

; A complete independent result must survive the real post-arm check.
; In particular, reclaim changes the phase to FREE or RETIRED; proving only
; its quantities would omit that check and could hide a contract-stop.
(defthm fn2-cns-draining-expected-accepted-by-public-contract
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core)
                (fn2-cns-draining-reservedp core)
                (fn2-pool-semanticp (fn2-core-pool core)))
    (let ((out (fn2-cns-draining-expected id core)))
      (fn2-cns-arm-ok-p id *fn2-cns-state-draining*
        (nth 0 out) (nth 1 out) (nth 2 out) (nth 4 out))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn2-cns-draining-domainp fn2-cns-draining-expected
                 fn2-cns-arm-ok-p fn2-cns-arm-charge-ok-p fn2-cns-arm-next-ok-p
                 fn2-machine-phase-read-code fn2-machine-phase fn2-machine-idp
                 fn2-machine-kind fn2-machine-kind-read-code
                 fn2-machine-slot fn2-machine-slot-read-code
                 fn2-machines-kind fn2-machines-slot fn2-machines-rows
                 fn2-cns-phase fn2-cns-rows fn2-core-stop-reason
                 fn2-core-machines fn2-cns-table fn2-core-control
                 fn2-cns-drain-child fn2-cns-drain-child-index
                 fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index
                 fn2-cns-drain-put-child fn2-cns-drain-put-cells
                 fn2-cns-drain-put-cell fn2-cns-drain-put)
                (fn2-corep fn2-core-wfp fn2-pool-semanticp
                 fn2-cns-draining-reservedp fn2-cns-drain-releasablep
                 fn2-cns-drain-released-pool fn2-cns-drain-cleared-sched)))))

; Modular component transport only. The extra direct-arm conclusion is
; discharged by the actual held/final arm proof in the composition book;
; it must never become an extra hypothesis of the original public claim.
(defthm fn2-cns-draining-component-to-public
  (implies
   (and (fn2-corep core) (fn2-core-wfp core)
        (natp budget) (fn2-cns-draining-domainp id core)
        (fn2-cns-draining-reservedp core)
        (fn2-pool-semanticp (fn2-core-pool core))
        (mv-let (b s d r after) (fn2-cns-run-draining id budget core)
          (fn2-cns-draining-resultp id core b s d r after)))
   (mv-let (b s d r after) (fn2-cns-run id budget core)
     (fn2-cns-draining-resultp id core b s d r after)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-draining-public-selection
                 fn2-cns-draining-expected-accepted-by-public-contract)
           :in-theory
           (e/d (fn2-cns-run fn2-machine-contract-check fn2-cns-draining-resultp)
                (fn2-cns-run-draining fn2-cns-snapshot-read-code fn2-cns-row-phase
                 fn2-cns-arm-ok-p fn2-cns-draining-expected fn2-corep fn2-core-wfp
                 fn2-cns-draining-domainp fn2-cns-draining-reservedp
                 fn2-pool-semanticp)))))
