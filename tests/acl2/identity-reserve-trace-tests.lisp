(in-package "ACL2")
(include-book "../../books/identity-reserve-trace")
(include-book "store-identity-reserve-tests")

; Reachable positive: a completed undertaking, actual open/barriers and
; nonempty retained debt. Twenty semantic refusals burn only the one ordinary
; identity left after protecting its release, then refuse before reservation.
(assert-event
 (and (fn-rfh-ready-p *idr-near*)
      (<= (nfix *idr-debt*)
          (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *idr-near*))))
      (fn-rfh-ready-p (fn-idrt-run 20 *idr-near* *idr-debt*))
      (<= (nfix *idr-debt*)
          (- *fn-sf-max-uint*
             (fn-sf-frontier (fn-sn-files (fn-idrt-run 20 *idr-near* *idr-debt*)))))
      (equal (fn-idrt-run 20 *idr-near* *idr-debt*) *idr-one-burn*)
      (equal (fn-idr-reservation (fn-idrt-run 20 *idr-near* *idr-debt*)
                                 *idr-debt* nil) :identity-reserve)
      (natp (fn-idr-reservation (fn-idrt-run 20 *idr-near* *idr-debt*)
                                *idr-debt* *idr-release*))
      (equal (fn-node-retention (fn-sn-node (fn-idrt-run 20 *idr-near* *idr-debt*)))
             (fn-node-retention (fn-sn-node *idr-near*)))) )

; Removal: retain readiness; an already unfunded promise cannot be repaired
; merely by refusing additional ordinary reservations.
(assert-event
 (and (fn-rfh-ready-p *idr-near*)
      (not (<= (nfix *idr-too-much*)
               (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *idr-near*)))))
      (not (and (fn-rfh-ready-p (fn-idrt-run 20 *idr-near* *idr-too-much*))
                (<= (nfix *idr-too-much*)
                    (- *fn-sf-max-uint* (fn-sf-frontier
                         (fn-sn-files (fn-idrt-run 20 *idr-near* *idr-too-much*)))))))))

(defconst *idrt-mid-reserved* (fn-olr-sn-reserve *idr-near*))

; Removal: actual reachable reserved phase, with funded remaining debt.
; Ordinary gate refusal does not magically restore readiness.
(assert-event
 (and (<= (nfix *idr-debt*)
          (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *idrt-mid-reserved*))))
      (not (fn-rfh-ready-p *idrt-mid-reserved*))
      (not (and (fn-rfh-ready-p (fn-idrt-run 20 *idrt-mid-reserved* *idr-debt*))
                (<= (nfix *idr-debt*)
                    (- *fn-sf-max-uint* (fn-sf-frontier
                         (fn-sn-files (fn-idrt-run 20 *idrt-mid-reserved* *idr-debt*)))))))))

; Complete unconditional frame tooth with nonempty retained history.
(assert-event
 (and (equal (fn-sf-records (fn-sn-files (fn-idrt-run 20 *idr-near* *idr-debt*)))
             (fn-sf-records (fn-sn-files *idr-near*)))
      (equal (fn-sn-groups (fn-idrt-run 20 *idr-near* *idr-debt*))
             (fn-sn-groups *idr-near*))
      (equal (fn-sn-capacity (fn-idrt-run 20 *idr-near* *idr-debt*))
             (fn-sn-capacity *idr-near*))))
