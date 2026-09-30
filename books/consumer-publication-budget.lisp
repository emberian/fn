; Remote consumer publication: actual constructed wire charge, not the
; old local event's fixed 512-octet preflight. This decision is consumed
; before frontier allocation. Constructor charge/canonical carries are
; separate obligations; this book never traverses a query or Store tree.
(in-package "ACL2")
(include-book "store-profile-carried")
(include-book "consumer-publication-charge")

(defun fn-cpb-verdict-at (v profile used bytes-used debt wire-octets)
  (declare (xargs :guard t))
  (if (and v
           (fn-cpc-admissiblep
            (fn-pvc-pf v *fn-bs-pf-max-transactions* profile)
            (fn-pvc-pf v *fn-bs-pf-max-history-octets* profile)
            (fn-pvc-pf v *fn-bs-pf-max-record-octets* profile)
            (fn-smr-reserve-octets) used bytes-used debt wire-octets))
      :admissible
    :unaffordable))

(defun fn-cpb-verdict-carried (carry profile used bytes-used debt wire-octets)
  (declare (xargs :guard t))
  (fn-cpb-verdict-at (fn-pvc-admittedp carry profile) profile
                     used bytes-used debt wire-octets))

; The subject is the same bounded decision the owner wrapper will call.
; The charge correspondence belongs to the event constructor, not a
; recomputation over its shared group/context trees at this boundary.
(defthm fn-cpb-admission-keeps-actual-charge-and-release-headroom
  (implies
   (equal (fn-cpb-verdict-at v profile used bytes-used debt wire-octets)
          :admissible)
   (and (natp used) (natp bytes-used) (natp debt) (posp wire-octets)
        (<= wire-octets
            (fn-pvc-pf v *fn-bs-pf-max-record-octets* profile))
        (fn-pvc-history-admissiblep v profile bytes-used wire-octets)
        (fn-pvc-roomp v profile (+ 1 used) (+ bytes-used wire-octets)
                      (fn-cvec-debt-step :consumer debt))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpb-verdict-at fn-cpc-admissiblep
                                    fn-pvc-history-admissiblep fn-pvc-roomp
                                    fn-pvc-sbud-verdict-at fn-pvc-budget
                                    fn-cvec-debt-step fn-sbud-admitp
                                    fn-smr-reserve-octets))))

(defthm fn-cpb-carried-verdict-is-current-profile-verdict
  (implies (fn-pvc-carryp carry)
           (equal (fn-cpb-verdict-carried carry profile used bytes-used debt
                                          wire-octets)
                  (fn-cpb-verdict-at (fn-bs-profile-admittedp profile)
                                     profile used bytes-used debt wire-octets)))
  :hints (("Goal" :in-theory '(fn-cpb-verdict-carried
                               fn-pvc-admittedp-is-the-verdict))))

(in-theory (disable fn-cpb-verdict-at fn-cpb-verdict-carried))
