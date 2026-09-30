; Remote consumer publication: actual constructed wire charge, not the
; old local event's fixed 512-octet preflight. This decision is consumed
; before frontier allocation. Constructor charge/canonical carries are
; separate obligations; this book never traverses a query or Store tree.
(in-package "ACL2")
(include-book "store-profile-carried")
(include-book "consumer-publication-charge")
(include-book "consumer-event-charge")

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

; Actual host-called decision: the wire charge comes from the admitted event
; constructor, not caller-supplied bytes or a kind ceiling.
(defun fn-cpb-event-verdict-carried (carry profile used bytes-used debt event)
  (declare (xargs :guard t))
  (fn-cpb-verdict-carried carry profile used bytes-used debt
                          (fn-cec-event-charge event)))

; History H and payload R count the Store event encoding, not its external
; physical frame envelope. This relation connects to the maintained history
; sum actually consumed by the owner. Physical and canonical allocation remain
; distinct carried resource obligations.
(defthm fn-cpb-consumer-charge-is-persisted-row-octets
  (implies (fn-cpe-eventp event)
           (equal (fn-cec-event-charge event) (fn-sbud-row-octets event)))
  :hints (("Goal"
           :use ((:instance fn-cpe-is-disjoint-from-old-event-kinds-by-shape
                            (x event))
                 (:instance fn-held-is-no-wire-event (x event))
                 (:instance fn-hstxa-is-no-wire-event (x event)))
           :in-theory (e/d (fn-sbud-row-octets fn-store-event-encode)
                           (fn-cec-event-charge fn-cpe-encode fn-cpe-eventp
                            fn-held-p fn-hstxa-p fn-record-p
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p
                            fn-stxa-p)))))

(local
 (defthm fn-cpb-event-admission-has-valid-event
   (implies (equal (fn-cpb-event-verdict-carried carry profile used bytes-used
                                               debt event) :admissible)
            (fn-cpe-eventp event))
   :hints (("Goal" :in-theory
            (e/d (fn-cpb-event-verdict-carried fn-cpb-verdict-carried
                   fn-cpb-verdict-at fn-cpc-admissiblep fn-cec-event-charge)
                 (fn-cec-event-charge-is-encoded-length fn-cpe-eventp
                  fn-cpe-encode fn-pvc-admittedp))))))

(defthm fn-cpb-event-admission-keeps-actual-row-and-release-headroom
  (implies
   (equal (fn-cpb-event-verdict-carried carry profile used bytes-used debt event)
          :admissible)
   (and (fn-cpe-eventp event)
        (posp (fn-sbud-row-octets event))
        (fn-pvc-history-admissiblep (fn-pvc-admittedp carry profile) profile
                                    bytes-used (fn-sbud-row-octets event))
        (fn-pvc-roomp (fn-pvc-admittedp carry profile) profile
                      (+ 1 used) (+ bytes-used (fn-sbud-row-octets event))
                      (fn-cvec-debt-step :consumer debt))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpb-admission-keeps-actual-charge-and-release-headroom
                            (v (fn-pvc-admittedp carry profile))
                            (wire-octets (fn-cec-event-charge event)))
                 (:instance fn-cpb-event-admission-has-valid-event))
           :in-theory (e/d (fn-cpb-event-verdict-carried fn-cpb-verdict-carried)
                            (fn-cec-event-charge fn-cec-event-charge-is-encoded-length
                             fn-cpb-verdict-at fn-cpe-eventp fn-cpe-encode
                             fn-sbud-row-octets fn-pvc-admittedp fn-pvc-roomp
                             fn-pvc-history-admissiblep)))))

; Exact current FNCE authority-event history admission. This does not grant
; canonical/path allocation, a quantum or retired graph lifetime funding.
(defun fn-cpb-authority-event-verdict-carried
    (carry profile used bytes-used debt event)
  (declare (xargs :guard t))
  (fn-cpb-verdict-carried carry profile used bytes-used debt
                          (fn-cac-event-charge event)))

(local
 (defthm fn-cpb-authority-has-no-old-wire-kind
   (implies (fn-cac-eventp event)
            (and (not (fn-record-p event))
                 (not (fn-store-retention-event-p event))
                 (not (fn-stxe-p event)) (not (fn-stxk-p event))
                 (not (fn-stxa-p event))))
   :hints (("Goal" :in-theory
            (e/d (fn-cac-eventp fn-record-p fn-record-shapep
                  fn-store-retention-event-p fn-stxe-p fn-stxe-shapep
                  fn-stxk-p fn-stxk-shapep fn-stxa-p fn-stxa-shapep fn-cp-nth)
                 (fn-cac-operationp fn-cac-u64p))))))

(defthm fn-cpb-authority-charge-is-persisted-row-octets
  (implies (fn-cac-eventp event)
           (equal (fn-cac-event-charge event) (fn-sbud-row-octets event)))
  :hints (("Goal"
           :use ((:instance fn-cpb-authority-has-no-old-wire-kind)
                 (:instance fn-held-is-no-wire-event (x event))
                 (:instance fn-hstxa-is-no-wire-event (x event)))
           :in-theory
           (e/d (fn-sbud-row-octets fn-store-event-encode)
                (fn-cac-event-charge fn-cac-encode fn-cac-eventp
                 fn-held-p fn-hstxa-p fn-record-p fn-store-retention-event-p
                 fn-stxe-p fn-stxk-p fn-stxa-p)))))

(local
 (defthm fn-cpb-authority-admission-has-valid-event
   (implies (equal (fn-cpb-authority-event-verdict-carried
                   carry profile used bytes-used debt event) :admissible)
            (fn-cac-eventp event))
   :hints (("Goal" :in-theory
            (e/d (fn-cpb-authority-event-verdict-carried fn-cpb-verdict-carried
                  fn-cpb-verdict-at fn-cpc-admissiblep fn-cac-event-charge)
                 (fn-cac-event-charge-is-exact-encoding fn-cac-eventp
                  fn-cac-encode fn-pvc-admittedp))))))

(defthm fn-cpb-authority-admission-keeps-actual-row-and-release-headroom
  (implies
   (equal (fn-cpb-authority-event-verdict-carried
           carry profile used bytes-used debt event) :admissible)
   (and (fn-cac-eventp event)
        (posp (fn-sbud-row-octets event))
        (fn-pvc-history-admissiblep (fn-pvc-admittedp carry profile) profile
                                    bytes-used (fn-sbud-row-octets event))
        (fn-pvc-roomp (fn-pvc-admittedp carry profile) profile
                      (+ 1 used) (+ bytes-used (fn-sbud-row-octets event))
                      (fn-cvec-debt-step :consumer-authority debt))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpb-admission-keeps-actual-charge-and-release-headroom
                            (v (fn-pvc-admittedp carry profile))
                            (wire-octets (fn-cac-event-charge event)))
                 (:instance fn-cpb-authority-admission-has-valid-event))
           :in-theory
           (e/d (fn-cpb-authority-event-verdict-carried fn-cpb-verdict-carried
                 fn-cvec-debt-step)
                (fn-cac-event-charge fn-cac-event-charge-is-exact-encoding
                 fn-cpb-verdict-at fn-cac-eventp fn-cac-encode
                 fn-sbud-row-octets fn-pvc-admittedp fn-pvc-roomp
                 fn-pvc-history-admissiblep)))))

(in-theory (disable fn-cpb-verdict-at fn-cpb-verdict-carried
                    fn-cpb-event-verdict-carried fn-cpb-authority-event-verdict-carried))
