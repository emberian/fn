; fn: the Store's capacity as a resource vector (PRF-138, STO-020).
;
; gpt-6's review of wave 2 (planning/review-2026-09-26-gpt6-wave2.md, section
; 3): "committed use + in-flight reservations + completion/maintenance debt
; <= admitted capacity", with the components kept apart, and admission never
; consuming the last resource its own promise needs.  This book states that
; vector over the values the owner carries and proves it is a maintained
; invariant: established at init, preserved by every admitted record of every
; kind, and by reclaim and profile upgrade.
;
; The components, and where each is bounded:
;
;   transactions  the Store's transaction namespace, one `%020d.txn' per
;                 committed record, bounded by the profile's T for the life of
;                 the store (compaction and reclaim keep the count:
;                 `fn-sbud-used-names-the-transaction-namespace').
;   history       the committed record octets (unframed, the sum the open
;                 path counts: `fn-sbud-record-octets'), bounded by H.
;   completion    DEBT, the forward undertakings the Store holds open.  Each
;   debt          :undertake record pins a :forward obligation whose
;                 discharge is a :release record (books/store-node-retention,
;                 `fn-snrt-retention-of-apply-retention-event'), so an
;                 accepted undertaking is a promise to write one more record.
;   maintenance   one more :release record for the maintenance release
;                 (PRF-129, books/store-maintenance-reserve).
;   charge        the retention ledger's reserved charge against its
;                 capacity.  It is pre-paid: a pin's charge includes the
;                 permanent unit of its own release record, and a release
;                 never raises the reserved charge
;                 (`fn-cvec-release-never-raises-the-charge').
;   configuration the configuration namespace's generations, bounded by the
;   generations   profile's max-config-generations.  The operator's content
;                 release (`retention set') is a configuration record, so
;                 every other configuration record leaves the last
;                 generation to it (`fn-cvec-config-generations').
;   workspace     disk.  Compaction and reclamation write no Store record;
;                 their pack is checked against the free octets the host
;                 observes (`fn-cverb-pack-fits-the-disk',
;                 `fn-rclp-pack-fits-the-disk').  That observation is not
;                 ownership: ENVIRONMENTAL ASSUMPTION, no concurrent writer
;                 takes the observed space before the pack is written.  When
;                 it fails, the write fails before the selection (the pack
;                 publication's EIO cuts: exit 3, the store reopens, the rerun
;                 converges), so the promise is "refused or uncertain, never
;                 torn", not "completes".
;
; The vector's reservation: the profile's gate admits DEBT + 1 release
; records after the committed state, one after another
; (`fn-cvec-roomp').  With no open undertaking it is exactly PRF-129's
; reservation (`fn-cvec-roomp-without-debt-is-the-reserve'); the gate
; (`fn-cvec-verdict-at') differs from PRF-129's only for :undertake, which
; must leave room for its own release as well
; (`fn-cvec-verdict-without-debt-is-the-reserve-gate').
;
; Host calls: host/owner-host.lisp `fn-owner-publication-verdict' (every
; served non-article record, BP admission's retention included) answers
; `fn-cvec-verdict-at'; `fn-owner-prepare' and `fn-owner-prepare-buffer'
; (the served POST and the BP transit) hand `fn-cvec-article-budget-for' to
; `fn-pcar-sbud-prepare'; the debt they pass is `fn-cvec-debt-extend' of the
; owner's carried (K . DEBT) over the committed records, the same carriage
; as the octets (`fn-owner-record-octets').  host/store-node-host.lisp
; `fn-store-sn-publication-verdict' and `fn-store-sn-article-verdict' (the
; developer `store post') answer `fn-cvec-verdict-at' and
; `fn-cvec-article-verdict-at'; `fn-store-cfg-native-admin-authorize' hands
; `fn-cvec-config-generations' to `fn-native-admin-publication-authorize'.
(in-package "ACL2")
(include-book "store-maintenance-reserve")

(local (in-theory (disable fn-sbud-budget-is-the-profile-admissibility
                           fn-bs-publication-admissiblep fn-bs-profile-validp
                           fn-bs-profile-of fn-bs-profile-admittedp
                           fn-bs-profile-max-history-octets
                           fn-sbud-article-figure)))

; -----------------------------------------------------------------------------
; Completion debt over the committed records

(defun fn-cvec-debt-step (kind debt)
  "The open undertakings after one committed record of KIND."
  (declare (xargs :guard t))
  (cond ((equal kind :undertake) (+ 1 (nfix debt)))
        ((equal kind :release) (nfix (- (nfix debt) 1)))
        (t (nfix debt))))

(defun fn-cvec-debt-from (debt records)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-cvec-debt-from (fn-cvec-debt-step (fn-store-event-kind (car records))
                                            debt)
                         (cdr records))
    (nfix debt)))

(defun fn-cvec-record-debt (records)
  "The completion debt of a committed record list."
  (declare (xargs :guard t))
  (fn-cvec-debt-from 0 records))

; The owner carries CACHE = (K . DEBT), the debt of the first K committed
; records, and extends it by the records committed since, as it carries the
; octets (`fn-sbud-bytes-extend').
(defun fn-cvec-debt-cache-validp (cache records)
  (declare (xargs :guard (true-listp records)))
  (and (consp cache) (natp (car cache)) (<= (car cache) (len records))
       (equal (cdr cache) (fn-cvec-record-debt (take (car cache) records)))))

(defun fn-cvec-debt-extend (cache records)
  (declare (xargs :guard (true-listp records)))
  (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
           (<= (car cache) (len records)))
      (fn-cvec-debt-from (cdr cache) (nthcdr (car cache) records))
    (fn-cvec-record-debt records)))

(local
 (defthm fn-cvec-debt-from-append
   (equal (fn-cvec-debt-from d (append x y))
          (fn-cvec-debt-from (fn-cvec-debt-from d x) y))))

(local
 (defthm fn-cvec-debt-from-of-nfix
   (equal (fn-cvec-debt-from (nfix d) x) (fn-cvec-debt-from d x))))

(local
 (defthm fn-cvec-take-nthcdr-append
   (implies (and (natp k) (<= k (len x)))
            (equal (append (take k x) (nthcdr k x)) x))))

; KEYSTONE (the carried debt is the history's debt).
(defthm fn-cvec-debt-extend-is-the-record-debt
  (implies (fn-cvec-debt-cache-validp cache records)
           (equal (fn-cvec-debt-extend cache records)
                  (fn-cvec-record-debt records)))
  :hints (("Goal" :use ((:instance fn-cvec-debt-from-append
                                   (d 0) (x (take (car cache) records))
                                   (y (nthcdr (car cache) records))))
           :in-theory (disable fn-cvec-debt-from-append))))

(local
 (defthm fn-cvec-debt-from-take-len
   (equal (fn-cvec-debt-from d (take (len x) x))
          (fn-cvec-debt-from d x))
   :hints (("Goal" :induct (fn-cvec-debt-from d x)))))

(defthm fn-cvec-full-debt-cache-is-valid
  (fn-cvec-debt-cache-validp (cons (len records) (fn-cvec-record-debt records))
                             records))

; -----------------------------------------------------------------------------
; The debt is the ledger's open forward obligations
;
; An :undertake record's replay admits a :forward pin, a :release record's
; removes the :forward pin it matches (`fn-snrt-retention-of-apply-retention-event').
; Over the ledger functions those are one more and one fewer open forward
; obligation.

(defun fn-cvec-forward-count (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (+ (if (and (consp (car pins))
                  (equal (fn-retain-obligation-kind (car pins)) :forward))
             1 0)
         (fn-cvec-forward-count (cdr pins)))
    0))

(defthm fn-cvec-admit-forward-adds-one-debt
  (implies (fn-retain-admissiblep s id subject :forward evidence charge)
           (equal (fn-cvec-forward-count
                   (fn-retain-pins (fn-retain-admit s id subject :forward
                                                    evidence charge)))
                  (+ 1 (fn-cvec-forward-count (fn-retain-pins s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-retain-admit) (fn-retain-admissiblep)))))

(local
 (defthm fn-cvec-forward-count-of-remove-found
   (implies (and (consp (fn-retain-find-id id pins))
                 (equal (fn-retain-obligation-kind (fn-retain-find-id id pins))
                        :forward))
            (equal (fn-cvec-forward-count (fn-retain-remove-id id pins))
                   (+ -1 (fn-cvec-forward-count pins))))))

(defthm fn-cvec-release-forward-removes-one-debt
  (let ((pin (fn-retain-find-id id (fn-retain-pins s))))
    (implies (and (fn-retain-statep s)
                  (fn-retain-matching-releasep pin id subject :forward evidence))
             (equal (fn-cvec-forward-count
                     (fn-retain-pins (fn-retain-release s id subject :forward
                                                        evidence)))
                    (+ -1 (fn-cvec-forward-count (fn-retain-pins s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-retain-release
                                     fn-retain-matching-releasep))))

; The charge component is pre-paid: a release never raises the reserved
; charge (each pin's charge is positive and includes its release unit).
(local
 (defthm fn-cvec-find-is-obligation
   (implies (and (fn-retain-obligation-listp pins)
                 (consp (fn-retain-find-id id pins)))
            (fn-retain-obligationp (fn-retain-find-id id pins)))))

(defthm fn-cvec-release-never-raises-the-charge
  (implies (fn-retain-statep s)
           (<= (fn-retain-reserved (fn-retain-release s id subject kind evidence))
               (fn-retain-reserved s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-retain-release)
           :expand ((fn-retain-statep s)
                    (fn-retain-obligationp
                     (fn-retain-find-id id (fn-retain-pins s))))
           :use ((:instance fn-cvec-find-is-obligation
                            (pins (fn-retain-pins s)))))))

; -----------------------------------------------------------------------------
; The reservation

(defun fn-cvec-roomp (profile used bytes-used debt)
  "The capacity vector holds: after the committed USED records and BYTES-USED
octets, the profile's gate admits DEBT + 1 release records in turn (one per
open undertaking and the maintenance release)."
  (declare (xargs :guard t))
  (and (natp used) (natp bytes-used)
       (fn-smr-roomp profile (+ used (nfix debt))
                     (+ bytes-used (* (nfix debt) (fn-smr-reserve-octets))))))

(defun fn-cvec-verdict-at (profile kind used bytes-used debt)
  "The publication verdict for one more record of KIND at DEBT open
undertakings.  A release is the profile's gate (it discharges a debt or
consumes the maintenance release); every other kind is admitted only if the
vector holds after it at its worst case, its own promise included."
  (declare (xargs :guard t))
  (if (equal kind :release)
      (fn-sbud-verdict-at profile kind used bytes-used)
    (if (and (equal (fn-sbud-verdict-at profile kind used bytes-used) :admissible)
             (fn-cvec-roomp profile (+ 1 (nfix used))
                            (+ (nfix bytes-used)
                               (fn-store-publication-ceiling kind))
                            (fn-cvec-debt-step kind debt)))
        :admissible
      :unaffordable)))

(defun fn-cvec-article-verdict-at (profile used bytes-used payload-length
                                           group-count debt)
  (declare (xargs :guard t))
  (if (and (equal (fn-sbud-article-verdict-at profile used bytes-used
                                              payload-length group-count)
                  :admissible)
           (fn-cvec-roomp profile (+ 1 (nfix used))
                          (+ (nfix bytes-used)
                             (fn-sbud-article-figure payload-length group-count))
                          debt))
      :admissible
    :unaffordable))

(defun fn-cvec-article-budget (profile used bytes-used payload-length
                                       group-count debt)
  (declare (xargs :guard t))
  (if (fn-cvec-roomp profile (+ 1 (nfix used))
                     (+ (nfix bytes-used)
                        (fn-sbud-article-figure payload-length group-count))
                     debt)
      (fn-sbud-article-budget profile bytes-used payload-length group-count)
    0))

(defun fn-cvec-article-budget-for (profile used bytes-used record debt)
  (declare (xargs :guard t))
  (fn-cvec-article-budget profile used bytes-used
                          (len (fn-record-payload record))
                          (len (fn-record-groups record)) debt))

; What `status' prints: the octets and transactions the vector reserves at
; DEBT, and whether the committed state has them.
(defun fn-cvec-report (profile used bytes-used debt)
  (declare (xargs :guard t))
  (list (* (+ 1 (nfix debt)) (fn-smr-reserve-octets))
        (+ 1 (nfix debt))
        (nfix debt)
        (if (fn-cvec-roomp profile used bytes-used debt) :held :short)))

; -----------------------------------------------------------------------------
; Keystones

(local (in-theory (e/d (fn-smr-roomp fn-sbud-verdict-at fn-sbud-admitp
                        fn-bs-history-admissiblep)
                       (fn-sbud-budget))))

(defthm fn-cvec-roomp-naturals
  (implies (fn-cvec-roomp profile used bytes-used debt)
           (and (natp used) (natp bytes-used)))
  :rule-classes :forward-chaining)

(defthm fn-cvec-roomp-without-debt-is-the-reserve
  (implies (and (natp used) (natp bytes-used))
           (equal (fn-cvec-roomp profile used bytes-used 0)
                  (fn-smr-roomp profile used bytes-used))))

(defthm fn-cvec-verdict-without-debt-is-the-reserve-gate
  (implies (and (natp used) (natp bytes-used)
                (not (equal kind :undertake)))
           (equal (fn-cvec-verdict-at profile kind used bytes-used 0)
                  (fn-smr-verdict-at profile kind used bytes-used)))
  :hints (("Goal" :in-theory (enable fn-smr-verdict-at))))

(defthm fn-cvec-roomp-antitone-in-octets
  (implies (and (fn-cvec-roomp profile used b debt)
                (natp b2) (<= b2 b))
           (fn-cvec-roomp profile used b2 debt))
  :rule-classes nil)

; Where the vector holds, the committed octets are within H and the committed
; count below T: the bounds the open path checks.
(defthm fn-cvec-roomp-is-within-the-profile
  (implies (fn-cvec-roomp profile used b debt)
           (and (fn-profile-replay-within-boundp profile (nfix b))
                (< (nfix used)
                   (fn-bs-profile-max-transactions profile))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-profile-replay-within-boundp
                                     fn-sbud-budget
                                     fn-bs-publication-admissiblep))))

;  KEYSTONE (full never means a promise it cannot discharge).  Where the vector
; holds at DEBT, every one of the DEBT releases and the maintenance release is
; admitted by the profile's gate in turn: the J-th, after J releases of at
; most the release ceiling each, whatever their order.
(defthm fn-cvec-roomp-discharges-every-debt
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (natp j) (<= j (nfix debt))
                (natp b2)
                (<= b2 (+ bytes-used (* j (fn-smr-reserve-octets)))))
           (equal (fn-cvec-verdict-at profile :release (+ used j) b2 debt)
                  :admissible))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sbud-budget
                                     fn-bs-publication-admissiblep))))

;  KEYSTONE (an admitted record keeps the vector).  A record of a kind other
; than the release, admitted at (USED, BYTES-USED, DEBT) and within its
; kind's worst case, leaves the vector holding at the next committed state,
; the debt its own undertaking adds included.
(defthm fn-cvec-admission-keeps-the-vector
  (implies (and (equal (fn-cvec-verdict-at profile kind used bytes-used debt)
                       :admissible)
                (not (equal kind :release))
                (natp octets)
                (<= octets (fn-store-publication-ceiling kind)))
           (fn-cvec-roomp profile (+ 1 used) (+ bytes-used octets)
                          (fn-cvec-debt-step kind debt)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-publication-admissiblep)
                                  (fn-store-publication-ceiling)))))

;  KEYSTONE (a release discharges a debt and keeps the vector).  Where the
; vector holds with at least one open undertaking, a release record of at
; most the release ceiling leaves it holding with one fewer.
(defthm fn-cvec-release-keeps-the-vector
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (posp debt)
                (natp octets)
                (<= octets (fn-smr-reserve-octets)))
           (fn-cvec-roomp profile (+ 1 used) (+ bytes-used octets)
                          (fn-cvec-debt-step :release debt)))
  :rule-classes nil)

; The article figure bounds the narrow record (records-shape).
(local
 (defthm fn-cvec-figure-bounds-the-record
   (implies (not (fn-record-widep record))
            (<= (len (fn-record-encode record))
                (fn-sbud-article-figure (len (fn-record-payload record))
                                        (len (fn-record-groups record)))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-sbud-article-figure-bounds-the-record
                                    (payload-length (len (fn-record-payload record)))
                                    (group-count (len (fn-record-groups record)))))))))

;  KEYSTONE (the served article prepare keeps the vector).
(defthm fn-cvec-prepare-keeps-the-vector
  (implies (and (not (equal (fn-sbud-prepare
                             oc record
                             (fn-cvec-article-budget-for
                              profile (fn-sbud-used (fn-sbud-oc-store oc))
                              bytes-used record debt))
                            oc))
                (not (fn-record-widep record)))
           (and (fn-cvec-roomp profile
                               (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                               (+ bytes-used (len (fn-record-encode record)))
                               debt)
                (fn-profile-replay-within-boundp
                 profile (+ bytes-used (len (fn-record-encode record))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-roomp-antitone-in-octets
                                   (used (+ 1 (fn-sbud-used (fn-sbud-oc-store oc))))
                                   (b (+ bytes-used
                                         (fn-sbud-article-figure
                                          (len (fn-record-payload record))
                                          (len (fn-record-groups record)))))
                                   (b2 (+ bytes-used (len (fn-record-encode record)))))
                        (:instance fn-sbud-prepare-under-article-budget-keeps-history
                                   (bytes-used bytes-used)))
           :in-theory (e/d (fn-sbud-prepare fn-cvec-article-budget-for
                            fn-cvec-article-budget fn-sbud-article-budget-for
                            fn-sbud-article-budget)
                           (fn-cvec-roomp fn-smr-roomp
                            fn-opc-prepare fn-sbud-used
                            fn-profile-replay-within-boundp)))))

;  KEYSTONE (the developer `store post' keeps the vector).
(defthm fn-cvec-article-verdict-keeps-the-vector
  (implies (and (equal (fn-cvec-article-verdict-at profile used bytes-used
                                                   payload-length group-count
                                                   debt)
                       :admissible)
                (not (fn-record-widep record))
                (<= (len (fn-record-payload record)) (nfix payload-length))
                (<= (len (fn-record-groups record)) (nfix group-count)))
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (len (fn-record-encode record)))
                          debt))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-roomp-antitone-in-octets
                                   (used (+ 1 used))
                                   (b (+ bytes-used (fn-sbud-article-figure
                                                     payload-length group-count)))
                                   (b2 (+ bytes-used (len (fn-record-encode record)))))
                        (:instance fn-sbud-article-figure-bounds-the-record))
           :in-theory (e/d (fn-cvec-article-verdict-at fn-sbud-article-verdict-at)
                           (fn-cvec-roomp fn-smr-roomp)))))

;  KEYSTONE (PRF-126 widths: the article verdict keeps the vector for every
; record whose charge fits u32, whatever its sequence, txid, generation and
; stamp widths).
(defthm fn-cvec-article-verdict-keeps-the-vector-at-producer-width
  (implies (and (equal (fn-cvec-article-verdict-at profile used bytes-used
                                                   payload-length group-count
                                                   debt)
                       :admissible)
                (fn-record-uint32p (fn-record-charge record))
                (<= (len (fn-record-payload record)) (nfix payload-length))
                (<= (len (fn-record-groups record)) (nfix group-count)))
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (len (fn-record-encode record)))
                          debt))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-roomp-antitone-in-octets
                                   (used (+ 1 used))
                                   (b (+ bytes-used (fn-sbud-article-figure
                                                     payload-length group-count)))
                                   (b2 (+ bytes-used (len (fn-record-encode record)))))
                        (:instance fn-sbud-article-figure-bounds-the-producer-record))
           :in-theory (e/d (fn-cvec-article-verdict-at fn-sbud-article-verdict-at
                            fn-sbud-admitp fn-bs-history-admissiblep)
                           (fn-cvec-roomp fn-smr-roomp fn-record-uint32p)))))

;  KEYSTONE (the vector holds from init).
(defthm fn-cvec-admitted-profile-starts-held
  (implies (fn-bs-profile-admittedp profile)
           (fn-cvec-roomp profile 0 0 0))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-smr-admitted-profile-starts-reserved))
           :in-theory (disable fn-smr-roomp fn-sbud-verdict-at))))

; A profile upgrade keeps the vector: T and H only grow.
(defthm fn-cvec-profile-upgrade-keeps-the-vector
  (implies (and (fn-profile-upgradep old new)
                (fn-cvec-roomp old used bytes-used debt))
           (fn-cvec-roomp new used bytes-used debt))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-smr-profile-upgrade-keeps-the-reserve
                                   (used (+ (nfix used) (nfix debt)))
                                   (bytes-used (+ (nfix bytes-used)
                                                  (* (nfix debt)
                                                     (fn-smr-reserve-octets))))))
           :in-theory (disable fn-smr-roomp fn-profile-upgradep))))

; -----------------------------------------------------------------------------
; The composed statement
;
; A history is admitted from (USED, BYTES-USED, DEBT) when each record, at the
; state its prefix leaves, is admitted by the gate the host calls for its
; kind and is within the figure that gate charged.  For an article that is
; the article gate at its own payload and group counts, and the figure bounds
; the record whose charge fits u32 at every producer width (PRF-126,
; `fn-sbud-article-figure-bounds-the-producer-record'; the producers that
; establish the premise are PRF-123's).  For every other kind it is the kind's
; publication ceiling, which the record's own codec bound must meet: a
; premise here, not a proof that every producer meets it (the signed
; composite and peer-carried producers are outside PRF-123/126).  A release
; is admitted only against an open undertaking.

(defun fn-cvec-record-figure (record)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-store-event-kind record) :article)
      (fn-sbud-article-figure (len (fn-record-payload record))
                              (len (fn-record-groups record)))
    (fn-store-publication-ceiling (fn-store-event-kind record))))

(defun fn-cvec-record-admittedp (profile used bytes-used debt record)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-store-event-kind record)))
    (and (if (equal kind :article)
             (and (fn-record-p record)
                  (equal (fn-cvec-article-verdict-at
                          profile used bytes-used (len (fn-record-payload record))
                          (len (fn-record-groups record)) debt)
                         :admissible))
           (and (equal (fn-cvec-verdict-at profile kind used bytes-used debt)
                       :admissible)
                (or (not (equal kind :release)) (posp debt))))
         (if (equal kind :article)
             (fn-record-uint32p (fn-record-charge record))
           (<= (len (fn-store-event-encode record))
               (fn-store-publication-ceiling kind))))))

(defun fn-cvec-history-admittedp (profile used bytes-used debt records)
  (declare (xargs :guard t :verify-guards nil :measure (len records)))
  (if (consp records)
      (let ((rest (fn-cvec-history-admittedp
                   profile (+ 1 (nfix used))
                   (+ (nfix bytes-used)
                      (len (fn-store-event-encode (car records))))
                   (fn-cvec-debt-step (fn-store-event-kind (car records)) debt)
                   (cdr records))))
        (and (fn-cvec-record-admittedp profile used bytes-used debt
                                       (car records))
             rest))
    t))

(local (in-theory (disable fn-smr-roomp fn-sbud-verdict-at fn-sbud-admitp
                           fn-bs-history-admissiblep)))

(local
 (defthm fn-cvec-roomp-of-nfix-debt
   (equal (fn-cvec-roomp profile used b (nfix d))
          (fn-cvec-roomp profile used b d))))


;  KEYSTONE (one committed record of any kind keeps the vector).
(defthm fn-cvec-record-keeps-the-vector
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (natp debt)
                (fn-cvec-record-admittedp profile used bytes-used debt record))
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (len (fn-store-event-encode record)))
                          (fn-cvec-debt-step (fn-store-event-kind record) debt)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cvec-article-verdict-keeps-the-vector-at-producer-width
                            (payload-length (len (fn-record-payload record)))
                            (group-count (len (fn-record-groups record))))
                 (:instance fn-cvec-release-keeps-the-vector
                            (octets (len (fn-store-event-encode record))))
                 (:instance fn-cvec-admission-keeps-the-vector
                            (kind (fn-store-event-kind record))
                            (octets (len (fn-store-event-encode record)))))
           :in-theory (e/d (fn-cvec-record-admittedp fn-cvec-debt-step
                            fn-store-event-article-encoding-is-legacy-record-encoding)
                           (fn-cvec-roomp fn-cvec-verdict-at
                            fn-cvec-article-verdict-at
                            fn-store-event-kind fn-store-event-encode
                            fn-store-publication-ceiling fn-record-uint32p
                            fn-record-p)))))

;  The vector part of the composed statement, by induction over the history.
(local
 (defun fn-cvec-history-induction (used bytes-used debt records)
   (declare (xargs :measure (len records)))
   (if (consp records)
       (fn-cvec-history-induction
        (+ 1 used) (+ bytes-used (len (fn-store-event-encode (car records))))
        (fn-cvec-debt-step (fn-store-event-kind (car records)) debt)
        (cdr records))
     (list used bytes-used debt))))

(local
 (defthm fn-cvec-history-admittedp-of-cons
   (implies (consp records)
            (equal (fn-cvec-history-admittedp profile used bytes-used debt records)
                   (and (fn-cvec-record-admittedp profile used bytes-used debt
                                                  (car records))
                        (fn-cvec-history-admittedp
                         profile (+ 1 (nfix used))
                         (+ (nfix bytes-used)
                            (len (fn-store-event-encode (car records))))
                         (fn-cvec-debt-step (fn-store-event-kind (car records))
                                            debt)
                         (cdr records)))))
   :hints (("Goal" :expand ((fn-cvec-history-admittedp profile used bytes-used
                                                        debt records))
            :in-theory (disable fn-cvec-history-admittedp
                                fn-cvec-record-admittedp fn-cvec-debt-step
                                fn-store-event-kind fn-store-event-encode)))))

(local
 (defthm fn-cvec-record-octets-of-cons
   (implies (consp records)
            (equal (fn-sbud-record-octets records)
                   (+ (len (fn-store-event-encode (car records)))
                      (fn-sbud-record-octets (cdr records)))))
   :hints (("Goal" :in-theory (enable fn-sbud-record-octets)))))

(local
 (defthm fn-cvec-record-octets-of-atom
   (implies (not (consp records))
            (equal (fn-sbud-record-octets records) 0))
   :hints (("Goal" :in-theory (enable fn-sbud-record-octets)))))

(local
 (defthm fn-cvec-debt-from-of-cons
   (implies (consp records)
            (equal (fn-cvec-debt-from debt records)
                   (fn-cvec-debt-from
                    (fn-cvec-debt-step (fn-store-event-kind (car records)) debt)
                    (cdr records))))))

(local
 (defthm fn-cvec-debt-from-of-atom
   (implies (not (consp records))
            (equal (fn-cvec-debt-from debt records) (nfix debt)))))

(local
 (defthm fn-cvec-debt-step-natural
   (natp (fn-cvec-debt-step kind debt))
   :rule-classes :type-prescription))

(local
 (defthm fn-cvec-record-step
   (implies (and (fn-cvec-roomp profile used bytes-used debt)
                 (natp debt)
                 (fn-cvec-record-admittedp profile used bytes-used debt record))
            (fn-cvec-roomp profile (+ 1 used)
                           (+ bytes-used (len (fn-store-event-encode record)))
                           (fn-cvec-debt-step (fn-store-event-kind record) debt)))
   :hints (("Goal" :use fn-cvec-record-keeps-the-vector
            :in-theory (disable fn-cvec-roomp fn-cvec-record-admittedp
                                fn-cvec-debt-step fn-store-event-kind
                                fn-store-event-encode)))))

(local
 (defthm fn-cvec-admitted-history-keeps-roomp
   (implies (and (fn-cvec-roomp profile used bytes-used debt)
                 (natp debt)
                 (fn-cvec-history-admittedp profile used bytes-used debt records))
            (fn-cvec-roomp profile (+ used (len records))
                           (+ bytes-used (fn-sbud-record-octets records))
                           (fn-cvec-debt-from debt records)))
   :hints (("Goal" :induct (fn-cvec-history-induction used bytes-used debt records)
            :in-theory (disable fn-cvec-history-admittedp fn-sbud-record-octets
                                fn-cvec-debt-from fn-cvec-roomp
                                fn-cvec-record-admittedp fn-cvec-debt-step
                                fn-store-event-kind fn-store-event-encode)))))

;  KEYSTONE (the composed statement, PRF-138).  From a state where the vector
; holds, a history of mixed record kinds each admitted by the host-called gate
; of its kind leaves the vector holding at the committed count, the ACTUAL
; committed record octets (`fn-sbud-record-octets', the unframed sum the open
; path counts) and the history's debt; so the history is within H and below
; T, which is what the selected open path admits.
(defthm fn-cvec-admitted-history-keeps-the-vector
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (natp debt)
                (fn-cvec-history-admittedp profile used bytes-used debt records))
           (and (fn-cvec-roomp profile (+ used (len records))
                               (+ bytes-used (fn-sbud-record-octets records))
                               (fn-cvec-debt-from debt records))
                (fn-profile-replay-within-boundp
                 profile (+ bytes-used (fn-sbud-record-octets records)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-admitted-history-keeps-roomp)
                        (:instance fn-cvec-roomp-is-within-the-profile
                                   (used (+ used (len records)))
                                   (b (+ bytes-used (fn-sbud-record-octets records)))
                                   (debt (fn-cvec-debt-from debt records))))
           :in-theory (disable fn-cvec-roomp fn-cvec-history-admittedp
                               fn-profile-replay-within-boundp))))

;  KEYSTONE (from init).  A store initialised under an admitted profile whose
; history each record of which the host-called gate admitted is within H and
; below T, and holds the vector at its history's debt.
(defthm fn-cvec-admitted-history-from-init
  (implies (and (fn-bs-profile-admittedp profile)
                (fn-cvec-history-admittedp profile 0 0 0 records))
           (and (fn-cvec-roomp profile (len records)
                               (fn-sbud-record-octets records)
                               (fn-cvec-record-debt records))
                (fn-profile-replay-within-boundp
                 profile (fn-sbud-record-octets records))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-admitted-profile-starts-held)
                        (:instance fn-cvec-admitted-history-keeps-the-vector
                                   (used 0) (bytes-used 0) (debt 0)))
           :in-theory (disable fn-cvec-roomp fn-cvec-history-admittedp))))

(in-theory (disable fn-cvec-roomp fn-cvec-verdict-at fn-cvec-article-verdict-at
                    fn-cvec-article-budget fn-cvec-article-budget-for
                    fn-cvec-report fn-cvec-debt-extend fn-cvec-record-debt
                    fn-cvec-history-admittedp
                    fn-cvec-record-admittedp fn-cvec-record-figure))
