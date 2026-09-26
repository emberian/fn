; fn: the maintenance reservation (PKT-169 as decided, STO-019, PRF-129).
;
; A full store must always be able to finish or safely abandon its own
; maintenance (the Fable mandate, section 8, the reservation paragraph).
; Maintenance has two demands, and each is met where it lives:
;
;   The release record.  An authorized release is a Store record (the
;   retention ledger's :release event, host/native/owner.lisp
;   `fnn-owner-retention-commit', gated by `fn-owner-publication-verdict'
;   at kind :release).  Before this book the history gate admitted every
;   record while its own worst case fit H, so a store filled by articles
;   refused the release that would let the operator regain space.  Here
;   every admission other than the release itself leaves room for one
;   release: after it, `fn-sbud-verdict-at' still admits a :release record.
;   The reservation is the profile's own gate at kind :release (its
;   transaction budget, its record ceiling, its history bound H) and the
;   release record's codec ceiling (`fn-store-publication-ceiling' :release,
;   the event codec's maximum); no constant of its own.  `status' prints it
;   (`fn-smr-report').
;
;   The cleanup work.  Compaction and reclamation write no Store record: the
;   pack they publish is read at open under the compaction unit
;   (`*fn-cc-max-octets*'), not under H, and a reclaiming pack's records are
;   shorter (`fn-rclp-freed-is-the-admission-count'), so they need no room
;   in H.  Their demand is disk: the pack is checked against the free octets
;   the host observes (books/store-compact-verb.lisp
;   `fn-cverb-pack-fits-the-disk', books/store-reclaim-pack.lisp
;   `fn-rclp-pack-fits-the-disk').
;
;   The release's configuration record (`retention set') lives in the
;   configuration namespace, bounded by the profile's max-config-generations
;   and the configuration record bound, never by H or by Store admission:
;   no Store admission can take its room.
;
;   The BP namespace keeps its own reservation, the FNBS received-namespace
;   debt cover (books/bp-node-debt.lisp `fn-bpnd-coverp',
;   `fn-bpnd-spend-admission-preserves-cover'); a bundle delivered into the
;   Store is admitted by the same host-called Store gates as a POST (the
;   transit prepare is `fn-owner-prepare'), so this reservation covers it.
;
; Host calls: host/owner-host.lisp `fn-owner-prepare' and
; `fn-owner-prepare-buffer' (the served POST and the BP transit) hand
; `fn-smr-article-budget-for' to `fn-pcar-sbud-prepare';
; `fn-owner-publication-verdict' (every other served record kind, BP
; admission's retention, identity, consumer and topic events) answers
; `fn-smr-verdict-at'; host/store-node-host.lisp
; `fn-store-sn-article-verdict' (the developer `store post') answers
; `fn-smr-article-verdict-at'.
(in-package "ACL2")
(include-book "store-budget-article")

(local (in-theory (disable fn-sbud-budget-is-the-profile-admissibility
                           fn-bs-publication-admissiblep fn-bs-profile-validp
                           fn-bs-profile-of fn-bs-profile-admittedp
                           fn-bs-profile-max-history-octets
                           fn-sbud-article-figure)))

; -----------------------------------------------------------------------------
; The reservation

(defun fn-smr-roomp (profile used bytes-used)
  "The maintenance reservation holds at USED committed records and
BYTES-USED committed octets: the profile's gate admits one release record."
  (declare (xargs :guard t))
  (equal (fn-sbud-verdict-at profile :release used bytes-used) :admissible))

(defun fn-smr-reserve-octets ()
  "The history octets the reservation holds: the release record's ceiling."
  (declare (xargs :guard t))
  (fn-store-publication-ceiling :release))

; What `status' prints: the octets and transactions reserved and whether the
; reservation holds at the committed state.
(defun fn-smr-report (profile used bytes-used)
  (declare (xargs :guard t))
  (list (fn-smr-reserve-octets) 1
        (if (fn-smr-roomp profile used bytes-used) :held :short)))

; -----------------------------------------------------------------------------
; The reserving gates the host calls

(defun fn-smr-verdict-at (profile kind used bytes-used)
  "The publication verdict for one more record of KIND.  A release consumes
the reservation; every other kind is admitted only if the reservation holds
after it at its worst case."
  (declare (xargs :guard t))
  (if (equal kind :release)
      (fn-sbud-verdict-at profile kind used bytes-used)
    (if (and (equal (fn-sbud-verdict-at profile kind used bytes-used) :admissible)
             (fn-smr-roomp profile (+ 1 (nfix used))
                           (+ (nfix bytes-used) (fn-store-publication-ceiling kind))))
        :admissible
      :unaffordable)))

(defun fn-smr-article-verdict-at (profile used bytes-used payload-length group-count)
  "The article verdict of the developer `store post': the article's own
figure, and the reservation after it."
  (declare (xargs :guard t))
  (if (and (equal (fn-sbud-article-verdict-at profile used bytes-used
                                              payload-length group-count)
                  :admissible)
           (fn-smr-roomp profile (+ 1 (nfix used))
                         (+ (nfix bytes-used)
                            (fn-sbud-article-figure payload-length group-count))))
      :admissible
    :unaffordable))

(defun fn-smr-article-budget (profile used bytes-used payload-length group-count)
  "The transaction budget the served prepare is handed for one article:
`fn-sbud-article-budget' when the reservation holds after the article at its
figure, else 0 (the prepare refuses and the owner answers :unaffordable)."
  (declare (xargs :guard t))
  (if (fn-smr-roomp profile (+ 1 (nfix used))
                    (+ (nfix bytes-used)
                       (fn-sbud-article-figure payload-length group-count)))
      (fn-sbud-article-budget profile bytes-used payload-length group-count)
    0))

(defun fn-smr-article-budget-for (profile used bytes-used record)
  (declare (xargs :guard t))
  (fn-smr-article-budget profile used bytes-used
                         (len (fn-record-payload record))
                         (len (fn-record-groups record))))

; -----------------------------------------------------------------------------
; Keystones

; The reservation is monotone: fewer committed octets keep it (a reclaim
; lowers the committed octets, `fn-rclp-freed-is-the-admission-count').
(defthm fn-smr-roomp-antitone-in-octets
  (implies (and (fn-smr-roomp profile used b)
                (natp b2) (<= b2 b))
           (fn-smr-roomp profile used b2))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-verdict-at fn-bs-history-admissiblep)
                                  (fn-sbud-budget fn-sbud-admitp)))))

; Where the reservation holds, the committed octets are within H.
(defthm fn-smr-roomp-is-within-the-bound
  (implies (fn-smr-roomp profile used b)
           (fn-profile-replay-within-boundp profile b))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-verdict-at fn-bs-history-admissiblep
                                   fn-profile-replay-within-boundp)
                                  (fn-sbud-budget fn-sbud-admitp)))))

;  KEYSTONE (an admitted record keeps the reservation).  If the served gate
; admits one record of a kind other than the release at USED records and
; BYTES-USED octets, and the record is within its kind's worst case, then
; after it commits the profile's gate still admits a release record.
(defthm fn-smr-admission-keeps-the-reserve
  (implies (and (equal (fn-smr-verdict-at profile kind used bytes-used)
                       :admissible)
                (not (equal kind :release))
                (natp octets)
                (<= octets (fn-store-publication-ceiling kind)))
           (fn-smr-roomp profile (+ 1 used) (+ bytes-used octets)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-smr-roomp-antitone-in-octets
                                   (used (+ 1 used))
                                   (b (+ bytes-used
                                         (fn-store-publication-ceiling kind)))
                                   (b2 (+ bytes-used octets))))
           :in-theory (e/d (fn-smr-verdict-at fn-bs-publication-admissiblep)
                           (fn-smr-roomp fn-sbud-verdict-at
                            fn-store-publication-ceiling)))))

;  KEYSTONE (a reserved store admits its release).  Where the reservation
; holds, the served gate admits a release record: a full store can publish
; the release that begins its maintenance.
(defthm fn-smr-reserve-admits-the-release
  (implies (fn-smr-roomp profile used bytes-used)
           (equal (fn-smr-verdict-at profile :release used bytes-used)
                  :admissible))
  :rule-classes nil)

;  KEYSTONE (the served gate is still the profile's gates).  An admitted
; record of any kind passes the count and history gates of its kind
; (`fn-sbud-verdict-is-the-count-and-history-admissibility').
(defthm fn-smr-admission-is-within-the-profile
  (implies (equal (fn-smr-verdict-at profile kind used bytes-used) :admissible)
           (equal (fn-sbud-verdict-at profile kind used bytes-used) :admissible))
  :rule-classes nil)

; The article figure bounds the narrow record (records-shape).
(local
 (defthm fn-smr-figure-bounds-the-record
   (implies (not (fn-record-widep record))
            (<= (len (fn-record-encode record))
                (fn-sbud-article-figure (len (fn-record-payload record))
                                        (len (fn-record-groups record)))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-sbud-article-figure-bounds-the-record
                                    (payload-length (len (fn-record-payload record)))
                                    (group-count (len (fn-record-groups record)))))))))

;  KEYSTONE (the served article prepare keeps the reservation).  A prepare
; that staged under the reserving budget of the record it stages, at the
; count the prepare reads and BYTES-USED committed octets, leaves room for a
; release once the record commits, and keeps the history within H.
(defthm fn-smr-prepare-keeps-the-reserve
  (implies (and (not (equal (fn-sbud-prepare
                             oc record
                             (fn-smr-article-budget-for
                              profile (fn-sbud-used (fn-sbud-oc-store oc))
                              bytes-used record))
                            oc))
                (not (fn-record-widep record)))
           (and (fn-smr-roomp profile
                              (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                              (+ bytes-used (len (fn-record-encode record))))
                (fn-profile-replay-within-boundp
                 profile (+ bytes-used (len (fn-record-encode record))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-smr-roomp-antitone-in-octets
                                   (used (+ 1 (fn-sbud-used (fn-sbud-oc-store oc))))
                                   (b (+ bytes-used
                                         (fn-sbud-article-figure
                                          (len (fn-record-payload record))
                                          (len (fn-record-groups record)))))
                                   (b2 (+ bytes-used (len (fn-record-encode record)))))
                        (:instance fn-smr-roomp-is-within-the-bound
                                   (used (+ 1 (fn-sbud-used (fn-sbud-oc-store oc))))
                                   (b (+ bytes-used (len (fn-record-encode record))))))
           :in-theory (e/d (fn-sbud-prepare fn-smr-article-budget-for
                            fn-smr-article-budget fn-sbud-admitp
                            fn-sbud-article-budget fn-bs-history-admissiblep)
                           (fn-smr-roomp
                            fn-sbud-article-budget-for
                            fn-opc-prepare fn-sbud-budget fn-sbud-used
                            fn-profile-replay-within-boundp)))))

; The article verdict admits only natural counts and octets.
(local
 (defthm fn-smr-article-verdict-naturals
   (implies (equal (fn-sbud-article-verdict-at profile used bytes-used
                                               payload-length group-count)
                   :admissible)
            (and (natp used) (natp bytes-used)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sbud-article-verdict-at fn-sbud-admitp
                                    fn-bs-history-admissiblep)
                                   (fn-sbud-budget))))))

;  KEYSTONE (the developer `store post' keeps the reservation).
(defthm fn-smr-article-verdict-keeps-the-reserve
  (implies (and (equal (fn-smr-article-verdict-at profile used bytes-used
                                                  payload-length group-count)
                       :admissible)
                (not (fn-record-widep record))
                (<= (len (fn-record-payload record)) (nfix payload-length))
                (<= (len (fn-record-groups record)) (nfix group-count)))
           (fn-smr-roomp profile (+ 1 used)
                         (+ bytes-used (len (fn-record-encode record)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-smr-roomp-antitone-in-octets
                                   (used (+ 1 used))
                                   (b (+ bytes-used (fn-sbud-article-figure
                                                     payload-length group-count)))
                                   (b2 (+ bytes-used (len (fn-record-encode record)))))
                        (:instance fn-sbud-article-figure-bounds-the-record)
                        (:instance fn-smr-article-verdict-naturals))
           :in-theory (e/d (fn-smr-article-verdict-at)
                           (fn-smr-roomp fn-sbud-article-verdict-at)))))

;  KEYSTONE (the reservation holds from init).  A fresh store under any
; profile a store may be opened under starts with the reservation: the
; profile validation's minimum record ceiling (196,608) is above the release
; record's ceiling, H is at least the record ceiling and T at least 1.
(defthm fn-smr-admitted-profile-starts-reserved
  (implies (fn-bs-profile-admittedp profile)
           (fn-smr-roomp profile 0 0))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-profile-validp-facts
                                   (values (fn-bs-profile-of profile))))
           :in-theory (e/d (fn-bs-profile-admittedp fn-sbud-verdict-at
                            fn-sbud-budget fn-sbud-admitp
                            fn-bs-history-admissiblep
                            fn-bs-profile-max-transactions
                            fn-bs-profile-max-history-octets
                            fn-bs-profile-record-ceiling
                            fn-bs-profile-max-record-octets
                            fn-bs-profile-field fn-bs-publication-admissiblep
                            fn-bs-pf)
                           (fn-bs-profile-validp fn-bs-profile-validp-facts
                            fn-sbud-verdict-is-the-count-and-history-admissibility
                            fn-bs-profile-of)))))

; An upgrade keeps the reservation: the budget and H only grow.
(defthm fn-smr-profile-upgrade-keeps-the-reserve
  (implies (and (fn-profile-upgradep old new)
                (fn-smr-roomp old used bytes-used))
           (fn-smr-roomp new used bytes-used))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-profile-upgrade-budget-grows (kind :release))
                        (:instance fn-profile-upgrade-keeps-replay-bound
                                   (aggregate (+ bytes-used
                                                 (fn-store-publication-ceiling
                                                  :release)))))
           :in-theory (e/d (fn-sbud-verdict-at fn-sbud-admitp
                            fn-bs-history-admissiblep
                            fn-profile-replay-within-boundp)
                           (fn-sbud-budget fn-profile-upgradep)))))

(in-theory (disable fn-smr-roomp fn-smr-verdict-at fn-smr-article-verdict-at
                    fn-smr-article-budget fn-smr-article-budget-for fn-smr-report))
