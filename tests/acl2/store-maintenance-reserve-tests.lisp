; Witnesses and teeth for books/store-maintenance-reserve (PKT-169, PRF-129).
; The profile is packet 1's *pmt-old* (H = 250 000); the release record's
; ceiling is 4 096 octets.
(in-package "ACL2")
(include-book "store-budget-article-tests")
(include-book "../../books/store-maintenance-reserve")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")

(defconst *smt-h* 250000)
; *pmt-old* budgets 4 transactions: the fourth is the release's.
(assert-event (equal (fn-sbud-budget *pmt-old* :release) 4))
(assert-event
 (and (equal (fn-sbud-verdict-at *pmt-old* :undertake 3 0) :admissible)
      (equal (fn-smr-verdict-at *pmt-old* :undertake 3 0) :unaffordable)
      (equal (fn-smr-verdict-at *pmt-old* :release 3 0) :admissible)))
(assert-event (equal (fn-bs-profile-max-history-octets *pmt-old*) *smt-h*))
(assert-event (equal (fn-smr-reserve-octets) 4096))
(assert-event (fn-bs-profile-admittedp *pmt-old*))

; -----------------------------------------------------------------------------
; fn-smr-admission-keeps-the-reserve
;
; Reachable witness at the boundary: an undertaking (worst case 4 096) at
; H - 8 192 committed octets is admitted, and after a 4 096-octet record the
; reservation holds with no octet to spare.
(defconst *smt-b* (- *smt-h* 8192))
(assert-event
 (and (equal (fn-smr-verdict-at *pmt-old* :undertake 2 *smt-b*) :admissible)
      (fn-smr-roomp *pmt-old* 3 (+ *smt-b* 4096))
      (not (fn-smr-roomp *pmt-old* 3 (+ *smt-b* 4097)))))
; One octet more committed and the served gate refuses; the old gate (the
; profile's alone) still admits, and after it no release fits: F2's shape.
(assert-event
 (and (equal (fn-smr-verdict-at *pmt-old* :undertake 2 (1+ *smt-b*)) :unaffordable)
      (equal (fn-sbud-verdict-at *pmt-old* :undertake 2 (1+ *smt-b*)) :admissible)
      (not (fn-smr-roomp *pmt-old* 3 (+ (1+ *smt-b*) 4096)))))
; Tooth, the verdict: the profile's gate alone admits at H - 4 096 and the
; reservation is gone after the record.
(must-fail-checked
 (defthm smt-keeps-without-the-verdict
   (implies (and (equal (fn-sbud-verdict-at *pmt-old* :undertake 2 (- *smt-h* 4096))
                        :admissible)
                 (natp 4096) (<= 4096 (fn-store-publication-ceiling :undertake)))
            (fn-smr-roomp *pmt-old* 3 *smt-h*))
   :rule-classes nil))
(assert-event (equal (fn-sbud-verdict-at *pmt-old* :undertake 2 (- *smt-h* 4096))
                     :admissible))
; Tooth, the kind: a release is admitted at H - 4 096 (it consumes the
; reservation) and none is left after it.
(assert-event
 (and (equal (fn-smr-verdict-at *pmt-old* :release 2 (- *smt-h* 4096)) :admissible)
      (not (fn-smr-roomp *pmt-old* 3 *smt-h*))))
; Tooth, the record within its kind's worst case: 4 097 octets at the
; boundary witness break the reservation.
(assert-event
 (and (equal (fn-smr-verdict-at *pmt-old* :undertake 2 *smt-b*) :admissible)
      (not (<= 4097 (fn-store-publication-ceiling :undertake)))
      (not (fn-smr-roomp *pmt-old* 3 (+ *smt-b* 4097)))))
; Tooth, a natural record length: half an octet is no committed length.
(assert-event
 (and (equal (fn-smr-verdict-at *pmt-old* :undertake 2 *smt-b*) :admissible)
      (not (fn-smr-roomp *pmt-old* 3 (+ *smt-b* 1/2)))))

; fn-smr-reserve-admits-the-release: witness, and the tooth (without the
; reservation, at H - 4 095, no release is admitted).
(assert-event (equal (fn-smr-verdict-at *pmt-old* :release 2 (- *smt-h* 4096))
                     :admissible))
(assert-event
 (and (not (fn-smr-roomp *pmt-old* 2 (- *smt-h* 4095)))
      (equal (fn-smr-verdict-at *pmt-old* :release 2 (- *smt-h* 4095))
             :unaffordable)))

; fn-smr-roomp-antitone-in-octets: a reclaim that frees octets keeps the
; reservation; its tooth (more octets, not fewer) loses it.
(assert-event (and (fn-smr-roomp *pmt-old* 3 (- *smt-h* 4096))
                   (fn-smr-roomp *pmt-old* 3 1000)
                   (not (fn-smr-roomp *pmt-old* 3 (- *smt-h* 4095)))))

; fn-smr-admitted-profile-starts-reserved: every preset and the D27
; defaults start reserved; the tooth, a profile no store opens under.
(assert-event (fn-smr-roomp *fn-bs-profile-development* 0 0))
(assert-event (fn-smr-roomp *fn-bs-profile-scale* 0 0))
(assert-event (fn-smr-roomp *fn-bs-profile-defaults* 0 0))
(assert-event (and (not (fn-bs-profile-admittedp '(7 1 2 3 4 5)))
                   (not (fn-smr-roomp '(7 1 2 3 4 5) 0 0))))

; -----------------------------------------------------------------------------
; The article gates (fn-smr-article-verdict-keeps-the-reserve and
; fn-smr-prepare-keeps-the-reserve), charged the payload since memory landing
; 3+4 (the memberships and header columns are the memory equation's).  Packet
; 1's article (32 768 octets, 400 groups) under packet 1's H of 250 000.
(defconst *smt-gate* (fn-sbud-article-gate-figure 32768 400))
(assert-event (equal *smt-gate* 32768))
(defconst *smt-safe* (- (- *smt-h* *smt-gate*) 4096))
; Reachable witness: at H - payload - 4 096 the article is admitted by both
; gates, the served budget is the profile's, and after the record the
; reservation holds and H is kept.
(assert-event
 (and (equal (fn-smr-article-verdict-at *pmt-old* 1 *smt-safe* 32768 400) :admissible)
      (equal (len (fn-record-payload *pmt-record*)) 32768)
      (equal (fn-smr-article-budget-for *pmt-old* 1 *smt-safe* *pmt-record*) 4)
      (fn-sbud-admitp (fn-smr-article-budget-for *pmt-old* 1 *smt-safe* *pmt-record*) 1)
      (fn-smr-roomp *pmt-old* 2 (+ *smt-safe* (len (fn-record-payload *pmt-record*))))
      (fn-profile-replay-within-boundp
       *pmt-old* (+ *smt-safe* (len (fn-record-payload *pmt-record*))))))
; One octet more committed: packet 1's gate alone admits (budget 4) and the
; reserving gate refuses (budget 0), the owner answers :unaffordable.
(assert-event
 (and (equal (fn-sbud-article-budget-for *pmt-old* (1+ *smt-safe*) *pmt-record*) 4)
      (equal (fn-smr-article-budget-for *pmt-old* 1 (1+ *smt-safe*) *pmt-record*) 0)
      (equal (fn-smr-article-verdict-at *pmt-old* 1 (1+ *smt-safe*) 32768 400)
             :unaffordable)))
; Tooth, the verdict / the staged prepare: at H - payload packet 1's gate
; admits the article and after it no release fits.
(assert-event
 (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 (- *smt-h* *smt-gate*) 32768 400)
             :admissible)
      (not (fn-smr-roomp *pmt-old* 2 *smt-h*))))
(must-fail-checked
 (defthm smt-prepare-without-the-staging
   (fn-smr-roomp *pmt-old* 2 *smt-h*)
   :rule-classes nil))
; The width does not matter: the record in no group with every integer field
; at 2^32 (*sbat-tight-charge*, wide) admitted at H - 65 536 - 4 096 keeps
; the reservation (H = 1 000 000).
(assert-event
 (let ((r *sbat-tight-charge*)
       (b (- (- 1000000 65536) 4096)))
   (and (equal (fn-smr-article-verdict-at *sbat-p* 1 b 65536 0) :admissible)
        (fn-record-widep r)
        (fn-smr-roomp *sbat-p* 2 (+ b (len (fn-record-payload r)))))))
; Tooth, the payload count: asked for (0, 1), the 32 768-octet article is
; admitted at H - 4 096 and no release fits after it.
(assert-event
 (let ((b (- *smt-h* 4096)))
   (and (equal (fn-smr-article-verdict-at *pmt-old* 1 b 0 1) :admissible)
        (not (fn-smr-roomp *pmt-old* 2 (+ b (len (fn-record-payload *pmt-record*))))))))
; A non-natural BYTES-USED is refused by the budget itself (the history gate
; reads a natural committed sum), so the prepare keystone needs no such
; hypothesis: at -1 000 000 the budget is 0.
(assert-event (equal (fn-smr-article-budget-for *pmt-old* 1 -1000000 *pmt-record*) 0))

; The status report.
(assert-event (equal (fn-smr-report *pmt-old* 3 (- *smt-h* 4096)) '(4096 1 :held)))
(assert-event (equal (fn-smr-report *pmt-old* 3 (- *smt-h* 4095)) '(4096 1 :short)))

; -----------------------------------------------------------------------------
; Teeth bound to the two article keystones (defteeth; witness, one removal per
; hypothesis and an edit mutation, derived from the fixtures above).  The
; verdict keystone's article is packet 1's (*pmt-record*); the served
; prepare's is store-budget-article-tests' held row *osbt-second* on its owner
; *osbt-reserved* (one committed record, so the prepare stages), the row the
; host stages, its payload field the arena handle.
(defconst *smt-pl* (len (fn-record-payload *pmt-record*)))
(defconst *smt-gc* (len (fn-record-groups *pmt-record*)))
(defconst *smt-row-gate*
  (fn-sbud-article-gate-figure (len (fn-record-payload *osbt-second*))
                               (len (fn-record-groups *osbt-second*))))
(defconst *smt-row-safe* (- (- *smt-h* *smt-row-gate*) (fn-smr-reserve-octets)))

(defteeth fn-smr-article-verdict-keeps-the-reserve
  :claim (((verdict (equal (fn-smr-article-verdict-at profile used bytes-used
                                                      payload-length group-count)
                           :admissible))
           (payload (<= (len (fn-record-payload record)) (nfix payload-length))))
          (fn-smr-roomp profile (+ 1 used)
                        (+ bytes-used (len (fn-record-payload record)))))
  :subject fn-smr-article-verdict-at
  :witness ((profile *pmt-old*) (used 1)
            (bytes-used (- (- *smt-h* *smt-pl*) (fn-smr-reserve-octets)))
            (payload-length *smt-pl*) (group-count *smt-gc*) (record *pmt-record*))
  :breaks ((verdict ((profile *pmt-old*) (used 1)
                     (bytes-used (1+ (- (- *smt-h* *smt-pl*) (fn-smr-reserve-octets))))
                     (payload-length *smt-pl*) (group-count *smt-gc*) (record *pmt-record*)))
           (payload ((profile *pmt-old*) (used 1)
                     (bytes-used (- *smt-h* (fn-smr-reserve-octets)))
                     (payload-length 0) (group-count 1) (record *pmt-record*))))
  :mutations ((reserve-spent-on-the-whole-encoding
               (:conclusion (fn-smr-roomp profile (+ 1 used)
                                          (+ bytes-used (len (fn-record-encode record)))))
               ((profile *pmt-old*) (used 1)
                (bytes-used (- (- *smt-h* *smt-pl*) (fn-smr-reserve-octets)))
                (payload-length *smt-pl*) (group-count *smt-gc*) (record *pmt-record*))
               :fault "an admitted article leaving the release's room charged its whole encoding, not its payload")))

(defteeth fn-smr-prepare-keeps-the-reserve
  :claim (((staged (not (equal (fn-sbud-prepare
                                oc record
                                (fn-smr-article-budget-for
                                 profile (fn-sbud-used (fn-sbud-oc-store oc))
                                 bytes-used record))
                               oc))))
          (and (fn-smr-roomp profile
                             (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                             (+ bytes-used (len (fn-record-payload record))))
               (fn-profile-replay-within-boundp
                profile (+ bytes-used (len (fn-record-payload record))))))
  :subject fn-sbud-prepare
  :witness ((oc *osbt-reserved*) (record *osbt-second*) (profile *pmt-old*)
            (bytes-used *smt-row-safe*))
  :breaks ((staged ((oc *osbt-reserved*) (record *osbt-second*) (profile *pmt-old*)
                    (bytes-used (1+ *smt-row-safe*)))))
  :mutations ((release-room-one-octet-short
               (:conclusion (and (fn-smr-roomp profile
                                               (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                                               (+ 1 bytes-used (len (fn-record-payload record))))
                                 (fn-profile-replay-within-boundp
                                  profile (+ bytes-used (len (fn-record-payload record))))))
               ((oc *osbt-reserved*) (record *osbt-second*) (profile *pmt-old*)
                (bytes-used *smt-row-safe*))
               :fault "a staged row leaving the release's reserve one octet short of the record ceiling")))
