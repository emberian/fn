; Witnesses and teeth for books/store-maintenance-reserve (PKT-169, PRF-129).
; The profile is packet 1's *pmt-old* (H = 250 000); the release record's
; ceiling is 4 096 octets.
(in-package "ACL2")
(include-book "store-budget-article-tests")
(include-book "../../books/store-maintenance-reserve")
(include-book "must-fail-checked")

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
; fn-smr-prepare-keeps-the-reserve).  Packet 1's article (32 768 octets,
; 400 groups, figure 266 251 since lane membership-budget: its record's
; 138 251 and 400 memberships at 320).  Under packet 1's H of 250 000 the
; crosspost never fits; these witnesses take the same profile with
; H = 500 000.
(defconst *smt-p* (fn-bs-profile-set-fields *pmt-old* '((2 . 500000))))
(defconst *smt-h2* 500000)
(assert-event (fn-bs-profile-admittedp *smt-p*))
(defconst *smt-fig* (fn-sbud-article-figure 32768 400))
(assert-event (equal *smt-fig* 266251))
(assert-event (equal (fn-smr-article-verdict-at *pmt-old* 1 0 32768 400) :unaffordable))
(defconst *smt-safe* (- (- *smt-h2* *smt-fig*) 4096))
; Reachable witness: at H - figure - 4 096 the article is admitted by both
; gates, the served budget is the profile's, and after the record the
; reservation holds.
(assert-event
 (and (equal (fn-smr-article-verdict-at *smt-p* 1 *smt-safe* 32768 400) :admissible)
      (not (fn-record-widep *pmt-record*))
      (<= (len (fn-record-payload *pmt-record*)) 32768)
      (<= (len (fn-record-groups *pmt-record*)) 400)
      (equal (fn-smr-article-budget-for *smt-p* 1 *smt-safe* *pmt-record*) 4)
      (fn-sbud-admitp (fn-smr-article-budget-for *smt-p* 1 *smt-safe* *pmt-record*) 1)
      (fn-smr-roomp *smt-p* 2 (+ *smt-safe* *pmt-len*))))
; One octet more committed: packet 1's gate alone admits (budget 4) and the
; reserving gate refuses (budget 0), the owner answers :unaffordable.
(assert-event
 (and (equal (fn-sbud-article-budget-for *smt-p* (1+ *smt-safe*) *pmt-record*) 4)
      (equal (fn-smr-article-budget-for *smt-p* 1 (1+ *smt-safe*) *pmt-record*) 0)
      (equal (fn-smr-article-verdict-at *smt-p* 1 (1+ *smt-safe*) 32768 400)
             :unaffordable)))
; Tooth, the verdict / the staged prepare: a 32 768-octet article in one
; group (*sbat-one*) at H - figure: the old gates admit it and after it no
; release fits.  (The 400-group article's memberships now leave the
; release's room: 128 000 octets charged, none stored.)
(defconst *smt-one-fig* (fn-sbud-article-figure 32768 1))
(defconst *smt-one-len* (len (fn-record-encode-impl *sbat-one*)))
(assert-event
 (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 (- *smt-h* *smt-one-fig*) 32768 1)
             :admissible)
      (not (fn-smr-roomp *pmt-old* 2 (+ (- *smt-h* *smt-one-fig*) *smt-one-len*)))))
(must-fail-checked
 (defthm smt-prepare-without-the-staging
   (fn-smr-roomp *pmt-old* 2 (+ (- *smt-h* *smt-one-fig*) *smt-one-len*))
   :rule-classes nil))
; Tooth, narrowness: the record in no group with every integer field at
; 2^32 (*sbat-tight-charge*, 66 622 octets against its figure 66 619;
; a one-group record's membership charge now covers its widening): admitted
; by the reserving verdict at H - 66 619 - 4 096, and the reservation is
; lost.
(assert-event
 (let ((r *sbat-tight-charge*) (b (- (- *smt-h* 66619) 4096)))
   (and (equal (fn-smr-article-verdict-at *pmt-old* 1 b 65536 0) :admissible)
        (fn-record-widep r)
        (<= (len (fn-record-payload r)) 65536)
        (<= (len (fn-record-groups r)) 0)
        (not (fn-smr-roomp *pmt-old* 2 (+ b (len (fn-record-encode r))))))))
; Tooth, the payload count: asked for (0, 1) the one-group article overflows.
(assert-event
 (let ((b (- (- *smt-h* (fn-sbud-article-figure 0 1)) 4096)))
   (and (equal (fn-smr-article-verdict-at *pmt-old* 1 b 0 1) :admissible)
        (<= (len (fn-record-groups *sbat-one*)) 1)
        (not (fn-smr-roomp *pmt-old* 2 (+ b *smt-one-len*))))))
; Tooth, the group count: asked for (32 768, 1) the 400-group article
; overflows (H = 500 000).
(assert-event
 (let ((b (- (- *smt-h2* (fn-sbud-article-figure 32768 1)) 4096)))
   (and (equal (fn-smr-article-verdict-at *smt-p* 1 b 32768 1) :admissible)
        (<= (len (fn-record-payload *pmt-record*)) 32768)
        (not (fn-smr-roomp *smt-p* 2 (+ b *pmt-len*))))))
; A non-natural BYTES-USED is refused by the budget itself (the history gate
; reads a natural committed sum), so the prepare keystone needs no such
; hypothesis: at -1 000 000 the budget is 0.
(assert-event (equal (fn-smr-article-budget-for *pmt-old* 1 -1000000 *pmt-record*) 0))

; The status report.
(assert-event (equal (fn-smr-report *pmt-old* 3 (- *smt-h* 4096)) '(4096 1 :held)))
(assert-event (equal (fn-smr-report *pmt-old* 3 (- *smt-h* 4095)) '(4096 1 :short)))
