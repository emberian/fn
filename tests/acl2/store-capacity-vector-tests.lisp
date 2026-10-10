; Witnesses and teeth for books/store-capacity-vector (PRF-138, STO-020).
; The profile is packet 1's *pmt-old* with T raised to 8 (H = 250 000, the
; release ceiling R = 4 096): room for several open undertakings.
(in-package "ACL2")
(include-book "../../books/store-capacity-vector")
(include-book "../../books/store-intern")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")

(defconst *cvt-p*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults*
                            '((1 . 8) (2 . 250000) (3 . 196608) (4 . 32768)
                              (5 . 500) (7 . 4))))
(defconst *cvt-h* 250000)
(defconst *cvt-r* 4096)
(assert-event (and (fn-bs-profile-admittedp *cvt-p*)
                   (equal (fn-sbud-budget *cvt-p* :release) 8)
                   (equal (fn-bs-profile-max-history-octets *cvt-p*) *cvt-h*)
                   (equal (fn-smr-reserve-octets) *cvt-r*)))

;  An article record: 1 000 octets in one group, charged its payload at the
; gate (memory landing 3+4: its membership and header columns are the memory
; equation's), and a wide record past its record figure
; (store-budget-article-tests' shape).
(defconst *cvt-record*
  (fn-record-make 1 1 1 "<cvt@example.invalid>"
                  (make-list 1000 :initial-element 65) (list "fn.test")
                  "archive-a" "content-a" "release-a" 9 841000000))
(defconst *cvt-len* (len (fn-record-encode-impl *cvt-record*)))
(defconst *cvt-fig* (fn-sbud-article-figure 1000 1))
; The gate charges the payload.
(defconst *cvt-gate* (fn-sbud-article-gate-figure 1000 1))
(assert-event (equal *cvt-gate* 1000))
(defun cvt-full-record (n)
  (fn-record-make n n n (coerce (make-list 250 :initial-element #\m) 'string)
                  (make-list 195264 :initial-element 65)
                  (list (coerce (make-list 256 :initial-element #\a) 'string))
                  (coerce (make-list 256 :initial-element #\o) 'string)
                  (coerce (make-list 256 :initial-element #\s) 'string)
                  (coerce (make-list 256 :initial-element #\e) 'string) n n))
(assert-event
 (and (fn-record-p *cvt-record*)
      (not (fn-record-widep *cvt-record*))
      (fn-record-uint32p (fn-record-charge *cvt-record*))
      (<= *cvt-len* *cvt-fig*)))

; A retention :undertake event and a :release event (records the gates see
; by kind; their encoded lengths are what the history counts).
(defconst *cvt-undertake*
  (fn-store-retention-event-make :undertake 1 1 1 "work-a" "subject-a"
                                 "evidence-a" 3))
(defconst *cvt-release*
  (fn-store-retention-event-make :release 2 2 2 "work-a" "subject-a"
                                 "evidence-a" 0))
(assert-event
 (and (equal (fn-store-event-kind *cvt-undertake*) :undertake)
      (equal (fn-store-event-kind *cvt-release*) :release)
      (<= (len (fn-store-event-encode *cvt-undertake*)) *cvt-r*)
      (<= (len (fn-store-event-encode *cvt-release*)) *cvt-r*)))

; -----------------------------------------------------------------------------
; The debt and its carriage

(assert-event
 (and (equal (fn-cvec-record-debt (list *cvt-undertake*)) 1)
      (equal (fn-cvec-record-debt (list *cvt-undertake* *cvt-release*)) 0)
      (equal (fn-cvec-record-debt (list *cvt-undertake* *cvt-record*
                                        *cvt-undertake*)) 2)
      (equal (fn-cvec-debt-extend '(1 . 1)
                                  (list *cvt-undertake* *cvt-record*
                                        *cvt-undertake*))
             2)))
; fn-cvec-debt-extend-is-the-record-debt, tooth: a cache that is not the
; debt of its prefix gives another answer.
(assert-event
 (and (not (fn-cvec-debt-cache-validp '(1 . 0) (list *cvt-undertake*
                                                    *cvt-undertake*)))
      (not (equal (fn-cvec-debt-extend '(1 . 0) (list *cvt-undertake*
                                                      *cvt-undertake*))
                  (fn-cvec-record-debt (list *cvt-undertake* *cvt-undertake*))))))

; The ledger: an admitted :forward pin is one more debt, its matching release
; one fewer.
(defconst *cvt-ledger* (fn-retain-initial-state 100))
(defconst *cvt-ledger-1*
  (fn-retain-admit *cvt-ledger* "work-a" "subject-a" :forward
                   "evidence-a" 3))
(assert-event
 (and (fn-retain-admissiblep *cvt-ledger* "work-a" "subject-a" :forward
                             "evidence-a" 3)
      (equal (fn-cvec-forward-count (fn-retain-pins *cvt-ledger-1*)) 1)
      (equal (fn-cvec-forward-count
              (fn-retain-pins (fn-retain-release *cvt-ledger-1* "work-a"
                                                 "subject-a" :forward
                                                 "evidence-a")))
             0)
      (<= (fn-retain-reserved (fn-retain-release *cvt-ledger-1* "work-a"
                                                 "subject-a" :forward
                                                 "evidence-a"))
          (fn-retain-reserved *cvt-ledger-1*))))
; Tooth (admission): an inadmissible pin (charge past the capacity) adds none.
(assert-event
 (and (not (fn-retain-admissiblep *cvt-ledger* "work-b" "subject-b" :forward
                                  "evidence-b" 101))
      (equal (fn-cvec-forward-count
              (fn-retain-pins (fn-retain-admit *cvt-ledger* "work-b" "subject-b"
                                               :forward "evidence-b"
                                               101)))
             0)))
; Tooth (release): evidence that does not match releases nothing.
(assert-event
 (equal (fn-cvec-forward-count
         (fn-retain-pins (fn-retain-release *cvt-ledger-1* "work-a" "subject-a"
                                            :forward "other")))
        1))

; -----------------------------------------------------------------------------
; The reservation

; With no debt it is PRF-129's.
(assert-event
 (and (equal (fn-cvec-roomp *cvt-p* 3 (- *cvt-h* *cvt-r*) 0)
             (fn-smr-roomp *cvt-p* 3 (- *cvt-h* *cvt-r*)))
      (equal (fn-cvec-verdict-at *cvt-p* :article 3 1000 0)
             (fn-smr-verdict-at *cvt-p* :article 3 1000))))
; ... and the gate differs from PRF-129's exactly for an undertaking, which
; must keep its own release: at H - 2R PRF-129 admits it, the vector does not.
(assert-event
 (and (equal (fn-smr-verdict-at *cvt-p* :undertake 3 (- *cvt-h* (* 2 *cvt-r*)))
             :admissible)
      (equal (fn-cvec-verdict-at *cvt-p* :undertake 3 (- *cvt-h* (* 2 *cvt-r*)) 0)
             :unaffordable)
      (equal (fn-cvec-verdict-at *cvt-p* :undertake 3 (- *cvt-h* (* 3 *cvt-r*)) 0)
             :admissible)))

; fn-cvec-roomp-discharges-every-debt.  Reachable witness: debt 2 at
; (1, H - 3R): the vector holds with no octet to spare, and the second debt's
; release (J = 2) is admitted after two releases of R octets.
(defconst *cvt-b* (- *cvt-h* (* 3 *cvt-r*)))
(assert-event
 (and (fn-cvec-roomp *cvt-p* 1 *cvt-b* 2)
      (not (fn-cvec-roomp *cvt-p* 1 (1+ *cvt-b*) 2))
      (equal (fn-cvec-verdict-at *cvt-p* :release 3 (+ *cvt-b* (* 2 *cvt-r*)) 2)
             :admissible)
      (equal (fn-cvec-verdict-at *cvt-p* :release 1 *cvt-b* 2) :admissible)))
; Tooth, the vector: one octet more committed and the J = 2 release is refused.
(assert-event
 (and (not (fn-cvec-roomp *cvt-p* 1 (1+ *cvt-b*) 2))
      (equal (fn-cvec-verdict-at *cvt-p* :release 3
                                 (+ (1+ *cvt-b*) (* 2 *cvt-r*)) 2)
             :unaffordable)))
; Tooth, J within the debt (and the maintenance release): J = 3 at the
; same state is past it.
(assert-event
 (equal (fn-cvec-verdict-at *cvt-p* :release 4 (+ *cvt-b* (* 3 *cvt-r*)) 2)
        :unaffordable))
; Tooth, the committed octets after J releases within J*R: one octet more.
(assert-event
 (equal (fn-cvec-verdict-at *cvt-p* :release 3 (+ *cvt-b* (* 2 *cvt-r*) 1) 2)
        :unaffordable))
; Tooth, natural J: J = 1/2 names no release after a whole number of them.
(assert-event
 (equal (fn-cvec-verdict-at *cvt-p* :release 3/2 *cvt-b* 2) :unaffordable))
; Tooth, a natural B2: a non-natural committed length is not admitted.
(assert-event
 (equal (fn-cvec-verdict-at *cvt-p* :release 3 1/2 2) :unaffordable))
; fn-cvec-admission-keeps-the-vector.  Witness: an undertaking admitted at
; (1, H - 4R) with debt 1 leaves the vector at debt 2 with no octet to spare.
(defconst *cvt-u* (- *cvt-h* (* 4 *cvt-r*)))
(assert-event
 (and (equal (fn-cvec-verdict-at *cvt-p* :undertake 1 *cvt-u* 1) :admissible)
      (fn-cvec-roomp *cvt-p* 2 (+ *cvt-u* *cvt-r*) 2)
      (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-u* *cvt-r* 1) 2))))
; Tooth, the verdict: one octet later the profile's gate still admits the
; undertaking but the vector is gone after it.
(assert-event
 (and (equal (fn-sbud-verdict-at *cvt-p* :undertake 1 (1+ *cvt-u*)) :admissible)
      (equal (fn-cvec-verdict-at *cvt-p* :undertake 1 (1+ *cvt-u*) 1)
             :unaffordable)
      (not (fn-cvec-roomp *cvt-p* 2 (+ (1+ *cvt-u*) *cvt-r*) 2))))
; Tooth, the kind: a release admitted there leaves no room for debt 2.
(assert-event
 (and (equal (fn-cvec-verdict-at *cvt-p* :release 1 (1+ *cvt-u*) 1) :admissible)
      (not (fn-cvec-roomp *cvt-p* 2 (+ (1+ *cvt-u*) *cvt-r*) 2))))
; Tooth, within the kind's ceiling: R + 1 octets break it.
(assert-event
 (and (not (<= (+ *cvt-r* 1) (fn-store-publication-ceiling :undertake)))
      (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-u* *cvt-r* 1) 2))))
; Tooth, natural octets: half an octet is no committed length.
(assert-event (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-u* 1/2) 2)))
(assert-event (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-u* *cvt-r* 1/2) 2)))

; fn-cvec-release-keeps-the-vector.  Witness: debt 2 at (1, H - 3R); a
; release of R octets leaves debt 1 held.
(assert-event
 (and (fn-cvec-roomp *cvt-p* 1 *cvt-b* 2)
      (equal (fn-cvec-debt-step :release 2) 1)
      (fn-cvec-roomp *cvt-p* 2 (+ *cvt-b* *cvt-r*) 1)))
; Tooth, the vector before it.
(assert-event (not (fn-cvec-roomp *cvt-p* 2 (+ (1+ *cvt-b*) *cvt-r*) 1)))
; Tooth, an open debt: at debt 0 the release consumes the maintenance
; release and the vector does not hold after it.
(assert-event
 (and (fn-cvec-roomp *cvt-p* 1 (- *cvt-h* *cvt-r*) 0)
      (equal (fn-cvec-debt-step :release 0) 0)
      (not (fn-cvec-roomp *cvt-p* 2 *cvt-h* 0))))
; Tooth, within the release ceiling.
(assert-event (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-b* *cvt-r* 1) 1)))
; The vector's counts are natural (fn-cvec-roomp-naturals): no negative
; count or octets holds it.
(assert-event
 (and (not (fn-cvec-roomp *cvt-p* -3 *cvt-b* 2))
      (not (fn-cvec-roomp *cvt-p* 1 -8192 2))
      (fn-cvec-roomp *cvt-p* 7 0 0)
      (not (fn-cvec-roomp *cvt-p* 8 0 0))))

; The article gates (fn-cvec-article-verdict-keeps-the-vector,
; fn-cvec-prepare-keeps-the-vector): packet 1's article (figure *cvt-fig*).
; Witness with debt 1: at H - figure - 2R admitted, budget the profile's,
; and after the record the vector holds.
(defconst *cvt-a* (- (- *cvt-h* *cvt-gate*) (* 2 *cvt-r*)))
(assert-event
 (and (equal (fn-cvec-article-verdict-at *cvt-p* 1 *cvt-a* 1000 1 1)
             :admissible)
      (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-a* *cvt-record* 1) 8)
      (<= (len (fn-record-payload *cvt-record*)) 1000)
      (<= (len (fn-record-groups *cvt-record*)) 1)
      (fn-cvec-roomp *cvt-p* 2 (+ *cvt-a* (len (fn-record-payload *cvt-record*))) 1)))
; Tooth, the verdict: the gate blind to the open undertaking (the vector at
; debt 0, PRF-129's reservation) admits at H - figure - R, and with debt 1
; open the vector refuses (budget 0): the open undertaking's release would be
; the room the article took.
(assert-event
 (and (equal (fn-cvec-article-verdict-at *cvt-p* 1 (+ *cvt-a* *cvt-r*) 1000 1 0)
             :admissible)
      (equal (fn-cvec-article-verdict-at *cvt-p* 1 (+ *cvt-a* *cvt-r*) 1000 1 1)
             :unaffordable)
      (equal (fn-cvec-article-budget-for *cvt-p* 1 (+ *cvt-a* *cvt-r*)
                                         *cvt-record* 1)
             0)))
; (The article at the octets the gate charges it, its payload.)
(must-fail-checked
 (defthm cvt-article-without-the-verdict
   (fn-cvec-roomp *cvt-p* 2 (+ *cvt-a* *cvt-r* *cvt-gate*) 1)
   :rule-classes nil))
; The width: the gate charges the payload, so no narrowness is assumed.  The
; widest record of no payload the codec makes (every integer field at 2^32)
; is charged nothing and keeps the vector.
(defconst *cvt-tight*
  (fn-record-make 4294967296 4294967296 4294967296
                  (coerce (make-list 250 :initial-element #\a) 'string)
                  nil nil
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  4294967296 4294967296))
(assert-event
 (let ((r *cvt-tight*)
       (b (- *cvt-h* (* 2 *cvt-r*))))
   (and (fn-record-widep r)
        (equal (fn-sbud-article-gate-figure 0 0) 0)
        (equal (fn-cvec-article-verdict-at *cvt-p* 1 b 0 0 1) :admissible)
        (fn-cvec-roomp *cvt-p* 2 (+ b (len (fn-record-payload r))) 1))))
; Tooth, the counts: a narrow record with more payload than the verdict was
; asked for (195 264 octets against 1 000) is past the figure it charged.
(assert-event
 (let ((r (cvt-full-record 1)))
   (and (not (fn-record-widep r))
        (equal (fn-cvec-article-verdict-at *cvt-p* 1 *cvt-a* 1000 1 1) :admissible)
        (< *cvt-fig* (len (fn-record-encode-impl r)))
        (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-a* (len (fn-record-encode-impl r)))
                            1)))))

; fn-cvec-admitted-profile-starts-held: the presets and packet 1's profile;
; the tooth, a profile no store opens under.
(assert-event
 (and (fn-cvec-roomp *cvt-p* 0 0 0)
      (fn-cvec-roomp (fn-bs-config-for-profile :development) 0 0 0)
      (fn-cvec-roomp (fn-bs-config-for-profile :scale) 0 0 0)
      (not (fn-cvec-roomp '(1 2 3) 0 0 0))))

; -----------------------------------------------------------------------------
; The composed statement (fn-cvec-admitted-history-keeps-the-vector,
; fn-cvec-admitted-history-from-init): an undertaking, packet 1's article
; and the undertaking's release, from init, each admitted at its prefix.
(defconst *cvt-undertake-2*
  (fn-store-retention-event-make :undertake 2 2 2 "work-b" "subject-b"
                                 "evidence-b" 3))
(defconst *cvt-release-2*
  (fn-store-retention-event-make :release 4 4 4 "work-b" "subject-b"
                                 "evidence-b" 0))
(defconst *cvt-history*
  (list *cvt-undertake* *cvt-undertake-2* *cvt-release* *cvt-release-2*))
(assert-event
 (and (fn-cvec-history-admittedp *cvt-p* 0 0 0 *cvt-history*)
      (fn-cvec-roomp *cvt-p* 4 (fn-sbud-record-octets *cvt-history*) 0)
      (equal (fn-cvec-record-debt *cvt-history*) 0)
      (equal (fn-cvec-record-debt (take 2 *cvt-history*)) 2)
      (fn-profile-replay-within-boundp *cvt-p*
                                       (fn-sbud-record-octets *cvt-history*))))
; Tooth, the vector at the start: from H - 2R committed the history's first
; undertaking is refused (it must keep its own release and the maintenance
; release).
(assert-event
 (not (fn-cvec-history-admittedp *cvt-p* 0 (- *cvt-h* (* 2 *cvt-r*)) 0
                                 *cvt-history*)))
; Tooth, admitted: a release with no open undertaking is not an admitted
; history record.
(assert-event
 (not (fn-cvec-history-admittedp *cvt-p* 0 0 0 (list *cvt-release*))))
; Tooth, a profile that is not admitted starts nowhere.
(assert-event
 (not (fn-cvec-history-admittedp '(1 2 3) 0 0 0 *cvt-history*)))

; -----------------------------------------------------------------------------
; A history with a retained ARTICLE (records-flip).  The row is the one the
; POST stages for *cvt-record* (books/store-intern.lisp fn-intern-row-at, at
; handle 0 under the empty keyring and generation 0): a held row of kind
; :article whose payload length, the facts' octets, is the wire record's
; 1 000, the length the host's gate fn-cvec-article-budget-for was asked of.
(defconst *cvt-row* (fn-intern-row-at *cvt-record* nil 0 0))
(assert-event
 (and (fn-held-p *cvt-row*)
      (equal (fn-store-event-kind *cvt-row*) :article)
      (equal (fn-record-payload *cvt-row*) 0)
      (equal (fn-cvec-row-payload-length *cvt-row*)
             (len (fn-record-payload *cvt-record*)))
      (equal (fn-cvec-row-payload-length *cvt-row*) 1000)
      (equal (fn-sbud-row-memberships *cvt-row*) 1)
      ;; its header charge, HCHARGE's per-record figure the memory equation
      ;; charges (books/charged-totals.lisp): 1,000 header octets (the
      ;; payload has no blank line) and a 21-octet Message-ID
      (equal (fn-sbud-held-heap-charge *cvt-row*) (+ (* 8 1000) (* 12 21)))
      ;; H charges the payload alone
      (equal (fn-sbud-row-octets *cvt-row*) 1000)
      (equal (fn-cvec-record-figure *cvt-row*) *cvt-gate*)))
(defconst *cvt-article-history* (list *cvt-undertake* *cvt-row* *cvt-release*))
(defconst *cvt-article-octets*
  (+ (len (fn-store-event-encode *cvt-undertake*)) (fn-sbud-row-octets *cvt-row*)
     (len (fn-store-event-encode *cvt-release*))))
; fn-cvec-admitted-history-keeps-the-vector and -from-init, with an article
; in the history: every hypothesis holds and so does each conclusion, at the
; article's 1 000 stored octets.
(assert-event
 (and (fn-bs-profile-admittedp *cvt-p*)
      (fn-cvec-roomp *cvt-p* 0 0 0)
      (fn-cvec-history-admittedp *cvt-p* 0 0 0 *cvt-article-history*)
      (equal (fn-sbud-record-octets *cvt-article-history*) *cvt-article-octets*)
      (fn-cvec-roomp *cvt-p* 3 *cvt-article-octets*
                     (fn-cvec-debt-from 0 *cvt-article-history*))
      (equal (fn-cvec-record-debt *cvt-article-history*) 0)
      (fn-profile-replay-within-boundp *cvt-p* *cvt-article-octets*)))
; Removal of the history hypothesis: from H - R - 999 committed the vector holds, the one-row
; history is not admitted, and the vector does not hold after it.
(assert-event
 (let ((b (- *cvt-h* (+ *cvt-r* 999))))
   (and (fn-cvec-roomp *cvt-p* 0 b 0)
        (not (fn-cvec-history-admittedp *cvt-p* 0 b 0 (list *cvt-row*)))
        (not (fn-cvec-roomp *cvt-p* 1 (+ b (fn-sbud-record-octets (list *cvt-row*)))
                            (fn-cvec-debt-from 0 (list *cvt-row*)))))))
; Removal of the vector hypothesis: at a debt no profile can pay the empty
; history is admitted, the vector does not hold, and the conclusion fails.
(assert-event
 (and (not (fn-cvec-roomp *cvt-p* 0 0 (expt 10 30)))
      (fn-cvec-history-admittedp *cvt-p* 0 0 (expt 10 30) nil)
      (not (fn-cvec-roomp *cvt-p* 0 (fn-sbud-record-octets nil)
                          (fn-cvec-debt-from (expt 10 30) nil)))))
; The natural-debt hypothesis the keystone once carried is gone (PKT-362):
; every reader fixes the debt, so a debt of -1 reads as 0.
(assert-event
 (and (equal (fn-cvec-roomp *cvt-p* 0 0 -1) (fn-cvec-roomp *cvt-p* 0 0 0))
      (equal (fn-cvec-debt-step :release -1) 0)
      (not (fn-cvec-record-admittedp *cvt-p* 0 0 -1 *cvt-release*))))
; fn-cvec-record-keeps-the-vector at the article, at the state its prefix
; leaves (one undertaking open).
(assert-event
 (let ((b (len (fn-store-event-encode *cvt-undertake*))))
   (and (fn-cvec-roomp *cvt-p* 1 b 1)
        (fn-cvec-record-admittedp *cvt-p* 1 b 1 *cvt-row*)
        (fn-cvec-roomp *cvt-p* 2 (+ b (fn-sbud-row-octets *cvt-row*))
                       (fn-cvec-debt-step :article 1)))))
; Tooth, the article arm's verdict: from H - R - 999 committed the vector
; holds, but the article's payload (1 000) does not fit beside the
; maintenance release, so the row is not admitted.
(assert-event
 (let ((b (- *cvt-h* (+ *cvt-r* 999))))
   (and (fn-cvec-roomp *cvt-p* 0 b 0)
        (not (fn-cvec-record-admittedp *cvt-p* 0 b 0 *cvt-row*))
        (not (fn-cvec-history-admittedp *cvt-p* 0 b 0 (list *cvt-row*))))))
; The arm the restatement replaced asked fn-record-p of the row: the wire
; record is not an article row (fn-cvec-wire-record-is-no-article-row) and
; the row is not a wire record, so under that arm this history was refused.
(assert-event
 (and (fn-record-p *cvt-record*)
      (not (equal (fn-store-event-kind *cvt-record*) :article))
      (not (fn-record-p *cvt-row*))))

; -----------------------------------------------------------------------------
; Lane keystone-audit (2026-09-27).  fn-cvec-article-verdict-keeps-the-vector-
; for-a-held-row at the retained article row *cvt-row* (payload length 1 000,
; the held facts' octets): the verdict at its payload length with one group
; and one undertaking open admits, and the vector holds after the row's
; stored octets.  Without the admissible verdict: one release record's room
; later the verdict is :unaffordable and the vector no longer holds.
(assert-event
 (and (equal (fn-cvec-article-verdict-at *cvt-p* 1 *cvt-a*
                                         (fn-cvec-row-payload-length *cvt-row*) 1 1)
             :admissible)
      (fn-cvec-roomp *cvt-p* (+ 1 1) (+ *cvt-a* (fn-cvec-row-payload-length *cvt-row*)) 1)))
; (The stored charge the conclusion names is the row's octets, its payload;
; a verdict refused one release record's room later than *cvt-a* + R: past
; the vector.)
(assert-event
 (let ((b (+ *cvt-a* *cvt-r* (- *cvt-gate* (fn-sbud-row-octets *cvt-row*)) 1)))
   (and (not (equal (fn-cvec-article-verdict-at *cvt-p* 1 b
                                                (fn-cvec-row-payload-length *cvt-row*) 1 1)
                    :admissible))
        (not (fn-cvec-roomp *cvt-p* (+ 1 1) (+ b (fn-sbud-row-octets *cvt-row*)) 1)))))

; ---------------------------------------------------------------------------
; The groups cost H nothing (memory landing 3+4; the membership charge and
; its word :memberships are deleted, the memberships are the memory
; equation's MEMBERSHIPS term).  The same 1 000-octet article in one group
; and in ten, at one committed record, no open undertaking and B committed
; octets where it fits beside the maintenance release with no octet to
; spare: both are admitted; one octet more and both are refused as the
; history.  An article whose payload does not fit is :history-exhausted, a
; spent T :unaffordable, and any other word passes through.
(defconst *cvt-groups-10*
  '("fn.t0" "fn.t1" "fn.t2" "fn.t3" "fn.t4" "fn.t5" "fn.t6" "fn.t7" "fn.t8" "fn.t9"))
(defconst *cvt-record-10*
  (fn-record-make 1 1 1 "<cvt10@example.invalid>"
                  (make-list 1000 :initial-element 65) *cvt-groups-10*
                  "archive-a" "content-a" "release-a" 9 841000000))
(defconst *cvt-big-10*
  (fn-record-make 1 1 1 "<cvtbig@example.invalid>"
                  (make-list 10000 :initial-element 65) *cvt-groups-10*
                  "archive-a" "content-a" "release-a" 9 841000000))
(assert-event (equal (fn-sbud-article-gate-figure 1000 10) (fn-sbud-article-gate-figure 1000 1)))
(defconst *cvt-mb* (- (- *cvt-h* *cvt-r*) 1000))
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-mb* *cvt-record* 0) 8))
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-mb* *cvt-record-10* 0) 8))
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 (1+ *cvt-mb*) *cvt-record* 0) 0))
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 (1+ *cvt-mb*) *cvt-record-10* 0) 0))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-p* 1 (1+ *cvt-mb*)
                                                   *cvt-record-10* 0)
                     :history-exhausted))
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-mb* *cvt-big-10* 0) 0))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-p* 1 *cvt-mb*
                                                   *cvt-big-10* 0)
                     :history-exhausted))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-p* 8 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-article-refusal-word :duplicate *cvt-p* 1 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :duplicate))
(assert-event (equal (fn-cvec-article-refusal-word :refused *cvt-p* 1 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :refused))

; -----------------------------------------------------------------------------
; Lane m1-durable-2 (2026-10-04).  KEYSTONES fn-cvec-article-refusal-word-
; names-the-history, -keeps-unaffordable-for-the-transactions, -under-the-
; budget-names-the-resource and fn-cvec-article-verdict-word-names-the-
; resource.  A small H: *cvt-p* with H = 200 000, the least H above its
; record ceiling R = 196 608 that leaves room for a few articles.
(defconst *cvt-th* (fn-bs-profile-set-fields *cvt-p* '((2 . 200000))))
(assert-event (and (fn-bs-profile-admittedp *cvt-th*)
                   (equal (fn-bs-profile-max-history-octets *cvt-th*) 200000)
                   (equal (fn-sbud-budget *cvt-th* :article) 8)
                   (equal (fn-sbud-budget *cvt-th* :release) 8)))
; Words at one edge (190 000 committed octets): the ten-group 1 000-octet
; article is admitted (its groups cost H nothing), the ten-group 10 000-octet
; one is refused as the history (:history-exhausted), and with T spent (8 of
; 8) the same article is :unaffordable.
(defconst *cvt-tb* 190000)
(assert-event (fn-sbud-admitp (fn-cvec-article-budget-for *cvt-th* 1 *cvt-tb* *cvt-record* 0) 1))
(assert-event (fn-sbud-admitp (fn-cvec-article-budget-for *cvt-th* 1 *cvt-tb* *cvt-record-10* 0) 1))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-th* 1 *cvt-tb*
                                                   *cvt-big-10* 0)
                     :history-exhausted))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-th* 8 *cvt-tb*
                                                   *cvt-big-10* 0)
                     :unaffordable))
; THE BAND (teeth for counting the vector's octet reservation as history).
; At B the history gate alone admits the one-group article, the vector's
; octet reservation (one release ceiling past it) does not: the history
; refuses, and the word is :history-exhausted.  A precedence that called
; every vector refusal :unaffordable would name this H refusal T.
(defconst *cvt-band* (+ 1 (- (- 200000 *cvt-gate*) *cvt-r*)))
(assert-event (and (fn-bs-history-admissiblep *cvt-th* *cvt-band* *cvt-gate*)
                   (not (fn-cvec-roomp *cvt-th* 2 (+ *cvt-band* *cvt-gate*) 0))
                   (fn-cvec-article-transactions-admitp *cvt-th* 1 0)
                   (not (fn-cvec-article-history-admitp *cvt-th* *cvt-band* *cvt-gate* 0))
                   (not (fn-sbud-admitp (fn-cvec-article-budget-for
                                         *cvt-th* 1 *cvt-band* *cvt-record* 0)
                                        1))
                   (equal (fn-cvec-article-refusal-word :unaffordable *cvt-th* 1
                                                        *cvt-band* *cvt-record* 0)
                          :history-exhausted)))
; One octet lower the article fits with the vector: admitted.
(assert-event (fn-sbud-admitp (fn-cvec-article-budget-for *cvt-th* 1 (- *cvt-band* 1)
                                                          *cvt-record* 0)
                              1))
; The vector's TRANSACTION reservation refusing is T, not H, whatever the
; octets: six open undertakings after one record leave no release for the
; seventh (1 + 1 + 6 = T), and at the band the word is :unaffordable.
(assert-event (and (not (fn-cvec-article-transactions-admitp *cvt-th* 1 6))
                   (fn-cvec-article-transactions-admitp *cvt-th* 1 5)))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-th* 1 *cvt-band*
                                                   *cvt-record* 6)
                     :unaffordable))
; Hypothesis-removal witness for -under-the-budget-names-the-resource: with
; the budget admitting (nothing refused), the word left for :unaffordable is
; :unaffordable although the transactions admit; only the budget's refusal
; makes :unaffordable mean T.
(assert-event (and (fn-sbud-admitp (fn-cvec-article-budget-for *cvt-th* 1 0 *cvt-record* 0) 1)
                   (fn-cvec-article-transactions-admitp *cvt-th* 1 0)
                   (equal (fn-cvec-article-refusal-word :unaffordable *cvt-th* 1 0
                                                        *cvt-record* 0)
                          :unaffordable)))
; Another word passes through, :history-exhausted included.
(assert-event (equal (fn-cvec-article-refusal-word :history-exhausted *cvt-th* 8 *cvt-tb*
                                                   *cvt-big-10* 0)
                     :history-exhausted))
; The developer `store post''s word over the same points.
(assert-event (equal (fn-cvec-article-verdict-word *cvt-th* 1 *cvt-tb* 1000 1 0) :admissible))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-th* 1 *cvt-tb* 1000 10 0) :admissible))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-th* 1 *cvt-tb* 10000 10 0)
                     :history-exhausted))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-th* 8 *cvt-tb* 10000 10 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-th* 1 *cvt-band* 1000 1 0)
                     :history-exhausted))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-th* 1 *cvt-band* 1000 1 6)
                     :unaffordable))

; ---------------------------------------------------------------------------
; The accepted-statement figure: the kind's publication ceiling (196 608),
; whatever the groups of the article a composite carries (memory landing
; 3+4: a composite is charged its encoding, its memberships are the memory
; equation's).  Under *cvt-p* with H = 2,500,000, at SB (one octet past the
; edge) the composite is refused in ten groups and in one, and the kind's
; generic verdict agrees; one octet lower both are admitted.
(defconst *cvt-ps* (fn-bs-profile-set-fields *cvt-p* '((2 . 2500000))))
(defconst *cvt-sf10* (fn-cvec-statement-figure 10))
(assert-event (equal *cvt-sf10* 196608))
(assert-event (equal (fn-cvec-statement-figure 1) 196608))
(defconst *cvt-sb* (+ 1 (- (- 2500000 *cvt-r*) *cvt-sf10*)))
(assert-event (equal (fn-cvec-verdict-at *cvt-ps* :accepted-statement 1 *cvt-sb* 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-statement-verdict-at *cvt-ps* 1 *cvt-sb* 10 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-statement-verdict-at *cvt-ps* 1 *cvt-sb* 1 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-statement-verdict-at *cvt-ps* 1 (1- *cvt-sb*) 1 0)
                     :admissible))
; A composite charged its figure at SB leaves the vector short.
(assert-event (not (fn-cvec-roomp *cvt-ps* 2 (+ *cvt-sb* *cvt-sf10*) 0)))

; fn-cvec-statement-admission-keeps-the-vector.  Witness: admitted one
; octet lower, a composite charged its whole figure keeps the vector.
(assert-event
 (and (equal (fn-cvec-statement-verdict-at *cvt-ps* 1 (1- *cvt-sb*) 10 0)
             :admissible)
      (fn-cvec-roomp *cvt-ps* 2 (+ (1- *cvt-sb*) *cvt-sf10*)
                     (fn-cvec-debt-step :accepted-statement 0))))
; Tooth, the verdict: at *cvt-sb* (refused) the same charge breaks it.
(must-fail-checked
 (defthm cvt-statement-without-the-verdict
   (fn-cvec-roomp *cvt-ps* 2 (+ *cvt-sb* *cvt-sf10*) 0)
   :rule-classes nil))
; Tooth, the charge within the figure: admitted, one octet past the figure
; at the edge breaks it.
(must-fail-checked
 (defthm cvt-statement-past-its-figure
   (fn-cvec-roomp *cvt-ps* 2 (+ (1- *cvt-sb*) (+ 1 *cvt-sf10*)) 0)
   :rule-classes nil))

; fn-cvec-statement-row-within-its-figure over a retained composite: the
; held row in one group inside a small composite (charge = its encoding,
; within the figure); the tooth, a composite whose encoding is past the
; ceiling (1,800,000 octets); and the strengthening (no held-octets
; premise): a composite carrying an article past the ceiling (250,000
; octets) is still within its figure, charged its encoding alone.
(defconst *cvt-stxa* (fn-stxa-make 1 5 5 0 '(1) '(1) '(1) '(1)))
(defconst *cvt-hstxa* (fn-hstxa-make *cvt-stxa* *cvt-row*))
(defconst *cvt-stxa-big*
  (fn-stxa-make 1 5 5 0 '(1) '(1) (make-list 1800000 :initial-element 7) '(1)))
(defconst *cvt-row-big*
  (fn-intern-row-at (fn-record-make 1 1 1 "<cvtbig-a@example.invalid>"
                                    (make-list 250000 :initial-element 65)
                                    (list "fn.test")
                                    "archive-a" "content-a" "release-a" 9 841000000)
                    nil 0 0))
(defconst *cvt-hstxa-big-article* (fn-hstxa-make *cvt-stxa* *cvt-row-big*))
(defconst *cvt-hstxa-big* (fn-hstxa-make *cvt-stxa-big* *cvt-row*))
(assert-event
 (and (fn-hstxa-p *cvt-hstxa*)
      (equal (fn-store-event-kind *cvt-hstxa*) :accepted-statement)
      (equal (fn-sbud-row-memberships *cvt-hstxa*) 1)
      (equal (fn-sbud-row-octets *cvt-hstxa*)
             (len (fn-store-event-encode *cvt-stxa*)))
      (<= (fn-sbud-row-octets *cvt-hstxa*) (fn-cvec-statement-figure 1))
      (<= (len (fn-store-event-encode *cvt-stxa*)) 196608)))
(assert-event
 (and (fn-hstxa-p *cvt-hstxa-big*)
      (< 196608 (len (fn-store-event-encode *cvt-stxa-big*)))
      (<= (fn-hf-octets (fn-held-facts (fn-hstxa-held *cvt-hstxa-big*))) 196608)
      (< (fn-cvec-statement-figure 1) (fn-sbud-row-octets *cvt-hstxa-big*))))
(assert-event
 (and (fn-hstxa-p *cvt-hstxa-big-article*)
      (<= (len (fn-store-event-encode *cvt-stxa*)) 196608)
      (< 196608 (fn-hf-octets (fn-held-facts (fn-hstxa-held *cvt-hstxa-big-article*))))
      (<= (fn-sbud-row-octets *cvt-hstxa-big-article*) (fn-cvec-statement-figure 1))))
; The history arm: the small composite one octet below *cvt-sb* is admitted
; and keeps the vector; the one past the ceiling is not.
(assert-event (fn-cvec-record-admittedp *cvt-ps* 1 (1- *cvt-sb*) 0 *cvt-hstxa*))
(assert-event (not (fn-cvec-record-admittedp *cvt-ps* 1 (1- *cvt-sb*) 0 *cvt-hstxa-big*)))

; The developer `store post''s word (fn-cvec-article-verdict-word) at
; *cvt-mb*: the article admitted in ten groups and in one, the ten-group
; article past H refused as the history, and the count gate refusing is T.
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 1 *cvt-mb* 1000 10 0)
                     :admissible))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 1 *cvt-mb* 1000 1 0)
                     :admissible))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 1 *cvt-mb* 10000 10 0)
                     :history-exhausted))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 8 *cvt-mb* 1000 10 0)
                     :unaffordable))

; -----------------------------------------------------------------------------
; Teeth bound to the keystones named below (defteeth; witness, one removal per
; hypothesis and an edit mutation, derived from the fixtures above).  The
; verdict keystones' article is *cvt-record* / its retained row *cvt-row*
; (payload length 1 000, one group, one undertaking open); the served
; prepare's teeth are in store-capacity-vector-prepare-tests (its witness is
; owner-store-budget-tests' owner, whose arena constant this book's includers
; also define).
(defconst *cvt-pl* (len (fn-record-payload *cvt-record*)))
(defconst *cvt-gc* (len (fn-record-groups *cvt-record*)))

; A composite whose encoding is just past the publication ceiling (its
; payload list as long as the ceiling is in octets), the smallest the removals
; below need.
(defconst *cvt-stxa-over*
  (fn-stxa-make 1 5 5 0 '(1) '(1)
                (make-list (fn-store-publication-ceiling :accepted-statement) :initial-element 7)
                '(1)))
(defconst *cvt-hstxa-over* (fn-hstxa-make *cvt-stxa-over* *cvt-row*))

(defteeth fn-cvec-article-verdict-keeps-the-vector
  :claim (((verdict (equal (fn-cvec-article-verdict-at profile used bytes-used
                                                       payload-length group-count debt)
                           :admissible))
           (payload (<= (len (fn-record-payload record)) (nfix payload-length))))
          (fn-cvec-roomp profile (+ 1 used)
                         (+ bytes-used (len (fn-record-payload record)))
                         debt))
  :subject fn-cvec-article-verdict-at
  :witness ((profile *cvt-p*) (used 1) (bytes-used *cvt-a*) (payload-length *cvt-pl*)
            (group-count *cvt-gc*) (debt 1) (record *cvt-record*))
  :breaks ((verdict ((profile *cvt-p*) (used 1) (bytes-used (+ *cvt-a* *cvt-r*))
                     (payload-length *cvt-pl*) (group-count *cvt-gc*) (debt 1)
                     (record *cvt-record*)))
           (payload ((profile *cvt-p*) (used 1) (bytes-used *cvt-a*) (payload-length *cvt-pl*)
                     (group-count *cvt-gc*) (debt 1) (record (cvt-full-record 1)))))
  :mutations ((vector-spent-on-the-whole-encoding
               (:conclusion (fn-cvec-roomp profile (+ 1 used)
                                           (+ bytes-used (len (fn-record-encode record)))
                                           debt))
               ((profile *cvt-p*) (used 1) (bytes-used *cvt-a*) (payload-length *cvt-pl*)
                (group-count *cvt-gc*) (debt 1) (record *cvt-record*))
               :fault "an admitted article leaving the vector charged its whole encoding, not its payload")))

(defteeth fn-cvec-article-verdict-keeps-the-vector-for-a-held-row
  :claim (((verdict (equal (fn-cvec-article-verdict-at profile used bytes-used
                                                       (fn-cvec-row-payload-length record)
                                                       group-count debt)
                           :admissible)))
          (fn-cvec-roomp profile (+ 1 used)
                         (+ bytes-used (fn-cvec-row-payload-length record))
                         debt))
  :subject fn-cvec-article-verdict-at
  :witness ((profile *cvt-p*) (used 1) (bytes-used *cvt-a*) (group-count *cvt-gc*)
            (debt 1) (record *cvt-row*))
  :breaks ((verdict ((profile *cvt-p*) (used 1)
                     (bytes-used (+ *cvt-a* *cvt-r* 1)) (group-count *cvt-gc*)
                     (debt 1) (record *cvt-row*))))
  :mutations ((verdict-forgets-an-open-undertaking
               (:conclusion (fn-cvec-roomp profile (+ 1 used)
                                           (+ bytes-used (fn-cvec-row-payload-length record))
                                           (+ 1 debt)))
               ((profile *cvt-p*) (used 1) (bytes-used *cvt-a*) (group-count *cvt-gc*)
                (debt 1) (record *cvt-row*))
               :fault "the verdict read one open undertaking too few, its release's room spent")))

(defteeth fn-cvec-held-row-within-its-figure
  :claim (()
          (equal (fn-sbud-article-gate-figure (fn-cvec-row-payload-length record) group-count)
                 (fn-cvec-row-payload-length record)))
  :subject fn-sbud-article-gate-figure
  :witness ((record *cvt-row*) (group-count *cvt-gc*))
  :breaks ()
  :mutations ((gate-charges-the-groups-again
               (:conclusion (equal (fn-sbud-article-gate-figure
                                    (fn-cvec-row-payload-length record) group-count)
                                   (+ (fn-cvec-row-payload-length record) group-count)))
               ((record *cvt-row*) (group-count *cvt-gc*))
               :fault "the gate figure charging the row's groups again, the deleted membership charge")))

(defteeth fn-cvec-statement-row-within-its-figure
  :claim (((composite (fn-hstxa-p row))
           (encoding (<= (len (fn-store-event-encode (fn-hstxa-stxa row)))
                         (fn-store-publication-ceiling :accepted-statement))))
          (<= (fn-sbud-row-octets row)
              (fn-cvec-statement-figure (fn-sbud-row-memberships row))))
  :subject fn-sbud-row-octets
  :witness ((row *cvt-hstxa*))
  :breaks ((composite ((row *cvt-stxa-over*))
                      :logical "a wire statement event is no composite row; fn-hstxa-stxa reads it outside its guard")
           (encoding ((row *cvt-hstxa-over*))))
  :mutations ((figure-read-as-the-group-count
               (:conclusion (<= (fn-sbud-row-octets row) (fn-sbud-row-memberships row)))
               ((row *cvt-hstxa*))
               :fault "the statement figure read as the row's group count, not the publication ceiling")))
