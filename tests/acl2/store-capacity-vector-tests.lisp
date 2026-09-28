; Witnesses and teeth for books/store-capacity-vector (PRF-138, STO-020).
; The profile is packet 1's *pmt-old* with T raised to 8 (H = 250 000, the
; release ceiling R = 4 096): room for several open undertakings.
(in-package "ACL2")
(include-book "../../books/store-capacity-vector")
(include-book "../../books/store-intern")
(include-book "must-fail-checked")

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

;  An article record: 1 000 octets in one group (figure 2 664: 2 344 and
; its membership's 320 since lane membership-budget), and a wide
; record past its figure (store-budget-article-tests' shape).
(defconst *cvt-record*
  (fn-record-make 1 1 1 "<cvt@example.invalid>"
                  (make-list 1000 :initial-element 65) (list "fn.test")
                  "archive-a" "content-a" "release-a" 9 841000000))
(defconst *cvt-len* (len (fn-record-encode-impl *cvt-record*)))
(defconst *cvt-fig* (fn-sbud-article-figure 1000 1))
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
(defconst *cvt-a* (- (- *cvt-h* *cvt-fig*) (* 2 *cvt-r*)))
(assert-event
 (and (equal (fn-cvec-article-verdict-at *cvt-p* 1 *cvt-a* 1000 1 1)
             :admissible)
      (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-a* *cvt-record* 1) 8)
      (<= (len (fn-record-payload *cvt-record*)) 1000)
      (<= (len (fn-record-groups *cvt-record*)) 1)
      (fn-cvec-roomp *cvt-p* 2 (+ *cvt-a* *cvt-len*) 1)))
; Tooth, the verdict: PRF-129's article gate admits at H - figure - R with
; debt 1 open, and the vector refuses (budget 0): the open undertaking's
; release would be the room the article took.
(assert-event
 (and (equal (fn-smr-article-verdict-at *cvt-p* 1 (+ *cvt-a* *cvt-r*) 1000 1)
             :admissible)
      (equal (fn-cvec-article-verdict-at *cvt-p* 1 (+ *cvt-a* *cvt-r*) 1000 1 1)
             :unaffordable)
      (equal (fn-cvec-article-budget-for *cvt-p* 1 (+ *cvt-a* *cvt-r*)
                                         *cvt-record* 1)
             0)))
(must-fail-checked
 (defthm cvt-article-without-the-verdict
   (fn-cvec-roomp *cvt-p* 2 (+ *cvt-a* *cvt-r* *cvt-len*) 1)
   :rule-classes nil))
; Tooth, narrowness: a wide record past its figure at the witness state.
; A record in one group no longer serves (its membership's 320 octets cover
; the widening, lane membership-budget): the record in no group with every
; integer field at 2^32 encodes to 66 622 octets against its figure 66 619.
(defconst *cvt-tight*
  (fn-record-make 4294967296 4294967296 4294967296
                  (coerce (make-list 250 :initial-element #\a) 'string)
                  (make-list 65536 :initial-element 65) nil
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  4294967296 4294967296))
(assert-event
 (let ((r *cvt-tight*)
       (b (- (- *cvt-h* 66619) (* 2 *cvt-r*))))
   (and (fn-record-widep r)
        (equal (fn-sbud-article-figure 65536 0) 66619)
        (equal (len (fn-record-encode-impl r)) 66622)
        (equal (fn-cvec-article-verdict-at *cvt-p* 1 b 65536 0 1) :admissible)
        (not (fn-cvec-roomp *cvt-p* 2 (+ b (len (fn-record-encode-impl r))) 1)))))
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
      (equal (fn-sbud-row-octets *cvt-row*) (+ 1000 320))
      (equal (fn-cvec-record-figure *cvt-row*) *cvt-fig*)))
(defconst *cvt-article-history* (list *cvt-undertake* *cvt-row* *cvt-release*))
(defconst *cvt-article-octets*
  (+ (len (fn-store-event-encode *cvt-undertake*)) (+ 1000 320)
     (len (fn-store-event-encode *cvt-release*))))
; fn-cvec-admitted-history-keeps-the-vector and -from-init, with an article
; in the history: every hypothesis holds and so does each conclusion, at the
; article's 1 000 stored octets and its one membership's 320.
(assert-event
 (and (fn-bs-profile-admittedp *cvt-p*)
      (fn-cvec-roomp *cvt-p* 0 0 0)
      (fn-cvec-history-admittedp *cvt-p* 0 0 0 *cvt-article-history*)
      (equal (fn-sbud-record-octets *cvt-article-history*) *cvt-article-octets*)
      (fn-cvec-roomp *cvt-p* 3 *cvt-article-octets*
                     (fn-cvec-debt-from 0 *cvt-article-history*))
      (equal (fn-cvec-record-debt *cvt-article-history*) 0)
      (fn-profile-replay-within-boundp *cvt-p* *cvt-article-octets*)))
; fn-cvec-record-keeps-the-vector at the article, at the state its prefix
; leaves (one undertaking open).
(assert-event
 (let ((b (len (fn-store-event-encode *cvt-undertake*))))
   (and (fn-cvec-roomp *cvt-p* 1 b 1)
        (fn-cvec-record-admittedp *cvt-p* 1 b 1 *cvt-row*)
        (fn-cvec-roomp *cvt-p* 2 (+ b (fn-sbud-row-octets *cvt-row*))
                       (fn-cvec-debt-step :article 1)))))
; Tooth, the article arm's verdict: from H - R - 1 000 committed the vector
; holds, but the article's figure (2 664) does not fit beside the
; maintenance release, so the row is not admitted.
(assert-event
 (let ((b (- *cvt-h* (+ *cvt-r* 1000))))
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
(assert-event
 (and (not (equal (fn-cvec-article-verdict-at *cvt-p* 1 (+ *cvt-a* *cvt-r*)
                                              (fn-cvec-row-payload-length *cvt-row*) 1 1)
                  :admissible))
      (not (fn-cvec-roomp *cvt-p* (+ 1 1)
                          (+ *cvt-a* *cvt-r* (fn-cvec-row-payload-length *cvt-row*)) 1))))

; -----------------------------------------------------------------------------
; Lane membership-budget (2026-09-27).  KEYSTONE fn-cvec-article-refusal-word-
; names-the-memberships.  The same 1 000-octet article in one group and in
; ten, at one committed record, no open undertaking and B committed octets
; chosen so that the ten-group article's record fits beside the maintenance
; release but its 3 200 octets of memberships do not: the one-group article
; is admitted, the ten-group one refused, and the host's word for it is
; :memberships.  An article whose record alone does not fit stays
; :unaffordable, and any other word passes through.
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
(assert-event (equal *cvt-fig* 2664))
(assert-event (equal (fn-sbud-article-figure 1000 10) 7893))
(assert-event (equal (fn-sbud-article-record-figure 1000 10) 4693))
(defconst *cvt-mb* (+ 1 (- (- *cvt-h* *cvt-r*) 7893)))
; The one-group article: admitted (the budget is T), the word never asked.
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-mb* *cvt-record* 0) 8))
; The ten-group article: refused (budget 0), and without its memberships
; every gate would admit it.
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-mb* *cvt-record-10* 0) 0))
(assert-event (fn-cvec-article-memberships-refusedp *cvt-p* 1 *cvt-mb* 1000 10 0))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-p* 1 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :memberships))
; Its record too large even without memberships: :unaffordable, the store full.
(assert-event (equal (fn-cvec-article-budget-for *cvt-p* 1 *cvt-mb* *cvt-big-10* 0) 0))
(assert-event (not (fn-cvec-article-memberships-refusedp *cvt-p* 1 *cvt-mb* 10000 10 0)))
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-p* 1 *cvt-mb*
                                                   *cvt-big-10* 0)
                     :unaffordable))
; The count gate refusing (8 committed of T = 8): :unaffordable, not the
; memberships.
(assert-event (equal (fn-cvec-article-refusal-word :unaffordable *cvt-p* 8 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :unaffordable))
; Another word passes through, whatever the article.
(assert-event (equal (fn-cvec-article-refusal-word :duplicate *cvt-p* 1 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :duplicate))
(assert-event (equal (fn-cvec-article-refusal-word :refused *cvt-p* 1 *cvt-mb*
                                                   *cvt-record-10* 0)
                     :refused))

; -----------------------------------------------------------------------------
; The accepted-statement figure (lane bp-retention-leftovers, membership-
; budget's deferral).  Under *cvt-p* (R = 196 608, so the kind's count
; budget is T) a composite whose article is in ten groups is charged
; 196 608 + 3 200 = 199 808; at 46 097 committed octets the vector holds
; after the ceiling alone (the gate before this lane admitted it) but not
; after the figure: the ten-group composite is refused, a one-group one
; admitted.
(assert-event (equal (fn-cvec-statement-figure 10) 199808))
(assert-event (equal (fn-cvec-statement-figure 1) 196928))
(defconst *cvt-sb* 46097)
(assert-event (equal (fn-cvec-verdict-at *cvt-p* :accepted-statement 1 *cvt-sb* 0)
                     :admissible))
(assert-event (equal (fn-cvec-statement-verdict-at *cvt-p* 1 *cvt-sb* 10 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-statement-verdict-at *cvt-p* 1 *cvt-sb* 1 0)
                     :admissible))
; The bug the old gate had: its admission, followed by a composite charged
; its figure, leaves the vector short.
(assert-event (not (fn-cvec-roomp *cvt-p* 2 (+ *cvt-sb* 199808) 0)))

; fn-cvec-statement-admission-keeps-the-vector.  Witness: admitted one
; octet lower, a composite charged its whole figure keeps the vector.
(assert-event
 (and (equal (fn-cvec-statement-verdict-at *cvt-p* 1 (1- *cvt-sb*) 10 0)
             :admissible)
      (fn-cvec-roomp *cvt-p* 2 (+ (1- *cvt-sb*) 199808)
                     (fn-cvec-debt-step :accepted-statement 0))))
; Tooth, the verdict: at *cvt-sb* (refused) the same charge breaks it.
(must-fail-checked
 (defthm cvt-statement-without-the-verdict
   (fn-cvec-roomp *cvt-p* 2 (+ *cvt-sb* 199808) 0)
   :rule-classes nil))
; Tooth, the charge within the figure: admitted, one octet past the figure
; at the edge breaks it.
(must-fail-checked
 (defthm cvt-statement-past-its-figure
   (fn-cvec-roomp *cvt-p* 2 (+ (1- *cvt-sb*) 199809) 0)
   :rule-classes nil))

; fn-cvec-statement-row-within-its-figure over a retained composite: the
; held row in one group inside a small composite (charge = encoding + 320,
; within the figure) and inside one whose article record alone is past the
; ceiling (charge past the figure, encoding past the ceiling).
(defconst *cvt-stxa* (fn-stxa-make 1 5 5 0 '(1) '(1) '(1) '(1)))
(defconst *cvt-hstxa* (fn-hstxa-make *cvt-stxa* *cvt-row*))
(defconst *cvt-stxa-big*
  (fn-stxa-make 1 5 5 0 '(1) '(1) (make-list 200000 :initial-element 7) '(1)))
(defconst *cvt-hstxa-big* (fn-hstxa-make *cvt-stxa-big* *cvt-row*))
(assert-event
 (and (fn-hstxa-p *cvt-hstxa*)
      (equal (fn-store-event-kind *cvt-hstxa*) :accepted-statement)
      (equal (fn-sbud-row-memberships *cvt-hstxa*) 1)
      (equal (fn-sbud-row-octets *cvt-hstxa*)
             (+ (len (fn-store-event-encode *cvt-stxa*)) 320))
      (<= (fn-sbud-row-octets *cvt-hstxa*) (fn-cvec-statement-figure 1))
      (<= (len (fn-store-event-encode *cvt-stxa*)) 196608)))
(assert-event
 (and (fn-hstxa-p *cvt-hstxa-big*)
      (< 196608 (len (fn-store-event-encode *cvt-stxa-big*)))
      (< (fn-cvec-statement-figure 1) (fn-sbud-row-octets *cvt-hstxa-big*))))
; The history arm: the small composite at *cvt-sb* is admitted and keeps
; the vector.
(assert-event (fn-cvec-record-admittedp *cvt-p* 1 *cvt-sb* 0 *cvt-hstxa*))
(assert-event (not (fn-cvec-record-admittedp *cvt-p* 1 *cvt-sb* 0 *cvt-hstxa-big*)))

; The developer `store post''s word (fn-cvec-article-verdict-word): the
; ten-group article at *cvt-mb* is refused for its memberships, the
; one-group one admitted, the ten-group article past its record figure
; refused as the store's budget, and the count gate refusing is not the
; memberships.
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 1 *cvt-mb* 1000 10 0)
                     :memberships))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 1 *cvt-mb* 1000 1 0)
                     :admissible))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 1 *cvt-mb* 10000 10 0)
                     :unaffordable))
(assert-event (equal (fn-cvec-article-verdict-word *cvt-p* 8 *cvt-mb* 1000 10 0)
                     :unaffordable))
