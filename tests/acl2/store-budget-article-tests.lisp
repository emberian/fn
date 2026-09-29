; Teeth for books/store-budget-article (packet 1 decided: the history gate
; charges an article at its own worst case).  The witness is packet 1's
; 135 641-octet article in 400 groups (tests/acl2/profile-monotonicity-tests):
; admitted by the old gate and then refused at the next open; refused by the
; new gate where it would overflow H, admitted and safe where it fits.
(in-package "ACL2")
(include-book "profile-monotonicity-tests")
(include-book "../../books/store-budget-article")
(include-book "must-fail-checked")

(defconst *sbat-fig* (fn-sbud-article-figure 32768 400))
; Lane heap-pool: the gate charges the record figure and the header charge at
; its worst (8 x 32,768 and 12 x 250).
(defconst *sbat-gate* (fn-sbud-article-gate-figure 32768 400))
(assert-event (equal *sbat-gate* (+ *sbat-fig* (* 8 32768) 3000)))
(assert-event (equal *sbat-fig* 266251))
(assert-event (<= *pmt-len* *sbat-fig*))
; Lane membership-budget: the figure is the record ceiling (138 251) and the
; 400 memberships at 320 octets each (128 000).  Under packet 1's H of
; 250 000 the crosspost can never be paid for: refused even into an empty
; store, where its record alone would fit.
(assert-event (equal (fn-sbud-article-record-figure 32768 400) 403395))
(assert-event (equal *sbat-fig* (+ 138251 (* 400 *fn-sbud-membership-octets*))))
(assert-event (equal (fn-sbud-article-verdict-at *pmt-old* 0 0 32768 400) :unaffordable))
; (Since lane heap-pool its header charge at its worst alone, 265,144, is past
; H too: the record without its memberships, 403,395 with that charge.)
(assert-event (equal (fn-sbud-article-record-figure 32768 400)
                     (+ 138251 (fn-sbud-article-header-figure 32768))))
(assert-event (not (fn-bs-history-admissiblep *pmt-old* 0 (fn-sbud-article-record-figure 32768 400))))
(assert-event (fn-bs-history-admissiblep *pmt-old* 0 (fn-record-encoded-octets-ceiling 32768 400)))
; The witnesses below that admit it use the same profile with H = 1 000 000
; (500 000 before lane heap-pool's header charge).
(defconst *sbat-p* (fn-bs-profile-set-fields *pmt-old* '((2 . 1000000))))
(assert-event (fn-bs-profile-admittedp *sbat-p*))
(assert-event (equal (fn-sbud-budget *sbat-p* :article) (fn-sbud-budget *pmt-old* :article)))

; Before: the old gate admits it at 184 462 committed octets and the total
; is past H (the open refuses).  After: the article verdict refuses it there,
; and the served prepare's budget is 0.
(assert-event (equal (fn-sbud-verdict-at *pmt-old* :article 1 *pmt-used-octets*)
                     :admissible))
(assert-event (not (fn-profile-replay-within-boundp
                    *pmt-old* (+ *pmt-used-octets* *pmt-len*))))
(assert-event (equal (fn-sbud-article-verdict-at *pmt-old* 1 *pmt-used-octets*
                                                 32768 400)
                     :unaffordable))
(assert-event (equal (fn-sbud-article-budget-for *pmt-old* *pmt-used-octets*
                                                 *pmt-record*)
                     0))
(assert-event (not (fn-sbud-admitp
                    (fn-sbud-article-budget-for *pmt-old* *pmt-used-octets*
                                                *pmt-record*)
                    1)))

; KEYSTONE fn-sbud-article-verdict-keeps-history, reachable witness: at
; H - 531 395 committed octets (H = 1 000 000) the verdict admits the article,
; which is narrow and within the counts, and the total is within H.
(defconst *sbat-safe* (- 1000000 *sbat-gate*))
(assert-event
 (and (equal (fn-sbud-article-verdict-at *sbat-p* 1 *sbat-safe* 32768 400)
             :admissible)
      (not (fn-record-widep *pmt-record*))
      (<= (len (fn-record-payload *pmt-record*)) 32768)
      (<= (len (fn-record-groups *pmt-record*)) 400)
      (fn-profile-replay-within-boundp *sbat-p* (+ *sbat-safe* *pmt-len*))))
(assert-event (equal (fn-sbud-article-budget-for *sbat-p* *sbat-safe*
                                                 *pmt-record*)
                     4))
; One octet more committed and the gate refuses.
(assert-event (equal (fn-sbud-article-verdict-at *sbat-p* 1 (1+ *sbat-safe*)
                                                 32768 400)
                     :unaffordable))

; Hypothesis: the verdict.  At 184 462 the verdict refuses and the total is
; past H (above).
(must-fail-checked
 (defthm sbat-without-the-verdict
   (implies (and (not (fn-record-widep record))
                 (<= (len (fn-record-payload record)) (nfix payload-length))
                 (<= (len (fn-record-groups record)) (nfix group-count)))
            (fn-profile-replay-within-boundp
             profile (+ bytes-used (len (fn-record-encode record)))))
   :rule-classes nil))
; Hypothesis: narrowness.  A record at (195 264, 1) with 256-octet fields is
; 196 589 octets narrow and 196 609 with its five integer fields at 2^32;
; since lane membership-budget its one membership's 320 octets cover that
; widening, so the tooth is a record in no group (below, *sbat-tight-charge*:
; wide, 66 622 octets against its figure 66 619).
(defun sbat-full-record (n)
  (fn-record-make n n n (coerce (make-list 250 :initial-element #\m) 'string)
                  (make-list 195264 :initial-element 65)
                  (list (coerce (make-list 256 :initial-element #\a) 'string))
                  (coerce (make-list 256 :initial-element #\o) 'string)
                  (coerce (make-list 256 :initial-element #\s) 'string)
                  (coerce (make-list 256 :initial-element #\e) 'string) n n))
(assert-event (equal (fn-sbud-article-figure 195264 1) 196928))
(assert-event
 (let ((r (sbat-full-record 4294967296)))
   (and (fn-record-widep r)
        (<= (len (fn-record-encode r)) (fn-sbud-article-figure 195264 1)))))
(assert-event
 (let ((r (sbat-full-record 4294967295)))
   (and (not (fn-record-widep r))
        (<= (len (fn-record-encode r)) (fn-sbud-article-figure 195264 1)))))
; Hypothesis: the payload count.  Asked for (0, 1), an article of 32 768
; octets in one group is admitted at H - figure(0, 1) and overflows.  (The
; 400-group article no longer serves: asked for (0, 400) its memberships'
; 128 000 octets cover the payload.)
(defconst *sbat-one*
  (fn-record-make 1 1 1 "<sbat-one@example.invalid>"
                  (make-list 32768 :initial-element 65) (list "fn.test")
                  "archive-a" "content-a" "release-a" 9 841000000))
(assert-event
 (let ((b (- 250000 (fn-sbud-article-figure 0 1))))
   (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 b 0 1) :admissible)
        (not (fn-record-widep *sbat-one*))
        (<= (len (fn-record-groups *sbat-one*)) 1)
        (not (fn-profile-replay-within-boundp
              *pmt-old* (+ b (len (fn-record-encode *sbat-one*))))))))
; Hypothesis: the group count.  Asked for (32 768, 1), the 400-group article
; is admitted at H - figure(32 768, 1) (H = 500 000) and overflows.
; (Lane heap-pool: at the gate the 32,768-octet payload's header figure covers
; its 399 groups more; the tooth is the same 400 groups on a 2-octet payload,
; asked for (2, 1).)
(defconst *sbat-many*
  (fn-record-make 1 1 1 "<sbat-many@example.invalid>" (list 65 65)
                  (fn-record-groups *pmt-record*)
                  "archive-a" "content-a" "release-a" 9 841000000))
(assert-event
 (let ((b (- 1000000 (fn-sbud-article-gate-figure 2 1))))
   (and (equal (fn-sbud-article-verdict-at *sbat-p* 1 b 2 1) :admissible)
        (<= (len (fn-record-payload *sbat-many*)) 2)
        (equal (len (fn-record-groups *sbat-many*)) 400)
        (not (fn-profile-replay-within-boundp
              *sbat-p* (+ b (len (fn-record-encode *sbat-many*))))))))

; ---------------------------------------------------------------------------
; PRF-126: KEYSTONE fn-sbud-article-verdict-keeps-history-at-producer-width.
; Reachable-shape witness: packet 1's record with sequence, txid, generation
; and stamp moved to 2^32 (schema 2, what the allocator and clock produce
; past 2^32 - 1) and its charge kept: admitted at H - 266 251 as before, and
; the total is still within H (= 500 000), with no narrowness premise.
(defconst *sbat-wide*
  (fn-record-make 4294967296 4294967296 4294967296
                  (fn-record-msgid *pmt-record*) (fn-record-payload *pmt-record*)
                  (fn-record-groups *pmt-record*)
                  (fn-record-obligation-id *pmt-record*)
                  (fn-record-content-subject *pmt-record*)
                  (fn-record-release-evidence *pmt-record*)
                  (fn-record-charge *pmt-record*) 4294967296))
(assert-event
 (and (fn-record-p *sbat-wide*)
      (fn-record-widep *sbat-wide*)
      (fn-record-uint32p (fn-record-charge *sbat-wide*))
      (equal (fn-sbud-article-verdict-at *sbat-p* 1 *sbat-safe* 32768 400)
             :admissible)
      (fn-profile-replay-within-boundp
       *sbat-p* (+ *sbat-safe* (len (fn-record-encode *sbat-wide*))))))
; The charge hypothesis, affirmatively, against the record figure: the
; tightest record with no group, a 65 536-octet payload, every other field at
; its ceiling and sequence, txid, generation, stamp AND charge at 2^32
; encodes to 66 622 octets, three past its figure 66 619
; (fn-sbud-article-figure-bounds-the-producer-record).  At the gate (lane
; heap-pool) its header figure covers the three: the verdict at H - its gate
; figure admits it and the total is within H
; (fn-sbud-article-verdict-keeps-history-for-every-record).
(defconst *sbat-tight-charge*
  (fn-record-make 4294967296 4294967296 4294967296
                  (coerce (make-list 250 :initial-element #\a) 'string)
                  (make-list 65536 :initial-element 65) nil
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  (coerce (make-list 256 :initial-element #\m) 'string)
                  4294967296 4294967296))
(assert-event
 (and (fn-record-p *sbat-tight-charge*)
      (not (fn-record-uint32p (fn-record-charge *sbat-tight-charge*)))
      (equal (fn-sbud-article-figure 65536 0) 66619)
      (equal (len (fn-record-encode *sbat-tight-charge*)) 66622)
      (< (fn-sbud-article-figure 65536 0) (len (fn-record-encode *sbat-tight-charge*)))
      (equal (fn-sbud-article-verdict-at *sbat-p* 1
                                         (- 1000000 (fn-sbud-article-gate-figure 65536 0))
                                         65536 0)
             :admissible)
      (fn-profile-replay-within-boundp
       *sbat-p* (+ (- 1000000 (fn-sbud-article-gate-figure 65536 0))
                   (len (fn-record-encode *sbat-tight-charge*))))))
; The same record is the narrowness hypothesis's tooth for
; fn-sbud-article-figure-bounds-the-record: wide, within its counts (65 536,
; 0), and three octets past its record figure.
(assert-event
 (and (fn-record-widep *sbat-tight-charge*)
      (<= (len (fn-record-payload *sbat-tight-charge*)) 65536)
      (<= (len (fn-record-groups *sbat-tight-charge*)) 0)))
(must-fail-checked
 (defthm sbat-producer-width-without-the-charge-hypothesis
   (implies (and (equal (fn-sbud-article-verdict-at profile used bytes-used
                                                    payload-length group-count)
                        :admissible)
                 (<= (len (fn-record-payload record)) (nfix payload-length))
                 (<= (len (fn-record-groups record)) (nfix group-count)))
            (fn-profile-replay-within-boundp
             profile (+ bytes-used (len (fn-record-encode record)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory) :use ((:instance fn-sbud-article-verdict-keeps-history-at-producer-width))))))
