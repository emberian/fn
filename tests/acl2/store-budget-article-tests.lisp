; Teeth for books/store-budget-article (packet 1 decided: the history gate
; charges an article at its own worst case).  The witness is packet 1's
; 135 641-octet article in 400 groups (tests/acl2/profile-monotonicity-tests):
; admitted by the old gate and then refused at the next open; refused by the
; new gate where it would overflow H, admitted and safe where it fits.
(in-package "ACL2")
(include-book "profile-monotonicity-tests")
(include-book "../../books/store-budget-article")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sbat-fig* (fn-sbud-article-figure 32768 400))
(assert-event (equal *sbat-fig* 138251))
(assert-event (<= *pmt-len* *sbat-fig*))

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
; H - 138 251 committed octets the verdict admits the article, which is
; narrow and within the counts, and the total is within H.
(defconst *sbat-safe* (- 250000 *sbat-fig*))
(assert-event
 (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 *sbat-safe* 32768 400)
             :admissible)
      (not (fn-record-widep *pmt-record*))
      (<= (len (fn-record-payload *pmt-record*)) 32768)
      (<= (len (fn-record-groups *pmt-record*)) 400)
      (fn-profile-replay-within-boundp *pmt-old* (+ *sbat-safe* *pmt-len*))))
(assert-event (equal (fn-sbud-article-budget-for *pmt-old* *sbat-safe*
                                                 *pmt-record*)
                     4))
; One octet more committed and the gate refuses.
(assert-event (equal (fn-sbud-article-verdict-at *pmt-old* 1 (1+ *sbat-safe*)
                                                 32768 400)
                     :unaffordable))

; Hypothesis: the verdict.  At 184 462 the verdict refuses and the total is
; past H (above).
(must-fail
 (defthm sbat-without-the-verdict
   (implies (and (not (fn-record-widep record))
                 (<= (len (fn-record-payload record)) (nfix payload-length))
                 (<= (len (fn-record-groups record)) (nfix group-count)))
            (fn-profile-replay-within-boundp
             profile (+ bytes-used (len (fn-record-encode record)))))
   :rule-classes nil))
; Hypothesis: narrowness.  A record at (195 264, 1) with 256-octet fields is
; 196 589 octets narrow and 196 609 with its five integer fields at 2^32:
; admitted at H - 196 608, the wide one is one octet past H.
(defun sbat-full-record (n)
  (fn-record-make n n n (coerce (make-list 250 :initial-element #\m) 'string)
                  (make-list 195264 :initial-element 65)
                  (list (coerce (make-list 256 :initial-element #\a) 'string))
                  (coerce (make-list 256 :initial-element #\o) 'string)
                  (coerce (make-list 256 :initial-element #\s) 'string)
                  (coerce (make-list 256 :initial-element #\e) 'string) n n))
(assert-event (equal (fn-sbud-article-figure 195264 1) 196608))
(assert-event
 (let ((r (sbat-full-record 4294967296)) (b (- 250000 196608)))
   (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 b 195264 1) :admissible)
        (fn-record-widep r)
        (<= (len (fn-record-payload r)) 195264)
        (<= (len (fn-record-groups r)) 1)
        (not (fn-profile-replay-within-boundp
              *pmt-old* (+ b (len (fn-record-encode r))))))))
(assert-event
 (let ((r (sbat-full-record 4294967295)) (b (- 250000 196608)))
   (and (not (fn-record-widep r))
        (fn-profile-replay-within-boundp
         *pmt-old* (+ b (len (fn-record-encode r)))))))
; Hypothesis: the payload count.  Asked for (0, 400), the article (32 768,
; 400) is admitted at H - figure(0, 400) and overflows.
(assert-event
 (let ((b (- 250000 (fn-sbud-article-figure 0 400))))
   (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 b 0 400) :admissible)
        (<= (len (fn-record-groups *pmt-record*)) 400)
        (not (fn-profile-replay-within-boundp *pmt-old* (+ b *pmt-len*))))))
; Hypothesis: the group count.  Asked for (32 768, 1), the 400-group article
; is admitted at H - figure(32 768, 1) and overflows.
(assert-event
 (let ((b (- 250000 (fn-sbud-article-figure 32768 1))))
   (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 b 32768 1) :admissible)
        (<= (len (fn-record-payload *pmt-record*)) 32768)
        (not (fn-profile-replay-within-boundp *pmt-old* (+ b *pmt-len*))))))

; fn-profile-upgrade-keeps-article-verdict: the upgrade that raised A (packet
; 1's counterexample 2 for the profile-derived figure) keeps this verdict.
(assert-event (fn-profile-upgradep *pmt-old* *pmt-new*))
(assert-event (equal (fn-sbud-article-verdict-at *pmt-new* 1 *sbat-safe* 32768 400)
                     :admissible))
; Its hypothesis: not an upgrade (H lowered to 200 000) refuses the state.
(defconst *sbat-lower-h* (fn-bs-profile-set-fields *pmt-old* '((3 . 200000))))
(assert-event (fn-bs-profile-validp *sbat-lower-h*))
(assert-event (not (fn-profile-upgradep *pmt-old* *sbat-lower-h*)))
(assert-event (equal (fn-sbud-article-verdict-at *sbat-lower-h* 1 *sbat-safe*
                                                 32768 400)
                     :unaffordable))
