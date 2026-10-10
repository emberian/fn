; Teeth for books/store-budget-article (memory landing 3+4, RULINGS
; 2026-10-09 21:50: the history budget H charges a held article its payload
; octets alone; its record figure is the encoding ceiling, and its
; memberships and header columns are the memory equation's MEMBERSHIPS and
; HCHARGE terms, books/memory-model.lisp).  The witness is packet 1's
; 32 768-octet article in 400 groups (tests/acl2/profile-monotonicity-tests).
(in-package "ACL2")
(include-book "profile-monotonicity-tests")
(include-book "../../books/store-budget-article")
(include-book "must-fail-checked")

(defconst *sbat-fig* (fn-sbud-article-figure 32768 400))
(defconst *sbat-gate* (fn-sbud-article-gate-figure 32768 400))
; The record figure is the encoding ceiling; the gate charges the payload.
(assert-event (equal *sbat-fig* 138251))
(assert-event (equal *sbat-fig* (fn-record-encoded-octets-ceiling 32768 400)))
(assert-event (equal *sbat-gate* 32768))
(assert-event (<= *pmt-len* *sbat-fig*))
(assert-event (equal (len (fn-record-payload *pmt-record*)) *sbat-gate*))

; KEYSTONE fn-sbud-article-verdict-keeps-history, reachable witness: at
; H - 32 768 committed octets (H = 250 000) the verdict admits the article,
; the served prepare is handed the article budget, and the committed octets
; with its payload are within H.  The 400 groups no longer cost H: they are
; the memory gate's (books/admission-memory.lisp).
(defconst *sbat-safe* (- 250000 *sbat-gate*))
(assert-event
 (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 *sbat-safe* 32768 400) :admissible)
      (equal (fn-sbud-article-budget-for *pmt-old* *sbat-safe* *pmt-record*)
             (fn-sbud-budget *pmt-old* :article))
      (fn-profile-replay-within-boundp
       *pmt-old* (+ *sbat-safe* (len (fn-record-payload *pmt-record*))))))
; One octet more committed and the gate refuses, the prepare's budget is 0.
(assert-event (equal (fn-sbud-article-verdict-at *pmt-old* 1 (1+ *sbat-safe*) 32768 400)
                     :unaffordable))
(assert-event (equal (fn-sbud-article-budget-for *pmt-old* (1+ *sbat-safe*) *pmt-record*) 0))
(assert-event (not (fn-sbud-admitp (fn-sbud-article-budget-for *pmt-old* (1+ *sbat-safe*)
                                                               *pmt-record*)
                                   1)))
(assert-event (not (fn-profile-replay-within-boundp
                    *pmt-old* (+ (1+ *sbat-safe*) (len (fn-record-payload *pmt-record*))))))

; Hypothesis: the verdict.  At H - 32 767 the payload overflows H.
(must-fail-checked
 (defthm sbat-without-the-verdict
   (implies (<= (len (fn-record-payload record)) (nfix payload-length))
            (fn-profile-replay-within-boundp
             profile (+ bytes-used (len (fn-record-payload record)))))
   :rule-classes nil))
; Hypothesis: the payload count.  Asked for (0, 1), the 32 768-octet article
; is admitted at H and overflows.
(assert-event
 (and (equal (fn-sbud-article-verdict-at *pmt-old* 1 250000 0 1) :admissible)
      (not (fn-profile-replay-within-boundp
            *pmt-old* (+ 250000 (len (fn-record-payload *pmt-record*)))))))
; The widths no longer matter to H: the same article with sequence, txid,
; generation and stamp at 2^32 is charged its payload, within H at the same
; committed octets (the deleted producer-width twin).
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
      (equal (fn-sbud-article-budget-for *pmt-old* *sbat-safe* *sbat-wide*)
             (fn-sbud-budget *pmt-old* :article))
      (fn-profile-replay-within-boundp
       *pmt-old* (+ *sbat-safe* (len (fn-record-payload *sbat-wide*))))))

; ---------------------------------------------------------------------------
; The record figure (fn-sbud-article-figure-bounds-the-record and
; -bounds-the-producer-record): the encoding ceiling the log and the open's
; input bound use (books/store-replay-bound.lisp).
; Hypothesis: narrowness (bounds-the-record).  A record at (195 264, 1) with
; 256-octet fields is 196 589 octets narrow, within its figure 196 608, and
; 196 609 with its five integer fields at 2^32: one octet past it.
(defun sbat-full-record (n)
  (fn-record-make n n n (coerce (make-list 250 :initial-element #\m) 'string)
                  (make-list 195264 :initial-element 65)
                  (list (coerce (make-list 256 :initial-element #\a) 'string))
                  (coerce (make-list 256 :initial-element #\o) 'string)
                  (coerce (make-list 256 :initial-element #\s) 'string)
                  (coerce (make-list 256 :initial-element #\e) 'string) n n))
(assert-event (equal (fn-sbud-article-figure 195264 1) 196608))
(assert-event
 (let ((r (sbat-full-record 4294967296)))
   (and (fn-record-widep r)
        (equal (len (fn-record-encode r)) 196609)
        (< (fn-sbud-article-figure 195264 1) (len (fn-record-encode r))))))
(assert-event
 (let ((r (sbat-full-record 4294967295)))
   (and (not (fn-record-widep r))
        (equal (len (fn-record-encode r)) 196589)
        (<= (len (fn-record-encode r)) (fn-sbud-article-figure 195264 1)))))
(defconst *sbat-p* (fn-bs-profile-set-fields *pmt-old* '((2 . 1000000))))
(assert-event (fn-bs-profile-admittedp *sbat-p*))
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
      (fn-record-widep *sbat-tight-charge*)
      (<= (len (fn-record-payload *sbat-tight-charge*)) 65536)
      (<= (len (fn-record-groups *sbat-tight-charge*)) 0)
      (equal (fn-sbud-article-figure 65536 0) 66619)
      (equal (len (fn-record-encode *sbat-tight-charge*)) 66622)))
; Hypothesis: the charge within u32 (bounds-the-producer-record); the record
; above is three octets past its figure.
(must-fail-checked
 (defthm sbat-producer-figure-without-the-charge-hypothesis
   (implies (and (<= (len (fn-record-payload record)) (nfix payload-length))
                 (<= (len (fn-record-groups record)) (nfix group-count)))
            (<= (len (fn-record-encode record))
                (fn-sbud-article-figure payload-length group-count)))
   :rule-classes nil))
; Its charge is kept, though: admitted at H - 65 536 it keeps H, wide.
(assert-event
 (and (equal (fn-sbud-article-verdict-at *sbat-p* 1 (- 1000000 65536) 65536 0) :admissible)
      (fn-profile-replay-within-boundp
       *sbat-p* (+ (- 1000000 65536) (len (fn-record-payload *sbat-tight-charge*))))))
