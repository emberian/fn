; Teeth for books/number-durability.lisp (PRF-903, lane durability-bugs).
;
; The fixture is tests/acl2/config-physical-replay-tests.lisp's history
; (the default configuration, a capacity decrease and an increase; an
; undertaking and its release; an article of fn.test at txid 7), extended by
; a second article at txid 8.  XS is the history a reader saw (the first
; article's number visible), YS the history recovery opens after a crash
; that kept the second article's record, ZS a rival history that is NOT an
; extension of XS (another article took txid 7 and number 1: what a lost
; VISIBLE number would look like), BS an extension of XS whose last record
; does not replay (the open refuses it).
;
; Per keystone: a reachable witness asserting every hypothesis and the
; conclusion; then, per retained hypothesis, a value at which the others
; hold and it fails, asserted, the conclusion false there, and a must-fail
; of the theorem without it.

(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/number-durability")
(include-book "held-rows-tests")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *ndt-stamp* *fn-cfg-default-stamp*)
(defconst *ndt-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-cpr" "subject" "evidence" 10))
(defconst *ndt-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-cpr" "subject" "evidence" 0))
(defconst *ndt-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *ndt-stamp*))
(defconst *ndt-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *ndt-stamp*))
(defconst *ndt-configs*
  (list *fn-cfg-default-record* *ndt-decrease* *ndt-increase*))

(defconst *ndt-a1*
  (fn-record-make 2 7 7 "<one@example.invalid>" '(65) '("fn.test")
                  "archive-one" "subject" "evidence" 2 841000000))
(defconst *ndt-a2*
  (fn-record-make 3 8 8 "<two@example.invalid>" '(66) '("fn.test")
                  "archive-two" "subject" "evidence" 2 841000001))
(defconst *ndt-rival*
  (fn-record-make 2 7 7 "<rival@example.invalid>" '(67) '("fn.test")
                  "archive-rival" "subject" "evidence" 2 841000002))
(defconst *ndt-bad*
  (fn-record-make 9 8 7 "<bad@example.invalid>" '(68) '("fn.test")
                  "archive-bad" "subject" "evidence" 2 841000003))

(defconst *ndt-xs* (fn-hrt-rows (list *ndt-undertake* *ndt-release* *ndt-a1*) nil 0))
(defconst *ndt-ys* (fn-hrt-rows (list *ndt-undertake* *ndt-release* *ndt-a1* *ndt-a2*) nil 0))
(defconst *ndt-zs* (fn-hrt-rows (list *ndt-undertake* *ndt-release* *ndt-rival*) nil 0))
(defconst *ndt-bs* (fn-hrt-rows (list *ndt-undertake* *ndt-release* *ndt-a1* *ndt-bad*) nil 0))
(defconst *ndt-f* 9)

(defun ndt-articles (events)
  (fn-state-articles (fn-node-acceptance (fn-cst-replay-node *ndt-configs* events *ndt-f*))))
(defun ndt-nexts (events)
  (fn-state-nexts (fn-node-acceptance (fn-cst-replay-node *ndt-configs* events *ndt-f*))))
(defun ndt-view-at (version raw-events)
  ; A view at VERSION whose archive and raw list are RAW-EVENTS' replay
  ; (the live history's prefix of that length, for an honest view).
  (let ((acc (fn-node-acceptance (fn-cst-replay-node *ndt-configs* raw-events *ndt-f*))))
    (fn-own-view-make-visible version *ndt-f* (fn-ctl-visible-state acc nil nil) nil nil nil nil
                              (fn-state-articles acc) nil nil)))
(defun ndt-owner (live view)
  (fn-own-make (fn-sn-open-state (fn-cpo-open-observed *ndt-configs* *ndt-f* live))
               view nil 0 0 nil nil nil nil nil nil nil nil nil nil))
(defconst *ndt-o* (ndt-owner *ndt-ys* (ndt-view-at 3 (fn-own-take 3 *ndt-ys*))))
(defun ndt-recovered-articles (o recovered)
  (fn-state-articles (fn-node-acceptance
    (fn-sn-node (fn-sn-open-state (fn-cpo-open-observed (fn-sn-config-history (fn-own-store o)) *ndt-f* recovered))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ndur-replay-extension-keeps-every-number.
; Hypotheses: (H1) YS extends XS, (H2) YS opens, (H3) XS's replay holds N.

(defun ndt-k1-concl (xs ys g n)
  (and (equal (fn-ndur-holder g n (ndt-articles ys)) (fn-ndur-holder g n (ndt-articles xs)))
       (< n (fn-next-number g (ndt-nexts ys)))))

; Witness: fn.test 1 is <one> before the crash and after it; fn.test's next
; number is 2 on the view and 3 after the recovered second article.
(assert! (fn-sf-prefixp *ndt-xs* *ndt-ys*))
(assert! (fn-cst-replay-node *ndt-configs* *ndt-ys* *ndt-f*))
(assert! (equal (fn-ndur-holder "fn.test" 1 (ndt-articles *ndt-xs*)) "<one@example.invalid>"))
(assert! (equal (fn-ndur-holder "fn.test" 1 (ndt-articles *ndt-ys*)) "<one@example.invalid>"))
(assert! (equal (ndt-nexts *ndt-ys*) '(("fn.letters" . 1) ("fn.test" . 3))))
(assert! (ndt-k1-concl *ndt-xs* *ndt-ys* "fn.test" 1))

; H1 fails: ZS (another article at txid 7 holding fn.test 1) opens and XS
; holds 1, but ZS does not extend XS; the conclusion is false.
(assert! (not (fn-sf-prefixp *ndt-xs* *ndt-zs*)))
(assert! (fn-cst-replay-node *ndt-configs* *ndt-zs* *ndt-f*))
(assert! (fn-ndur-holder "fn.test" 1 (ndt-articles *ndt-xs*)))
(assert! (not (ndt-k1-concl *ndt-xs* *ndt-zs* "fn.test" 1)))
(must-fail-checked
 (defthm ndt-k1-without-extension
   (implies (and (fn-cst-replay-node configs ys f2)
                 (fn-ndur-holder g n (fn-state-articles
                                      (fn-node-acceptance (fn-cst-replay-node configs xs f1)))))
            (equal (fn-ndur-holder g n (fn-state-articles
                                        (fn-node-acceptance (fn-cst-replay-node configs ys f2))))
                   (fn-ndur-holder g n (fn-state-articles
                                        (fn-node-acceptance (fn-cst-replay-node configs xs f1))))))))

; H2 fails: BS extends XS and XS holds 1, but BS's last record does not
; replay (sequence 9 after 2): no node, and 1 is held by nobody.
(assert! (fn-sf-prefixp *ndt-xs* *ndt-bs*))
(assert! (not (fn-cst-replay-node *ndt-configs* *ndt-bs* *ndt-f*)))
(assert! (not (ndt-k1-concl *ndt-xs* *ndt-bs* "fn.test" 1)))
(must-fail-checked
 (defthm ndt-k1-without-open
   (implies (and (fn-sf-prefixp xs ys)
                 (fn-ndur-holder g n (fn-state-articles
                                      (fn-node-acceptance (fn-cst-replay-node configs xs f1)))))
            (< n (fn-next-number g (fn-state-nexts
                                    (fn-node-acceptance (fn-cst-replay-node configs ys f2))))))))

; H3 fails: fn.test 2 was not issued on XS (its next number is 2); after
; the recovery that kept the second article, 2 is <two>: legitimately a
; first issue, and the conclusion (same holder, below the next) is false.
(assert! (not (fn-ndur-holder "fn.test" 2 (ndt-articles *ndt-xs*))))
(assert! (equal (fn-ndur-holder "fn.test" 2 (ndt-articles *ndt-ys*)) "<two@example.invalid>"))
(assert! (not (ndt-k1-concl *ndt-xs* *ndt-ys* "fn.test" 2)))
(must-fail-checked
 (defthm ndt-k1-without-issue
   (implies (and (fn-sf-prefixp xs ys)
                 (fn-cst-replay-node configs ys f2))
            (equal (fn-ndur-holder g n (fn-state-articles
                                        (fn-node-acceptance (fn-cst-replay-node configs ys f2))))
                   (fn-ndur-holder g n (fn-state-articles
                                        (fn-node-acceptance (fn-cst-replay-node configs xs f1))))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ndur-recovery-keeps-every-visible-number.  *NDT-O* is a live
; owner on the opened history YS whose view is at version 3 (XS: fn.test 1
; visible, the second article's record written but not in the view).
; Hypotheses: (R1) the view is the configured replay of its prefix, (R2) its
; version is at most FENCED, (R3) the recovered history extends the first
; FENCED live records, (R4) the host's open of it succeeds, (R5) the view
; holds N.

(defun ndt-k2-hyps-but (o fenced recovered g n skip)
  (let* ((st (fn-own-store o))
         (live (fn-sf-records (fn-sn-files st))))
    (and (or (eq skip :r1) (fn-ocl-view-historyp o))
         (or (eq skip :r2) (<= (fn-own-view-version (fn-own-view o)) (nfix fenced)))
         (or (eq skip :r3) (fn-sf-prefixp (fn-own-take fenced live) recovered))
         (or (eq skip :r4) (fn-sn-open-okp (fn-cpo-open-observed (fn-sn-config-history st)
                                                                  *ndt-f* recovered)))
         (or (eq skip :r5) (and (fn-ndur-holder g n (fn-own-view-raw (fn-own-view o))) t)))))

(defun ndt-k2-concl (o recovered g n)
  (let* ((st (fn-own-store o))
         (node (fn-sn-node (fn-sn-open-state
                            (fn-cpo-open-observed (fn-sn-config-history st) *ndt-f* recovered)))))
    (and (equal (fn-ndur-holder g n (fn-state-articles (fn-node-acceptance node)))
                (fn-ndur-holder g n (fn-own-view-raw (fn-own-view o))))
         (< n (fn-next-number g (fn-state-nexts (fn-node-acceptance node)))))))

; Witness: power lost after the view's three records were fenced and before
; the second article's: recovery opens XS; fn.test 1 is <one>, next 2.
(assert! (ndt-k2-hyps-but *ndt-o* 3 *ndt-xs* "fn.test" 1 nil))
(assert! (not (fn-sf-prefixp *ndt-ys* *ndt-xs*)))
(assert! (ndt-k2-concl *ndt-o* *ndt-xs* "fn.test" 1))
(assert! (equal (ndt-recovered-articles *ndt-o* *ndt-xs*) (ndt-articles *ndt-xs*)))

; R1 fails: a view claiming the rival holds fn.test 1 is not the replay of
; the live prefix; recovery of XS gives 1 to <one>.
(defconst *ndt-o-lying* (ndt-owner *ndt-ys* (ndt-view-at 3 *ndt-zs*)))
(assert! (not (fn-ocl-view-historyp *ndt-o-lying*)))
(assert! (ndt-k2-hyps-but *ndt-o-lying* 3 *ndt-xs* "fn.test" 1 :r1))
(assert! (not (ndt-k2-concl *ndt-o-lying* *ndt-xs* "fn.test" 1)))

; R2 fails: only two records were fenced when the view showed three -- the
; visible article was not durable -- and the recovered history is the rival.
(assert! (not (<= 3 2)))
(assert! (ndt-k2-hyps-but *ndt-o* 2 *ndt-zs* "fn.test" 1 :r2))
(assert! (not (ndt-k2-concl *ndt-o* *ndt-zs* "fn.test" 1)))

; R3 fails: three records fenced, but the recovered history does not keep
; them (a device that lost fenced writes).
(assert! (not (fn-sf-prefixp (fn-own-take 3 *ndt-ys*) *ndt-zs*)))
(assert! (ndt-k2-hyps-but *ndt-o* 3 *ndt-zs* "fn.test" 1 :r3))
(assert! (not (ndt-k2-concl *ndt-o* *ndt-zs* "fn.test" 1)))

; R4 fails: the recovered history extends the fenced prefix but its open is
; refused (the malformed fourth record).
(assert! (not (fn-sn-open-okp (fn-cpo-open-observed *ndt-configs* *ndt-f* *ndt-bs*))))
(assert! (ndt-k2-hyps-but *ndt-o* 3 *ndt-bs* "fn.test" 1 :r4))
(assert! (not (ndt-k2-concl *ndt-o* *ndt-bs* "fn.test" 1)))

; R5 fails: fn.test 2 is not in the view; after the recovery of YS it is <two>.
(assert! (ndt-k2-hyps-but *ndt-o* 3 *ndt-ys* "fn.test" 2 :r5))
(assert! (not (ndt-k2-hyps-but *ndt-o* 3 *ndt-ys* "fn.test" 2 nil)))
(assert! (not (ndt-k2-concl *ndt-o* *ndt-ys* "fn.test" 2)))

(must-fail-checked
 (defthm ndt-k2-without-fence
   (let* ((st (fn-own-store o))
          (live (fn-sf-records (fn-sn-files st)))
          (raw (fn-own-view-raw (fn-own-view o)))
          (node (fn-sn-node (fn-sn-open-state
                             (fn-cpo-open-observed (fn-sn-config-history st)
                                                   frontier recovered)))))
     (implies (and (fn-ocl-view-historyp o)
                   (fn-sf-prefixp (fn-own-take fenced live) recovered)
                   (fn-sn-open-okp (fn-cpo-open-observed (fn-sn-config-history st)
                                                         frontier recovered))
                   (fn-ndur-holder g n raw))
              (equal (fn-ndur-holder g n (fn-state-articles (fn-node-acceptance node)))
                     (fn-ndur-holder g n raw))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ndur-prepare-never-allocates-below-the-watermark.
; Hypotheses: (A1) S is an acceptance state, (A2) N is below its next number.

(defconst *ndt-s* (fn-node-acceptance (fn-cst-replay-node *ndt-configs* *ndt-xs* *ndt-f*)))
(defconst *ndt-stamp-a1* (fn-record-stamp *ndt-a1*))
(defun ndt-staged (s)
  (fn-pending-memberships
   (fn-state-pending (fn-accept-prepare s 9 "<three@example.invalid>" 1 '("fn.test")
                                        *ndt-stamp-a1*))))

; Witness: after recovery of XS the first POST to fn.test stages number 2.
(assert! (fn-statep *ndt-s*))
(assert! (< 1 (fn-next-number "fn.test" (fn-state-nexts *ndt-s*))))
(assert! (equal (ndt-staged *ndt-s*) '(("fn.test" . 2))))
(assert! (not (fn-pair-memberp (cons "fn.test" 1) (ndt-staged *ndt-s*))))

; A2 fails: 2 is not below the next number, and 2 is what is staged.
(assert! (not (< 2 (fn-next-number "fn.test" (fn-state-nexts *ndt-s*)))))
(assert! (fn-pair-memberp (cons "fn.test" 2) (ndt-staged *ndt-s*)))

; A1 fails: a malformed state (a pending proposal holding fn.test 0 under a
; next number of 2) is not an acceptance state; the prepare leaves it, and
; 0, below the next number, is staged.
(defconst *ndt-bad-s*
  (fn-make-state '("fn.letters" "fn.test") '(("fn.letters" . 1) ("fn.test" . 2)) nil 9
                 (fn-make-pending 8 8 "<x@example.invalid>" 0 '("fn.test") '(("fn.test" . 0))
                                  t *ndt-stamp-a1*)
                 nil))
(assert! (not (fn-statep *ndt-bad-s*)))
(assert! (< 0 (fn-next-number "fn.test" (fn-state-nexts *ndt-bad-s*))))
;; By the logical definition: the prepare's guard is fn-statep, which this
;; state fails, so its value is asked of the prover, not evaluated.
(defthm ndt-bad-state-stages-a-low-number
  (fn-pair-memberp (cons "fn.test" 0) (ndt-staged *ndt-bad-s*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(must-fail-checked
 (defthm ndt-alloc-without-statep
   (implies (< n (fn-next-number g (fn-state-nexts s)))
            (not (fn-pair-memberp (cons g n)
                                  (fn-pending-memberships
                                   (fn-state-pending
                                    (fn-accept-prepare s generation msgid payload groups stamp))))))))
(must-fail-checked
 (defthm ndt-alloc-without-watermark
   (implies (fn-statep s)
            (not (fn-pair-memberp (cons g n)
                                  (fn-pending-memberships
                                   (fn-state-pending
                                    (fn-accept-prepare s generation msgid payload groups stamp))))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ndur-crash-trace-never-reissues-a-number.
; Hypotheses: (T1) the epochs are a crash trace, (T2) the first holds N.

(defun ndt-k4-concl (epochs g n)
  (and (equal (fn-ndur-holder g n (fn-ndur-epoch-articles *ndt-configs* (car (last epochs))))
              (fn-ndur-holder g n (fn-ndur-epoch-articles *ndt-configs* (car epochs))))
       (< n (fn-next-number g (fn-ndur-epoch-nexts *ndt-configs* (car (last epochs)))))))

; Witness: XS, then a crash that kept the second article (YS), then a crash
; that lost nothing more.
(defconst *ndt-trace* (list (cons *ndt-xs* *ndt-f*) (cons *ndt-ys* *ndt-f*) (cons *ndt-ys* *ndt-f*)))
(assert! (fn-ndur-crash-tracep *ndt-configs* *ndt-trace*))
(assert! (fn-ndur-holder "fn.test" 1 (fn-ndur-epoch-articles *ndt-configs* (car *ndt-trace*))))
(assert! (ndt-k4-concl *ndt-trace* "fn.test" 1))

; T1 fails: the second epoch lost the first's visible article.
(defconst *ndt-lossy* (list (cons *ndt-xs* *ndt-f*) (cons *ndt-zs* *ndt-f*)))
(assert! (not (fn-ndur-crash-tracep *ndt-configs* *ndt-lossy*)))
(assert! (fn-ndur-holder "fn.test" 1 (fn-ndur-epoch-articles *ndt-configs* (car *ndt-lossy*))))
(assert! (not (ndt-k4-concl *ndt-lossy* "fn.test" 1)))

; T2 fails: fn.test 2 was never issued in the first epoch.
(assert! (not (fn-ndur-holder "fn.test" 2 (fn-ndur-epoch-articles *ndt-configs* (car *ndt-trace*)))))
(assert! (not (ndt-k4-concl *ndt-trace* "fn.test" 2)))

(must-fail-checked
 (defthm ndt-trace-without-tracep
   (implies (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car epochs)))
            (equal (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car (last epochs))))
                   (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car epochs)))))))
(must-fail-checked
 (defthm ndt-trace-without-issue
   (implies (fn-ndur-crash-tracep configs epochs)
            (< n (fn-next-number g (fn-ndur-epoch-nexts configs (car (last epochs))))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ndur-recovery-never-reissues-a-logged-txid.
; Hypotheses: (X1) the host's open of RECOVERED succeeds, (X2) RECOVERED
; extends FENCED, (X3) E is a fenced record.

(defconst *ndt-a1-row* (caddr *ndt-xs*))
(defconst *ndt-far* (fn-record-make 5 12 12 "<far@example.invalid>" '(69) '("fn.test")
                                    "archive-far" "subject" "evidence" 2 841000004))
(defconst *ndt-far-row* (car (fn-hrt-rows (list *ndt-far*) nil 0)))
(defun ndt-tx-concl (recovered e)
  (< (fn-store-event-txid e)
     (fn-state-next-txid (fn-node-acceptance
                          (fn-sn-node (fn-sn-open-state
                                       (fn-cpo-open-observed *ndt-configs* *ndt-f* recovered)))))))

; Witness: the first article (txid 7) was fenced; after the open of XS the
; next txid is the frontier 9, and the next prepare stages 9.
(assert! (fn-sn-open-okp (fn-cpo-open-observed *ndt-configs* *ndt-f* *ndt-xs*)))
(assert! (fn-sf-prefixp *ndt-xs* *ndt-xs*))
(assert! (member-equal *ndt-a1-row* *ndt-xs*))
(assert! (equal (fn-store-event-txid *ndt-a1-row*) 7))
(assert! (ndt-tx-concl *ndt-xs* *ndt-a1-row*))
(assert! (equal (fn-pending-txid (fn-state-pending
                                  (fn-accept-prepare *ndt-s* 9 "<three@example.invalid>" 1
                                                     '("fn.test") *ndt-stamp-a1*)))
                9))

; X1 fails: the open of BS is refused; nothing is opened.
(assert! (not (fn-sn-open-okp (fn-cpo-open-observed *ndt-configs* *ndt-f* *ndt-bs*))))
(assert! (fn-sf-prefixp *ndt-xs* *ndt-bs*))
;; The refused open carries no node: its next txid is not a number, and the
;; conclusion is false by the logical definition of < (asked of the prover).
(defthm ndt-tx-refused-open-conclusion-fails
  (not (ndt-tx-concl *ndt-bs* *ndt-a1-row*))
  :rule-classes nil)

; X2 fails: a fenced record at txid 12 the recovered history does not hold.
(assert! (equal (fn-store-event-txid *ndt-far-row*) 12))
(assert! (not (fn-sf-prefixp (list *ndt-far-row*) *ndt-xs*)))
(assert! (member-equal *ndt-far-row* (list *ndt-far-row*)))
(assert! (not (ndt-tx-concl *ndt-xs* *ndt-far-row*)))

; X3 fails: the same record, not among the fenced ones.
(assert! (not (member-equal *ndt-far-row* *ndt-xs*)))
(assert! (not (ndt-tx-concl *ndt-xs* *ndt-far-row*)))

(must-fail-checked
 (defthm ndt-tx-without-open
   (implies (and (fn-sf-prefixp fenced recovered) (member-equal e fenced))
            (< (fn-store-event-txid e)
               (fn-state-next-txid (fn-node-acceptance
                                    (fn-sn-node (fn-sn-open-state
                                                 (fn-cpo-open-observed configs frontier recovered)))))))))
(must-fail-checked
 (defthm ndt-tx-without-member
   (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier recovered))
            (< (fn-store-event-txid e)
               (fn-state-next-txid (fn-node-acceptance
                                    (fn-sn-node (fn-sn-open-state
                                                 (fn-cpo-open-observed configs frontier recovered)))))))))
(must-fail-checked
 (defthm ndt-tx-without-extension
   (implies (and (fn-sn-open-okp (fn-cpo-open-observed configs frontier recovered))
                 (member-equal e fenced))
            (< (fn-store-event-txid e)
               (fn-state-next-txid (fn-node-acceptance
                                    (fn-sn-node (fn-sn-open-state
                                                 (fn-cpo-open-observed configs frontier recovered)))))))))
