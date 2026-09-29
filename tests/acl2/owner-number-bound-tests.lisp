; Teeth for books/owner-number-bound.lisp (lane join-f2-5, PKT-615's
; follow-up, NNT-057).  The fixtures are store-number-bound-tests' (the mixed
; journal of acceptance-stamp-tests, its first article *ast-journal-r0* in
; "stamp.test").  onbt- is this book's prefix.
(in-package "ACL2")
(include-book "store-number-bound-tests")
(include-book "../../books/owner-number-bound")

; fn-onb-node-boundp is proof vocabulary (defun-nx); its executable body,
; proved equal to it, is what the witnesses evaluate.
(defun onbt-node-boundp (node)
  (let ((a (fn-node-acceptance node)))
    (and (fn-nntp-nexts-boundedp (fn-state-nexts a))
         (implies (fn-state-pending a)
                  (fn-snb-groups-fitp (fn-pending-groups (fn-state-pending a))
                                      (fn-state-nexts a))))))

(defthm onbt-node-boundp-is-onb-node-boundp
  (equal (onbt-node-boundp node) (fn-onb-node-boundp node))
  :hints (("Goal" :in-theory (enable fn-onb-node-boundp))))

; KEYSTONE fn-onb-node-boundp-of-replay-apply-record, reachable positive
; witness: the initial node is bound (no pending allocation), the article
; fits, and the node after it is bound; nothing is pending after the
; completion.
(assert-event (onbt-node-boundp *ast-replay-initial*))
(assert-event (fn-snb-record-fitp *ast-replay-initial* *ast-journal-r0*))
(assert-event (consp *snbt-r0-after*))
(assert-event (onbt-node-boundp *snbt-r0-after*))
(assert-event (null (fn-state-pending (fn-node-acceptance *snbt-r0-after*))))

; The boundary: one below the bound still fits; the node after is bound.
(assert-event (onbt-node-boundp *snbt-below*))
(assert-event (fn-snb-record-fitp *snbt-below* *ast-journal-r0*))
(assert-event (onbt-node-boundp *snbt-below-after*))

; Hypothesis removal, fn-snb-record-fitp: at the bound the retained
; hypothesis holds, the omitted one fails, and so does the conclusion.
(assert-event (onbt-node-boundp *snbt-at*))
(assert-event (not (fn-snb-record-fitp *snbt-at* *ast-journal-r0*)))
(assert-event (not (onbt-node-boundp *snbt-at-after*)))

; Hypothesis removal, fn-onb-node-boundp before (corrupted state: a
; watermark past the bound no admitted history reaches): the record fits,
; the node before is not bound, and neither is the node after.
(assert-event (fn-snb-record-fitp *snbt-bad* *ast-journal-r0*))
(assert-event (not (onbt-node-boundp *snbt-bad*)))
(assert-event (not (onbt-node-boundp *snbt-bad-after*)))

; The in-flight allocation: a node prepared with the article's groups at the
; initial node carries a pending allocation that fits
; (fn-onb-node-boundp-of-prepare); at the bound the staged allocation would
; not fit, which is the prepare the admission refuses
; (fn-psrv-event-numberedp, fn-onb-boundp-of-psrv-prepare).
(snbt-defconst *onbt-prepared* (fn-sn-prepare-node *ast-replay-initial* *ast-journal-r0*))
(assert-event (fn-state-pending (fn-node-acceptance *onbt-prepared*)))
(assert-event (onbt-node-boundp *onbt-prepared*))
(snbt-defconst *onbt-prepared-at* (fn-sn-prepare-node *snbt-at* *ast-journal-r0*))
(assert-event (fn-state-pending (fn-node-acceptance *onbt-prepared-at*)))
(assert-event (not (onbt-node-boundp *onbt-prepared-at*)))

; ---------------------------------------------------------------------------
; The record in flight (lane join-f2-6).  fn-onb-inflight-fitp is proof
; vocabulary; its executable body, proved equal to it, is what is evaluated.
(defun onbt-inflight-fitp (s)
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files)))
    (and (implies (fn-sf-record-phasep phase)
                  (or (fn-held-p (fn-sf-record-candidate files))
                      (fn-snb-record-fitp (fn-sn-node s) (fn-sf-record-candidate files))))
         (implies (equal phase :completing)
                  (or (fn-held-p (fn-sn-completion-record s))
                      (fn-snb-record-fitp (fn-sn-node s) (fn-sn-completion-record s)))))))

(defthm onbt-inflight-fitp-is-onb-inflight-fitp
  (equal (onbt-inflight-fitp s) (fn-onb-inflight-fitp s))
  :hints (("Goal" :in-theory (enable fn-onb-inflight-fitp))))

; KEYSTONE fn-onb-store-boundp-of-finish, reachable positive witness: the
; signed composite of acceptance-stamp-tests, staged by the identity prepare
; (its candidate is the composite row) and published to :completing; the
; node is bound, the composite in flight fits, the finish is enabled, and the
; node after the finish is bound.
(assert-event (equal (fn-sf-phase (fn-sn-files *ast-composite-prepared*)) :record-staged))
(assert-event (fn-hstxa-p (fn-sf-record-candidate (fn-sn-files *ast-composite-prepared*))))
(assert-event (onbt-inflight-fitp *ast-composite-prepared*))
(assert-event (onbt-node-boundp (fn-sn-node *ast-composite-completing*)))
(assert-event (onbt-inflight-fitp *ast-composite-completing*))
(assert-event (fn-sn-completion-enabledp *ast-composite-completing*))
(assert-event (onbt-node-boundp (fn-sn-node (fn-sn-finish *ast-composite-completing*))))

; Hypothesis removal, the record in flight (a constructed Store: its node's
; watermark for the composite's group AT the bound, which the identity
; prepare's admission refuses): the node is bound (the retained part), the
; composite in flight does not fit (the omitted part), the finish is still
; enabled (the replay does not test the bound; the admission does), and the
; node after it is not bound.
(snbt-defconst *onbt-completing-at*
  (fn-sn-update *ast-composite-completing* (fn-sn-files *ast-composite-completing*)
                (snbt-with-nexts (fn-sn-node *ast-composite-completing*)
                                 (list (cons "example" *fn-nntp-max-article-number*)))))
(snbt-defconst *onbt-completing-at-finished* (fn-sn-finish *onbt-completing-at*))
(assert-event (onbt-node-boundp (fn-sn-node *onbt-completing-at*)))
(assert-event (not (onbt-inflight-fitp *onbt-completing-at*)))
(assert-event (with-guard-checking :none (fn-sn-completion-enabledp *onbt-completing-at*)))
(assert-event (not (onbt-node-boundp (fn-sn-node *onbt-completing-at-finished*))))
