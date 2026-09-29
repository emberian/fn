; Teeth for books/owner-number-bound.lisp (lane join-f2-5, PKT-615's
; follow-up, NNT-057).  The fixtures are store-number-bound-tests' (the mixed
; journal of acceptance-stamp-tests, its first article *ast-journal-r0* in
; "stamp.test").  onbt- is this book's prefix.
(in-package "ACL2")
(include-book "store-number-bound-tests")
(include-book "../../books/owner-number-bound")

; KEYSTONE fn-onb-node-boundp-of-replay-apply-record, reachable positive
; witness: the initial node is bound (no pending allocation), the article
; fits, and the node after it is bound; nothing is pending after the
; completion.
(assert-event (fn-onb-node-boundp *ast-replay-initial*))
(assert-event (fn-snb-record-fitp *ast-replay-initial* *ast-journal-r0*))
(assert-event (consp *snbt-r0-after*))
(assert-event (fn-onb-node-boundp *snbt-r0-after*))
(assert-event (null (fn-state-pending (fn-node-acceptance *snbt-r0-after*))))

; The boundary: one below the bound still fits; the node after is bound.
(assert-event (fn-onb-node-boundp *snbt-below*))
(assert-event (fn-snb-record-fitp *snbt-below* *ast-journal-r0*))
(assert-event (fn-onb-node-boundp *snbt-below-after*))

; Hypothesis removal, fn-snb-record-fitp: at the bound the retained
; hypothesis holds, the omitted one fails, and so does the conclusion.
(assert-event (fn-onb-node-boundp *snbt-at*))
(assert-event (not (fn-snb-record-fitp *snbt-at* *ast-journal-r0*)))
(assert-event (not (fn-onb-node-boundp *snbt-at-after*)))

; Hypothesis removal, fn-onb-node-boundp before (corrupted state: a
; watermark past the bound no admitted history reaches): the record fits,
; the node before is not bound, and neither is the node after.
(assert-event (fn-snb-record-fitp *snbt-bad* *ast-journal-r0*))
(assert-event (not (fn-onb-node-boundp *snbt-bad*)))
(assert-event (not (fn-onb-node-boundp *snbt-bad-after*)))

; The in-flight allocation: a node prepared with the article's groups at the
; initial node carries a pending allocation that fits
; (fn-onb-node-boundp-of-prepare); at the bound the staged allocation would
; not fit, which is the prepare the admission refuses
; (fn-psrv-event-numberedp, fn-onb-boundp-of-psrv-prepare).
(snbt-defconst *onbt-prepared* (fn-sn-prepare-node *ast-replay-initial* *ast-journal-r0*))
(assert-event (fn-state-pending (fn-node-acceptance *onbt-prepared*)))
(assert-event (fn-onb-node-boundp *onbt-prepared*))
(snbt-defconst *onbt-prepared-at* (fn-sn-prepare-node *snbt-at* *ast-journal-r0*))
(assert-event (fn-state-pending (fn-node-acceptance *onbt-prepared-at*)))
(assert-event (not (fn-onb-node-boundp *onbt-prepared-at*)))
