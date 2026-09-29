; Teeth for books/store-number-bound.lisp and books/store-number-projection.lisp
; (lane join-f2-615, PKT-615: RFC 3977 section 6's article-number bound kept
; by admission).  The Store records are acceptance-stamp-tests' mixed journal
; (a legacy article, a stamped article, a retention event and a signed
; composite in "stamp.test"), replayed from the initial node.  The owner-level
; refusal's teeth are in owner-prepare-served-tests and
; owner-prepare-outcome-tests.
(in-package "ACL2")
(include-book "acceptance-stamp-tests")
(include-book "../../books/store-number-projection")

(defun snbt-with-nexts (node nexts)
  (let ((a (fn-node-acceptance node)))
    (fn-node-make-state (fn-make-state (strip-cars nexts) nexts (fn-state-articles a)
                                       (fn-state-next-txid a) (fn-state-pending a)
                                       (fn-state-fenced a))
                        (fn-node-retention node) (fn-node-stage node) (fn-node-bindings node))))

(defun snbt-nexts (node) (fn-state-nexts (fn-node-acceptance node)))

; The constructed nodes below are not reachable (their watermarks name no
; articles), so the replay step is evaluated without its guard.
(defmacro snbt-defconst (name form)
  `(make-event (list 'defconst ',name (list 'quote (with-guard-checking :none ,form)))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-snb-replay-apply-record-keeps-nexts-bounded.
; Reachable positive witness: the first article of the journal at the
; initial node: both hypotheses, the step taken (an article installed), and
; the conclusion.
(defconst *snbt-r0-after* (fn-replay-apply-record *ast-replay-initial* *ast-journal-r0*))
(assert-event (fn-nntp-nexts-boundedp (snbt-nexts *ast-replay-initial*)))
(assert-event (fn-snb-record-fitp *ast-replay-initial* *ast-journal-r0*))
(assert-event (consp *snbt-r0-after*))
(assert-event (equal (snbt-nexts *snbt-r0-after*) '(("stamp.test" . 2))))
(assert-event (fn-nntp-nexts-boundedp (snbt-nexts *snbt-r0-after*)))

; Constructed boundary (reaching it takes 2,147,483,646 articles): the
; group's watermark one below the bound still fits, and the watermark after
; is the bound itself.
(defconst *snbt-below* (snbt-with-nexts *ast-replay-initial*
                                        (list (cons "stamp.test" (1- *fn-nntp-max-article-number*)))))
(snbt-defconst *snbt-below-after* (fn-replay-apply-record *snbt-below* *ast-journal-r0*))
(assert-event (fn-snb-record-fitp *snbt-below* *ast-journal-r0*))
(assert-event (equal (snbt-nexts *snbt-below-after*)
                     (list (cons "stamp.test" *fn-nntp-max-article-number*))))
(assert-event (fn-nntp-nexts-boundedp (snbt-nexts *snbt-below-after*)))

; Hypothesis removal, fn-snb-record-fitp: the watermark AT the bound.  The
; retained hypothesis holds (every watermark within the bound), the omitted
; one fails, and the conclusion fails: the replay step (which does not test
; the bound; the admission does) takes the watermark past it.
(defconst *snbt-at* (snbt-with-nexts *ast-replay-initial*
                                     (list (cons "stamp.test" *fn-nntp-max-article-number*))))
(assert-event (fn-nntp-nexts-boundedp (snbt-nexts *snbt-at*)))
(assert-event (not (fn-snb-record-fitp *snbt-at* *ast-journal-r0*)))
(snbt-defconst *snbt-at-after* (fn-replay-apply-record *snbt-at* *ast-journal-r0*))
(assert-event (consp *snbt-at-after*))
(assert-event (not (fn-nntp-nexts-boundedp (snbt-nexts *snbt-at-after*))))

; Hypothesis removal, fn-nntp-nexts-boundedp before (a CORRUPTED state: a
; second group whose watermark is past the bound, which no admitted history
; makes): the record fits, the omitted hypothesis fails, and so does the
; conclusion (the step installs the article and keeps the other watermark).
(defconst *snbt-bad* (snbt-with-nexts *ast-replay-initial*
                                      (list (cons "stamp.test" 1)
                                            (cons "other.test" (+ 1 *fn-nntp-max-article-number*)))))
(assert-event (fn-snb-record-fitp *snbt-bad* *ast-journal-r0*))
(assert-event (not (fn-nntp-nexts-boundedp (snbt-nexts *snbt-bad*))))
(snbt-defconst *snbt-bad-after* (fn-replay-apply-record *snbt-bad* *ast-journal-r0*))
(assert-event (consp *snbt-bad-after*))
(assert-event (not (fn-nntp-nexts-boundedp (snbt-nexts *snbt-bad-after*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-snb-replay-keeps-nexts-bounded and
; fn-snb-replayed-acceptance-is-projection.  Reachable positive witness: the
; whole mixed journal (article, article, retention, composite) replays from
; the initial node, every record fits at its own prefix, and the replayed
; acceptance is a projection with no article counted.
(defconst *snbt-replayed*
  (fn-node-acceptance (fn-replay-result-node (fn-replay *ast-journal-groups* 20 *ast-mixed-journal*))))
(assert-event (fn-snb-history-fitp (fn-node-initial-state *ast-journal-groups* 20) *ast-mixed-journal*))
(assert-event (fn-nntp-nexts-boundedp (fn-state-nexts *snbt-replayed*)))
(assert-event (equal (fn-state-nexts *snbt-replayed*) '(("stamp.test" . 4))))
(assert-event (fn-statep *snbt-replayed*))
(assert-event (fn-nntp-safe-group-listp (fn-state-groups *snbt-replayed*)))
(assert-event (fn-nntp-projectionp *snbt-replayed*))

; Hypothesis removal, the history's fit (fn-snb-replay-keeps-nexts-bounded):
; replayed from a node whose watermark is at the bound, the first article
; does not fit, and the replayed watermarks leave the bound.
(snbt-defconst *snbt-at-fit* (fn-snb-history-fitp *snbt-at* *ast-mixed-journal*))
(snbt-defconst *snbt-at-replayed*
               (fn-replay-result-node (fn-replay-loop *snbt-at* *ast-mixed-journal* 0)))
(assert-event (not *snbt-at-fit*))
(assert-event (not (fn-nntp-nexts-boundedp (snbt-nexts *snbt-at-replayed*))))
