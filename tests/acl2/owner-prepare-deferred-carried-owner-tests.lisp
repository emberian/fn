;; Owner-level teeth for books/owner-prepare-deferred-carried.lisp (lane
;; served-incremental-2), on owner-log-ocl-tests' configured owner
;; (*lgt-reserved*) driven by the events ACL2 proposes
;; (owner-prepare-served-events-tests).
(in-package "ACL2")
(include-book "owner-prepare-served-events-tests")
(include-book "../../books/owner-prepare-deferred-carried")

; -----------------------------------------------------------------------------
; Owner level: fn-pdc-ocfg-prepare-consumer-preserves-invariant and
; fn-pdc-psrv-prepare-topic-preserves-invariant, and the entries' words.
; Reachable positive witness: the antecedent fn-lgoc-invariantp holds on the
; configured owner at :reserved; the carried prepares stage the events ACL2
; proposed, are the reference owners the host installed before
; (*pse-consumer-staged*, *pse-topic-staged*), and the conclusion holds.
(assert-event (fn-lgoc-invariantp *lgt-reserved*))
(make-event `(defconst *pdt-consumer-staged*
               ',(fn-pdc-ocfg-prepare-consumer *lgt-reserved* *pse-consumer-event*)))
(assert-event (equal *pdt-consumer-staged* *pse-consumer-staged*))
(assert-event (equal (lgt-phase *pdt-consumer-staged*) :record-staged))
(assert-event (fn-lgoc-invariantp *pdt-consumer-staged*))
(assert-event (equal (mv-nth 0 (fn-pdc-pout-prepare-consumer *lgt-reserved* *pse-consumer-event*))
                     :prepared))
(make-event `(defconst *pdt-topic-staged*
               ',(fn-pdc-psrv-prepare-topic *lgt-reserved* *pse-topic-event*)))
(assert-event (equal *pdt-topic-staged* *pse-topic-staged*))
(assert-event (fn-lgoc-invariantp *pdt-topic-staged*))
(assert-event (equal (mv-nth 0 (fn-pdc-pout-prepare-topic *lgt-reserved* *pse-topic-event*))
                     :prepared))
; Hypothesis-removal witness (CORRUPTED STATE, labelled: owner-prepare-served-
; events-tests' *lgt-bad-reserved*, the topic counter moved): the antecedent
; fails, and so does the conclusion after each carried prepare.
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (not (fn-lgoc-invariantp
                    (fn-pdc-ocfg-prepare-consumer *lgt-bad-reserved* *pse-consumer-event*))))
(assert-event (not (fn-lgoc-invariantp
                    (fn-pdc-psrv-prepare-topic *lgt-bad-reserved* *pse-topic-event*))))
; A refused prepare answers :refused and leaves the owner unchanged: the
; consumer bootstrap proposed again after it committed.
(assert-event (equal (mv-nth 0 (fn-pdc-pout-prepare-consumer *pse-consumer-finished* *pse-consumer-event*))
                     :refused))
(assert-event (equal (lgt-store (mv-nth 1 (fn-pdc-pout-prepare-consumer *pse-consumer-finished*
                                                                       *pse-consumer-event*)))
                     (lgt-store *pse-consumer-finished*)))
