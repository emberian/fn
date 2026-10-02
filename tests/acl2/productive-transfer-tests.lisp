; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- its closure reaches books/productive-transfer, a Codex-era book that never certified (fn-pct-tick-offers-the-queued-article fails). The code stays; it certifies again with that book.
; Complete literal antecedents and conclusions for productive transfer.
(in-package "ACL2")
(include-book "../../books/productive-transfer")
(include-book "owner-feed-tests")
(include-book "must-fail-checked")

(defun pctt-offer-hyps (peer tbl obs)
 (declare (xargs :mode :program) (ignorable peer tbl obs))
 (let* ((e (fn-own-feed-entry-of peer tbl)) (f (fn-own-feed-entry-feed e)) (msgid (fn-feed-head-queued (fn-feed-queue f))) (attempt (fn-feed-next-attempt f)) (result (fn-own-feed-port-tick-peer peer tbl obs)) (g (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feed-port-table result))))) (declare (ignorable e f msgid attempt result g)) (list (fn-pct-selectablep f obs) (fn-feed-records-portp (fn-feed-tick-records f obs)))))

(defun pctt-offer-conclusion (peer tbl obs)
 (declare (xargs :mode :program) (ignorable peer tbl obs))
 (let* ((e (fn-own-feed-entry-of peer tbl)) (f (fn-own-feed-entry-feed e)) (msgid (fn-feed-head-queued (fn-feed-queue f))) (attempt (fn-feed-next-attempt f)) (result (fn-own-feed-port-tick-peer peer tbl obs)) (g (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feed-port-table result))))) (declare (ignorable e f msgid attempt result g)) (and (equal (fn-own-feed-port-status result) :accepted) (equal (fn-own-feed-port-effects result) (list (cons peer (list (list :command (fn-feed-conn f) (fn-feed-offer-line msgid (fn-feed-streamingp (fn-feed-limits-of f)))))))) (equal (fn-own-feed-port-records result) (list (fn-feed-journal-entry :feed-offer (list (fn-feed-peer f) msgid attempt (nfix (fn-clock-monotonic obs)))))) (equal (fn-feed-state-of msgid (fn-feed-queue g)) (fn-feed-offered attempt)) (equal (fn-feed-next-attempt g) (+ 1 attempt)))))

(defun pctt-send-hyps (peer tbl response article obs)
 (declare (xargs :mode :program) (ignorable peer tbl response article obs))
 (let* ((e (fn-own-feed-entry-of peer tbl)) (f (fn-own-feed-entry-feed e)) (msgid (fn-feed-response-msgid response)) (attempt (fn-feed-state-attempt (fn-feed-state-of msgid (fn-feed-queue f)))) (result (fn-own-feed-port-observe-peer peer tbl response article obs)) (g (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feed-port-table result))))) (declare (ignorable e f msgid attempt result g)) (list (fn-feedp f) (member-equal (fn-feed-response-code response) '(335 238)) (fn-feed-offeredp (fn-feed-state-of msgid (fn-feed-queue f))) (natp (fn-feed-conn f)) (fn-feed-records-portp (fn-feed-observe-records f response obs)))))

(defun pctt-send-conclusion (peer tbl response article obs)
 (declare (xargs :mode :program) (ignorable peer tbl response article obs))
 (let* ((e (fn-own-feed-entry-of peer tbl)) (f (fn-own-feed-entry-feed e)) (msgid (fn-feed-response-msgid response)) (attempt (fn-feed-state-attempt (fn-feed-state-of msgid (fn-feed-queue f)))) (result (fn-own-feed-port-observe-peer peer tbl response article obs)) (g (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feed-port-table result))))) (declare (ignorable e f msgid attempt result g)) (and (equal (fn-own-feed-port-status result) :accepted) (equal (fn-own-feed-port-effects result) (list (cons peer (list (list :command (fn-feed-conn f) (if (fn-feed-streamingp (fn-feed-limits-of f)) (append (fn-feed-takethis-line msgid) article) article)))))) (equal (fn-own-feed-port-records result) (list (fn-feed-journal-entry :feed-sent (list (fn-feed-peer f) msgid attempt)))) (equal (fn-feed-state-of msgid (fn-feed-queue g)) (fn-feed-sent attempt)) (equal (fn-feed-next-attempt g) (fn-feed-next-attempt f)))))


(defun pctt-allp (xs)
 (declare (xargs :mode :program))
 (if (consp xs) (and (car xs) (pctt-allp (cdr xs))) t))
(defun pctt-retainedp (xs omitted)
 (declare (xargs :mode :program))
 (if (consp xs)
     (and (if (zp omitted) (not (car xs)) (car xs))
          (if (zp omitted) (pctt-allp (cdr xs))
            (pctt-retainedp (cdr xs) (1- omitted)))) nil))
(defun pctt-table (f)
 (declare (xargs :mode :program))
 (fn-own-feed-put "nodeB" *oft-b* f *oft-connected*))
(defconst *pctt-f* (fn-own-feed-find "nodeB" *oft-connected*))
(defconst *pctt-offered* (fn-own-feed-find "nodeB" (car *oft-ticked*)))
(defconst *pctt-response* (fn-feed-response 238 *oft-msgid*))
(defconst *pctt-large-attempt* (expt 2 64))
(defconst *pctt-over-offer*
 (fn-feed-make (fn-feed-peer *pctt-f*) (fn-feed-limits-of *pctt-f*)
               (fn-feed-queue *pctt-f*) (fn-feed-contact *pctt-f*)
               (fn-feed-backoff-until *pctt-f*) (fn-feed-conn *pctt-f*)
               *pctt-large-attempt*))
(defconst *pctt-over-send*
 (fn-feed-make (fn-feed-peer *pctt-offered*) (fn-feed-limits-of *pctt-offered*)
               (fn-feed-queue-set-state (fn-feed-queue *pctt-offered*) *oft-msgid*
                                       (fn-feed-offered *pctt-large-attempt*))
               (fn-feed-contact *pctt-offered*) (fn-feed-backoff-until *pctt-offered*)
               (fn-feed-conn *pctt-offered*) (+ 1 *pctt-large-attempt*)))
; PRF-1055: complete reachable antecedent and conclusion, then removals.
(assert-event
 (and (fn-own-feed-tablep *oft-connected*)
      (pctt-allp (pctt-offer-hyps "nodeB" *oft-connected* *oft-obs*))
      (pctt-offer-conclusion "nodeB" *oft-connected* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-offer-hyps "nodeB" *oft-accepted* *oft-obs*) 0)
      (not (pctt-offer-conclusion "nodeB" *oft-accepted* *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-offer-conclusion "nodeB" *oft-accepted* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-offer-hyps "nodeB" (pctt-table *pctt-over-offer*) *oft-obs*) 1)
      (not (pctt-offer-conclusion "nodeB" (pctt-table *pctt-over-offer*) *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-offer-conclusion "nodeB" (pctt-table *pctt-over-offer*) *oft-obs*)))

; PRF-1062: actual successful request carries all article bytes.
(assert-event
 (and (fn-own-feed-tablep (car *oft-ticked*))
      (pctt-allp (pctt-send-hyps "nodeB" (car *oft-ticked*) *pctt-response*
                               *oft-article* *oft-obs*))
      (pctt-send-conclusion "nodeB" (car *oft-ticked*) *pctt-response*
                            *oft-article* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-send-hyps "nodeB" (pctt-table (fn-feed-make (fn-feed-peer *pctt-offered*) nil (fn-feed-queue *pctt-offered*) (fn-feed-contact *pctt-offered*) (fn-feed-backoff-until *pctt-offered*) 3 (fn-feed-next-attempt *pctt-offered*))) *pctt-response*
                                     *oft-article* *oft-obs*) 0)
      (not (pctt-send-conclusion "nodeB" (pctt-table (fn-feed-make (fn-feed-peer *pctt-offered*) nil (fn-feed-queue *pctt-offered*) (fn-feed-contact *pctt-offered*) (fn-feed-backoff-until *pctt-offered*) 3 (fn-feed-next-attempt *pctt-offered*))) *pctt-response*
                                *oft-article* *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-send-conclusion "nodeB" (pctt-table (fn-feed-make (fn-feed-peer *pctt-offered*) nil (fn-feed-queue *pctt-offered*) (fn-feed-contact *pctt-offered*) (fn-feed-backoff-until *pctt-offered*) 3 (fn-feed-next-attempt *pctt-offered*))) *pctt-response*
                                   *oft-article* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-send-hyps "nodeB" (car *oft-ticked*) (fn-feed-response 239 *oft-msgid*)
                                     *oft-article* *oft-obs*) 1)
      (not (pctt-send-conclusion "nodeB" (car *oft-ticked*) (fn-feed-response 239 *oft-msgid*)
                                *oft-article* *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-send-conclusion "nodeB" (car *oft-ticked*) (fn-feed-response 239 *oft-msgid*)
                                   *oft-article* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-send-hyps "nodeB" *oft-connected* *pctt-response*
                                     *oft-article* *oft-obs*) 2)
      (not (pctt-send-conclusion "nodeB" *oft-connected* *pctt-response*
                                *oft-article* *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-send-conclusion "nodeB" *oft-connected* *pctt-response*
                                   *oft-article* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-send-hyps "nodeB" (pctt-table (fn-feed-with-conn *pctt-offered* nil)) *pctt-response*
                                     *oft-article* *oft-obs*) 3)
      (not (pctt-send-conclusion "nodeB" (pctt-table (fn-feed-with-conn *pctt-offered* nil)) *pctt-response*
                                *oft-article* *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-send-conclusion "nodeB" (pctt-table (fn-feed-with-conn *pctt-offered* nil)) *pctt-response*
                                   *oft-article* *oft-obs*)))

(assert-event
 (and (pctt-retainedp (pctt-send-hyps "nodeB" (pctt-table *pctt-over-send*) *pctt-response*
                                     *oft-article* *oft-obs*) 4)
      (not (pctt-send-conclusion "nodeB" (pctt-table *pctt-over-send*) *pctt-response*
                                *oft-article* *oft-obs*))))
(must-fail-checked
 (assert-event (pctt-send-conclusion "nodeB" (pctt-table *pctt-over-send*) *pctt-response*
                                   *oft-article* *oft-obs*)))

; MUTATION: an offer record cannot stand in for the article-sent record.
(must-fail-checked
 (assert-event
  (equal (fn-own-feed-port-records
          (fn-own-feed-port-observe-peer "nodeB" (car *oft-ticked*)
                                        *pctt-response* *oft-article* *oft-obs*))
         (list (fn-feed-journal-entry :feed-offer
                (list (fn-feed-peer *pctt-offered*) *oft-msgid*
                      (fn-feed-next-attempt *pctt-offered*) 5000))))))
; PRF-1056 positive quiet branch: the queued article lacks a connection.
(assert-event
 (let* ((f (fn-own-feed-find "nodeB" *oft-accepted*))
        (r (fn-own-feed-port-tick-peer "nodeB" *oft-accepted* *oft-obs*)))
  (and (fn-own-feed-entry-of "nodeB" *oft-accepted*) (fn-feedp f)
       (null (fn-feed-selection f *oft-obs*))
       (equal (fn-own-feed-port-status r) :accepted)
       (null (fn-own-feed-port-effects r)) (null (fn-own-feed-port-records r))
       (equal (fn-own-feed-find "nodeB" (fn-own-feed-port-table r)) f))))
; PRF-1056 positive refusal branch: finite codec cannot carry the attempt.
(assert-event
 (let* ((tbl (pctt-table *pctt-over-offer*))
        (f (fn-own-feed-find "nodeB" tbl))
        (r (fn-own-feed-port-tick-peer "nodeB" tbl *oft-obs*)))
  (and (fn-own-feed-entry-of "nodeB" tbl)
       (or (not (fn-feedp f))
           (not (fn-feed-records-portp (fn-feed-tick-records f *oft-obs*))))
       (equal (fn-own-feed-port-status r) :refused)
       (equal (fn-own-feed-port-table r) tbl)
       (null (fn-own-feed-port-effects r)) (null (fn-own-feed-port-records r)))))
; Refusal premise removal: a valid representable offer is accepted.
(assert-event
 (let ((r (fn-own-feed-port-tick-peer "nodeB" *oft-connected* *oft-obs*)))
  (and (fn-own-feed-entry-of "nodeB" *oft-connected*)
       (fn-feedp *pctt-f*)
       (fn-feed-records-portp (fn-feed-tick-records *pctt-f* *oft-obs*))
       (not (equal (fn-own-feed-port-status r) :refused)))))
(must-fail-checked
 (assert-event (equal (fn-own-feed-port-status
                      (fn-own-feed-port-tick-peer "nodeB" *oft-connected* *oft-obs*))
                     :refused)))
; Bound-entry removal: no entry is ignored, not refused.
(assert-event
 (and (not (fn-own-feed-entry-of "nodeB" nil))
      (not (fn-feedp (fn-own-feed-find "nodeB" nil)))
      (not (equal (fn-own-feed-port-status
                   (fn-own-feed-port-tick-peer "nodeB" nil *oft-obs*)) :refused))))
(must-fail-checked
 (assert-event (equal (fn-own-feed-port-status
                      (fn-own-feed-port-tick-peer "nodeB" nil *oft-obs*)) :refused)))
; PRF-1056 quiet-arm removal: a selectable valid feed has effects.
(assert-event
 (and (fn-feedp *pctt-f*) (fn-feed-selection *pctt-f* *oft-obs*)
      (fn-own-feed-port-effects
       (fn-own-feed-port-tick-peer "nodeB" *oft-connected* *oft-obs*))))
(must-fail-checked
 (assert-event
  (null (fn-own-feed-port-effects
         (fn-own-feed-port-tick-peer "nodeB" *oft-connected* *oft-obs*)))))
; CORRUPTED STATE / quiet-arm feedp removal: malformed feed, no selection,
; is refused, so the accepted-quiet conclusion fails. All retained
; hypotheses of this arm (just no selection) hold affirmatively.
(assert-event
 (let* ((bad (pctt-table nil)) (f (fn-own-feed-find "nodeB" bad))
        (r (fn-own-feed-port-tick-peer "nodeB" bad *oft-obs*)))
  (and (not (fn-feedp f)) (null (fn-feed-selection f *oft-obs*))
       (not (equal (fn-own-feed-port-status r) :accepted)))))
(must-fail-checked
 (assert-event (equal (fn-own-feed-port-status
                      (fn-own-feed-port-tick-peer "nodeB" (pctt-table nil) *oft-obs*))
                     :accepted)))
