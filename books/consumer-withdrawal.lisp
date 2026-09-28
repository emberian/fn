; fn: withdrawal events for local consumers (PKT-710; lane friend-blockers-2;
; the stranger rehearsal's stop 7, planning/evidence/stranger-rehearsal-
; 2026-09-27.md; specs/consumer-progress.md "Withdrawals").
;
; DECIDED (PKT-710): a consumer gets the withdrawal event, never the
; withdrawn content.  A consumer's poll selects history events by the
; article's groups (books/consumer-poll-index.lisp fn-col-poll-scan), so
; before this book a consumer was handed an article its author had already
; cancelled, with no mark, and a cancel committed after delivery (filed in
; control.cancel, which the consumer's group is not) never reached it.
;
; The withdrawal decision this book reads is the one NNTP's `430 withdrawn'
; reads: the owner's committed view's withdrawn articles and withdrawal
; records (books/owner.lisp fn-own-view-withdrawn, fn-own-view-withdrawals;
; books/control-served.lisp fn-ctl-msgid-withdrawn).  Two deliveries:
;
;   (a) an article already withdrawn when its own position is polled is
;       delivered as a withdrawal report (its Message-ID, no content) in
;       place of its report, at the same cursor
;       (`fn-cwd-page-never-serves-withdrawn-content');
;   (b) an event whose withdrawal record withdrew an article of the
;       consumer's group (a cancel, a supersession) is delivered, at its own
;       position, as a withdrawal report naming that article
;       (`fn-cwd-scan-delivers-a-withdrawing-cause'), and its cursor moves
;       past that position (`fn-cwd-scan-withdrawal-advances').
;
; A consumer that polls after the cancel can meet the same Message-ID twice
; (at the article's position and at the cancel's): delivery is at least
; once, keyed by Message-ID, as every event is.  The report names only the
; withdrawn article, which is of the consumer's group; the cancel's own
; Message-ID and group are not disclosed.
;
; Everything else is the poll it was: the host calls `fn-cwd-page' over the
; answer the plain, bound or waiting poll computed, and while nothing is
; withdrawn the page IS that answer (`fn-cwd-page-without-withdrawals-is-
; the-answer'), so every guarantee PRF-116, PRF-177, PRF-234 and PRF-252
; prove of it holds unchanged.  The scan that finds (b) is the poll's scan
; with one more stopping arm (`fn-cwd-scan-is-the-poll-scan-unless-a-
; withdrawal').
;
; Cost per poll (pessimistic, the scan's 16-event window W, the view's
; withdrawal records R and withdrawn list N): one more window of 16 index
; lookups, and per scanned event not of the group a walk of R, each record
; whose cause matches probing N: 16 x (R + N) comparisons in the worst case,
; and one walk of N for (a).  The walk of N is the one `430 withdrawn'
; makes per ARTICLE.
;
; ON DEV AT 2026-09-27 the view's withdrawn list is empty (cancels withdraw
; nothing until lane flip-L8-2 lands control-visible's live refresh), so the
; page is the answer; the (a) and (b) arms take effect with that refresh,
; through the same two accessors, with no change here.
;
; Host callers: host/owner-host.lisp fn-owner-consumer-local-poll and
; fn-owner-consumer-local-bound-poll (fn-cwd-page over fn-cbind-plain-poll-over
; and fn-cbind-poll-over, the polls over the live arena) and
; fn-owner-consumer-local-wait-step (fn-cwd-wait-step-over).
;
; Prefix `fn-cwd-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "consumer-wait")
(include-book "consumer-reason")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ctl-withdrawalp))))

; The progress book's unfolding of the poll (a rewrite rule whose hypothesis
; is the poll's page) expands fn-col-poll and its scan inside every goal
; that mentions a poll; the lemmas here reason about the two scans instead.
(local (in-theory (disable fn-col-poll-is-the-index-window-scan-unfolds)))

; -----------------------------------------------------------------------------
; The view's withdrawal decision.

(defun fn-cwd-withdrawn (o)
  (declare (xargs :guard t))
  (fn-own-view-withdrawn (fn-own-view o)))

(defun fn-cwd-records (o)
  (declare (xargs :guard t))
  (fn-own-view-withdrawals (fn-own-view o)))

; The Message-ID of a history event whose article the view withdrew, or nil.
(defun fn-cwd-event-withdrawn-msgid (event withdrawn)
  (declare (xargs :guard t))
  (let ((m (fn-ctl-event-msgid event)))
    (and m (consp (fn-ctl-msgid-withdrawn m withdrawn)) m)))

; The Message-ID of an article of GROUP (its name as text) that a withdrawal
; record caused by CAUSE withdrew, or nil.
(defun fn-cwd-cause-target (cause ws withdrawn group)
  (declare (xargs :guard t))
  (if (consp ws)
      (let* ((w (car ws))
             (target (and cause (fn-ctl-withdrawalp w)
                          (equal (fn-ctl-w-cause w) cause)
                          (fn-ctl-w-target w)))
             (a (and target (fn-ctl-msgid-withdrawn target withdrawn))))
        (if (and (consp a)
                 (true-listp (fn-article-groups a))
                 (member-equal group (fn-article-groups a)))
            target
          (fn-cwd-cause-target cause (cdr ws) withdrawn group)))
    nil))

(defthm fn-cwd-cause-target-of-no-withdrawn
  (not (fn-cwd-cause-target cause ws nil group))
  :hints (("Goal" :in-theory (enable fn-ctl-msgid-withdrawn))))

; -----------------------------------------------------------------------------
; The scan: fn-col-poll-scan with one more stopping arm, (:withdrawal NEXT
; TARGET) at an event whose record withdrew an article of the group.

(defun fn-cwd-scan (events group position frontier budget ws withdrawn)
  (declare (xargs :guard (and (true-listp events) (fn-cp-idp group)
                              (natp position) (natp frontier) (natp budget))
                  :measure (nfix budget)
                  ;; The measure and the guard need only the budget's and the
                  ;; position's types: the event and record predicates stay
                  ;; closed (the admission was 3.0 s with them open).
                  :hints (("Goal" :in-theory
                           (disable fn-col-poll-article fn-col-poll-articlep
                                    fn-col-poll-compositep fn-cwd-cause-target
                                    fn-store-event-p fn-store-event-sequence
                                    fn-record-groups fn-record-octets-string
                                    fn-ctl-event-msgid member-equal)))
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-col-poll-article fn-col-poll-articlep
                                          fn-col-poll-compositep fn-cwd-cause-target
                                          fn-store-event-p fn-store-event-sequence
                                          fn-record-groups fn-record-octets-string
                                          fn-ctl-event-msgid member-equal)))))
  (if (or (zp budget) (<= (nfix frontier) (nfix position)))
      (list :scan position nil)
    (if (not (consp events)) (list :refused :history)
      (let* ((event (car events))
             (article (fn-col-poll-article event)))
        (cond
         ((or (not (fn-store-event-p event))
              (not (equal (fn-store-event-sequence event) position)))
          (list :refused :history))
         ((and (fn-col-poll-compositep event) (not article))
          (list :refused :article-binding))
         ((and (fn-col-poll-articlep article)
               (true-listp (fn-record-groups article))
               (member-equal (fn-record-octets-string group)
                             (fn-record-groups article)))
          (list :scan (1+ position) event))
         ((fn-cwd-cause-target (fn-ctl-event-msgid event) ws withdrawn
                               (fn-record-octets-string group))
          (list :withdrawal (1+ position)
                (fn-cwd-cause-target (fn-ctl-event-msgid event) ws withdrawn
                                     (fn-record-octets-string group))))
         (t (fn-cwd-scan (cdr events) group (1+ position)
                         frontier (1- budget) ws withdrawn)))))))

; Unless it stops at a withdrawal, the scan is the poll's.
(defthm fn-cwd-scan-is-the-poll-scan-unless-a-withdrawal
  (implies (not (equal (car (fn-cwd-scan events group position frontier
                                         budget ws withdrawn))
                       :withdrawal))
           (equal (fn-cwd-scan events group position frontier budget ws withdrawn)
                  (fn-col-poll-scan events group position frontier budget)))
  :hints (("Goal" :induct (fn-cwd-scan events group position frontier
                                       budget ws withdrawn)
           :in-theory (e/d (fn-col-poll-scan)
                           (fn-cwd-cause-target fn-col-poll-article
                            fn-col-poll-articlep fn-col-poll-compositep
                            fn-store-event-p fn-store-event-sequence
                            fn-record-groups fn-record-octets-string
                            fn-ctl-event-msgid member-equal)))))

; With nothing withdrawn the scan never stops at a withdrawal.
(defthm fn-cwd-scan-of-no-withdrawn
  (equal (fn-cwd-scan events group position frontier budget ws nil)
         (fn-col-poll-scan events group position frontier budget))
  :hints (("Goal" :induct (fn-cwd-scan events group position frontier
                                       budget ws nil)
           :in-theory (e/d (fn-col-poll-scan fn-cwd-cause-target-of-no-withdrawn)
                           (fn-cwd-cause-target fn-col-poll-article
                            fn-col-poll-articlep fn-col-poll-compositep
                            fn-store-event-p fn-store-event-sequence
                            fn-record-groups fn-record-octets-string
                            fn-ctl-event-msgid member-equal)))))

(in-theory (disable fn-cwd-scan-is-the-poll-scan-unless-a-withdrawal
                    fn-cwd-scan-of-no-withdrawn))

; KEYSTONE (b1: the position advances).  A withdrawal the scan stops at lies
; past the consumer's position and within the frontier: its cursor (built
; from NEXT exactly as the poll builds its own, `fn-cwd-poll') moves the
; consumer past the withdrawing event and never past the journal.
(defthm fn-cwd-scan-withdrawal-advances
  (let ((r (fn-cwd-scan events group position frontier budget ws withdrawn)))
    (implies (and (natp position) (equal (car r) :withdrawal))
             (and (natp (cadr r))
                  (< position (cadr r))
                  (<= (cadr r) (nfix frontier))
                  (caddr r))))
  :hints (("Goal" :induct (fn-cwd-scan events group position frontier
                                       budget ws withdrawn)
           :in-theory (disable fn-cwd-cause-target fn-col-poll-article
                            fn-col-poll-articlep fn-col-poll-compositep
                            fn-store-event-p fn-store-event-sequence
                            fn-record-groups fn-record-octets-string
                            fn-ctl-event-msgid member-equal))))

; KEYSTONE (b2: a withdrawing cause is delivered, not skipped).  When the
; event at the consumer's position is a history event there, is no article
; of the group, and withdrew (by its record, in the view) an article of the
; group, the scan stops at it and names that article.
(defthm fn-cwd-scan-delivers-a-withdrawing-cause
  (let ((event (car events))
        (g (fn-record-octets-string group)))
    (implies (and (posp budget) (natp position) (< position (nfix frontier))
                  (consp events)
                  (fn-store-event-p event)
                  (equal (fn-store-event-sequence event) position)
                  (not (and (fn-col-poll-compositep event)
                            (not (fn-col-poll-article event))))
                  (not (and (fn-col-poll-articlep (fn-col-poll-article event))
                            (true-listp (fn-record-groups (fn-col-poll-article event)))
                            (member-equal g (fn-record-groups
                                             (fn-col-poll-article event)))))
                  (fn-cwd-cause-target (fn-ctl-event-msgid event) ws withdrawn g))
             (equal (fn-cwd-scan events group position frontier budget ws withdrawn)
                    (list :withdrawal (1+ position)
                          (fn-cwd-cause-target (fn-ctl-event-msgid event)
                                               ws withdrawn g)))))
  :hints (("Goal" :expand ((fn-cwd-scan events group position frontier
                                        budget ws withdrawn))
           :in-theory (disable fn-cwd-cause-target fn-col-poll-article
                               fn-col-poll-articlep fn-col-poll-compositep))))

; -----------------------------------------------------------------------------
; The poll over the scan: the owner's scope and window, as fn-col-poll.
; (:withdrawal CURSOR-OCTETS TARGET), (:scan EVENT) with the event the
; poll's scan selected (nil for none), or the poll's refusal.

(defun fn-cwd-poll (o consumer fn-hist)
  (declare (xargs :stobjs fn-hist :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cwd-scan)))))
  (let* ((store (fn-own-store o))
         (s (fn-sn-consumer store))
         (scoped (fn-col-scope-entry s consumer)))
    (if (not (eq (car scoped) :scope))
        scoped
      (let* ((entry (fn-cp-nth 1 scoped))
             (position (fn-cp-nth 7 entry))
             (frontier (fn-cp-nth 3 s))
             (scan (fn-cwd-scan
                    (fn-col-poll-index-window
                     fn-hist position frontier
                     *fn-col-poll-max-scan*)
                    (fn-cp-nth 3 entry) position frontier
                    *fn-col-poll-max-scan*
                    (fn-cwd-records o) (fn-cwd-withdrawn o))))
        (cond ((eq (car scan) :withdrawal)
               (list :withdrawal
                     (fn-cp-cursor-encode
                      (update-nth 9 (fn-cp-nth 1 scan)
                                  (fn-cp-scope-cursor s entry)))
                     (fn-cp-nth 2 scan)))
              ((eq (car scan) :scan) (list :scan (fn-cp-nth 2 scan)))
              (t scan))))))

; -----------------------------------------------------------------------------
; The page the host serves: the poll's ANSWER (plain, bound or waiting) with
; the withdrawals in it.  A refusal is the answer.

(defun fn-cwd-withdrawal-page (cursor msgid)
  (declare (xargs :guard t))
  (let ((report (fn-ncr-withdrawal-report (fn-record-string-octets msgid))))
    (if report (list :poll cursor report) (list :refused :report))))

(defun fn-cwd-page (o consumer answer fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (if (not (and (consp answer) (eq (car answer) :poll)))
      answer
    (let ((w (fn-cwd-poll o consumer fn-hist)))
      (cond ((eq (car w) :withdrawal)
             (fn-cwd-withdrawal-page (cadr w) (caddr w)))
            ((and (eq (car w) :scan)
                  (consp (cdr answer)) (consp (cddr answer)) (caddr answer)
                  (fn-cwd-event-withdrawn-msgid (cadr w) (fn-cwd-withdrawn o)))
             (fn-cwd-withdrawal-page
              (cadr answer)
              (fn-cwd-event-withdrawn-msgid (cadr w) (fn-cwd-withdrawn o))))
            (t answer)))))

(defthm fn-cwd-scan-of-no-withdrawn-is-no-withdrawal
  (not (equal (car (fn-cwd-scan events group position frontier budget ws nil))
              :withdrawal))
  :hints (("Goal" :induct (fn-cwd-scan events group position frontier
                                       budget ws nil)
           :in-theory (e/d (fn-cwd-cause-target-of-no-withdrawn)
                           (fn-cwd-cause-target fn-col-poll-article
                            fn-col-poll-articlep fn-col-poll-compositep
                            fn-store-event-p fn-store-event-sequence
                            fn-record-groups fn-record-octets-string
                            fn-ctl-event-msgid member-equal)))))

(local
 (defthm fn-cwd-scope-entry-is-a-scope-or-a-refusal
   (or (equal (car (fn-col-scope-entry s consumer)) :scope)
       (equal (car (fn-col-scope-entry s consumer)) :refused))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-col-scope-entry)))))

(defthm fn-cwd-poll-of-no-withdrawn
  (implies (null (fn-cwd-withdrawn o))
           (not (equal (car (fn-cwd-poll o consumer fn-hist)) :withdrawal)))
  :hints (("Goal" :use ((:instance fn-cwd-scope-entry-is-a-scope-or-a-refusal
                                   (s (fn-sn-consumer (fn-own-store o)))))
           :in-theory (e/d (fn-cwd-poll)
                           (fn-cwd-scan fn-cwd-withdrawn fn-cwd-records
                            fn-col-scope-entry fn-col-poll-index-window
                            fn-cp-cursor-encode fn-cp-scope-cursor)))))

(defthm fn-cwd-event-withdrawn-msgid-of-nil
  (not (fn-cwd-event-withdrawn-msgid e nil))
  :hints (("Goal" :in-theory (enable fn-ctl-msgid-withdrawn))))

; KEYSTONE (the page is the answer while nothing is withdrawn).  With the
; view's withdrawn list empty, what the host serves is exactly the poll's
; answer, whatever the answer is.
(defthm fn-cwd-page-without-withdrawals-is-the-answer
  (implies (null (fn-cwd-withdrawn o))
           (equal (fn-cwd-page o consumer answer fn-hist) answer))
  :hints (("Goal" :in-theory (e/d (fn-cwd-page)
                                  (fn-cwd-poll fn-cwd-withdrawn
                                   fn-cwd-event-withdrawn-msgid)))))

; The event fn-cwd-poll's :scan names is the poll's selected event.
(defthm fn-cwd-poll-scan-is-the-poll
  (let ((w (fn-cwd-poll o consumer fn-hist))
        (d (fn-col-poll o consumer fn-hist)))
    (implies (and (equal (car w) :scan) (equal (car d) :poll))
             (equal (cadr w) (caddr d))))
  :hints (("Goal" :in-theory (e/d (fn-cwd-poll fn-col-poll)
                                  (fn-cwd-withdrawn fn-cwd-records
                                   fn-col-scope-entry fn-col-poll-index-window
                                   fn-cp-cursor-encode fn-cp-scope-cursor
                                   fn-col-poll-scan fn-cwd-scan))
           :use ((:instance fn-cwd-scan-is-the-poll-scan-unless-a-withdrawal
                            (events (fn-col-poll-index-window
                                     fn-hist
                                     (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry
                                                                (fn-sn-consumer (fn-own-store o))
                                                                consumer)))
                                     (fn-cp-nth 3 (fn-sn-consumer (fn-own-store o)))
                                     *fn-col-poll-max-scan*))
                            (group (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                                              (fn-sn-consumer (fn-own-store o))
                                                              consumer))))
                            (position (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry
                                                                 (fn-sn-consumer (fn-own-store o))
                                                                 consumer))))
                            (frontier (fn-cp-nth 3 (fn-sn-consumer (fn-own-store o))))
                            (budget *fn-col-poll-max-scan*)
                            (ws (fn-cwd-records o))
                            (withdrawn (fn-cwd-withdrawn o)))))))

(local
 (defthm fn-cwd-col-scan-is-a-scan-or-a-refusal
   (or (equal (car (fn-col-poll-scan events group position frontier budget)) :scan)
       (equal (car (fn-col-poll-scan events group position frontier budget)) :refused))
   :rule-classes nil
   :hints (("Goal" :induct (fn-col-poll-scan events group position frontier budget)
            :in-theory (e/d (fn-col-poll-scan)
                            (fn-col-poll-article fn-col-poll-articlep
                             fn-col-poll-compositep))))))

; When the poll answers a page, the scan with withdrawals stops at a
; withdrawal or selects as the poll did.
(defthm fn-cwd-poll-of-a-page
  (implies (equal (car (fn-col-poll o consumer fn-hist)) :poll)
           (or (equal (car (fn-cwd-poll o consumer fn-hist)) :withdrawal)
               (equal (car (fn-cwd-poll o consumer fn-hist)) :scan)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwd-poll fn-col-poll)
                                  (fn-cwd-withdrawn fn-cwd-records
                                   fn-col-scope-entry fn-col-poll-index-window
                                   fn-cp-cursor-encode fn-cp-scope-cursor
                                   fn-col-poll-scan fn-cwd-scan))
           :use ((:instance fn-cwd-scan-is-the-poll-scan-unless-a-withdrawal
                            (events (fn-col-poll-index-window
                                     fn-hist
                                     (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry
                                                                (fn-sn-consumer (fn-own-store o))
                                                                consumer)))
                                     (fn-cp-nth 3 (fn-sn-consumer (fn-own-store o)))
                                     *fn-col-poll-max-scan*))
                            (group (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                                              (fn-sn-consumer (fn-own-store o))
                                                              consumer))))
                            (position (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry
                                                                 (fn-sn-consumer (fn-own-store o))
                                                                 consumer))))
                            (frontier (fn-cp-nth 3 (fn-sn-consumer (fn-own-store o))))
                            (budget *fn-col-poll-max-scan*)
                            (ws (fn-cwd-records o))
                            (withdrawn (fn-cwd-withdrawn o)))
                 (:instance fn-cwd-scope-entry-is-a-scope-or-a-refusal
                            (s (fn-sn-consumer (fn-own-store o))))
                 (:instance fn-cwd-col-scan-is-a-scan-or-a-refusal
                            (events (fn-col-poll-index-window
                                     fn-hist
                                     (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry
                                                                (fn-sn-consumer (fn-own-store o))
                                                                consumer)))
                                     (fn-cp-nth 3 (fn-sn-consumer (fn-own-store o)))
                                     *fn-col-poll-max-scan*))
                            (group (fn-cp-nth 3 (fn-cp-nth 1 (fn-col-scope-entry
                                                              (fn-sn-consumer (fn-own-store o))
                                                              consumer))))
                            (position (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry
                                                                 (fn-sn-consumer (fn-own-store o))
                                                                 consumer))))
                            (frontier (fn-cp-nth 3 (fn-sn-consumer (fn-own-store o))))
                            (budget *fn-col-poll-max-scan*))))))

; A withdrawal page is the refusal by name or a withdrawal report.
(defthm fn-cwd-withdrawal-page-is-a-withdrawal-or-a-refusal
  (let ((p (fn-cwd-withdrawal-page cursor msgid)))
    (or (equal (car p) :refused)
        (and (equal (car p) :poll)
             (equal (car (fn-ncr-withdrawal-decode (caddr p))) :withdrawn))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ncr-withdrawal-roundtrip
                                   (msgid (fn-record-string-octets msgid))))
           :in-theory (e/d (fn-cwd-withdrawal-page)
                           (fn-ncr-withdrawal-roundtrip fn-ncr-withdrawal-report
                            fn-ncr-withdrawal-decode fn-record-string-octets)))))

; KEYSTONE (a: never the withdrawn content).  When the event the poll
; selects is an article the view withdrew, the page the host serves over any
; answer that carries a report is a refusal or a withdrawal report: the
; report `fn-ncr-withdrawal-decode' reads as (:withdrawn MSGID), which holds
; the Message-ID and nothing of the article.
(defthm fn-cwd-page-never-serves-withdrawn-content
  (let ((r (fn-cwd-page o consumer answer fn-hist))
        (d (fn-col-poll o consumer fn-hist)))
    (implies (and (equal (car answer) :poll) (caddr answer)
                  (equal (car d) :poll) (caddr d)
                  (fn-cwd-event-withdrawn-msgid (caddr d) (fn-cwd-withdrawn o)))
             (or (equal (car r) :refused)
                 (equal (car (fn-ncr-withdrawal-decode (caddr r))) :withdrawn))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cwd-poll-scan-is-the-poll)
                 (:instance fn-cwd-poll-of-a-page)
                 (:instance fn-cwd-withdrawal-page-is-a-withdrawal-or-a-refusal
                            (cursor (cadr (fn-cwd-poll o consumer fn-hist)))
                            (msgid (caddr (fn-cwd-poll o consumer fn-hist))))
                 (:instance fn-cwd-withdrawal-page-is-a-withdrawal-or-a-refusal
                            (cursor (cadr answer))
                            (msgid (fn-cwd-event-withdrawn-msgid
                                    (cadr (fn-cwd-poll o consumer fn-hist))
                                    (fn-cwd-withdrawn o)))))
           :in-theory (union-theories '(fn-cwd-page) (theory 'minimal-theory)))))

; KEYSTONE (b3: the delivered withdrawal is the scan's).  When the scan stops
; at a withdrawing cause, the page over any accepted answer is the
; withdrawal report naming the scan's article, at the cursor fn-cwd-poll
; built from the scan's NEXT (or, for a Message-ID no report can carry, the
; refusal by name, never the article).
(defthm fn-cwd-page-of-a-withdrawal
  (let ((w (fn-cwd-poll o consumer fn-hist)))
    (implies (and (equal (car answer) :poll)
                  (equal (car w) :withdrawal))
             (equal (fn-cwd-page o consumer answer fn-hist)
                    (fn-cwd-withdrawal-page (cadr w) (caddr w)))))
  :hints (("Goal" :in-theory (e/d (fn-cwd-page) (fn-cwd-poll)))))

; A refusal (the bound gate's, the scope's) is served unchanged.
(defthm fn-cwd-page-of-a-refusal
  (implies (not (equal (car answer) :poll))
           (equal (fn-cwd-page o consumer answer fn-hist) answer))
  :hints (("Goal" :in-theory (enable fn-cwd-page))))

; -----------------------------------------------------------------------------
; The wait (PRF-252) over the page: a waiting consumer is woken and answered
; by a withdrawal exactly as by an article.  The poll it runs is the one the
; host's wait runs, over the live payload arena (books/consumer-wait.lisp
; fn-cwait-poll-over, the records flip).

(defun fn-cwd-wait-page-over (oc acfg consumer secret fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :verify-guards nil))
  (fn-cwd-page (fn-ocfg-owner oc) consumer
               (fn-cwait-poll-over oc acfg consumer secret fn-arena fn-hist) fn-hist))

(defun fn-cwd-wait-step-over (oc acfg consumer secret elapsed seconds fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :verify-guards nil))
  (fn-cwait-decide (fn-cwd-wait-page-over oc acfg consumer secret fn-arena fn-hist)
                   elapsed seconds))

(local
 (defthm fn-cwd-empty-pagep-is-a-list
   (implies (not (consp x)) (not (fn-cwait-empty-pagep x)))))

; KEYSTONE (the wait answers the page at its return point): the step answers
; exactly the page, or sleeps, only on an empty page before the deadline, as
; fn-cwait-step-over-is-the-poll-or-a-sleep-on-an-empty-page for the poll.
(defthm fn-cwd-wait-step-over-is-the-page-or-a-sleep-on-an-empty-page
  (let ((r (fn-cwd-wait-step-over oc acfg consumer secret elapsed seconds fn-arena fn-hist))
        (p (fn-cwd-wait-page-over oc acfg consumer secret fn-arena fn-hist)))
    (and (or (equal r (list :answer p))
             (and (equal (car r) :sleep)
                  (fn-cwait-empty-pagep p)
                  (natp elapsed)
                  (< elapsed (fn-cwait-deadline-ms seconds))
                  (posp (cadr r))
                  (equal (+ elapsed (cadr r))
                         (fn-cwait-deadline-ms seconds))))
         (implies (<= (fn-cwait-deadline-ms seconds) elapsed)
                  (equal r (list :answer p)))
         (implies (not (fn-cwait-empty-pagep p))
                  (equal r (list :answer p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwd-wait-step-over fn-cwait-decide
                                   fn-cwd-empty-pagep-is-a-list)
                                  (fn-cwd-wait-page-over fn-cwait-empty-pagep)))))

(verify-guards fn-cwd-wait-page-over)
(verify-guards fn-cwd-wait-step-over)
