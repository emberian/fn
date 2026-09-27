; Teeth for books/consumer-withdrawal (PKT-710; lane friend-blockers-2): the
; consumer gets the withdrawal event, never the withdrawn content.
;
; Two kinds of witness, labelled:
;   * CONSTRUCTED (the first part): consumer-owner-local-tests' committed
;     Store, with the view's withdrawn list and records WRITTEN BY HAND
;     (`cwdt-with-withdrawals', an update-nth of the view) and a stand-in
;     report as the answer.  They exercise the arms; they are not states the
;     host reaches.
;   * REACHED (the second part, lane audit-fixes): the withdrawals are the
;     ones fn-own-refresh decided when an author cancel completed through the
;     owner's POST events (owner-cancel-refresh-tests' path), and the answer
;     is the host's: host/owner-host.lisp fn-owner-consumer-local-poll serves
;     `(fn-cwd-page owner consumer (fn-cbind-plain-poll-over ocfg consumer
;     fn-arena))', the plain poll over the arena that interned the rows.
(in-package "ACL2")
(include-book "../../books/consumer-withdrawal")
(include-book "consumer-owner-local-tests")
(include-book "owner-cancel-refresh-tests") ; the flipped owner's cancel through the POST path
(include-book "must-fail-checked")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-col-poll-h (o consumer)
  ; fn-col-poll over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-col-poll o consumer fn-hist) fn-hist))
      ans)))
(defun fn-cwd-page-h (o consumer answer)
  ; fn-cwd-page over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-cwd-page o consumer answer fn-hist) fn-hist))
      ans)))
(defun fn-cwd-poll-h (o consumer)
  ; fn-cwd-poll over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-cwd-poll o consumer fn-hist) fn-hist))
      ans)))
(defun fn-col-poll-index-window-hx (hist position frontier budget)
  ; fn-col-poll-index-window over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-col-poll-index-window fn-hist position frontier budget) fn-hist))
      ans)))

; The owner O with its view's withdrawal records WS and withdrawn list N.
(defun cwdt-with-withdrawals (o ws n)
  (update-nth 1 (update-nth 8 n (update-nth 6 ws (fn-own-view o))) o))

(defconst *cwdt-o* (fn-own-start *colt-after-article* 2))
(defconst *cwdt-target* (fn-make-article "<poll@fn.test>" 0 '("fn.test") nil t nil))
(defconst *cwdt-record*
  (fn-ctl-withdrawal-make "<poll@fn.test>" "<cancel@fn.test>" "alice" :author 1))
(defconst *cwdt-ow* (cwdt-with-withdrawals *cwdt-o* (list *cwdt-record*)
                                         (list *cwdt-target*)))
(assert-event (equal (fn-cwd-withdrawn *cwdt-ow*) (list *cwdt-target*)))
(assert-event (equal (fn-cwd-records *cwdt-ow*) (list *cwdt-record*)))
(assert-event (null (fn-cwd-withdrawn *cwdt-o*)))
(defconst *cwdt-msgid* (fn-record-string-octets "<poll@fn.test>"))

; CONSTRUCTED answers: pages of the poll's own cursor carrying a stand-in
; article report (the host's answer is fn-cbind-plain-poll-over's, which
; reads a held row's report through the arena; the REACHED part below uses
; it).  Every keystone here holds over ANY answer.
(defconst *cwdt-report* '(65 66 67))
(defconst *cwdt-d* (fn-col-poll-h *cwdt-o* *colt-id*))
(assert-event (equal (car *cwdt-d*) :poll))
(assert-event (equal (caddr *cwdt-d*) *colt-article*))
(defconst *cwdt-answer* (list :poll (cadr *cwdt-d*) *cwdt-report*))

; ---------------------------------------------------------------------------
; fn-cwd-page-without-withdrawals-is-the-answer.  Positive: the view has no
; withdrawn article, and the page is the answer.
(assert-event (null (fn-cwd-withdrawn *cwdt-o*)))
(assert-event (equal (fn-cwd-page-h *cwdt-o* *colt-id* *cwdt-answer*) *cwdt-answer*))
; Hypothesis (nothing withdrawn): with the article withdrawn the page is
; not the answer.
(assert-event (not (equal (fn-cwd-page-h *cwdt-ow* *colt-id* *cwdt-answer*)
                          *cwdt-answer*)))

; ---------------------------------------------------------------------------
; fn-cwd-page-never-serves-withdrawn-content.  Positive: the answer carries a
; report, the poll selects <poll@fn.test>, the view withdrew it; the page
; is the withdrawal report of its Message-ID at the answer's cursor.
(defconst *cwdt-answer-w* (list :poll (cadr (fn-col-poll-h *cwdt-ow* *colt-id*)) *cwdt-report*))
(defconst *cwdt-d-w* (fn-col-poll-h *cwdt-ow* *colt-id*))
(defconst *cwdt-page-w* (fn-cwd-page-h *cwdt-ow* *colt-id* *cwdt-answer-w*))
(assert-event (equal (car *cwdt-answer-w*) :poll))
(assert-event (caddr *cwdt-answer-w*))
(assert-event (equal (car *cwdt-d-w*) :poll))
(assert-event (equal (caddr *cwdt-d-w*) *colt-article*))
(assert-event (equal (fn-cwd-event-withdrawn-msgid (caddr *cwdt-d-w*)
                                                   (fn-cwd-withdrawn *cwdt-ow*))
                     "<poll@fn.test>"))
(assert-event (equal (fn-ncr-withdrawal-decode (caddr *cwdt-page-w*))
                     (list :withdrawn *cwdt-msgid*)))
(assert-event (equal *cwdt-page-w*
                     (list :poll (cadr *cwdt-answer-w*)
                           (fn-ncr-withdrawal-report *cwdt-msgid*))))
; No octet of the article's payload is in the page's report.
(assert-event (equal (len (caddr *cwdt-page-w*)) (+ 5 (len *cwdt-msgid*))))
; Hypothesis (the view withdrew it): without it the report is the article's.
(assert-event (equal (fn-cwd-page-h *cwdt-o* *colt-id* *cwdt-answer*) *cwdt-answer*))
(assert-event (not (equal (car (fn-ncr-withdrawal-decode *cwdt-report*)) :withdrawn)))
; Hypothesis (the answer carries a report): an empty page stays empty, and
; is not a withdrawal.
(defconst *cwdt-empty* (list :poll (cadr *cwdt-answer-w*) nil))
(assert-event (equal (fn-cwd-page-h *cwdt-ow* *colt-id* *cwdt-empty*) *cwdt-empty*))
; fn-cwd-page-of-a-refusal: the bound gate's refusal is served unchanged.
(assert-event (equal (fn-cwd-page-h *cwdt-ow* *colt-id* '(:refused :credential))
                     '(:refused :credential)))
; An unknown consumer's refusal is its own.
(assert-event (equal (fn-cwd-poll-h *cwdt-ow* '(88)) '(:refused :unknown-consumer)))

; ---------------------------------------------------------------------------
; (b) A cancel after delivery: a history with the article at 2 and a cancel
; in control.cancel at 3; the consumer's scan starts at 3 (past the article).
(defconst *cwdt-cancel*
  (fn-held-plain (fn-record-make 3 3 3 "<cancel@fn.test>" '(67)
                  '("control.cancel") "cancel-pin" "cancel-content"
                  "cancel-release" 1 841000002) 1))
(defconst *cwdt-group-text* (fn-record-octets-string *colt-group*))
(assert-event (equal *cwdt-group-text* "fn.test"))
(assert-event (equal (fn-ctl-event-msgid *cwdt-cancel*) "<cancel@fn.test>"))
(assert-event (equal (fn-cwd-cause-target "<cancel@fn.test>" (list *cwdt-record*)
                                          (list *cwdt-target*) *cwdt-group-text*)
                     "<poll@fn.test>"))

; fn-cwd-scan-delivers-a-withdrawing-cause.  Positive: a positive budget,
; the position below the frontier, the event at the position is a history
; event there, no unbound composite, no article of fn.test, and its record
; withdrew an fn.test article: the scan stops at it and names the article.
(assert-event (fn-store-event-p *cwdt-cancel*))
(assert-event (equal (fn-store-event-sequence *cwdt-cancel*) 3))
(assert-event (not (and (fn-col-poll-compositep *cwdt-cancel*)
                        (not (fn-col-poll-article *cwdt-cancel*)))))
(assert-event (not (member-equal *cwdt-group-text*
                                 (fn-record-groups (fn-col-poll-article *cwdt-cancel*)))))
(defconst *cwdt-scan-b*
  (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 3 4 16
               (list *cwdt-record*) (list *cwdt-target*)))
(assert-event (equal *cwdt-scan-b* (list :withdrawal 4 "<poll@fn.test>")))
; fn-cwd-scan-withdrawal-advances: past the position, within the frontier.
(assert-event (and (< 3 (cadr *cwdt-scan-b*)) (<= (cadr *cwdt-scan-b*) 4)))
; Hypothesis (the record withdrew an article of the group): the same cancel
; with nothing withdrawn, or withdrawing an article of another group, or a
; record caused by another article, is scanned past, as the poll scans.
(assert-event (equal (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 3 4 16
                                  (list *cwdt-record*) nil)
                     (fn-col-poll-scan (list *cwdt-cancel*) *colt-group* 3 4 16)))
(assert-event (equal (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 3 4 16
                                  (list *cwdt-record*)
                                  (list (fn-make-article "<poll@fn.test>" 0
                                                         '("fn.other") nil t nil)))
                     (list :scan 4 nil)))
(assert-event (equal (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 3 4 16
                                  (list (fn-ctl-withdrawal-make
                                         "<poll@fn.test>" "<other@fn.test>"
                                         "alice" :author 1))
                                  (list *cwdt-target*))
                     (list :scan 4 nil)))
; Hypothesis (a budget, the frontier ahead): none, no withdrawal.
(assert-event (equal (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 3 4 0
                                  (list *cwdt-record*) (list *cwdt-target*))
                     (list :scan 3 nil)))
(assert-event (equal (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 3 3 16
                                  (list *cwdt-record*) (list *cwdt-target*))
                     (list :scan 3 nil)))
; Hypothesis (the event is at the position): a gap is the history refusal.
(assert-event (equal (fn-cwd-scan (list *cwdt-cancel*) *colt-group* 2 4 16
                                  (list *cwdt-record*) (list *cwdt-target*))
                     '(:refused :history)))
; An article of the group before the cancel is selected first (the scan is
; the poll's there): fn-cwd-scan-is-the-poll-scan-unless-a-withdrawal.
(assert-event (equal (fn-cwd-scan (list *colt-article* *cwdt-cancel*) *colt-group* 2 4 16
                                  (list *cwdt-record*) (list *cwdt-target*))
                     (fn-col-poll-scan (list *colt-article* *cwdt-cancel*)
                                       *colt-group* 2 4 16)))
(assert-event (equal (fn-cwd-scan (list *colt-article* *cwdt-cancel*) *colt-group* 2 4 16
                                  (list *cwdt-record*) (list *cwdt-target*))
                     (list :scan 3 *colt-article*)))

; ---------------------------------------------------------------------------
; fn-cwd-page-of-a-withdrawal over a committed Store: groups fn.test and
; control.cancel, consumer (7) on fn.test, and the cancel in control.cancel
; at sequence 2, the consumer's position.  The view withdrew <poll@fn.test>
; (an fn.test article) by the cancel's record.  The poll's own page is empty
; (no fn.test article in the window); the page is the withdrawal.
(defconst *cwdt-boot2*
  (colt-commit (fn-sn-initial '("fn.test" "control.cancel") 16)
               (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
(defconst *cwdt-reg2* (fn-col-register (fn-own-start *cwdt-boot2* 2) 256 *colt-id* *colt-group*))
(assert-event (eq (car *cwdt-reg2*) :write))
(defconst *cwdt-s2* (colt-commit *cwdt-boot2* (cadr *cwdt-reg2*)))
(defconst *cwdt-cancel2*
  (fn-held-plain (fn-record-make 2 2 2 "<cancel@fn.test>" '(67)
                  '("control.cancel") "cancel-pin" "cancel-content"
                  "cancel-release" 1 841000002) 0))
(defconst *cwdt-s-cancel*
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare (colt-reserve *cwdt-s2*) *cwdt-cancel2*)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(assert-event (equal (fn-sf-phase (fn-sn-files *cwdt-s-cancel*)) :ready))
(defconst *cwdt-o-cancel*
  (cwdt-with-withdrawals (fn-own-start *cwdt-s-cancel* 2)
                         (list *cwdt-record*) (list *cwdt-target*)))
; The poll (without withdrawals) scans past the cancel: an empty page.
(defconst *cwdt-d-cancel* (fn-col-poll-h *cwdt-o-cancel* *colt-id*))
(assert-event (equal (car *cwdt-d-cancel*) :poll))
(assert-event (null (caddr *cwdt-d-cancel*)))
; Positive: the answer is accepted, fn-cwd-poll stops at the withdrawal.
(defconst *cwdt-w-cancel* (fn-cwd-poll-h *cwdt-o-cancel* *colt-id*))
(assert-event (equal (car *cwdt-w-cancel*) :withdrawal))
(assert-event (equal (caddr *cwdt-w-cancel*) "<poll@fn.test>"))
; Its cursor is the poll's cursor shape, at the cancel's next position (3).
(assert-event (equal (fn-cp-nth 9 (fn-cp-nth 1 (fn-cp-cursor-decode (cadr *cwdt-w-cancel*))))
                     3))
(defconst *cwdt-empty-cancel* (list :poll (cadr *cwdt-d-cancel*) nil))
(assert-event (equal (fn-cwd-page-h *cwdt-o-cancel* *colt-id* *cwdt-empty-cancel*)
                     (fn-cwd-withdrawal-page (cadr *cwdt-w-cancel*) (caddr *cwdt-w-cancel*))))
(assert-event (equal (fn-cwd-page-h *cwdt-o-cancel* *colt-id* *cwdt-empty-cancel*)
                     (list :poll (cadr *cwdt-w-cancel*)
                           (fn-ncr-withdrawal-report *cwdt-msgid*))))
; Hypothesis (the answer is accepted): a refusal is served unchanged.
(assert-event (equal (fn-cwd-page-h *cwdt-o-cancel* *colt-id* '(:refused :access))
                     '(:refused :access)))
; Hypothesis (a withdrawal): with nothing withdrawn, the empty page stays.
(assert-event (equal (fn-cwd-page-h (fn-own-start *cwdt-s-cancel* 2) *colt-id*
                                  *cwdt-empty-cancel*)
                     *cwdt-empty-cancel*))

; ---------------------------------------------------------------------------
; fn-cwd-wait-step-over-is-the-page-or-a-sleep-on-an-empty-page: a withdrawal page
; is not empty, so a wait answers it at once (fn-cwait-decide over the page).
(assert-event (not (fn-cwait-empty-pagep *cwdt-page-w*)))
(assert-event (equal (fn-cwait-decide *cwdt-page-w* 0 300) (list :answer *cwdt-page-w*)))
(assert-event (equal (fn-cwait-decide *cwdt-empty* 0 300) (list :sleep 300000)))

; =============================================================================
; REACHED witnesses (lane audit-fixes, packet G6-2 of the keystone audit of
; 2026-09-27).  Everything above this line runs over a view whose withdrawn
; list and records were WRITTEN BY HAND (`cwdt-with-withdrawals', an
; `update-nth' of the view) and over a stand-in report: those are
; CONSTRUCTED-STATE witnesses, kept as such.  Below, the view is the one
; the owner's refresh built, and the answer is the host's:
;
;   * the Store is bootstrapped and consumer (7) registered on fn.letters
;     (consumer-owner-local-tests' commits), then owner-tests' owner opens a
;     reader and the CLI connection, and two POSTs run through the owner's
;     own events (owner-cancel-refresh-tests' `ocr-post': :begin, the
;     Store's prepare of the interned row, the I/O acknowledgements,
;     :complete, whose fn-own-refresh decides the withdrawals): T at
;     sequence 2 with `Cancel-Lock: sha256:L', then C at sequence 3,
;     `Control: cancel <T>' with the matching `Cancel-Key', posted to
;     fn.test (not the consumer's group);
;   * the answer is `fn-cbind-plain-poll-over' over an arena that interned
;     T's and C's bytes at the rows' handles 0 and 1 (the host call,
;     host/owner-host.lisp fn-owner-consumer-local-poll: `(fn-cwd-page
;     owner consumer (fn-cbind-plain-poll-over ocfg consumer fn-arena))');
;   * the consumer's acknowledgement of T's cursor is committed through the
;     Store (`fn-col-ack', the host's consumer ack) and the owner reopened
;     over that Store (`fn-own-start', the host's open).

(defconst *cwdr-letters* (fn-record-string-octets "fn.letters"))
(defconst *cwdr-boot*
  (colt-commit (fn-sn-initial *own-groups* 10) (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
(defconst *cwdr-reg* (fn-col-register (fn-own-start *cwdr-boot* 4) 256 *colt-id* *cwdr-letters*))
(assert-event (eq (car *cwdr-reg*) :write))
(defconst *cwdr-s-reg* (colt-commit *cwdr-boot* (cadr *cwdr-reg*)))
(defconst *cwdr-o0* (fn-own-start *cwdr-s-reg* 4))
(defconst *cwdr-a* (cdr (fn-own-open *cwdr-o0* nil)))
(defconst *cwdr-b* (in-arena-fn-own-step *sr-arena* *cwdr-a* '(:open)))
(assert-event (equal (fn-sf-frontier (fn-sn-files (fn-own-store *cwdr-b*))) 2))

(defun cwdr-row (sequence msgid bytes groups handle)
  (fn-hrt-row-at (fn-record-make sequence sequence sequence msgid bytes groups
                                 (concatenate 'string "own-pin:" msgid)
                                 (concatenate 'string "own-content:" msgid)
                                 (concatenate 'string "own-release:" msgid)
                                 2 841000000)
                 handle))
(defun cwdr-c-bytes (key group)
  (ocr-octets (list "From: friend <friend@example.invalid>"
                    (concatenate 'string "Newsgroups: " group)
                    "Subject: cmsg cancel <lt@example>" "Message-ID: <lc@example>"
                    "Control: cancel <lt@example>"
                    (concatenate 'string "Cancel-Key: sha256:" key))))
(defun cwdr-oc (o) (fn-ocfg-make o (fn-cfg-make 0 (fn-cfg-value (fn-cfg-initial))) nil nil))
(include-book "arena-hist-lift")
(bpr-lift-hist fn-cbind-plain-poll-over 2 (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner x1)))))

; The arguments `fn-cwd-poll' hands `fn-cwd-scan' (its let*, verbatim).
(defun cwdr-scan-args (o consumer)
  (let* ((store (fn-own-store o))
         (s (fn-sn-consumer store))
         (scoped (fn-col-scope-entry s consumer))
         (entry (fn-cp-nth 1 scoped))
         (position (fn-cp-nth 7 entry))
         (frontier (fn-cp-nth 3 s)))
    (list (fn-col-poll-index-window-hx (fn-sf-records (fn-sn-files store)) position frontier
                                    *fn-col-poll-max-scan*)
          (fn-cp-nth 3 entry) position frontier *fn-col-poll-max-scan*
          (fn-cwd-records o) (fn-cwd-withdrawn o))))
(defun cwdr-scan (args)
  (fn-cwd-scan (nth 0 args) (nth 1 args) (nth 2 args) (nth 3 args) (nth 4 args)
               (nth 5 args) (nth 6 args)))

; One scenario: T, then a cancel C (KEY, posted to GROUP); the owner after
; T, after C, and reopened after the consumer acknowledged T.
(defun cwdr-scenario (key group)
  (declare (xargs :verify-guards nil))
  (let* ((cb (cwdr-c-bytes key group))
         (payloads (list *ocr-t-bytes* cb))
         (rt (cwdr-row 2 "<lt@example>" *ocr-t-bytes* '("fn.letters") 0))
         (rc (cwdr-row 3 "<lc@example>" cb (list group) 1))
         (after-t (in-arena-ocr-post payloads *cwdr-b* rt))
         (after (in-arena-ocr-post payloads after-t rc))
         (answer (in-arena-fn-cbind-plain-poll-over payloads (cwdr-oc after) *colt-id*))
         (ack (fn-col-ack after (cadr answer)))
         (acked (fn-own-start (colt-commit (fn-own-store after) (cadr ack)) 4)))
    (list payloads after-t after answer ack acked)))

(defconst *cwdr* (cwdr-scenario *ocr-key* "fn.test"))
(defconst *cwdr-payloads* (nth 0 *cwdr*))
(defconst *cwdr-after-t* (nth 1 *cwdr*))
(defconst *cwdr-after* (nth 2 *cwdr*))
(defconst *cwdr-answer-a* (nth 3 *cwdr*))
(defconst *cwdr-acked* (nth 5 *cwdr*))

; Every owner is related, the refresh withdrew T and holds C's record.
(assert-event
 (and (fn-own-relation *cwdr-after-t*)
      (fn-own-relation *cwdr-after*)
      (fn-own-relation *cwdr-acked*)
      (eq (car (nth 4 *cwdr*)) :write)
      (equal (ocr-archive *cwdr-after-t*) (list "<lt@example>"))
      (null (fn-cwd-withdrawn *cwdr-after-t*))
      (equal (ocr-archive *cwdr-after*) (list "<lc@example>"))
      (equal (fn-article-msgids (fn-cwd-withdrawn *cwdr-after*)) (list "<lt@example>"))
      (equal (fn-article-msgids (fn-cwd-withdrawn *cwdr-acked*)) (list "<lt@example>"))
      (equal (len (fn-cwd-records *cwdr-after*)) 1)
      (equal (fn-ctl-w-cause (car (fn-cwd-records *cwdr-after*))) "<lc@example>")))

; ---------------------------------------------------------------------------
; fn-cwd-page-never-serves-withdrawn-content, REACHED.  The consumer at its
; registered position 2 polls T, which the refresh withdrew.  The host's
; answer carries T's own report (its bytes, read through the arena); the
; page the host serves is the withdrawal report of T's Message-ID.
(defconst *cwdr-d-a* (fn-col-poll-h *cwdr-after* *colt-id*))
(defconst *cwdr-page-a* (fn-cwd-page-h *cwdr-after* *colt-id* *cwdr-answer-a*))
(assert-event
 (and ;; the complete antecedent
      (equal (car *cwdr-answer-a*) :poll) (caddr *cwdr-answer-a*)
      (equal (car *cwdr-d-a*) :poll) (caddr *cwdr-d-a*)
      (equal (fn-cwd-event-withdrawn-msgid (caddr *cwdr-d-a*) (fn-cwd-withdrawn *cwdr-after*))
             "<lt@example>")
      ;; the conclusion
      (equal (car (fn-ncr-withdrawal-decode (caddr *cwdr-page-a*))) :withdrawn)
      ;; what it excludes: the answer was T's content
      (equal (fn-record-msgid (caddr *cwdr-d-a*)) "<lt@example>")
      (not (equal (car (fn-ncr-withdrawal-decode (caddr *cwdr-answer-a*))) :withdrawn))
      (equal (caddr *cwdr-page-a*)
             (fn-ncr-withdrawal-report (fn-record-string-octets "<lt@example>")))))

; Without (the view withdrew the selected article), REACHED: the owner
; after T only.  The same poll selects T, nothing is withdrawn, and the page
; is the answer: T's report, no refusal and no withdrawal.
(defconst *cwdr-d-t* (fn-col-poll-h *cwdr-after-t* *colt-id*))
(defconst *cwdr-answer-t*
  (in-arena-fn-cbind-plain-poll-over *cwdr-payloads* (cwdr-oc *cwdr-after-t*) *colt-id*))
(defconst *cwdr-page-t* (fn-cwd-page-h *cwdr-after-t* *colt-id* *cwdr-answer-t*))
(assert-event
 (and (equal (car *cwdr-answer-t*) :poll) (caddr *cwdr-answer-t*)
      (equal (car *cwdr-d-t*) :poll) (caddr *cwdr-d-t*)
      (not (fn-cwd-event-withdrawn-msgid (caddr *cwdr-d-t*) (fn-cwd-withdrawn *cwdr-after-t*)))
      (equal *cwdr-page-t* *cwdr-answer-t*)
      (not (equal (car *cwdr-page-t*) :refused))
      (not (equal (car (fn-ncr-withdrawal-decode (caddr *cwdr-page-t*))) :withdrawn))))
(must-fail-checked
 (assert-event
  (let ((r *cwdr-page-t*))
    (or (equal (car r) :refused)
        (equal (car (fn-ncr-withdrawal-decode (caddr r))) :withdrawn)))))

; Without (the answer carries a report), CONSTRUCTED answer over the reached
; owner: an accepted answer with no report is served as it is.
(defconst *cwdr-answer-empty* (list :poll (cadr *cwdr-answer-a*) nil))
(assert-event
 (let ((r (fn-cwd-page-h *cwdr-after* *colt-id* *cwdr-answer-empty*)))
   (and (equal (car *cwdr-answer-empty*) :poll) (not (caddr *cwdr-answer-empty*))
        (equal (car *cwdr-d-a*) :poll) (caddr *cwdr-d-a*)
        (fn-cwd-event-withdrawn-msgid (caddr *cwdr-d-a*) (fn-cwd-withdrawn *cwdr-after*))
        (equal r *cwdr-answer-empty*)
        (not (equal (car r) :refused))
        (not (equal (car (fn-ncr-withdrawal-decode (caddr r))) :withdrawn)))))

; Without (the answer is accepted), CONSTRUCTED answer: an answer of another
; kind carrying T's report is passed through unchanged, report and all (the
; host's answers are :poll or :refused, so this is the gate's shape, not a
; host state).
(defconst *cwdr-answer-other* (cons :other (cdr *cwdr-answer-a*)))
(assert-event
 (let ((r (fn-cwd-page-h *cwdr-after* *colt-id* *cwdr-answer-other*)))
   (and (not (equal (car *cwdr-answer-other*) :poll)) (caddr *cwdr-answer-other*)
        (equal (car *cwdr-d-a*) :poll) (caddr *cwdr-d-a*)
        (fn-cwd-event-withdrawn-msgid (caddr *cwdr-d-a*) (fn-cwd-withdrawn *cwdr-after*))
        (equal r *cwdr-answer-other*)
        (not (equal (car r) :refused))
        (not (equal (car (fn-ncr-withdrawal-decode (caddr r))) :withdrawn)))))

; (equal (car d) :poll) and (caddr d) have no separate removal: the poll
; answers (:poll CURSOR EVENT) or a two-element refusal, whose third element
; is NIL, and an event the view withdrew is not NIL.  Evaluated here: an
; unknown consumer's poll, and a withdrawn test of no event.
(assert-event
 (let ((d (fn-col-poll-h *cwdr-after* '(88))))
   (and (equal d '(:refused :unknown-consumer))
        (null (caddr d))
        (null (fn-cwd-event-withdrawn-msgid nil (fn-cwd-withdrawn *cwdr-after*))))))

; ---------------------------------------------------------------------------
; fn-cwd-scan-delivers-a-withdrawing-cause and fn-cwd-scan-withdrawal-
; advances, REACHED.  After the acknowledgement the consumer's position is
; 3, C's; C is posted to fn.test, and its record withdrew T, an fn.letters
; article.  The scan fn-cwd-poll runs (its own arguments) stops at C and
; names T; the poll's withdrawal cursor is at 4.
(defconst *cwdr-args-b* (cwdr-scan-args *cwdr-acked* *colt-id*))
(defconst *cwdr-scan-b* (cwdr-scan *cwdr-args-b*))
(defmacro cwdr-b2-hyps (args)
  `(let* ((events (nth 0 ,args)) (group (nth 1 ,args)) (position (nth 2 ,args))
          (frontier (nth 3 ,args)) (budget (nth 4 ,args)) (ws (nth 5 ,args))
          (withdrawn (nth 6 ,args)) (event (car events))
          (g (fn-record-octets-string group)))
     (and (posp budget) (natp position) (< position (nfix frontier))
          (consp events)
          (fn-store-event-p event)
          (equal (fn-store-event-sequence event) position)
          (not (and (fn-col-poll-compositep event)
                    (not (fn-col-poll-article event))))
          (not (and (fn-col-poll-articlep (fn-col-poll-article event))
                    (true-listp (fn-record-groups (fn-col-poll-article event)))
                    (member-equal g (fn-record-groups (fn-col-poll-article event)))))
          (fn-cwd-cause-target (fn-ctl-event-msgid event) ws withdrawn g))))
(defmacro cwdr-b2-concl (args)
  `(let* ((events (nth 0 ,args)) (group (nth 1 ,args)) (position (nth 2 ,args))
          (ws (nth 5 ,args)) (withdrawn (nth 6 ,args)) (event (car events))
          (g (fn-record-octets-string group)))
     (equal (cwdr-scan ,args)
            (list :withdrawal (1+ position)
                  (fn-cwd-cause-target (fn-ctl-event-msgid event) ws withdrawn g)))))
(defmacro cwdr-b1-concl (args)
  `(let ((r (cwdr-scan ,args)) (position (nth 2 ,args)) (frontier (nth 3 ,args)))
     (and (natp (cadr r)) (< position (cadr r)) (<= (cadr r) (nfix frontier)) (caddr r))))

(assert-event
 (and (equal (nth 2 *cwdr-args-b*) 3)
      (equal (nth 1 *cwdr-args-b*) *cwdr-letters*)
      (equal (fn-ctl-event-msgid (car (nth 0 *cwdr-args-b*))) "<lc@example>")
      (cwdr-b2-hyps *cwdr-args-b*)
      (cwdr-b2-concl *cwdr-args-b*)
      (equal *cwdr-scan-b* (list :withdrawal 4 "<lt@example>"))
      ;; b1: the complete antecedent and conclusion
      (natp (nth 2 *cwdr-args-b*)) (equal (car *cwdr-scan-b*) :withdrawal)
      (cwdr-b1-concl *cwdr-args-b*)
      ;; the poll the host reaches delivers it
      (equal (car (fn-cwd-poll-h *cwdr-acked* *colt-id*)) :withdrawal)
      (equal (caddr (fn-cwd-poll-h *cwdr-acked* *colt-id*)) "<lt@example>")))

; The page over the host's answer at that position is the withdrawal: the
; poll itself finds no fn.letters article there (an empty page).
(defconst *cwdr-answer-b*
  (in-arena-fn-cbind-plain-poll-over *cwdr-payloads* (cwdr-oc *cwdr-acked*) *colt-id*))
(assert-event
 (let ((w (fn-cwd-poll-h *cwdr-acked* *colt-id*)))
   (and (equal (car *cwdr-answer-b*) :poll)
        (null (caddr *cwdr-answer-b*))
        (equal (fn-cwd-page-h *cwdr-acked* *colt-id* *cwdr-answer-b*)
               (fn-cwd-withdrawal-page (cadr w) (caddr w)))
        (equal (caddr (fn-cwd-page-h *cwdr-acked* *colt-id* *cwdr-answer-b*))
               (fn-ncr-withdrawal-report (fn-record-string-octets "<lt@example>"))))))

; Without (the record withdrew an article of the group), REACHED: the same
; run with a Cancel-Key that opens nothing.  C's record is made and
; declines, nothing is withdrawn, and the scan passes C: no withdrawal (b2),
; and the scan's answer names no article (b1: (car r) is not :withdrawal and
; the conclusion's (caddr r) fails).
(defconst *cwdr-other* (cwdr-scenario *ocr-other-key* "fn.test"))
(defconst *cwdr-args-other* (cwdr-scan-args (nth 5 *cwdr-other*) *colt-id*))
(assert-event
 (let* ((args *cwdr-args-other*) (events (nth 0 args)) (event (car events))
        (g (fn-record-octets-string (nth 1 args))))
   (and (fn-own-relation (nth 5 *cwdr-other*))
        (equal (len (fn-cwd-records (nth 5 *cwdr-other*))) 1)
        (null (fn-cwd-withdrawn (nth 5 *cwdr-other*)))
        (equal (nth 2 args) 3)
        (posp (nth 4 args)) (natp (nth 2 args)) (< (nth 2 args) (nfix (nth 3 args)))
        (consp events) (fn-store-event-p event)
        (equal (fn-store-event-sequence event) (nth 2 args))
        (not (and (fn-col-poll-compositep event) (not (fn-col-poll-article event))))
        (not (and (fn-col-poll-articlep (fn-col-poll-article event))
                  (true-listp (fn-record-groups (fn-col-poll-article event)))
                  (member-equal g (fn-record-groups (fn-col-poll-article event)))))
        (not (fn-cwd-cause-target (fn-ctl-event-msgid event) (nth 5 args) (nth 6 args) g))
        (not (cwdr-b2-concl args))
        (not (equal (car (cwdr-scan args)) :withdrawal))
        (not (cwdr-b1-concl args)))))
(must-fail-checked (assert-event (cwdr-b2-concl *cwdr-args-other*)))
(must-fail-checked (assert-event (cwdr-b1-concl *cwdr-args-other*)))

; Without (the event is no article of the group), REACHED: the same run with
; C posted to fn.letters.  C is then an article of the consumer's group and
; the scan selects it as the poll does: no withdrawal.
(defconst *cwdr-letters-run* (cwdr-scenario *ocr-key* "fn.letters"))
(defconst *cwdr-args-letters* (cwdr-scan-args (nth 5 *cwdr-letters-run*) *colt-id*))
(assert-event
 (let* ((args *cwdr-args-letters*) (events (nth 0 args)) (event (car events))
        (g (fn-record-octets-string (nth 1 args))))
   (and (fn-own-relation (nth 5 *cwdr-letters-run*))
        (equal (fn-article-msgids (fn-cwd-withdrawn (nth 5 *cwdr-letters-run*)))
               (list "<lt@example>"))
        (equal (nth 2 args) 3)
        (posp (nth 4 args)) (natp (nth 2 args)) (< (nth 2 args) (nfix (nth 3 args)))
        (consp events) (fn-store-event-p event)
        (equal (fn-store-event-sequence event) (nth 2 args))
        (not (and (fn-col-poll-compositep event) (not (fn-col-poll-article event))))
        (fn-col-poll-articlep (fn-col-poll-article event))
        (true-listp (fn-record-groups (fn-col-poll-article event)))
        (member-equal g (fn-record-groups (fn-col-poll-article event)))
        (fn-cwd-cause-target (fn-ctl-event-msgid event) (nth 5 args) (nth 6 args) g)
        (equal (cwdr-scan args) (list :scan 4 event))
        (not (cwdr-b2-concl args)))))
(must-fail-checked (assert-event (cwdr-b2-concl *cwdr-args-letters*)))

; Without (a budget), (the position below the frontier) and (the event at
; the position): CONSTRUCTED arguments over the reached scan (the host
; always passes the poll's window of 16 and the consumer's own position):
; budget 0, the frontier at the position, and position 2 over the window
; that starts at 3.  None is a withdrawal.
(defconst *cwdr-args-no-budget* (update-nth 4 0 *cwdr-args-b*))
(defconst *cwdr-args-at-frontier* (update-nth 3 3 *cwdr-args-b*))
(defconst *cwdr-args-gap* (update-nth 2 2 *cwdr-args-b*))
(assert-event
 (and (not (posp (nth 4 *cwdr-args-no-budget*)))
      (equal (cwdr-scan *cwdr-args-no-budget*) (list :scan 3 nil))
      (not (cwdr-b2-concl *cwdr-args-no-budget*))
      (not (< (nth 2 *cwdr-args-at-frontier*) (nfix (nth 3 *cwdr-args-at-frontier*))))
      (equal (cwdr-scan *cwdr-args-at-frontier*) (list :scan 3 nil))
      (not (cwdr-b2-concl *cwdr-args-at-frontier*))
      (not (equal (fn-store-event-sequence (car (nth 0 *cwdr-args-gap*)))
                  (nth 2 *cwdr-args-gap*)))
      (equal (cwdr-scan *cwdr-args-gap*) '(:refused :history))
      (not (cwdr-b2-concl *cwdr-args-gap*))))
(must-fail-checked (assert-event (cwdr-b2-concl *cwdr-args-no-budget*)))
(must-fail-checked (assert-event (cwdr-b2-concl *cwdr-args-at-frontier*)))
(must-fail-checked (assert-event (cwdr-b2-concl *cwdr-args-gap*)))

; The other hypotheses of b2 have no separate removal, and b1's (natp
; position) none either: a store event's sequence is a natural, so the
; sequence hypothesis (and every :withdrawal, which only a matched event
; yields) implies (natp position); a store event is not NIL, so
; (consp events) follows from (fn-store-event-p (car events)).
(defthm cwdr-store-event-sequence-is-natural
  (implies (fn-store-event-p x) (natp (fn-store-event-sequence x)))
  :rule-classes nil)
(defthm cwdr-no-store-event-is-nil
  (not (fn-store-event-p nil))
  :rule-classes nil)
; The unbound-composite hypothesis: no composite event occurs in these
; histories (every event is a held row or a consumer event); no reached
; removal witness is claimed for it.
(assert-event (not (fn-col-poll-compositep (car (nth 0 *cwdr-args-b*)))))
