; Teeth for books/consumer-withdrawal (PKT-710; lane friend-blockers-2): the
; consumer gets the withdrawal event, never the withdrawn content.  The
; committed Store witnesses are consumer-owner-local-tests' (a bootstrapped
; history, consumer (7) registered on fn.test, the article <poll@fn.test>
; at sequence 2), and one more history with a cancel filed in
; control.cancel.  The view's withdrawal decision (withdrawn list, records)
; is set on the owner the way the live refresh will set it (lane
; flip-L8-2): on dev today it is empty.
(in-package "ACL2")
(include-book "../../books/consumer-withdrawal")
(include-book "consumer-owner-local-tests")
(include-book "std/testing/must-fail" :dir :system)

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

; The answers below are pages of the poll's own cursor carrying a stand-in
; article report: after the records flip the report of a held article row is
; read through the arena (books/history-fold-refinement.lisp
; fn-col-poll-report-over; the host still calls fn-col-poll-report, which
; refuses a held row :report, PKT recorded by this lane).  Every keystone
; here holds over ANY answer.
(defconst *cwdt-report* '(65 66 67))
(defconst *cwdt-d* (fn-col-poll *cwdt-o* *colt-id*))
(assert-event (equal (car *cwdt-d*) :poll))
(assert-event (equal (caddr *cwdt-d*) *colt-article*))
(defconst *cwdt-answer* (list :poll (cadr *cwdt-d*) *cwdt-report*))

; ---------------------------------------------------------------------------
; fn-cwd-page-without-withdrawals-is-the-answer.  Positive: the view has no
; withdrawn article, and the page is the answer.
(assert-event (null (fn-cwd-withdrawn *cwdt-o*)))
(assert-event (equal (fn-cwd-page *cwdt-o* *colt-id* *cwdt-answer*) *cwdt-answer*))
; Hypothesis (nothing withdrawn): with the article withdrawn the page is
; not the answer.
(assert-event (not (equal (fn-cwd-page *cwdt-ow* *colt-id* *cwdt-answer*)
                          *cwdt-answer*)))

; ---------------------------------------------------------------------------
; fn-cwd-page-never-serves-withdrawn-content.  Positive: the answer carries a
; report, the poll selects <poll@fn.test>, the view withdrew it; the page
; is the withdrawal report of its Message-ID at the answer's cursor.
(defconst *cwdt-answer-w* (list :poll (cadr (fn-col-poll *cwdt-ow* *colt-id*)) *cwdt-report*))
(defconst *cwdt-d-w* (fn-col-poll *cwdt-ow* *colt-id*))
(defconst *cwdt-page-w* (fn-cwd-page *cwdt-ow* *colt-id* *cwdt-answer-w*))
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
(assert-event (equal (fn-cwd-page *cwdt-o* *colt-id* *cwdt-answer*) *cwdt-answer*))
(assert-event (not (equal (car (fn-ncr-withdrawal-decode *cwdt-report*)) :withdrawn)))
; Hypothesis (the answer carries a report): an empty page stays empty, and
; is not a withdrawal.
(defconst *cwdt-empty* (list :poll (cadr *cwdt-answer-w*) nil))
(assert-event (equal (fn-cwd-page *cwdt-ow* *colt-id* *cwdt-empty*) *cwdt-empty*))
; fn-cwd-page-of-a-refusal: the bound gate's refusal is served unchanged.
(assert-event (equal (fn-cwd-page *cwdt-ow* *colt-id* '(:refused :credential))
                     '(:refused :credential)))
; An unknown consumer's refusal is its own.
(assert-event (equal (fn-cwd-poll *cwdt-ow* '(88)) '(:refused :unknown-consumer)))

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
(defconst *cwdt-d-cancel* (fn-col-poll *cwdt-o-cancel* *colt-id*))
(assert-event (equal (car *cwdt-d-cancel*) :poll))
(assert-event (null (caddr *cwdt-d-cancel*)))
; Positive: the answer is accepted, fn-cwd-poll stops at the withdrawal.
(defconst *cwdt-w-cancel* (fn-cwd-poll *cwdt-o-cancel* *colt-id*))
(assert-event (equal (car *cwdt-w-cancel*) :withdrawal))
(assert-event (equal (caddr *cwdt-w-cancel*) "<poll@fn.test>"))
; Its cursor is the poll's cursor shape, at the cancel's next position (3).
(assert-event (equal (fn-cp-nth 9 (fn-cp-nth 1 (fn-cp-cursor-decode (cadr *cwdt-w-cancel*))))
                     3))
(defconst *cwdt-empty-cancel* (list :poll (cadr *cwdt-d-cancel*) nil))
(assert-event (equal (fn-cwd-page *cwdt-o-cancel* *colt-id* *cwdt-empty-cancel*)
                     (fn-cwd-withdrawal-page (cadr *cwdt-w-cancel*) (caddr *cwdt-w-cancel*))))
(assert-event (equal (fn-cwd-page *cwdt-o-cancel* *colt-id* *cwdt-empty-cancel*)
                     (list :poll (cadr *cwdt-w-cancel*)
                           (fn-ncr-withdrawal-report *cwdt-msgid*))))
; Hypothesis (the answer is accepted): a refusal is served unchanged.
(assert-event (equal (fn-cwd-page *cwdt-o-cancel* *colt-id* '(:refused :access))
                     '(:refused :access)))
; Hypothesis (a withdrawal): with nothing withdrawn, the empty page stays.
(assert-event (equal (fn-cwd-page (fn-own-start *cwdt-s-cancel* 2) *colt-id*
                                  *cwdt-empty-cancel*)
                     *cwdt-empty-cancel*))

; ---------------------------------------------------------------------------
; fn-cwd-wait-step-over-is-the-page-or-a-sleep-on-an-empty-page: a withdrawal page
; is not empty, so a wait answers it at once (fn-cwait-decide over the page).
(assert-event (not (fn-cwait-empty-pagep *cwdt-page-w*)))
(assert-event (equal (fn-cwait-decide *cwdt-page-w* 0 300) (list :answer *cwdt-page-w*)))
(assert-event (equal (fn-cwait-decide *cwdt-empty* 0 300) (list :sleep 300000)))
