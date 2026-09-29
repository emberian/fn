; Witnesses and teeth for books/owner-time-bars.lisp (lane time-bars,
; 2026-09-28; PRF-384).  The ledgers are REACHED from fn-otb-ledger-init
; through the calls host/native/owner.lisp fnn-owner-commit-pipeline makes
; (fn-otb-issue, fn-otb-answer-early, fn-otb-complete); the journals are
; the host's (fn-otm-run from fn-otm-init, behind fn-otm-start-line's entry).
(in-package "ACL2")
(include-book "../../books/owner-time-bars")
(include-book "must-fail-checked")

(defun otbt-issue (l) (caddr (fn-otb-issue l)))
(defun otbt-early (l cids) (cadr (fn-otb-answer-early l cids)))
(defun otbt-done (l g cids) (caddr (fn-otb-complete l g cids)))
(defun otbt-text (s) (fn-osch-chars-octets (coerce s 'list)))

; --- A reached pipeline: batch 1 (members 1 2) completes normally; batch 2
; (members 3 4, and the next batch 5 prepared behind it) stalls: 3 4 5 are
; told uncertain; batch 2's late completion answers no one; batch 3 (member
; 5, now in flight, and 6 joined later) completes and answers only 6.
(defconst *otbt-l1* (otbt-issue (fn-otb-ledger-init)))
(assert-event (equal (fn-otb-issue (fn-otb-ledger-init)) (list :issued 1 '(1 t nil))))
(assert-event (equal (fn-otb-complete *otbt-l1* 1 '(1 2)) (list :apply '(1 2) '(1 nil nil))))
(defconst *otbt-l2* (otbt-issue (otbt-done *otbt-l1* 1 '(1 2))))
(assert-event (equal *otbt-l2* '(2 t nil)))
(assert-event (equal (fn-otb-answer-early *otbt-l2* '(3 4 5)) (list '(3 4 5) '(2 t (3 4 5)))))
(defconst *otbt-l2s* (otbt-early *otbt-l2* '(3 4 5)))
; A second early answer (a stop's release after the stall) tells no one again.
(assert-event (equal (car (fn-otb-answer-early *otbt-l2s* '(3 4 5))) nil))
; The late completion of generation 2: applies, answers nobody, forgets 3 4.
(assert-event (equal (fn-otb-complete *otbt-l2s* 2 '(3 4)) (list :apply nil '(2 nil (5)))))
(defconst *otbt-l3* (otbt-issue (otbt-done *otbt-l2s* 2 '(3 4))))
(assert-event (equal *otbt-l3* '(3 t (5))))
(assert-event (equal (fn-otb-complete *otbt-l3* 3 '(5 6)) (list :apply '(6) '(3 nil nil))))

; --- fn-otb-a-member-is-answered-once: a reached positive witness, the
; complete antecedent and every conclusion (L = *otbt-l3*, told (5); two
; early answers; members 5 6 7 8).
(defconst *otbt-xss* '((6 9) (9 7 7)))
(defun otbt-k1 (l xss cids)
  (let* ((r (fn-otb-early-run l xss))
         (early (car r))
         (c (fn-otb-complete (cadr r) (fn-otb-gen l) cids))
         (late (cadr c)))
    (list (and (fn-otb-open l) (no-duplicatesp-equal cids))
          (and (equal (car c) :apply)
               (no-duplicatesp-equal early)
               (not (intersectp-equal early (fn-otb-told l)))
               (no-duplicatesp-equal late)
               (subsetp-equal late cids)
               (not (intersectp-equal late (append (fn-otb-told l) early)))
               (subsetp-equal cids (append (fn-otb-told l) early late)))
          early late)))
(assert-event (equal (otbt-k1 *otbt-l3* *otbt-xss* '(5 6 7 8))
                     '(t t (6 9 7) (8))))
; Hypothesis removal, (fn-otb-open L): a ledger whose completion was already
; consumed.  The retained hypothesis holds; the omitted fails; the
; conclusion fails (the completion is refused, member 8 is answered by no one).
(defconst *otbt-closed* (otbt-done *otbt-l3* 3 '(5 6)))
(assert-event (and (no-duplicatesp-equal '(8))
                   (not (fn-otb-open *otbt-closed*))
                   (equal (otbt-k1 *otbt-closed* nil '(8)) '(nil nil nil nil))))
; Hypothesis removal, (no-duplicatesp-equal CIDS): a member listed twice is
; answered twice.  The ledger is open; the conclusion fails.
(assert-event (and (fn-otb-open *otbt-l3*)
                   (not (no-duplicatesp-equal '(8 8)))
                   (equal (otbt-k1 *otbt-l3* nil '(8 8)) '(nil nil nil (8 8)))))
(must-fail-checked
 (defthm otbt-tooth-answered-once-needs-open
   (let* ((r (fn-otb-early-run l xss))
          (c (fn-otb-complete (cadr r) (fn-otb-gen l) cids)))
     (implies (no-duplicatesp-equal cids)
              (subsetp-equal cids (append (fn-otb-told l) (car r) (cadr c)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; --- fn-otb-a-late-completion-is-consumed-once.
; Positive: generation 3 applies once; the same completion again is
; :consumed, another generation's :stale; neither answers or changes.
(assert-event (equal (fn-otb-complete *otbt-closed* 3 '(5 6)) (list :consumed nil *otbt-closed*)))
(assert-event (equal (fn-otb-complete *otbt-closed* 2 '(5 6)) (list :stale nil *otbt-closed*)))
; The successor's issue makes every earlier generation's completion stale.
(defconst *otbt-l4* (otbt-issue *otbt-closed*))
(assert-event (and (equal (fn-otb-gen *otbt-l4*) 4)
                   (equal (fn-otb-complete *otbt-l4* 3 '(5 6)) (list :stale nil *otbt-l4*))))
; Hypothesis removal for the "once applied" clause: a completion that did
; not apply (a stale one) is followed by one that does.
(assert-event (let* ((c (fn-otb-complete *otbt-l3* 2 '(5 6)))
                     (c2 (fn-otb-complete (caddr c) 3 '(5 6))))
                (and (equal (car c) :stale) (equal (car c2) :apply) (equal (cadr c2) '(6)))))

; --- fn-otb-a-deadline-keeps-the-io-owned.
(assert-event (let ((r (fn-otb-early-run *otbt-l2* '((3) (4 5)))))
                (and (fn-otb-open (cadr r)) (equal (fn-otb-gen (cadr r)) 2))))
(assert-event (equal (car (fn-otb-issue *otbt-l2*)) :fault))
(assert-event (equal (fn-otb-issue *otbt-l2*) (list :fault 2 *otbt-l2*)))

; --- fn-otb-a-late-page-is-unavailable-never-absent.
; Reached: a read began waiting at 1,000 ms; at 2,000 it waits 4,000 more;
; at 6,000 (the default deadline, 5,000) it is unavailable, 403; a page
; that completed is served whenever.
(assert-event (equal (fn-otb-dependency-step 1000 2000 0 nil) '(:wait 4000)))
(assert-event (equal (fn-otb-dependency-step 1000 5999 0 nil) '(:wait 1)))
(assert-event (equal (fn-otb-dependency-step 1000 6000 0 nil) :unavailable))
(assert-event (equal (fn-otb-dependency-step 1000 90000 0 t) :serve))
(assert-event (equal (fn-otb-dependency-step 1000 3000 2000 nil) :unavailable))
(assert-event (equal (fn-otb-unavailable-line 1000 6000 0)
                     (append (otbt-text "403 article temporarily unavailable; a page it needs was not read within 5000 ms (waited 5000 ms): it is not absent, try again later")
                             '(13 10))))
; Hypothesis removal for the wait clause, (<= SINCE NOW): a reading before
; the wait began (a host defect); the other hypotheses hold and the wait is
; measured from SINCE, not from NOW.
(assert-event (let ((st (fn-otb-dependency-step 1000 500 0 nil)))
                (and (natp 1000) (natp 500) (not (<= 1000 500))
                     (equal st '(:wait 5000))
                     (not (equal (+ 500 (cadr st)) (+ 1000 5000))))))

; --- fn-otb-a-restart-forgets-the-previous-clock-domain.
; Run 1: a barrier issued at 10,000 ms, slow at 12,000, stalled at 16,000,
; the posters told, the device back at 40,000.  Run 2 (a new process: its
; monotonic readings start near zero): a barrier issued at 50 ms that
; returns at 200.
(defconst *otbt-run1*
  (list (list :event :issue 10000 '(2000 6000 250))
        (list :event :clock 12000 nil)
        (list :event :clock 16000 nil)
        (list :note 2 1)
        (list :event :return 40000 nil)))
(defconst *otbt-run2*
  (list (list :event :issue 50 '(2000 6000 250))
        (list :event :return 200 nil)))
(defun otbt-entries (steps)
  (mv-let (es s) (fn-otm-run (fn-otm-init) steps) (declare (ignore s)) es))
(defconst *otbt-e1* (cons (fn-otm-start-entry 1234 t) (otbt-entries *otbt-run1*)))
(defconst *otbt-e2* (otbt-entries *otbt-run2*))
(defun otbt-replay (s es) (mv-let (v s2) (fn-otm-replay s es) (list v s2)))
(assert-event (equal (car (otbt-replay (fn-otm-init) *otbt-e1*)) :agrees))
(assert-event (equal (otbt-replay (fn-otm-init)
                                  (append *otbt-e1* (cons (fn-otm-start-entry 99 nil) *otbt-e2*)))
                     (otbt-replay (fn-otm-init) *otbt-e2*)))
(assert-event (equal (car (otbt-replay (fn-otm-init) *otbt-e2*)) :agrees))
; The start entry records the wall observation and no monotonic origin.
(assert-event (equal (fn-otm-start-entry 1234 t) '(0 0 0 1234 1 0 0)))
; Tooth: without the restart's start entry (run 2's readings spliced onto
; run 1's domain) the replay does not reproduce run 2: its first reading, 50,
; is below run 1's recorded 40,000.
(assert-event (not (equal (otbt-replay (fn-otm-init) (append *otbt-e1* *otbt-e2*))
                          (otbt-replay (fn-otm-init) *otbt-e2*))))
; Hypothesis removal, run 1 agreeing: a tampered run 1 (its stall word
; changed) stops the replay at run 1's entry, whatever follows.
(defconst *otbt-e1-bad*
  (append (take 3 *otbt-e1*) (list (update-nth 6 5 (nth 3 *otbt-e1*))) (nthcdr 4 *otbt-e1*)))
(assert-event (and (not (equal (car (otbt-replay (fn-otm-init) *otbt-e1-bad*)) :agrees))
                   (not (equal (otbt-replay (fn-otm-init)
                                            (append *otbt-e1-bad* (cons (fn-otm-start-entry 99 nil) *otbt-e2*)))
                               (otbt-replay (fn-otm-init) *otbt-e2*)))))
