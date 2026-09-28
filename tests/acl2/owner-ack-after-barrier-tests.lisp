; Teeth for books/owner-ack-after-barrier.lisp (lane ack-before-barrier).
; The fixtures are books/key-statements.lisp's (tests/acl2/key-statements-
; tests.lisp): a succession that acts (*kst-event*), the carried composite of
; the same statement, which declines (*kst-carried*), and an ordinary signed
; article's composite (*tha-event*).
(in-package "ACL2")
(include-book "../../books/owner-ack-after-barrier")
(include-book "key-statements-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *oabt-ml* (cdr (second *kst-new-keys*)))
; Members: (WORD EVENT SNAPSHOTS ROWS OBSERVED ED ML SEQUENCE TXID GENERATION).
(defconst *oabt-acting*
  (list :durable *kst-event* *kst-snapshots* *kst-rows* *oabt-ml* :verified :verified 5 6 7))
(defconst *oabt-declining*
  (list :durable *kst-carried* *kst-snapshots* *kst-rows* *oabt-ml* :verified :verified 5 6 7))
(defconst *oabt-article*
  (list :durable *tha-event* *kst-snapshots* *kst-rows* *oabt-ml* :verified :verified 5 6 7))

; -----------------------------------------------------------------------------
; The decision, reached.

; fn-oab-plan-only-after-the-fence and fn-oab-execute-only-after-the-fence:
; the acting statement's plan and change exist and it is fenced.
(assert-event (equal (fn-ks-plan *kst-event* *kst-snapshots* *kst-rows* *oabt-ml*
                                 :verified :verified)
                     (list :enroll *tha-principal* *kst-new-keys*)))
(assert-event (fn-ks-execute *kst-event* *kst-snapshots* *kst-rows* *oabt-ml*
                             :verified :verified 5 6 7))
(assert-event (equal (fn-oab-fence-before-change *kst-event*) t))
; The declining statement: a plan (the decline, whose line reports it), no
; change, fenced.
(assert-event (equal (fn-oab-mplan *oabt-declining*) (list :decline :carried)))
(assert-event (not (fn-oab-mchange *oabt-declining*)))
(assert-event (equal (fn-oab-mfence *oabt-declining*) t))
; fn-oab-recovered-statement-was-fenced: the open's recovery would act on
; the statement's record, and the route fenced it.
(assert-event (fn-ks-pending *kst-event*))
(assert-event (fn-oab-fence-before-change (fn-ks-pending *kst-event*)))

; Hypothesis removal (fn-oab-plan-only-after-the-fence's one hypothesis):
; an ordinary article's composite has no plan, and it is not fenced -- the
; conclusion fails without the hypothesis.  So an ordinary POST keeps the
; batch (no extra barrier).
(assert-event (null (fn-ks-plan *tha-event* *kst-snapshots* *kst-rows* *oabt-ml*
                                :verified :verified)))
(assert-event (equal (fn-oab-fence-before-change *tha-event*) nil))
(assert-event (null (fn-ks-pending *tha-event*)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-oab-quantum-reports-after-its-barrier, reached: an ordinary
; article, the acting statement, the declining one, in one batch whose
; barrier returned fenced.

(defconst *oabt-batch* (list *oabt-article* *oabt-acting* *oabt-declining*))
(make-event `(defconst *oabt-trace* ',(fn-oab-quantum *oabt-batch* :fenced)))

(assert-event (fn-oab-reports-follow-fences-p *oabt-trace* nil nil))
; Not vacuous: the trace holds the two statements' fences, both cuts, the
; executor's line naming the key change, and all three replies.
(assert-event (equal (fn-oab-drain 0 *oabt-batch*)
                     (list '(:take 0)
                           '(:take 1) '(:fence) '(:cut 1) '(:take (:k3 . 1))
                           '(:take 2) '(:fence) '(:cut 2))))
(assert-event (member-equal '(:line 1 (:k3 . 1)) *oabt-trace*))
(assert-event (member-equal '(:line 2) *oabt-trace*))
(assert-event (equal (fn-oab-reports 0 (fn-ocs-member-releases
                                         :complete (fn-oab-outcomes *oabt-batch*)))
                     '((:report 0) (:report 1) (:report 2))))
(assert-event (subsetp-equal '((:report 0) (:report 1) (:report 2)) *oabt-trace*))

; A failed barrier: the stop tells no member and writes no line.
(assert-event (equal (fn-oab-quantum *oabt-batch* :failed)
                     (fn-oab-drain 0 *oabt-batch*)))
(assert-event (fn-oab-reports-follow-fences-p (fn-oab-quantum *oabt-batch* :failed) nil nil))

; -----------------------------------------------------------------------------
; Mutation witnesses (the host's defect and two neighbours), each failing
; the property the keystone proves.

; M1, the defect log-recovery-2 diagnosed: the statement's cut and executor
; ran inside the drain with no fence of their own (the member's record only
; in the open batch).
(defun oabt-unfenced-steps (i m)
  (let ((durable (equal (fn-oab-mword m) :durable)))
    (append (list (list :take i))
            (and durable (fn-oab-mplan m) (list (list :cut i)))
            (and durable (fn-oab-mchange m) (list (list :take (cons :k3 i)))))))
(assert-event (not (fn-oab-reports-follow-fences-p
                    (append (oabt-unfenced-steps 0 *oabt-acting*)
                            (list '(:fence))
                            (fn-oab-complete 0 (list *oabt-acting*) :fenced))
                    nil nil)))
; M2: the executor's line written when it ran, not deferred to the COMPLETE
; (the key change is only in the open batch).
(assert-event (not (fn-oab-reports-follow-fences-p
                    (append (fn-oab-member-steps 0 *oabt-acting*)
                            (list '(:line 0 (:k3 . 0))))
                    nil nil)))
; M3: replies released without the batch's barrier (COMPLETE with no SYNC).
(assert-event (not (fn-oab-reports-follow-fences-p
                    (append (fn-oab-drain 0 (list *oabt-article*))
                            (fn-oab-complete 0 (list *oabt-article*) :fenced))
                    nil nil)))

; -----------------------------------------------------------------------------
; fn-oab-pipeline-reports-after-its-barriers, reached: an ordinary batch in
; flight and, prepared behind its barrier, a batch whose statement fences
; (awaiting the batch in flight first).
(make-event `(defconst *oabt-pipeline*
               ',(fn-oab-pipeline (list *oabt-article*) (list *oabt-acting* *oabt-article*)
                                  :fenced :fenced)))
(assert-event (fn-oab-reports-follow-fences-p *oabt-pipeline* nil nil))
(assert-event (member-equal '(:cut 1) *oabt-pipeline*))
(assert-event (member-equal '(:line 1 (:k3 . 1)) *oabt-pipeline*))
(assert-event (subsetp-equal '((:report 0) (:report 1) (:report 2)) *oabt-pipeline*))
; The batch in flight failed: nothing of either batch is told.
(assert-event (not (member-equal '(:report 1)
                                 (fn-oab-pipeline (list *oabt-article*) (list *oabt-acting*)
                                                  :failed :fenced))))

; -----------------------------------------------------------------------------
; fn-oab-every-kind-reports-after-its-barrier, reached for every kind; its
; hypothesis removed: a kind with no route in the table is unaccounted.
(defun oabt-every-kind (kinds)
  (or (atom kinds)
      (and (fn-oab-reports-follow-fences-p
            (fn-oab-kind-trace (car (car kinds)) *oabt-batch* :fenced) nil nil)
           (oabt-every-kind (cdr kinds)))))
(assert-event (oabt-every-kind *fn-oab-record-kinds*))
(assert-event (equal (len *fn-oab-record-kinds*) 14))
(assert-event (not (assoc-equal :unrouted *fn-oab-record-kinds*)))
(assert-event (not (fn-oab-reports-follow-fences-p
                    (fn-oab-kind-trace :unrouted *oabt-batch* :fenced) nil nil)))

; -----------------------------------------------------------------------------
; PRF-354 (lane full-vs-uncertain): a refusal that wrote nothing is told at
; its drain.  A full-store POST (:unaffordable) drained before an ordinary
; article, in a batch whose barrier FAILS: the refusal's reply is in the
; trace (naming no record), the batch kept only the article, and the keystone
; property holds.  Before PRF-354 the stop told the refusal uncertain.
(defconst *oabt-full*
  (list :unaffordable *tha-event* *kst-snapshots* *kst-rows* *oabt-ml* :verified :verified 5 6 7))
(defconst *oabt-full-batch* (list *oabt-full* *oabt-article*))
(assert-event (equal (fn-oab-drain 0 *oabt-full-batch*) '((:report) (:take 0))))
(assert-event (equal (fn-oab-kept *oabt-full-batch*) (list *oabt-article*)))
(assert-event (member-equal '(:report) (fn-oab-quantum *oabt-full-batch* :failed)))
(assert-event (fn-oab-reports-follow-fences-p (fn-oab-quantum *oabt-full-batch* :failed) nil nil))
; The article kept beside it is still told nothing when the barrier fails,
; and is told its outcome once it is fenced.
(assert-event (not (member-equal '(:report 0) (fn-oab-quantum *oabt-full-batch* :failed))))
(assert-event (member-equal '(:report 0) (fn-oab-quantum *oabt-full-batch* :fenced)))
(assert-event (fn-oab-reports-follow-fences-p (fn-oab-quantum *oabt-full-batch* :fenced) nil nil))
; A duplicate is not told at its drain: it stays in the batch (it may rest
; on a record the barrier has not fenced).
(assert-event (equal (fn-oab-kept (list (cons :duplicate (cdr *oabt-full*))))
                     (list (cons :duplicate (cdr *oabt-full*)))))
; Mutation witness (labelled): a told refusal whose reply named a record of
; its own -- a record it never took -- is what the property refuses.
(assert-event (not (fn-oab-reports-follow-fences-p '((:report 0)) nil nil)))
