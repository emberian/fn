; fn: every durability report follows the barrier that persisted it (lane
; ack-before-barrier, 2026-09-27).
;
; AGENTS.md: "Durable acceptance comes only from persisted state, never from a
; socket write, a transport ACK or an in-memory update."  On the record log
; (format 9) the served commit is the owner's batch quantum
; (host/native/owner.lisp fnn-owner-commit-start-locked, *fnn-log-batch*
; bound): each member's record joins the log's open batch and the member
; completes in memory; the batch's append and fdatasync come after the
; drain; only then (COMPLETE) do the members' lines, feed resolutions and
; replies leave (books/owner-commit-steps.lisp
; fn-ocs-members-told-only-after-the-barrier).
;
; The defect this book closes (log-recovery-2's diagnosis,
; planning/evidence/log-recovery-2026-09-27.md section 8): a served KEY
; STATEMENT (a kind-4 composite whose authored source carries a
; books/key-statements.lisp statement) ran its crash cut `statement-committed'
; and its executor (fn-ks-plan, the kind-3 key change and the
; `key-statement ...' log line) INSIDE the drain, i.e. before the batch's
; barrier: the cut killed with the statement in memory only (the next open
; had nothing to recover) and the log line reported a committed key change
; that no barrier had persisted.  The model (books/key-statements.lisp
; fn-ks-cut) is that the statement is DURABLE at the cut and its change is
; not.
;
; The repair, decided here: a commit whose event carries a statement
; (fn-oab-fence-before-change) fences the log's open batch -- itself and
; every member drained before it -- BEFORE the cut and the executor run
; (host/native/owner.lisp fnn-owner-statement-committed through
; fnn-owner-statement-barrier: fnn-log-commit-open-batch, which first awaits
; the barrier of a batch in flight).  The executor's kind-3 record then joins
; the open batch like any member, and its line is deferred to the COMPLETE
; that follows the kind-3's barrier.
;
; What is proved:
;   * fn-oab-plan-only-after-the-fence, fn-oab-execute-only-after-the-fence
;     and fn-oab-recovered-statement-was-fenced: the executor decides (acts
;     or declines) only on an event this route fenced first, and the open's
;     recovery acts only on such a record.
;   * KEYSTONE fn-oab-quantum-reports-after-its-barrier: over the host's
;     schedule of one batch quantum (fn-oab-quantum: START's drain with the
;     statement fence, SYNC's barrier, COMPLETE's lines and releases, the
;     releases ACL2's fn-ocs-member-releases over fn-ocs-commit-step's
;     action), every report -- a member's reply, the cut marker, a service
;     line, the executor's line -- names only records a barrier has
;     fenced (fn-oab-reports-follow-fences-p).
;   * fn-oab-pipeline-reports-after-its-barriers: the same for a batch in
;     flight and the next batch prepared behind it (START-NEXT), including a
;     statement drained behind the barrier.
;   * fn-oab-every-kind-reports-after-its-barrier: every record kind the
;     owner commits (*fn-oab-record-kinds*: articles, transit, statements and
;     their key changes in the quantum; identity, consumer, topic,
;     configuration, retention and XREDEEM's control records as a batch of
;     one, fnn-log-publish outside the quantum) reports only after its
;     barrier.
; The host's order of these steps is checked statically against the host
; source by tests/campaign/native_cuts.py verify_statement_cut_map (called by
; tools/native_program_check.py): the host function, not this model, is the
; subject, and that check is the named link.
(in-package "ACL2")
(include-book "key-statements")
(include-book "owner-commit-steps")

; -----------------------------------------------------------------------------
; The decision.  Host: host/owner-host.lisp fn-owner-statement-fence, called by
; host/native/owner.lisp fnn-owner-statement-committed after the commit of
; every kind-4 composite a served or relayed article makes.

(defun fn-oab-fence-before-change (event)
  (declare (xargs :guard t))
  (if (fn-ks-statement (fn-ks-source event)) t nil))

(defthm fn-oab-plan-only-after-the-fence
  (implies (fn-ks-plan event snapshots rows observed ed ml)
           (fn-oab-fence-before-change event))
  :hints (("Goal" :in-theory (e/d (fn-ks-plan)
                                  (fn-ks-statement fn-ks-source fn-ks-verdict
                                   fn-hsig-authored-source-fields
                                   fn-ctl-authorize fn-hl-current-enrollment
                                   fn-hsig-authorize fn-ks-pop-source
                                   fn-ks-msgid)))))

(defthm fn-oab-execute-only-after-the-fence
  (implies (fn-ks-execute event snapshots rows observed ed ml
                          sequence txid store-generation)
           (fn-oab-fence-before-change event))
  :hints (("Goal" :in-theory (disable fn-ks-execute fn-ks-statement fn-ks-source)
           :use fn-ks-execute-needs-a-statement)))

; The open's recovery (fn-ks-recover-recorded through fn-ks-pending) acts only
; on a statement: a record this route fenced before its change.
(defthm fn-oab-recovered-statement-was-fenced
  (implies (fn-ks-pending record)
           (fn-oab-fence-before-change record))
  :hints (("Goal" :in-theory (e/d (fn-ks-pending) (fn-ks-statement fn-ks-source)))))

(in-theory (disable fn-oab-fence-before-change))

; -----------------------------------------------------------------------------
; The host's schedule as a trace of steps:
;   (:take ID)     a record joins the log's open batch (fn-lgc-take)
;   (:fence)       an append and its barrier returned: every record taken
;                  so far is durable (fnn-log-commit-open-batch, or the
;                  syncer's fnn-log-sync-sealed-batch for a sealed batch)
;   (:cut ID)      the statement-committed crash point
;   (:line ID...)  a service line naming the records ID...
;   (:report ID)   a member's rendered reply
; A member is (WORD EVENT SNAPSHOTS ROWS OBSERVED ED ML SEQUENCE TXID
; GENERATION): WORD its outcome word, the rest the executor's inputs.  Member
; I's record is I, its key change (:k3 . I).

(defun fn-oab-mword (m) (declare (xargs :guard t)) (if (consp m) (car m) nil))
(defun fn-oab-margs (m) (declare (xargs :guard t)) (if (consp m) (cdr m) nil))
(defun fn-oab-at (k l)
  (declare (xargs :guard (natp k)))
  (cond ((atom l) nil) ((zp k) (car l)) (t (fn-oab-at (- k 1) (cdr l)))))

(defun fn-oab-mplan (m)
  (declare (xargs :guard t))
  (let ((a (fn-oab-margs m)))
    (fn-ks-plan (fn-oab-at 0 a) (fn-oab-at 1 a) (fn-oab-at 2 a) (fn-oab-at 3 a) (fn-oab-at 4 a) (fn-oab-at 5 a))))

(defun fn-oab-mchange (m)
  (declare (xargs :guard t))
  (let ((a (fn-oab-margs m)))
    (fn-ks-execute (fn-oab-at 0 a) (fn-oab-at 1 a) (fn-oab-at 2 a) (fn-oab-at 3 a) (fn-oab-at 4 a) (fn-oab-at 5 a)
                   (fn-oab-at 6 a) (fn-oab-at 7 a) (fn-oab-at 8 a))))

(defun fn-oab-mfence (m)
  (declare (xargs :guard t))
  (fn-oab-fence-before-change (fn-oab-at 0 (fn-oab-margs m))))

; START's drain of one member (fnn-owner-drain-one, then for a durable
; statement fnn-owner-statement-committed): the take; the statement's fence;
; the cut; the key change's take.
(defun fn-oab-member-steps (i m)
  (declare (xargs :guard t))
  (let ((durable (equal (fn-oab-mword m) :durable)))
    (append (list (list :take i))
            (and durable (fn-oab-mfence m) (list (list :fence)))
            (and durable (fn-oab-mplan m) (list (list :cut i)))
            (and durable (fn-oab-mchange m) (list (list :take (cons :k3 i)))))))

; The member's deferred lines (*fnn-owner-deferred*): its outcome line, and
; the executor's line naming the statement and its key change.
(defun fn-oab-member-lines (i m)
  (declare (xargs :guard t))
  (append (list (list :line i))
          (and (equal (fn-oab-mword m) :durable) (fn-oab-mplan m)
               (list (if (fn-oab-mchange m)
                         (list :line i (cons :k3 i))
                       (list :line i))))))

; PRF-354 (lane full-vs-uncertain): a member whose word is a refusal that
; wrote nothing (fn-ocs-told-at-drain-p) is told at its drain -- its reply
; names no record, for it took none -- and is not one of the batch's
; members, whose numbering skips it (host/native/owner.lisp
; fnn-owner-commit-start-locked).
(defun fn-oab-drain (i members)
  (declare (xargs :guard (natp i)))
  (if (consp members)
      (if (fn-ocs-told-at-drain-p (fn-oab-mword (car members)))
          (cons (list :report) (fn-oab-drain i (cdr members)))
        (append (fn-oab-member-steps i (car members))
                (fn-oab-drain (+ 1 (nfix i)) (cdr members))))
    nil))

; The members the batch keeps: the ones its COMPLETE (or stop) answers.
(defun fn-oab-kept (members)
  (declare (xargs :guard t))
  (if (consp members)
      (if (fn-ocs-told-at-drain-p (fn-oab-mword (car members)))
          (fn-oab-kept (cdr members))
        (cons (car members) (fn-oab-kept (cdr members))))
    nil))

(defun fn-oab-lines (i members)
  (declare (xargs :guard (natp i)))
  (if (consp members)
      (append (fn-oab-member-lines i (car members))
              (fn-oab-lines (+ 1 (nfix i)) (cdr members)))
    nil))

; The outcomes fn-ocs-member-releases reads: (WORD RENDERABLE).
(defun fn-oab-outcomes (members)
  (declare (xargs :guard t))
  (if (consp members)
      (cons (list (fn-oab-mword (car members)) t)
            (fn-oab-outcomes (cdr members)))
    nil))

(defun fn-oab-reports (i releases)
  (declare (xargs :guard (natp i)))
  (if (consp releases)
      (append (and (equal (car releases) :rendered) (list (list :report i)))
              (fn-oab-reports (+ 1 (nfix i)) (cdr releases)))
    nil))

; COMPLETE after the barrier's WORD (:fenced or :failed): ACL2's step and its
; releases; the lines go out only in a :complete.
(defun fn-oab-complete (i members word)
  (declare (xargs :guard (natp i)))
  (mv-let (action phase) (fn-ocs-commit-step :staged word)
    (declare (ignore phase))
    (append (and (equal action :complete) (fn-oab-lines i members))
            (fn-oab-reports i (fn-ocs-member-releases action (fn-oab-outcomes members))))))

; One batch quantum from an idle owner: START (drain, seal), SYNC, COMPLETE
; of the members the batch kept.
(defun fn-oab-quantum (members word)
  (declare (xargs :guard t))
  (append (fn-oab-drain 0 members)
          (and (equal word :fenced) (list (list :fence)))
          (fn-oab-complete 0 (fn-oab-kept members) word)))

; A batch in flight (A, members 0..) and the batch prepared behind its
; barrier (B, START-NEXT, numbered after A's): A's drain and seal, B's drain
; (a statement's fence awaits A's barrier first: fnn-log-commit-open-batch
; through fnn-log-await-sync), A's barrier and COMPLETE, B's seal, barrier and
; COMPLETE.
(defun fn-oab-pipeline (a b word-a word-b)
  (declare (xargs :guard t))
  (let ((n (len (fn-oab-kept a))))
    (append (fn-oab-drain 0 a)
            (fn-oab-drain n b)
            (and (equal word-a :fenced) (list (list :fence)))
            (fn-oab-complete 0 (fn-oab-kept a) word-a)
            (and (equal word-a :fenced) (equal word-b :fenced) (list (list :fence)))
            (fn-oab-complete n (fn-oab-kept b) (if (equal word-a :fenced) word-b :failed)))))

; The property: every record a report names was taken and then fenced.
(defun fn-oab-names-fenced-p (ids fenced)
  (declare (xargs :guard (true-listp fenced)))
  (if (consp ids)
      (and (member-equal (car ids) fenced)
           (fn-oab-names-fenced-p (cdr ids) fenced))
    t))

(defun fn-oab-reports-follow-fences-p (trace pending fenced)
  (declare (xargs :guard (and (true-listp pending) (true-listp fenced))))
  (if (consp trace)
      (let ((s (car trace)))
        (cond ((not (consp s)) nil)
              ((equal (car s) :take)
               (fn-oab-reports-follow-fences-p
                (cdr trace) (cons (if (consp (cdr s)) (cadr s) nil) pending) fenced))
              ((equal (car s) :fence)
               (fn-oab-reports-follow-fences-p (cdr trace) nil (append pending fenced)))
              (t (and (true-listp (cdr s))
                      (fn-oab-names-fenced-p (cdr s) fenced)
                      (fn-oab-reports-follow-fences-p (cdr trace) pending fenced)))))
    t))

; -----------------------------------------------------------------------------
; The trace's state after a prefix, and the lemmas the keystones compose.

(defun fn-oab-pending-after (trace pending)
  (declare (xargs :guard (true-listp pending)))
  (if (consp trace)
      (let ((s (car trace)))
        (cond ((not (consp s)) (fn-oab-pending-after (cdr trace) pending))
              ((equal (car s) :take)
               (fn-oab-pending-after (cdr trace) (cons (if (consp (cdr s)) (cadr s) nil) pending)))
              ((equal (car s) :fence) (fn-oab-pending-after (cdr trace) nil))
              (t (fn-oab-pending-after (cdr trace) pending))))
    pending))
(defun fn-oab-fenced-after (trace pending fenced)
  (declare (xargs :guard (and (true-listp pending) (true-listp fenced))))
  (if (consp trace)
      (let ((s (car trace)))
        (cond ((not (consp s)) (fn-oab-fenced-after (cdr trace) pending fenced))
              ((equal (car s) :take)
               (fn-oab-fenced-after (cdr trace) (cons (if (consp (cdr s)) (cadr s) nil) pending) fenced))
              ((equal (car s) :fence) (fn-oab-fenced-after (cdr trace) nil (append pending fenced)))
              (t (fn-oab-fenced-after (cdr trace) pending fenced))))
    fenced))
(defthm fn-oab-reports-follow-fences-p-of-append
  (equal (fn-oab-reports-follow-fences-p (append x y) pending fenced)
         (and (fn-oab-reports-follow-fences-p x pending fenced)
              (fn-oab-reports-follow-fences-p
               y (fn-oab-pending-after x pending)
               (fn-oab-fenced-after x pending fenced)))))
(defthm fn-oab-pending-after-of-append
  (equal (fn-oab-pending-after (append x y) pending)
         (fn-oab-pending-after y (fn-oab-pending-after x pending))))
(defthm fn-oab-fenced-after-of-append
  (equal (fn-oab-fenced-after (append x y) pending fenced)
         (fn-oab-fenced-after y (fn-oab-pending-after x pending)
                              (fn-oab-fenced-after x pending fenced))))

;; A report that names no record (a refusal told at its drain) keeps the
;; trace's state and needs no fence.
(defthm fn-oab-report-of-nothing-unfolds
  (and (equal (fn-oab-reports-follow-fences-p (cons '(:report) rest) pending fenced)
              (fn-oab-reports-follow-fences-p rest pending fenced))
       (equal (fn-oab-pending-after (cons '(:report) rest) pending)
              (fn-oab-pending-after rest pending))
       (equal (fn-oab-fenced-after (cons '(:report) rest) pending fenced)
              (fn-oab-fenced-after rest pending fenced))))

(defthm fn-oab-mplan-only-after-the-fence
  (implies (fn-oab-mplan m) (fn-oab-mfence m))
  :hints (("Goal" :in-theory (disable fn-ks-plan))))
(in-theory (disable fn-oab-mplan fn-oab-mchange fn-oab-mfence fn-oab-mword))
(defthm fn-oab-member-steps-follow-fences
  (fn-oab-reports-follow-fences-p (fn-oab-member-steps i m) pending fenced))

(defun fn-oab-drain-ind (i members pending fenced)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (consp members)
      (if (fn-ocs-told-at-drain-p (fn-oab-mword (car members)))
          (fn-oab-drain-ind i (cdr members) pending fenced)
        (fn-oab-drain-ind (+ 1 (nfix i)) (cdr members)
                          (fn-oab-pending-after (fn-oab-member-steps i (car members)) pending)
                          (fn-oab-fenced-after (fn-oab-member-steps i (car members)) pending fenced)))
    (list i pending fenced)))

(defthm fn-oab-reports-follow-fences-p-of-atom
  (implies (not (consp trace)) (fn-oab-reports-follow-fences-p trace pending fenced)))
(defthm fn-oab-drain-follows-fences
  (fn-oab-reports-follow-fences-p (fn-oab-drain i members) pending fenced)
  :hints (("Goal" :induct (fn-oab-drain-ind i members pending fenced)
           :in-theory (disable fn-oab-member-steps fn-oab-reports-follow-fences-p
                               fn-oab-pending-after fn-oab-fenced-after))))

(defthm fn-oab-member-equal-of-append
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))
(defun fn-oab-covered (i members fenced)
  (declare (xargs :guard (and (natp i) (true-listp fenced)) :measure (len members)))
  (if (consp members)
      (and (member-equal i fenced)
           (or (not (equal (fn-oab-mword (car members)) :durable))
               (not (fn-oab-mchange (car members)))
               (member-equal (cons :k3 i) fenced))
           (fn-oab-covered (+ 1 (nfix i)) (cdr members) fenced))
    t))
(defthm fn-oab-taken-stays-taken
  (implies (member-equal x (append pending fenced))
           (member-equal x (append (fn-oab-pending-after trace pending)
                                   (fn-oab-fenced-after trace pending fenced)))))
(defthm fn-oab-member-steps-take-the-member
  (let ((tk (append (fn-oab-pending-after (fn-oab-member-steps i m) pending)
                    (fn-oab-fenced-after (fn-oab-member-steps i m) pending fenced))))
    (and (member-equal i tk)
         (implies (and (equal (fn-oab-mword m) :durable) (fn-oab-mchange m))
                  (member-equal (cons :k3 i) tk)))))
(defthm fn-oab-drain-kept-step-unfolds
  (implies (and (consp members) (not (fn-ocs-told-at-drain-p (fn-oab-mword (car members)))))
           (and (equal (fn-oab-drain i members)
                       (append (fn-oab-member-steps i (car members))
                               (fn-oab-drain (+ 1 (nfix i)) (cdr members))))
                (equal (fn-oab-kept members) (cons (car members) (fn-oab-kept (cdr members))))))
  :hints (("Goal" :expand ((fn-oab-drain i members) (fn-oab-kept members))
           :in-theory (disable fn-oab-member-steps fn-ocs-told-at-drain-p))))
(defthm fn-oab-drain-told-step-unfolds
  (implies (and (consp members) (fn-ocs-told-at-drain-p (fn-oab-mword (car members))))
           (and (equal (fn-oab-drain i members) (cons '(:report) (fn-oab-drain i (cdr members))))
                (equal (fn-oab-kept members) (fn-oab-kept (cdr members)))))
  :hints (("Goal" :expand ((fn-oab-drain i members) (fn-oab-kept members))
           :in-theory (disable fn-oab-member-steps fn-ocs-told-at-drain-p))))
(defthm fn-oab-drain-and-kept-of-atom
  (implies (not (consp members))
           (and (equal (fn-oab-drain i members) nil)
                (equal (fn-oab-kept members) nil)))
  :hints (("Goal" :expand ((fn-oab-drain i members) (fn-oab-kept members)))))

(defthm fn-oab-drain-covers
  (fn-oab-covered i (fn-oab-kept members)
                  (append (fn-oab-pending-after (fn-oab-drain i members) pending)
                          (fn-oab-fenced-after (fn-oab-drain i members) pending fenced)))
  :hints (("Goal" :induct (fn-oab-drain-ind i members pending fenced)
           :in-theory (disable fn-oab-member-steps fn-oab-pending-after fn-oab-fenced-after
                               fn-oab-taken-stays-taken fn-ocs-told-at-drain-p
                               fn-oab-drain fn-oab-kept))
          ("Subgoal *1/2" :use ((:instance fn-oab-taken-stays-taken
                                 (x i) (trace (fn-oab-drain (+ 1 (nfix i)) (cdr members)))
                                 (pending (fn-oab-pending-after (fn-oab-member-steps i (car members)) pending))
                                 (fenced (fn-oab-fenced-after (fn-oab-member-steps i (car members)) pending fenced)))
                                (:instance fn-oab-taken-stays-taken
                                 (x (cons :k3 i)) (trace (fn-oab-drain (+ 1 (nfix i)) (cdr members)))
                                 (pending (fn-oab-pending-after (fn-oab-member-steps i (car members)) pending))
                                 (fenced (fn-oab-fenced-after (fn-oab-member-steps i (car members)) pending fenced)))
                                (:instance fn-oab-member-steps-take-the-member (m (car members)))))))

(defthm fn-oab-lines-follow-fences
  (implies (fn-oab-covered i members fenced)
           (fn-oab-reports-follow-fences-p (fn-oab-lines i members) pending fenced)))

(defun fn-oab-range-in (i n fenced)
  (declare (xargs :guard (and (natp i) (natp n) (true-listp fenced)) :measure (nfix n)))
  (if (zp n) t
    (and (member-equal i fenced)
         (fn-oab-range-in (+ 1 (nfix i)) (- n 1) fenced))))
(defthm fn-oab-reports-in-range-follow-fences
  (implies (fn-oab-range-in i (len releases) fenced)
           (fn-oab-reports-follow-fences-p (fn-oab-reports i releases) pending fenced)))
(defthm fn-oab-covered-range-in
  (implies (fn-oab-covered i members fenced)
           (fn-oab-range-in i (len members) fenced)))
(defthm fn-oab-len-outcomes
  (equal (len (fn-oab-outcomes members)) (len members)))
(defthm fn-oab-reports-follow-fences
  (implies (fn-oab-covered i members fenced)
           (fn-oab-reports-follow-fences-p
            (fn-oab-reports i (fn-ocs-member-releases action (fn-oab-outcomes members)))
            pending fenced))
  :hints (("Goal" :in-theory (disable fn-oab-reports fn-ocs-member-releases fn-oab-covered))))
(defthm fn-oab-no-rendered-outside-a-complete
  (implies (not (equal action :complete))
           (not (member-equal :rendered (fn-ocs-member-releases action outcomes))))
  :hints (("Goal" :induct (fn-ocs-member-releases action outcomes)
           :in-theory (e/d (fn-ocs-member-releases) (fn-ocs-member-release)))))
(defthm fn-oab-reports-of-unrendered
  (implies (not (member-equal :rendered releases))
           (equal (fn-oab-reports i releases) nil)))
(defthm fn-oab-reports-silent-outside-a-complete
  (implies (not (equal action :complete))
           (equal (fn-oab-reports i (fn-ocs-member-releases action outcomes)) nil))
  :hints (("Goal" :in-theory (disable fn-oab-reports fn-ocs-member-releases))))

(defthm fn-oab-lines-keep-the-state
  (and (equal (fn-oab-pending-after (fn-oab-lines i members) pending) pending)
       (equal (fn-oab-fenced-after (fn-oab-lines i members) pending fenced) fenced)))
(defthm fn-oab-reports-keep-the-state
  (and (equal (fn-oab-pending-after (fn-oab-reports i releases) pending) pending)
       (equal (fn-oab-fenced-after (fn-oab-reports i releases) pending fenced) fenced)))
(defthm fn-oab-complete-keeps-the-state
  (and (equal (fn-oab-pending-after (fn-oab-complete i members word) pending) pending)
       (equal (fn-oab-fenced-after (fn-oab-complete i members word) pending fenced) fenced))
  :hints (("Goal" :in-theory (disable fn-oab-lines fn-oab-reports))))
(defthm fn-oab-complete-follows-fences
  (implies (or (fn-oab-covered i members fenced) (not (equal word :fenced)))
           (fn-oab-reports-follow-fences-p (fn-oab-complete i members word) pending fenced))
  :hints (("Goal" :in-theory (disable fn-oab-lines fn-oab-reports fn-oab-covered
                                      fn-ocs-member-releases))))
(defun fn-oab-cov-ind (i members)
  (declare (xargs :guard (natp i)))
  (if (consp members) (fn-oab-cov-ind (+ 1 (nfix i)) (cdr members)) i))
(defthm fn-oab-covered-stays-covered
  (implies (fn-oab-covered i members (append pending fenced))
           (fn-oab-covered i members (append (fn-oab-pending-after trace pending)
                                             (fn-oab-fenced-after trace pending fenced))))
  :hints (("Goal" :induct (fn-oab-cov-ind i members)
           :in-theory (disable fn-oab-pending-after fn-oab-fenced-after
                               fn-oab-member-equal-of-append))))
(in-theory (disable fn-oab-complete fn-oab-drain fn-oab-kept fn-oab-drain-kept-step-unfolds
                    fn-oab-drain-told-step-unfolds fn-oab-drain-and-kept-of-atom))
(defthm fn-oab-quantum-reports-after-its-barrier
  (fn-oab-reports-follow-fences-p (fn-oab-quantum members word) nil nil)
  :hints (("Goal" :use ((:instance fn-oab-drain-covers (i 0) (pending nil) (fenced nil))))))

(defthm fn-oab-pipeline-reports-after-its-barriers
  (fn-oab-reports-follow-fences-p (fn-oab-pipeline a b word-a word-b) nil nil)
  :hints (("Goal" :in-theory (disable fn-oab-covered-stays-covered)
           :use ((:instance fn-oab-drain-covers (i 0) (members a) (pending nil) (fenced nil))
                 (:instance fn-oab-drain-covers (i (len (fn-oab-kept a))) (members b)
                            (pending (fn-oab-pending-after (fn-oab-drain 0 a) nil))
                            (fenced (fn-oab-fenced-after (fn-oab-drain 0 a) nil nil)))
                 (:instance fn-oab-covered-stays-covered (i 0) (members (fn-oab-kept a))
                            (trace (fn-oab-drain (len (fn-oab-kept a)) b))
                            (pending (fn-oab-pending-after (fn-oab-drain 0 a) nil))
                            (fenced (fn-oab-fenced-after (fn-oab-drain 0 a) nil nil)))))))

; -----------------------------------------------------------------------------
; Every record kind the owner commits, and its route.  :quantum: drained by
; the committer inside a batch quantum (fnn-owner-commit-start-locked, the
; only owner function that binds *fnn-log-batch*): fn-oab-quantum and
; fn-oab-pipeline.  :one: committed outside a quantum, a batch of one whose
; append and barrier fnn-log-publish runs before the record's place and
; finish (tests/campaign/native_cuts.py POST_LOG_ONE_CANDIDATE), or a
; configuration record's own immutable publication (books/journal-publish,
; host/native/admin.lisp fnn-admin-publish: the directory barrier before
; :durable).  Host entries: the served article and the relayed article
; (fnn-owner-attempt, fnn-owner-attempt-transit); the statement's kind-4
; composite and its key change (fnn-owner-statement-committed,
; fnn-owner-key-statement); the control socket's post and a BP application's
; submission (fnn-owner-complete-bound-submission); the identity events of
; host/native/hybrid-control.lisp and peer-invite.lisp; the key change at
; open and keys redecide (fnn-owner-key-statement-recover,
; host/native/keys.lisp); consumer, topic and retention events
; (fnn-owner-consumer-commit, fnn-owner-topic-commit, retention's
; fnn-owner-publish-prepared); configuration records and XREDEEM's
; publication (fnn-owner-live-reconfigure-locked, fnn-owner-redeem-quantum).
; tests/campaign/native_cuts.py verify_statement_cut_map checks that only
; the quantum (and the import's history write) binds *fnn-log-batch*.
(defconst *fn-oab-record-kinds*
  '((:served-article . :quantum) (:relayed-article . :quantum)
    (:statement . :quantum) (:key-change . :quantum)
    (:control-post . :one) (:bp-application . :one) (:identity . :one)
    (:key-change-at-open . :one) (:key-redecide . :one)
    (:consumer . :one) (:topic . :one) (:retention . :one)
    (:config . :one) (:redeem . :one)))

; A batch of one: its take, its barrier, then its report.
(defun fn-oab-one (id)
  (declare (xargs :guard t))
  (list (list :take id) (list :fence) (list :report id)))

; A kind with no route in the table is unaccounted: its report stands alone.
(defun fn-oab-kind-trace (kind members word)
  (declare (xargs :guard t))
  (let ((route (cdr (assoc-equal kind *fn-oab-record-kinds*))))
    (cond ((equal route :quantum) (fn-oab-quantum members word))
          ((equal route :one) (fn-oab-one kind))
          (t (list (list :report kind))))))

(defthm fn-oab-every-kind-reports-after-its-barrier
  (implies (assoc-equal kind *fn-oab-record-kinds*)
           (fn-oab-reports-follow-fences-p (fn-oab-kind-trace kind members word) nil nil)))

(in-theory (disable fn-oab-quantum fn-oab-pipeline fn-oab-kind-trace
                    fn-oab-reports-follow-fences-p))
