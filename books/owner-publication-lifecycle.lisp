; fn: the lifecycle of a checkpoint publication that captured and ended
; without a durable checkpoint (ledger RL-02; the coordinator's ruling of
; 2026-10-04 on /Users/ember/dev/redregg/work/FN-DECISION-RL01-RL02-20261004.md,
; with gpt-6's refinements, FN-GPT6-REVIEW-20261004.md section 2).
;
; THE DEFECT.  A capture sets the publication slot (fn-owner-sco-inflight at
; the captured COUNT, host/owner-host.lisp fn-owner-sco-capture).  The slot was
; released only by fn-owner-sco-publication-done, which the host called only
; when the history's NEXT existed (host/native/owner.lisp
; fnn-owner-publish-captured).  A history that is not encodable, or whose image
; row is refused by name, ended the publication before NEXT: the slot stayed set
; for the run (no automatic checkpoint, every `store compact' answered
; :coalesced, a reclaim pass refused as in flight, the record log without
; bound).  Releasing the slot alone is no repair: the due rule re-arms on every
; count change, so the same refusal would meet a full history walk and a log
; rotation on every later POST.
;
; THE RULE (one decision, ACL2's).  Every publication that captured ends in
; exactly one of three ways: a durable checkpoint, a deferral by name (the
; budget or the space, PKT-492: fn-owner-sco-publication-done), or an ABANDONED
; outcome, which this book settles: the capture's own slot is released and the
; outcome is classified by what could make another attempt meaningful.
;
;   :blocked       nothing in this process can: an unencodable history, a
;                  history image refused for a reason that is not a dependency
;                  (an inconsistency in the builder).  It stands until the
;                  code, the format or the history changes, which is a restart
;                  (the deferral is the owner's, in memory); the health report
;                  holds the deferral (exit 29) naming the reason.
;   :await-change  a dependency still in flight (the history image's pending
;                  suffix): eligible once the history has advanced past the
;                  capture (the dependency's completion, observed as the next
;                  commit) AND the backoff has elapsed, so a POST alone never
;                  re-arms it.
;   :backoff       a refusal or failure of the store's I/O that may pass: eligible
;                  once the backoff has elapsed, whatever the count: ordinary
;                  POSTs neither reset nor bypass it.
;
; The backoff doubles with each consecutive abandonment (a durable publication
; ends the run of them) and is capped; eligibility is by TIME (the owner's
; monotonic millisecond clock), because a rule in commits alone goes inert
; when admission stops to protect the log's remaining space.  The outcome is
; recorded as the owner's deferral, (:deferred REASON ESTIMATE BOUND CLASS
; ATTEMPTS NOT-BEFORE COUNT): the first four elements are the shape every
; consumer of a deferral reads (fn-nh-checkpoint-deferredp, the status line,
; the readiness observation), so `status' and `health' name the deferral and
; its reason without a second report; ESTIMATE is the attempts so far and BOUND
; the backoff just taken in milliseconds (0 for :blocked, which waits for no
; time).  Those two labels are the budget deferral's: the readers print them
; as `estimate=' and `budget='.
;
; WHAT IS PROVED, and what is stated and not provable here.
;
;  SAFETY.  A terminal outcome settles its OWN capture exactly once and can
;  release no other capture.  A capture's identity is its SERIAL, the owner's
;  capture counter, with the COUNT it captured (the slot's key, the one
;  fn-orc-release-slot uses); the count alone is not one, because a :backoff
;  abandonment is retried at the same count when no commit came between.  A
;  settlement by a capture that does not hold the slot changes nothing at all,
;  neither the slot nor the recorded deferral
;  (`fn-opl-settle-never-touches-another-capture'); a late callback of
;  publication A cannot release or overwrite publication B, even at A's count
;  (`fn-opl-late-settlement-of-a-cannot-release-b'); the holder's settlement
;  frees the slot and records one deferral (`fn-opl-settle-releases-the-holder');
;  a second settlement of the same capture is the identity
;  (`fn-opl-settle-is-once').
;
;  LIVENESS, under stated assumptions.  The ASSUMPTIONS are the host's, and
;  are witnessed natively, not proved here: (1) every capture's thread reaches
;  its done quantum (fnn-owner-publish-captured's unwinding), which settles it,
;  with the outcome the thread observed; (2) the monotonic clock advances; (3)
;  the owner's maintenance takes the due decision once a second
;  (fnn-owner-start-maintenance).  Under them: after a settlement the owner
;  decides again and never answers :inflight or :coalesce for the settled
;  capture (`fn-opl-after-settlement-the-owner-decides-again'); a :backoff
;  abandonment is due again at the same count once the capped backoff has
;  elapsed, with no commit (`fn-opl-backoff-is-retried-without-a-commit'); an
;  :await-change one becomes eligible once the history has advanced and the
;  capped delay has elapsed
;  (`fn-opl-await-change-is-eligible-after-completion-and-the-cap'); and a
;  :blocked one never captures again while it stands, which is the alarm
;  (`fn-opl-blocked-is-never-due').  An indefinitely blocked physical operation
;  is outside this book: releasing the logical slot says nothing about memory
;  or disk work that has not ended, which the publication thread's own
;  unwinding (pin release, buffer release, nursery) owns.
;
;  NOT BY POSTs.  A :backoff deferral's eligibility is a function of the clock
;  alone (`fn-opl-backoff-eligibility-ignores-the-count'), and before it no
;  number of commits makes the decision :due
;  (`fn-opl-backoff-is-not-hastened-by-commits'); an :await-change's count
;  condition is conjoined with the clock's, never a substitute for it.
;
;  PRESERVATION.  A record that is not an abandonment keeps the old decision
;  and the rule's ATTEMPTED (`fn-opl-blockedp-of-a-budget-or-space-deferral',
;  `fn-opl-attempted-of-a-budget-or-space-deferral').
;
; Statement-first teeth are in tests/acl2/owner-publication-lifecycle-tests.lisp.
(in-package "ACL2")
(include-book "owner-checkpoint-open")
(include-book "owner-checkpoint-writer")
(include-book "owner-reclaim")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The backoff: milliseconds of the owner's monotonic clock.  A policy of the
; owner's work, not a bound on stored data (D27).

(defconst *fn-opl-backoff-base-ms* 30000)
(defconst *fn-opl-backoff-cap-ms* 900000)

(defun fn-opl-delay (attempts)
  (declare (xargs :guard t))
  (min *fn-opl-backoff-cap-ms*
       (* *fn-opl-backoff-base-ms*
          (expt 2 (min 30 (nfix (- (nfix attempts) 1)))))))

(defthm fn-opl-delay-natp
  (natp (fn-opl-delay attempts))
  :rule-classes :type-prescription)

(defthm fn-opl-delay-is-capped
  (<= (fn-opl-delay attempts) *fn-opl-backoff-cap-ms*)
  :rule-classes :linear)

(defthm fn-opl-delay-is-at-least-the-base
  (<= *fn-opl-backoff-base-ms* (fn-opl-delay attempts))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The classification of an outcome the host observed, by what could make
; another attempt meaningful.  OUTCOME is one of (:unencodable),
; (:image-refused VERDICT), (:io-refusal), (:job-failure CLASS); anything else
; is retried under the backoff and reported as unclassified, never taken for
; permanent and never for free.  Answers (CLASS REASON); REASON is the word
; `status' and `health' print.

(defun fn-opl-classify (outcome)
  (declare (xargs :guard t))
  (cond ((equal outcome '(:unencodable))
         (list :blocked :blocked-unencodable-history))
        ((and (consp outcome) (eq (car outcome) :image-refused) (consp (cdr outcome)))
         (if (member-equal (cadr outcome) '((:refused :pending-suffix) (:refused :suffix)))
             (list :await-change :retry-on-history-advance-image-suffix)
           (list :blocked :blocked-history-image-refused)))
        ((equal outcome '(:io-refusal))
         (list :backoff :retry-after-backoff-store-io-refusal))
        ((and (consp outcome) (eq (car outcome) :job-failure))
         (list :backoff :retry-after-backoff-job-failure))
        (t (list :backoff :retry-after-backoff-unclassified))))

(defthm fn-opl-classify-class
  (or (equal (car (fn-opl-classify outcome)) :blocked)
      (equal (car (fn-opl-classify outcome)) :await-change)
      (equal (car (fn-opl-classify outcome)) :backoff))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-opl-classify))))

(defthm fn-opl-classify-reason
  (keywordp (cadr (fn-opl-classify outcome)))
  :hints (("Goal" :in-theory (enable fn-opl-classify))))

(in-theory (disable fn-opl-classify (:executable-counterpart fn-opl-classify)))

; -----------------------------------------------------------------------------
; The recorded deferral: (:deferred REASON ESTIMATE BOUND CLASS ATTEMPTS
; NOT-BEFORE COUNT).

(defun fn-opl-recordp (d)
  (declare (xargs :guard t))
  (and (true-listp d) (equal (len d) 8)
       (eq (car d) :deferred)
       (keywordp (nth 1 d))
       (natp (nth 2 d)) (natp (nth 3 d))
       (member-eq (nth 4 d) '(:blocked :await-change :backoff))
       (natp (nth 5 d)) (natp (nth 6 d)) (natp (nth 7 d))))

; The abandonments in a row: the previous record's, else none.
(defun fn-opl-attempts-before (prev)
  (declare (xargs :guard t))
  (if (fn-opl-recordp prev) (nth 5 prev) 0))

(defthm fn-opl-attempts-before-natp
  (natp (fn-opl-attempts-before prev))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-opl-attempts-before fn-opl-recordp))))

; A blocked deferral waits for no time; the others for the backoff.
(defun fn-opl-not-before (class now attempts)
  (declare (xargs :guard t))
  (if (eq class :blocked) 0 (+ (nfix now) (fn-opl-delay attempts))))

(defthm fn-opl-not-before-natp
  (natp (fn-opl-not-before class now attempts))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-opl-not-before))))

(defthm fn-opl-not-before-is-within-the-cap
  (<= (fn-opl-not-before class now attempts) (+ (nfix now) *fn-opl-backoff-cap-ms*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-opl-not-before))))

(defun fn-opl-record (outcome count now prev)
  (declare (xargs :guard t))
  (let* ((cr (fn-opl-classify outcome))
         (attempts (+ 1 (fn-opl-attempts-before prev))))
    (list :deferred (cadr cr) attempts
          (if (eq (car cr) :blocked) 0 (fn-opl-delay attempts))
          (car cr) attempts
          (fn-opl-not-before (car cr) now attempts)
          (nfix count))))

(defthm fn-opl-record-is-a-record
  (fn-opl-recordp (fn-opl-record outcome count now prev))
  :hints (("Goal" :in-theory (e/d (fn-opl-record fn-opl-recordp) (keywordp))
           :use (fn-opl-classify-class fn-opl-classify-reason))))

(defthm fn-opl-record-class
  (equal (nth 4 (fn-opl-record outcome count now prev)) (car (fn-opl-classify outcome)))
  :hints (("Goal" :in-theory (enable fn-opl-record))))

(defthm fn-opl-record-not-before
  (equal (nth 6 (fn-opl-record outcome count now prev))
         (fn-opl-not-before (car (fn-opl-classify outcome)) now
                            (+ 1 (fn-opl-attempts-before prev))))
  :hints (("Goal" :in-theory (enable fn-opl-record))))

(defthm fn-opl-record-count
  (equal (nth 7 (fn-opl-record outcome count now prev)) (nfix count))
  :hints (("Goal" :in-theory (enable fn-opl-record))))

(in-theory (disable fn-opl-record (:executable-counterpart fn-opl-record)))

; The record is a deferral for every consumer of one (the four elements
; fn-nh-checkpoint-deferredp, the status line and the readiness observation
; read): it carries the keyword reason and two naturals.
(defthm fn-opl-record-is-read-as-a-deferral
  (let ((d (fn-opl-record outcome count now prev)))
    (and (consp d) (equal (car d) :deferred)
         (keywordp (cadr d)) (natp (caddr d)) (natp (cadddr d))))
  :hints (("Goal" :in-theory (e/d (fn-opl-record) (keywordp))
           :use (fn-opl-classify-reason)))
  :rule-classes nil)

; Eligibility for another attempt, at COUNT committed records and the clock
; NOW.  Only an abandonment's record is eligible or not: a record that is not
; one is the budget or space deferral's, decided by fn-ock-publication-blockedp.
(defun fn-opl-eligiblep (d count now)
  (declare (xargs :guard t))
  (and (fn-opl-recordp d) (natp now) (natp count)
       (cond ((eq (nth 4 d) :backoff) (<= (nth 6 d) now))
             ((eq (nth 4 d) :await-change)
              (and (<= (nth 6 d) now) (< (nth 7 d) count)))
             (t nil))))

; The blocked rule of a recorded deferral, the due path's argument to
; fn-ock-publication-next and the requests' (fn-ock-request-word,
; fn-orc-request-word).  BUDGET and SPACE are the old rule's.
(defun fn-opl-blockedp (deferred budget space count now)
  (declare (xargs :guard t))
  (if (fn-opl-recordp deferred)
      (not (fn-opl-eligiblep deferred count now))
    (fn-ock-publication-blockedp deferred budget space)))

(defthm fn-opl-blockedp-of-a-budget-or-space-deferral
  (implies (not (fn-opl-recordp deferred))
           (equal (fn-opl-blockedp deferred budget space count now)
                  (fn-ock-publication-blockedp deferred budget space))))

; -----------------------------------------------------------------------------
; The publication's identity.  A capture is named by its SERIAL, the owner's
; capture counter after the capture (fn-opl-next-serial: one more than the
; one before, host/owner-host.lisp fn-owner-sco-capture), and by the COUNT it
; captured, the slot's key (fn-owner-sco-inflight, fn-orc-release-slot's
; (:publication COUNT)).  The count alone is not an identity: a :backoff
; abandonment is retried at the SAME count when no commit came in between
; (fn-opl-attempted below), so two captures can share a count; no two share a
; serial.

(defun fn-opl-next-serial (serial)
  (declare (xargs :guard t))
  (+ 1 (nfix serial)))

(defthm fn-opl-next-serial-natp
  (natp (fn-opl-next-serial serial))
  :rule-classes :type-prescription)

; Settlement.  HOLDSP: the capture (COUNT SERIAL) holds the slot: a
; publication's own slot, which no writing reclaim pass holds (the dry run
; holds none), at its own count (fn-orc-release-slot's rule for
; (:publication COUNT)), and it is the newest capture (CURRENT, the owner's
; serial now).

(defun fn-opl-holdsp (count serial pass inflight current)
  (declare (xargs :guard t))
  (and (or (not pass) (eq pass :dry-run))
       (natp inflight)
       (equal inflight count)
       (natp serial)
       (equal serial current)))

; The settlement of an abandoned capture: (PASS' INFLIGHT' DEFERRED').  A
; capture that does not hold the slot changes nothing.
(defun fn-opl-settle (count serial outcome now pass inflight current deferred)
  (declare (xargs :guard t))
  (if (fn-opl-holdsp count serial pass inflight current)
      (let ((rel (fn-orc-release-slot (list :publication count) pass inflight)))
        (list (car rel) (cadr rel) (fn-opl-record outcome count now deferred)))
    (list pass inflight deferred)))

; KEYSTONE (safety, no capture but one's own).  A settlement by a capture that
; does not hold the slot changes nothing: not the pass, not the slot, not the
; recorded deferral.
(defthm fn-opl-settle-never-touches-another-capture
  (implies (not (fn-opl-holdsp count serial pass inflight current))
           (equal (fn-opl-settle count serial outcome now pass inflight current deferred)
                  (list pass inflight deferred))))

; ... and so a late callback of publication A cannot release, or overwrite
; the deferral of, publication B: B's capture made the serial one past every
; serial before it, A's among them, even when B captured A's count.
(defthm fn-opl-late-settlement-of-a-cannot-release-b
  (implies (and (natp a) (natp s) (<= a s))
           (equal (fn-opl-settle count a outcome now pass inflight (fn-opl-next-serial s)
                                 deferred)
                  (list pass inflight deferred)))
  :hints (("Goal" :in-theory (enable fn-opl-holdsp fn-opl-next-serial))))

; KEYSTONE (safety, the holder settles).  The capture that holds the slot
; frees it, leaves the pass as it was, and records exactly one deferral.
(defthm fn-opl-settle-releases-the-holder
  (implies (fn-opl-holdsp count serial pass inflight current)
           (let ((r (fn-opl-settle count serial outcome now pass inflight current deferred)))
             (and (equal (car r) pass)
                  (equal (cadr r) nil)
                  (equal (caddr r) (fn-opl-record outcome count now deferred))
                  (fn-opl-recordp (caddr r)))))
  :hints (("Goal" :in-theory (enable fn-opl-holdsp fn-orc-release-slot))))

; KEYSTONE (safety, exactly once).  Settling a capture a second time, with
; any outcome and any later clock, is the identity: the first settlement is the
; only one.
(defthm fn-opl-settle-is-once
  (let ((r (fn-opl-settle count serial o1 now1 pass inflight current deferred)))
    (equal (fn-opl-settle count serial o2 now2 (car r) (cadr r) current (caddr r)) r))
  :hints (("Goal" :in-theory (enable fn-opl-holdsp fn-orc-release-slot))))

; KEYSTONE (liveness of the slot, given the host's assumption that the thread
; settles).  After the holder's settlement the owner decides again from the
; newest frontier and never answers that a publication is in flight or
; coalesces a request for the settled capture.
(defthm fn-opl-after-settlement-the-owner-decides-again
  (implies (fn-opl-holdsp count serial pass inflight current)
           (let ((r (fn-opl-settle count serial outcome now pass inflight current deferred)))
             (not (member-eq (fn-ock-publication-next durable cnt k attempted (cadr r) blockedp)
                             '(:inflight :coalesce)))))
  :hints (("Goal" :in-theory (enable fn-opl-holdsp fn-orc-release-slot fn-ock-publication-next))))

; -----------------------------------------------------------------------------
; Eligibility: what can make another attempt meaningful, and when.

; The alarm: a :blocked deferral is never eligible, at any count or time.
(defthm fn-opl-blocked-is-never-eligible
  (implies (equal (nth 4 d) :blocked)
           (not (fn-opl-eligiblep d count now)))
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep))))

; ... and the outcomes that classify as :blocked record a blocked deferral.
(defthm fn-opl-an-unencodable-history-blocks-for-good
  (let ((d (fn-opl-record '(:unencodable) count now prev)))
    (and (equal (nth 4 d) :blocked)
         (fn-opl-blockedp d budget space c2 now2)))
  :hints (("Goal" :in-theory (e/d (fn-opl-blockedp fn-opl-eligiblep fn-opl-classify)
                                  ()))))

; Not by POSTs: a :backoff deferral's eligibility does not read the count.
(defthm fn-opl-backoff-eligibility-ignores-the-count
  (implies (and (equal (nth 4 d) :backoff) (natp c1) (natp c2))
           (equal (fn-opl-eligiblep d c1 now) (fn-opl-eligiblep d c2 now)))
  ; not a rewrite rule: its two sides differ only in the count, so it loops
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep))))

; The backoff taken is the capped delay: a record is eligible no later than
; the cap after its abandonment (under the clock's advance).
(defthm fn-opl-record-not-before-is-within-the-cap
  (let ((d (fn-opl-record outcome count now prev)))
    (<= (nth 6 d) (+ (nfix now) *fn-opl-backoff-cap-ms*))))

(defthm fn-opl-backoff-is-eligible-within-the-cap
  (implies (and (natp now) (natp later) (natp count)
                (<= (+ now *fn-opl-backoff-cap-ms*) later)
                (equal (nth 4 (fn-opl-record outcome c0 now prev)) :backoff))
           (fn-opl-eligiblep (fn-opl-record outcome c0 now prev) count later))
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep)
           :use ((:instance fn-opl-record-not-before-is-within-the-cap
                            (outcome outcome) (count c0) (now now) (prev prev))
                 (:instance fn-opl-record-is-a-record
                            (outcome outcome) (count c0) (now now) (prev prev))))))

; An :await-change deferral needs BOTH: the history advanced past the capture
; and the backoff elapsed.  The clock alone is not the dependency's completion
; ...
(defthm fn-opl-await-change-needs-the-history-to-advance
  (implies (and (equal (nth 4 d) :await-change) (natp count) (<= count (nth 7 d)))
           (not (fn-opl-eligiblep d count now)))
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep))))

; ... and the count alone (a POST) is not eligibility.
(defthm fn-opl-await-change-needs-the-backoff-to-elapse
  (implies (and (equal (nth 4 d) :await-change) (natp now) (< now (nth 6 d)))
           (not (fn-opl-eligiblep d count now)))
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep))))

(defthm fn-opl-await-change-is-eligible-after-completion-and-the-cap
  (implies (and (natp now) (natp later) (natp count)
                (<= (+ now *fn-opl-backoff-cap-ms*) later)
                (< c0 count)
                (natp c0)
                (equal (nth 4 (fn-opl-record outcome c0 now prev)) :await-change))
           (fn-opl-eligiblep (fn-opl-record outcome c0 now prev) count later))
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep)
           :use ((:instance fn-opl-record-not-before-is-within-the-cap
                            (outcome outcome) (count c0) (now now) (prev prev))
                 (:instance fn-opl-record-is-a-record
                            (outcome outcome) (count c0) (now now) (prev prev))
                 (:instance fn-opl-record-count
                            (outcome outcome) (count c0) (now now) (prev prev))))))

; The repeated failure waits at least as long as the one before it (doubling,
; capped): a run of abandonments cannot tighten the retry.
(defthm fn-opl-delay-does-not-shrink
  (<= (fn-opl-delay attempts) (fn-opl-delay (+ 1 (nfix attempts))))
  :hints (("Goal" :in-theory (enable fn-opl-delay))))

; -----------------------------------------------------------------------------
; The due path.  The owner's rule (fn-ock-publication-duep) never captures the
; ATTEMPTED count again: a deferral by budget or space, or a durable
; publication, at that count would come out the same.  An abandonment's own
; eligibility replaces that conjunct: an eligible record frees the due rule to
; capture the same count again, because time, not a commit, is what made the
; attempt meaningful (gpt-6's review, section 2: a backoff counted in commits
; goes inert once admission stops to protect the log).  The owner's
; maintenance takes the decision once a second (host/native/owner.lisp
; fnn-owner-start-maintenance), so the clock is read without a POST.

(defun fn-opl-attempted (deferred attempted count now)
  (declare (xargs :guard t))
  (if (fn-opl-eligiblep deferred count now) nil attempted))

; Only an abandonment's record changes the rule's ATTEMPTED.
(defthm fn-opl-attempted-of-a-budget-or-space-deferral
  (implies (not (fn-opl-recordp deferred))
           (equal (fn-opl-attempted deferred attempted count now) attempted))
  :hints (("Goal" :in-theory (enable fn-opl-eligiblep))))

; KEYSTONE (liveness of the retry, under the host's assumptions: the thread
; settles, the clock advances, the maintenance decides).  A capture at COUNT
; that the rule had due, abandoned for a reason that may pass (:backoff), is
; due again at the SAME count once the capped backoff has elapsed: no commit,
; no POST and no operator is needed.
(defthm fn-opl-backoff-is-retried-without-a-commit
  (implies (and (fn-opl-holdsp count serial pass count current)
                (natp now) (natp later)
                (<= (+ now *fn-opl-backoff-cap-ms*) later)
                (equal (car (fn-opl-classify outcome)) :backoff)
                (fn-ock-publication-duep durable count k nil))
           (let* ((r (fn-opl-settle count serial outcome now pass count current deferred))
                  (d (caddr r)))
             (equal (fn-ock-publication-next durable count k
                                             (fn-opl-attempted d count count later)
                                             (cadr r)
                                             (fn-opl-blockedp d budget space count later))
                    :due)))
  :hints (("Goal" :in-theory (e/d (fn-opl-attempted fn-opl-blockedp fn-ock-publication-next)
                                  (fn-opl-settle))
           :use ((:instance fn-opl-settle-releases-the-holder (inflight count))
                 (:instance fn-opl-backoff-is-eligible-within-the-cap
                            (c0 count) (count count))
                 (:instance fn-opl-record-class (now now) (prev deferred))))))

; KEYSTONE (the alarm, on the due path).  A :blocked abandonment's record
; blocks every decision with nothing in flight, at every count and every
; time: it never captures again while the record stands (the owner's, in
; memory: a restart, with whatever code, format or history it brings, ends it;
; the operator's request and the writing reclaim pass read the same rule).
(defthm fn-opl-blocked-is-never-due
  (implies (and (fn-opl-recordp d) (equal (nth 4 d) :blocked)
                (not (natp inflight)))
           (equal (fn-ock-publication-next durable count k
                                           (fn-opl-attempted d attempted count now)
                                           inflight
                                           (fn-opl-blockedp d budget space count now))
                  :blocked))
  :hints (("Goal" :in-theory (enable fn-opl-blockedp fn-opl-eligiblep
                                     fn-ock-publication-next))))

; KEYSTONE (not by POSTs, on the due path).  Before a :backoff record's
; not-before, no count captures: a thousand commits decide :blocked.
(defthm fn-opl-backoff-is-not-hastened-by-commits
  (implies (and (fn-opl-recordp d) (equal (nth 4 d) :backoff)
                (natp now) (< now (nth 6 d))
                (not (natp inflight)))
           (equal (fn-ock-publication-next durable count k
                                           (fn-opl-attempted d attempted count now)
                                           inflight
                                           (fn-opl-blockedp d budget space count now))
                  :blocked))
  :hints (("Goal" :in-theory (enable fn-opl-blockedp fn-opl-eligiblep
                                     fn-ock-publication-next))))
