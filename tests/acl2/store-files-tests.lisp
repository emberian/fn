; Executable crash traces for the immutable-file publication kernel, and the
; teeth for the crash-point theorems in store-files-invariants.lisp.
;
; Each tooth below instantiates a keystone at a concrete witness with one
; hypothesis dropped and asserts the conclusion is then false.  The witnesses
; are reachable kernel states except where a hypothesis is the state
; recognizer itself, in which case the witness is a malformed tuple.
(in-package "ACL2")
(include-book "../../books/store-files-invariants")
(include-book "../../books/codec-attach")

(defconst *sf-groups* '("fn.letters" "fn.test"))
(defconst *sf-record-0*
  (fn-record-make 0 0 0 "<zero@example.invalid>" '(90)
                  '("fn.letters" "fn.test")
                  "archive-zero" "content-zero" "release-zero" 2 841000000))

(defconst *sf-s0* (fn-sf-initial-state))
(assert-event (fn-sf-statep *sf-s0*))

; -----------------------------------------------------------------------------
; Allocator crash points.

; :frontier-staged: the staging file may exist but no replacement can have
; been issued, so :new selects nothing (crash point staged-data-barrier is the
; analogue for records; the allocator has no host cut here).
(defconst *sf-fa0* (fn-sf-start-frontier *sf-s0*))
(assert-event (equal (fn-sf-phase *sf-fa0*) :frontier-staged))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-fa0* :new :absent)) 0))
(assert-event (not (fn-sf-crash-imagep *sf-fa0* 1 nil)))

; :frontier-data-durable: the host issues os.replace before it reports the
; result (crash point frontier-replace).  Old and new are both outcomes.
(defconst *sf-fa1* (fn-sf-frontier-file-result *sf-fa0* :ok))
(assert-event (equal (fn-sf-phase *sf-fa1*) :frontier-data-durable))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-fa1* :old :absent)) 0))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-fa1* :new :absent)) 1))
(assert-event (fn-sf-crash-imagep *sf-fa1* 0 nil))
(assert-event (fn-sf-crash-imagep *sf-fa1* 1 nil))
(assert-event (not (fn-sf-crash-imagep *sf-fa1* 2 nil)))
(assert-event (not (fn-sf-crash-imagep *sf-fa1* 0 (list *sf-record-0*))))
; Teeth for fn-sf-unobserved-frontier-replacement-crash-is-old-or-new.
; Phase hypothesis dropped: in :frontier-staged :new does not reach the candidate.
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier (fn-sf-crash *sf-fa0* :new :absent))
                       (fn-sf-frontier-candidate *sf-fa0*)))))
; Record-choice hypothesis dropped: an invalid choice makes the crash a no-op.
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier (fn-sf-crash *sf-fa1* :new :bogus))
                       (fn-sf-frontier-candidate *sf-fa1*)))))
; State hypothesis dropped: a malformed tuple in the phase is a no-op crash.
(defconst *sf-bogus-data-durable*
  (fn-sf-make :frontier-data-durable 0 1 '(not-a-record) nil nil nil 5))
(assert-event (not (fn-sf-statep *sf-bogus-data-durable*)))
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier (fn-sf-crash *sf-bogus-data-durable* :new :absent))
                       (fn-sf-frontier-candidate *sf-bogus-data-durable*)))))

; :frontier-attempted (crash point frontier-dir-barrier): still both values.
(defconst *sf-fa2* (fn-sf-frontier-replace-result *sf-fa1* :ok))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-fa2* :old :absent)) 0))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-fa2* :new :absent)) 1))

; An error reported by replace is also post-attempt uncertainty.  Recovery uses
; whichever whole frontier is observed, including the new value on the same
; logical adapter instance; it never consults the cached old value separately.
(defconst *sf-fa-error* (fn-sf-frontier-replace-result *sf-fa1* :error))
(assert-event (fn-sf-fencedp *sf-fa-error*))
(defconst *sf-fa-error-new* (fn-sf-crash *sf-fa-error* :new :absent))
(assert-event (equal (fn-sf-frontier *sf-fa-error-new*) 1))
(defconst *sf-unused-recovery-0*
  (fn-sf-recover *sf-fa-error-new* *sf-groups* 10))
(assert-event (equal (fn-sf-phase *sf-unused-recovery-0*) :recovering))
(defconst *sf-unused-recovery-1*
  (fn-sf-recovery-barrier *sf-unused-recovery-0* :ok))
(defconst *sf-unused-recovery-2*
  (fn-sf-recovery-barrier *sf-unused-recovery-1* :ok))
(defconst *sf-unused-recovery-3*
  (fn-sf-recovery-barrier *sf-unused-recovery-2* :ok))
(defconst *sf-unused-recovery-4*
  (fn-sf-recovery-barrier *sf-unused-recovery-3* :ok))
(defconst *sf-unused-recovered*
  (fn-sf-recovery-barrier *sf-unused-recovery-4* :ok))
(assert-event (equal (fn-sf-phase *sf-unused-recovered*) :ready))
(assert-event (equal (fn-sf-prepare-record *sf-unused-recovered* *sf-record-0*
                                           *sf-groups* 10)
                     *sf-unused-recovered*))

; A completed allocator directory barrier removes the old choice
; (fn-sf-completed-frontier-barrier-removes-old-choice): the barrier step is
; what constrains the crash, the crash asserts nothing about the barrier.
(defconst *sf-f1* (fn-sf-frontier-dir-result *sf-fa2* :ok))
(assert-event (fn-sf-statep *sf-f1*))
(assert-event (equal (fn-sf-phase *sf-f1*) :reserved))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-f1* :old :absent)) 1))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-f1* :new :absent)) 1))
(assert-event (not (fn-sf-crash-imagep *sf-f1* 0 nil)))
; Teeth.  Phase hypothesis dropped: from :frontier-data-durable the barrier
; step is a no-op and :old still selects the old value.
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier
                        (fn-sf-crash (fn-sf-frontier-dir-result *sf-fa1* :ok) :old :absent))
                       (fn-sf-frontier-candidate *sf-fa1*)))))
; State hypothesis dropped.
(defconst *sf-bogus-attempted*
  (fn-sf-make :frontier-attempted 0 1 '(not-a-record) nil nil nil 5))
(assert-event (not (fn-sf-statep *sf-bogus-attempted*)))
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier
                        (fn-sf-crash (fn-sf-frontier-dir-result *sf-bogus-attempted* :ok)
                                     :old :absent))
                       (fn-sf-frontier-candidate *sf-bogus-attempted*)))))

; A mismatched refusal is a no-op.  A real semantic refusal consumes the one
; durable reservation and cannot be mistaken for permission to reuse txid 0.
(assert-event (equal (fn-sf-refuse-reservation *sf-f1* 7) *sf-f1*))
(defconst *sf-refused* (fn-sf-refuse-reservation *sf-f1* 0))
(assert-event (equal (fn-sf-phase *sf-refused*) :ready))
(assert-event (equal (fn-sf-prepare-record *sf-refused* *sf-record-0*
                                           *sf-groups* 10)
                     *sf-refused*))

; -----------------------------------------------------------------------------
; Record crash points.

; Replay admits the core-produced record.  A known abort before the hard-link
; attempt leaves no final record and keeps the consumed frontier.
(defconst *sf-r0*
  (fn-sf-prepare-record *sf-f1* *sf-record-0* *sf-groups* 10))
(assert-event (equal (fn-sf-phase *sf-r0*) :record-staged))
; :record-staged (crash point staged-data-barrier): no link can have been
; issued, so :present selects nothing.
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-r0* :old :present)) nil))
(assert-event (not (fn-sf-crash-imagep *sf-r0* 1 (list *sf-record-0*))))

(defconst *sf-rdata* (fn-sf-record-file-result *sf-r0* :ok))
(assert-event (equal (fn-sf-phase *sf-rdata*) :record-data-durable))
; :record-data-durable (crash point final-link): the host issues os.link
; before it reports the result, so absence and the exact candidate are both
; outcomes (fn-sf-unobserved-record-link-crash-is-absent-or-present).
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-rdata* :old :absent)) nil))
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-rdata* :old :present))
                     (list *sf-record-0*)))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sf-rdata* :new :present)) 1))
(assert-event (fn-sf-crash-imagep *sf-rdata* 1 nil))
(assert-event (fn-sf-crash-imagep *sf-rdata* 1 (list *sf-record-0*)))
(assert-event (not (fn-sf-crash-imagep *sf-rdata* 0 nil)))
(assert-event (not (fn-sf-crash-imagep *sf-rdata* 2 (list *sf-record-0*))))
; The realizing choice reproduces each admissible image.
(assert-event (equal (fn-sf-records
                      (fn-sf-crash *sf-rdata*
                                   (fn-sf-image-frontier-choice *sf-rdata* 1)
                                   (fn-sf-image-record-choice
                                    *sf-rdata* (list *sf-record-0*))))
                     (list *sf-record-0*)))
(assert-event (equal (fn-sf-records
                      (fn-sf-crash *sf-rdata*
                                   (fn-sf-image-frontier-choice *sf-rdata* 1)
                                   (fn-sf-image-record-choice *sf-rdata* nil)))
                     nil))
; Teeth for fn-sf-unobserved-record-link-crash-is-absent-or-present.
; Phase hypothesis dropped: in :record-staged :present does not append.
(assert-event (with-guard-checking :none (not (equal (fn-sf-records (fn-sf-crash *sf-r0* :old :present))
                       (append (fn-sf-records *sf-r0*)
                               (list (fn-sf-record-candidate *sf-r0*)))))))
; Frontier-choice hypothesis dropped: an invalid choice is a no-op crash.
(assert-event (with-guard-checking :none (not (equal (fn-sf-records (fn-sf-crash *sf-rdata* :bogus :present))
                       (append (fn-sf-records *sf-rdata*)
                               (list (fn-sf-record-candidate *sf-rdata*)))))))
; State hypothesis dropped.
(defconst *sf-bogus-record-durable*
  (fn-sf-make :record-data-durable 1 nil nil *sf-record-0* nil nil 3))
(assert-event (not (fn-sf-statep *sf-bogus-record-durable*)))
(assert-event (with-guard-checking :none (not (equal (fn-sf-records (fn-sf-crash *sf-bogus-record-durable* :old :present))
                       (append (fn-sf-records *sf-bogus-record-durable*)
                               (list (fn-sf-record-candidate *sf-bogus-record-durable*)))))))

; The composed known abort is two kernel steps: :aborting is transient.
(defconst *sf-aborting* (fn-sf-prepublish-abort *sf-rdata*))
(assert-event (equal (fn-sf-phase *sf-aborting*) :aborting))
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-aborting* :old :present)) nil))
(assert-event (equal (fn-sf-abort-completion *sf-aborting* 0 7) *sf-aborting*))
(defconst *sf-aborted* (fn-sf-abort-completion *sf-aborting* 0 0))
(assert-event (equal (fn-sf-phase *sf-aborted*) :ready))
(assert-event (equal (fn-sf-frontier *sf-aborted*) 1))
(assert-event (equal (fn-sf-records *sf-aborted*) nil))
(assert-event (equal (fn-sf-prepare-record *sf-aborted* *sf-record-0*
                                           *sf-groups* 10)
                     *sf-aborted*))

; The next allocator operation creates a fresh one-use reservation.  Sequence 0
; now admits txid 1, while the known-aborted txid 0 remains unavailable.
(defconst *sf-record-1*
  (fn-record-make 0 1 1 "<one@example.invalid>" '(79)
                  '("fn.letters")
                  "archive-one" "content-one" "release-one" 1 841000000))
(defconst *sf-next-a0* (fn-sf-start-frontier *sf-aborted*))
(defconst *sf-next-a1* (fn-sf-frontier-file-result *sf-next-a0* :ok))
(defconst *sf-next-a2* (fn-sf-frontier-replace-result *sf-next-a1* :ok))
(defconst *sf-next-reserved* (fn-sf-frontier-dir-result *sf-next-a2* :ok))
(assert-event (equal (fn-sf-frontier *sf-next-reserved*) 2))
(assert-event (equal (fn-sf-phase *sf-next-reserved*) :reserved))
(assert-event (equal (fn-sf-phase
                      (fn-sf-prepare-record *sf-next-reserved* *sf-record-1*
                                            *sf-groups* 10))
                     :record-staged))

; :record-attempted (crash point directory-barrier): absence or the exact
; candidate.  The observed durable frontier remains the already-barriered
; value, never the process-cached value from before allocation.
(defconst *sf-linked* (fn-sf-record-link-result *sf-rdata* :ok))
(defconst *sf-crash-absent* (fn-sf-crash *sf-linked* :old :absent))
(defconst *sf-crash-present* (fn-sf-crash *sf-linked* :old :present))
(assert-event (equal (fn-sf-records *sf-crash-absent*) nil))
(assert-event (equal (fn-sf-records *sf-crash-present*)
                     (list *sf-record-0*)))
(assert-event (equal (fn-sf-frontier *sf-crash-present*) 1))
(assert-event (equal (fn-sf-phase
                      (fn-sf-recover *sf-crash-present* *sf-groups* 10))
                     :recovering))

; A completed transaction-directory barrier removes the absent choice
; (fn-sf-completed-record-barrier-removes-absent-choice); success remains
; impossible before matching core completion.
(defconst *sf-published* (fn-sf-record-dir-result *sf-linked* :ok))
(assert-event (equal (fn-sf-phase *sf-published*) :completing))
(assert-event (equal (fn-sf-emit-success *sf-published* 0 0) *sf-published*))
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-published* :old :absent))
                     (list *sf-record-0*)))
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-published* :new :present))
                     (list *sf-record-0*)))
(assert-event (not (fn-sf-crash-imagep *sf-published* 1 nil)))
(assert-event (fn-sf-crash-imagep *sf-published* 1 (list *sf-record-0*)))
; Teeth.  Phase hypothesis dropped: from :record-data-durable the barrier step
; is a no-op and :absent still selects absence.
(assert-event (with-guard-checking :none (not (equal (fn-sf-records
                        (fn-sf-crash (fn-sf-record-dir-result *sf-rdata* :ok) :old :absent))
                       (append (fn-sf-records *sf-rdata*)
                               (list (fn-sf-record-candidate *sf-rdata*)))))))
; State hypothesis dropped.
(defconst *sf-bogus-record-attempted*
  (fn-sf-make :record-attempted 1 nil nil *sf-record-0* nil nil 3))
(assert-event (not (fn-sf-statep *sf-bogus-record-attempted*)))
(assert-event (with-guard-checking :none (not (equal (fn-sf-records
                        (fn-sf-crash (fn-sf-record-dir-result *sf-bogus-record-attempted* :ok)
                                     :old :absent))
                       (append (fn-sf-records *sf-bogus-record-attempted*)
                               (list (fn-sf-record-candidate *sf-bogus-record-attempted*)))))))

; :completing admits only the exact matching completion
; (fn-sf-completing-admits-only-matching-completion).  A lost or rejected
; reply to fn-sn-finish is a host-side fence with the kernel still here; the
; only route onward is crash/replay, which retains the record.
(assert-event (equal (fn-sf-core-completion *sf-published* 0 7) *sf-published*))
(assert-event (equal (fn-sf-start-frontier *sf-published*) *sf-published*))
(defconst *sf-recovered-0*
  (fn-sf-recover (fn-sf-crash *sf-published* :old :absent)
                 *sf-groups* 10))
(assert-event (equal (fn-sf-phase *sf-recovered-0*) :recovering))
(assert-event (equal (fn-sf-records *sf-recovered-0*) (list *sf-record-0*)))

; Matching completion then acknowledgement: :completed is transient inside
; fn-sn-finish, and the acknowledgement lands in the ghost history.
(defconst *sf-core-ok* (fn-sf-core-completion *sf-published* 0 0))
(assert-event (equal (fn-sf-phase *sf-core-ok*) :completed))
(defconst *sf-acked* (fn-sf-emit-success *sf-core-ok* 0 0))
(assert-event (equal (fn-sf-phase *sf-acked*) :ready))
(assert-event (equal (fn-sf-successes *sf-acked*) '((0 . 0))))
; Crash point core-durable: death after fn-sn-finish returned is a crash from
; :ready; the acknowledged record is in every admissible image.
(assert-event (equal (fn-sf-records (fn-sf-crash *sf-acked* :new :absent))
                     (list *sf-record-0*)))
(assert-event (fn-sf-crash-imagep *sf-acked* 1 (list *sf-record-0*)))
(assert-event (not (fn-sf-crash-imagep *sf-acked* 1 nil)))

; Recovery performs actual fn-replay and remains unavailable until all five
; prerequisite barriers succeed.
(defconst *sf-recovered-1* (fn-sf-recovery-barrier *sf-recovered-0* :ok))
(defconst *sf-recovered-2* (fn-sf-recovery-barrier *sf-recovered-1* :ok))
(defconst *sf-recovered-3* (fn-sf-recovery-barrier *sf-recovered-2* :ok))
(defconst *sf-recovered-4* (fn-sf-recovery-barrier *sf-recovered-3* :ok))
(assert-event (not (equal (fn-sf-phase *sf-recovered-4*) :ready)))
(defconst *sf-recovered-5* (fn-sf-recovery-barrier *sf-recovered-4* :ok))
(assert-event (equal (fn-sf-phase *sf-recovered-5*) :ready))
(assert-event (equal (fn-sf-records *sf-recovered-5*)
                     (list *sf-record-0*)))

; A failed recovery barrier fences and cannot be bypassed by another barrier.
(defconst *sf-recovery-failed*
  (fn-sf-recovery-barrier *sf-recovered-2* :uncertain))
(assert-event (fn-sf-fencedp *sf-recovery-failed*))
(assert-event (equal (fn-sf-recovery-barrier *sf-recovery-failed* :ok)
                     *sf-recovery-failed*))
