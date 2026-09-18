; Executable crash traces for the immutable-file publication kernel.
(in-package "ACL2")
(include-book "../../books/store-files")

(defconst *sf-groups* '("fn.letters" "fn.test"))
(defconst *sf-record-0*
  (fn-record-make 0 0 0 "<zero@example.invalid>" '(90)
                  '("fn.letters" "fn.test")
                  "archive-zero" "content-zero" "release-zero" 2))

(defconst *sf-s0* (fn-sf-initial-state))
(assert-event (fn-sf-statep *sf-s0*))

; Before the allocator replace attempt, even :new is not an allowed crash
; observation.  After the attempt but before its directory barrier, old and new
; whole frontiers are both possible.
(defconst *sf-fa0* (fn-sf-start-frontier *sf-s0*))
(defconst *sf-fa1* (fn-sf-frontier-file-result *sf-fa0* :ok))
(assert-event (equal (fn-sf-frontier
                      (fn-sf-crash *sf-fa1* :new :absent)) 0))
(defconst *sf-fa2* (fn-sf-frontier-replace-result *sf-fa1* :ok))
(assert-event (equal (fn-sf-frontier
                      (fn-sf-crash *sf-fa2* :old :absent)) 0))
(assert-event (equal (fn-sf-frontier
                      (fn-sf-crash *sf-fa2* :new :absent)) 1))

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

; A completed allocator directory barrier removes the old choice.
(defconst *sf-f1* (fn-sf-frontier-dir-result *sf-fa2* :ok))
(assert-event (equal (fn-sf-frontier
                      (fn-sf-crash *sf-f1* :old :absent)) 1))
(assert-event (fn-sf-statep *sf-f1*))
(assert-event (equal (fn-sf-phase *sf-f1*) :reserved))

; Invalid refusal input is a no-op.  A real semantic refusal consumes the one
; durable reservation and cannot be mistaken for permission to reuse txid 0.
(assert-event (equal (fn-sf-refuse-reservation *sf-f1* 0 :invalid) *sf-f1*))
(defconst *sf-refused* (fn-sf-refuse-reservation *sf-f1* 0 :refused))
(assert-event (equal (fn-sf-phase *sf-refused*) :ready))
(assert-event (equal (fn-sf-prepare-record *sf-refused* *sf-record-0*
                                           *sf-groups* 10)
                     *sf-refused*))

; Replay admits the core-produced record.  A known abort before the hard-link
; attempt leaves no final record and keeps the consumed frontier.
(defconst *sf-r0*
  (fn-sf-prepare-record *sf-f1* *sf-record-0* *sf-groups* 10))
(assert-event (equal (fn-sf-phase *sf-r0*) :record-staged))
(defconst *sf-rdata* (fn-sf-record-file-result *sf-r0* :ok))
(defconst *sf-aborting* (fn-sf-prepublish-abort *sf-rdata*))
(defconst *sf-aborted* (fn-sf-abort-completion *sf-aborting* 0 0 :matching))
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
                  "archive-one" "content-one" "release-one" 1))
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

; Once the hard link is attempted, a crash can observe absence or the exact
; candidate record.  The observed durable frontier remains the already-barriered
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

; A completed transaction-directory barrier preserves the record for every
; later crash choice, but success remains impossible before matching core
; completion.
(defconst *sf-published* (fn-sf-record-dir-result *sf-linked* :ok))
(assert-event (equal (fn-sf-phase *sf-published*) :completing))
(assert-event (equal (fn-sf-emit-success *sf-published* 0 0) *sf-published*))
(assert-event (equal (fn-sf-records
                      (fn-sf-crash *sf-published* :old :absent))
                     (list *sf-record-0*)))

; A lost core-completion reply closes the mutation gate.  Crash/replay, not a
; cached core or allocator value, is the only route back toward ready.
(defconst *sf-core-lost* (fn-sf-core-completion *sf-published* 0 0 :lost))
(assert-event (fn-sf-fencedp *sf-core-lost*))
(assert-event (equal (fn-sf-start-frontier *sf-core-lost*) *sf-core-lost*))
(assert-event (equal (fn-sf-emit-success *sf-core-lost* 0 0) *sf-core-lost*))

; Matching completion opens the acknowledgement decision.  Losing the network
; success leaves the exact durable record and permits a later duplicate retry at
; the existing replay layer; it does not create another file here.
(defconst *sf-core-ok* (fn-sf-core-completion *sf-published* 0 0 :matching))
(assert-event (equal (fn-sf-phase *sf-core-ok*) :completed))
(defconst *sf-reply-lost* (fn-sf-lose-success *sf-core-ok* 0 0))
(assert-event (equal (fn-sf-phase *sf-reply-lost*) :ready))
(assert-event (equal (fn-sf-records *sf-reply-lost*)
                     (list *sf-record-0*)))

; Recovery performs actual fn-replay and remains unavailable until all five
; prerequisite barriers succeed.
(defconst *sf-recovered-0*
  (fn-sf-recover (fn-sf-crash *sf-core-lost* :old :absent)
                 *sf-groups* 10))
(assert-event (equal (fn-sf-phase *sf-recovered-0*) :recovering))
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
