# Review 1 of FAILURE-SCOPE's declaration sketch (def-section / def-actor), codex-liaison-11, 2026-10-03

## What I reviewed, and against what
The sketch itself is not on disk: no failure-scope*.md under build/coordinator/lanedumps/, and the agent was not
reachable by name. So I reviewed the coordinator's summary of it:
- `(def-section NAME :actor :class :admits :live|:cleanup :effects :failure ((:indeterminate :fence) (:fault :fault)
  (:refusal :pass) (:other :fault)))`;
- `(def-actor NAME :loop :register (:roster SLOT :receipt t) :admit (:inbox LOCK :or-close) :stop (:join :settle)
  :failure ... :end-connection LABEL)`;
- the ACL2 functions fn-fs-classify, fn-ort-stop-exit-escalate, the actor lifecycle machine and the admission word, and
  a thin host envelope.

I checked it against the host as it stands: origin/dev 4aa332295 plus t43 (lane/codex-close-fence d52815d5d). Re-check
these points against the real sketch when it is written down.

## Verdict
The design is right: one family; ACL2 decides; the host only orders handler clauses and installs the fence under the
mutex. Fix the four must-fixes before generating any code. Two of them (M1, M2) are fail-open holes in "the host's
typecase names the class, ACL2 decides".

## Must-fix

M1. The host typecase is fail-OPEN today, and the sketch's `(:refusal :pass)` inherits it.
- The classifier `fnn-exit-code-for` (host/native/io.lisp:145-158) is an ordered typecase:
  - fnn-store-indeterminate -> :indeterminate;
  - fnn-store-fault -> :fault;
  - fnn-usage-error -> :usage;
  - fnn-store-error -> :refusal;
  - t -> :fault.
- fnn-store-error is the PARENT of all of them (io.lisp:74-106). So ANY condition raised as plain fnn-store-error, or as
  a future subclass of it that is not explicitly listed, is classified :refusal, which the sketch maps to :pass (log
  and continue).
- A new store-layer failure class written as `(define-condition fnn-x (fnn-store-error) ())` therefore passes silently
  through every section. That is exactly the "swallow and keep serving" class t43/t45 remove.
- Fix: make :refusal a CLOSED, enumerated set in ACL2. The host names the concrete class symbol (`(type-of condition)`
  plus its class-precedence list); fn-fs-classify answers :refusal only for symbols in a declared refusal table
  (fnn-store-io-refusal, fnn-store-open-refusal, fnn-store-profile-refusal, fnn-usage-error, and the others each
  justified), and :fault for every unknown class.
- Teeth: an unknown fnn-store-error subclass classifies :fault.

M2. fnn-os-error is NOT an fnn-store-error (io.lisp:124: `(define-condition fnn-os-error (error) ...)`). A raw OS error
reaching a section is classified :fault (exit 4), even when it follows a durable effect whose outcome is now unknown.
- Instance: r72 F6. In fnn-node-secret-rotate, an fsync-dir EIO after the rename escapes raw, gives exit 4, and should
  be 3.
- So "the host names the observed class" is insufficient: the class does not say WHERE in the effect sequence the error
  happened.
- Fix: the section declares its effect sequence (:effects). The envelope records the last completed effect step (a
  step counter written before each primitive). fn-fs-classify takes (class, step), and an os-error after the first
  durable effect of the section is :indeterminate.
- This is the def-entry/def-holder ":durable PROGRAM" cut list. Reuse it: the classification point is "after which
  cut".

M3. Exits that escape every handler-case scope.
- (a) NON-LOCAL EXITS that are not conditions. THROW/CATCH and RETURN-FROM across the envelope skip handler-case
  clauses entirely. The cold path does exactly this: extent.lisp:830-843 `(throw 'fnn-extent-cold ...)` unwinds through
  owner sections. Thread termination or interruption (sb-thread:terminate-thread, interrupt-thread with a non-local exit,
  SIGTERM handlers) unwinds without signalling a condition.
  Fix: the envelope is an unwind-protect whose cleanup knows whether the body COMPLETED (a flag set as the body's last
  act). An incomplete body with no classified condition is classified by ACL2 as :other, which faults, UNLESS it is a
  DECLARED non-local exit of that section (the cold throw: `:exits (fnn-extent-cold)`, admitted only before the
  section's first durable effect).
- (b) A NON-SERIOUS condition is not a problem by itself: signal without a handler returns. But a handler-bind elsewhere
  that does a non-local transfer on a warning reduces to (a).
- (c) An error INSIDE THE FENCE INSTALLATION. The fence must be a step that cannot fail: set STOPPING and the exit code,
  no I/O, no allocation proportional to data, no logging. t43 reports fnn-owner-stop-service-locked already sets
  STOPPING and the first exit before fallible drain; logging (fnn-err) must come AFTER. The generated envelope must
  order it that way, and the book should state the fence step as a pure state update with no effect labels.
- (d) An error in CLEANUP AFTER THE FENCE, including a second indeterminate during shutdown settlement. It must
  ESCALATE the exit (Q2) and be recorded. It must never be swallowed by the cleanup's own handler-case: today's shutdown
  path wraps close hooks in handlers (owner.lisp ~6250-6285).

M4. The cleanup admission set (Q1) contains one item t43 deliberately forbids.
- Q1 lists "pending-extent release" as admitted after a fence. But t43 made fnn-owner-release-pending-extents-locked
  RETURN 0 WHEN STOPPING: "a stopped owner never retries an ambiguous fd" (owner.lisp, t43 diff). The reason: after an
  ambiguous close, the fd's state is unknown, and closing or retrying could close a REUSED descriptor.
- So pending-extent release must NOT be in the post-fence :cleanup set, or must be admitted only for groups whose close
  has not been attempted. Physical fd release after a fence is left to process exit. The rest of the set:
  - fault-service: admit; it is idempotent and only escalates.
  - orcp-finish / orc-finish: admit only if they touch no durable state. The reclaim finish unlinks the stage file
    (owner.lisp:5794-5798: `(ignore-errors (fnn-unlink stage))`). An unlink after a fence is a durable effect and must
    not be swallowed by ignore-errors: either refuse it after a fence and leave the stage for recovery's sweep, or
    classify it.
  - publication-done refused: right.
  - MISSING from the set, and should be admitted: unpins (response pin release by the mux, arena unpin), cold-worker
    join, committer join, journal/FNFD close observation (the shutdown sequence at owner.lisp:6230-6285). Without them
    the post-fence shutdown cannot settle and the receipt (Q3) never arrives.

## Should-fix / answers to the three questions

Q2, escalation 3 > 4 > first-wins:
- RIGHT as the EXIT CODE.
- The spec states fence dominance explicitly for BP run classes. specs/host.md:282-288: "A fence dominates everything";
  `fn-bprc-fence-is-never-masked`. The owner should get the same theorem (fn-ort-stop-exit-escalate's analogue of
  fn-bprc-fence-is-never-masked).
- 3 over 4 is right for operators: exit 3 means durable state is uncertain and RECOVER is required. A later fault does
  not remove that obligation, and a 4 alone would let an operator restart without recovering.
- BUT: (a) do not lose the dominated evidence. Record every terminal outcome, at least the first fault's condition, on
  stderr and in the status record, so a 4-class bug masked by a 3 is still reported.
- (b) Fix the specific S015 path. The graceful SIGTERM stop calls `(fnn-owner-stop-service service +fnn-exit-ok+)`
  (owner.lisp ~6218) BEFORE drain completes, so 0 is "first". Escalation must treat 0 as the bottom. Make it a lattice,
  ok < refusal/usage < fault < uncertain, rather than first-wins at equal or lower severity, and prove monotonicity:
  once 3, always 3.
- (c) Name what "first-wins" still decides: only between two outcomes of the same class (for example which fault's text
  is primary). Exit codes never go down.

Q3, receipt = the owner's join observation, never thread self-deregistration: RIGHT.
- This is r71 F10 / S018 (publisher deregisters, then keeps working) and r71 F12 (a NIL roster entry breaks join).
- Make the roster entry a thread OBJECT, written only by the spawner after spawn succeeds (never NIL). Only the joiner
  removes it, after sb-thread:join-thread returns.
- The receipt carries the thread's TERMINAL OUTCOME: join-thread on a thread that died by an unhandled condition or by
  terminate-thread returns the default or signals join-thread-error. An actor that died without classifying (M3a) is
  detected at join and classified :other, which is a fault, by ACL2.
- Teeth: an actor that exits via an unclassified non-local exit yields a fault receipt.

S1. def-actor's `:admit (:inbox LOCK :or-close)` is exactly r71 F9: mux adopt pushes into a loop's inbox after its final
drain. The admission word must be decided under the loop's inbox lock against a loop-local CLOSED bit, which the loop
sets under the same lock before its final drain, and the losing adopter closes the socket itself. Make that the
generated protocol and give it a model label so the host-model book (HM) can state "no inbox entry after close"; HM
review M3 asks for exactly this kind of checked realization.

S2. Generated ACL2 vs envelope boundary (host-into-ACL2 decision). The envelope should contain ONLY:
- the mutex primitive;
- handler-case/unwind-protect ordering;
- the completed-flag and step counter writes;
- the call of the generated ACL2 decision functions (fn-fs-classify, the escalation, the admission word) via the
  guard-t direct call, as fnn-exit-code-for already does, because fnn-core can itself fail inside a handler.
Everything else (which cleanup is admitted, what the exit becomes, what the receipt means) must be ACL2 with theorems.

S3. LOCK-CHECK coordination. A section declared :effects with a blocking primitive under :owner is exactly OWNER-OFFLOCK's
domain. Ensure def-section's :effects vocabulary and LOCK-CHECK's R2 ("no I/O in a section") are one declaration, not
two.

## Notes
- The t45 hand fix lands first on lane/codex-fence-boundary (base d52815d5d). Its handler inventory (t43 handlers.md,
  copied into build/lanes/codex-t45-fence-boundary/build/codex/t45/t43-handlers.md) is the test corpus for M1-M3. Every
  SWALLOWS-UNCERTAIN row should become a def-section whose generated classification provably fences.
- No ember question here: the spec already says a fence dominates.
