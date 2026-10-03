# Review 1 of the TCB-SHRINK plan (decisions/tcb-shrink-2026-10-03.md), codex-liaison-11, 2026-10-03

## Scope
- Reviewed by me against the ACL2 8.7 sources the image is built from (/opt/homebrew/opt/acl2/libexec) and the tree at
  origin/dev 4aa332295.
- I re-ran no lane's test. I ran only two read-only tools to verify claims: tools/host_loaded_check.py, and grep.

## Verdict
SOUND DIRECTION, START WITH THE COMMITTER, but four must-fixes before the first slice lands:
- one missed ACL2 concurrency fact;
- the claim "the code that runs is the code that is proved" needs two more named assumptions;
- the slice's acceptance list misses S014 and r71 F5/S003 and conflicts with OWNER-OFFLOCK on the seal;
- B8 means `make check` is red today.

## 1. The ACL2 8.7 concurrency facts (question 1)

| Plan's claim | Verdict | Evidence |
|---|---|---|
| A state global is the process-wide symbol-value | CONFIRMED | axioms.lisp:15977-15996 put-global: `(setf (symbol-value (global-symbol key)) value)` |
| The extracted core keeps every state global in one synchronized hash table | CONFIRMED | tools/extract/clruntime.lisp:14-24: f-get-global / f-put-global over `*xl-globals*`, `(declare (ignore state))`. Per-thread globals are impossible in the product. |
| One live object per stobj name; with-local-stobj makes a fresh one | CONFIRMED | basis-a.lisp:9711 with-local-stobj -> mv-let-for-with-local-stobj (creator per evaluation) |
| hons and memoize are not thread-safe | CONFIRMED by the plan's quotes; I did not re-read hons-raw.lisp line by line | |
| ACL2(p) is a separate executable; the image is plain ACL2 | CONFIRMED by the launcher name; not re-checked | |

MISSED, must be in the plan's fact list. M1: abstract-stobj export protection uses ONE process-wide unsynchronized cell.
- A defabsstobj export declared `:protect t` expands through with-inside-absstobj-update (other-events.lisp:23993-24015):
  ```lisp
  (let* ((,temp *inside-absstobj-update*) (,saved (svref ,temp 0))) ...
    (setf (svref ,temp 0) 1) (our-multiple-value-prog1 ,form (setf (svref ,temp 0) 0)) ...
    (incf (the fixnum (svref ,temp 0))) ... (decf ...)
  ```
  over `(defg *inside-absstobj-update* ...)` (axioms.lisp:29461), a global with no lock and no per-thread binding.
- fn's arena exports are declared `:protect t` (books/payload-arena-extent.lisp:1369-1376), and 20+ books define
  abstract stobjs. So two actors each running a protected export of their own private abstract stobj race on the same
  cell. Lost incf/decf updates leave it non-zero, which is ACL2's "illegal state" marker.
- our-multiple-value-prog1 is not unwind-protect, so a THROW out of a protected export leaves it elevated permanently.
  The cold-read path throws `fnn-extent-cold` from inside realizer calls.
- The served image never runs LD's chk-absstobj-invariants, so today the consequence is a corrupted diagnostic, not
  wrong answers. But the plan must
  (a) forbid :protect exports in actor stobjs, or bind the cell per thread, as the plan already does for hons spaces;
  (b) state why a stale cell is harmless in the served image;
  (c) never rely on it as a torn-update detector.

Other things that break when several threads run logic-mode code. These are not in the plan; mark each "checked" or
"assumed":
- M1b. Hard errors and guard violations are thrown to a catch tag (raw-ev-fncall / the fnn-call catch). Each actor
  thread's envelope must establish the same catch. Otherwise an `er hard` (5 books use cw / er hard / hard-error) or a
  *1* guard violation in an actor thread falls into ACL2's interface error path. That path prints through fmt, which
  reads state globals and writes *standard-co* (a shared stream; SBCL fd-streams are not thread-safe). Add a native
  case: a hard error inside an actor step yields one classified :fault observation, not a dead thread or a garbled log.
- M1c. A storage-condition (heap exhaustion) or a non-local exit in the middle of an actor step leaves that actor's
  CONCRETE stobj half-updated, because ordinary stobjs have no :protect. The envelope must treat any condition inside
  a step as the actor's death (fault), never re-step the torn stobj. Put it in the failure-scope table
  (failure-scope-review-1 M3).
- *1* counterparts read guard-checking-on through the live state on every call. Fine while it is constant, which
  io.lisp:8606 asserts at startup. Name it as an invariant: nothing in the served image writes it.
- `*aokp*` and defattach are process-wide and set at build. They are fine if no actor step calls a function that
  binds them, which ev / trans-eval would.
- The guard-spec cache is a :synchronized table (io.lisp:1278). Fine.
- The raw-dispatch table *fnn-raw-dispatch* is written only at image build. Name that as the invariant.

## 2. Primitive set and oracle generality for the committer (question 2)
- The set covers the committer: section, commit-lock and condition wait, spawn/join of the syncer, the mailbox, the
  log seal and fence, the clock.
- Gaps carried over from the HM review (host-model-review-1 S2):
  - F pread/pwrite: list EINTR handling as a primitive-internal retry or a returned word. The plan says "the caller
    retries: a decision", but a partial pwrite followed by EINTR on the continuation must be part of the same
    durable-effect step for classification.
  - fd reuse: the F family's A-PRIM-FILE says "a number is reused only after close". It needs the converse too: host
    code closes only fds it owns (the foreign-close case). Otherwise a double close elsewhere invalidates A-PRIM-FILE.
  - cv wait: the plan notes the mutex may not be held on timeout (owner.lisp:3496-3499). The oracle step must return
    that as part of the answer so the actor step re-acquires deliberately.
  - The syncer's answer vocabulary `(:failed :os ERRNO)` must be classified by the failure-scope table as UNCERTAIN
    (the fence's outcome after a failed fsync is unknown: crash-model-v2), never as refusal.
- The feed journal (S014) uses F-family primitives INSIDE the commit-start section (owner.lisp:2964 drain-one ->
  fnn-owner-feed-flush -> write-all + fsync, 897-903). The plan declares only `:io (fn-prim-log-seal)` for that
  section. Either the feed append is declared :io (another declared exception to R2, which OWNER-OFFLOCK is about to
  remove), or the section must not contain it. Decide before the slice.

## 3. "The code that runs is the code that is proved" above the envelope (question 3)
Holds only with these named assumptions or checks:
- (a) Raw dispatch of every actor step and section step. The plan says so. The definterface gap I found today (raw-with
  drops predefined-headed guard conjuncts such as `<`, `equal`, `consp` before fn-cd-uncovered-conjunct;
  definterface.lisp:507-513) must be closed first, or a raw-dispatched step can skip an unproved conjunct.
- (b) The ENVELOPE's ACTION interpreter (the mapping from an ACL2 action word to a primitive call) is ~300 lines of host
  code, unproved. It must be generated from the same ACTION vocabulary table the HM book reads (the plan's acceptance
  4). Make it a table-driven dispatch with no per-action host logic, plus a structure test that each table row maps to
  exactly one primitive.
- (c) SBCL's compilation of guard-verified definitions (A-SBCL-RUNTIME) and the mbe :exec arms. These exist today.
- (d) M1 and M1c above.
- (e) Macro expansion: actor steps written with def-loop or def-carried expansions are certified as expanded. Fine.
  with-local-stobj in the raw envelope is ACL2's raw macro. Fine.

## 4. The committer slice's acceptance items vs this week's defects (question 4)

| Defect | Caught? |
|---|---|
| S016 / B1 (committer swallows faults as stopped) | YES: theorem fn-cmt-a-fault-never-completes plus acceptance 3 (fault injected at fn-otb-issue, exit 4, no later mutation) |
| S015 (stop during barrier leaves wrong exit) | YES: acceptance 3 "a stop during the barrier ... exit 0 only when the stop predicate holds". Also needs failure-scope's monotone exit lattice. |
| S003 / r71 F5 (inline commit of a logical connection under :reader during a batch) | NOT CAUGHT by any acceptance item. The plan says a logical connection "submits to the mailbox" (HOST-LIFECYCLE's fnn-owner-feed-logical), but nothing in the slice tests that the inline path is gone. Add: a web POST during an in-flight batch is queued, never committed inline (the r71 F5 interleaving as a forced schedule). Also delete fnn-owner-commit-queued-locked's inline caller in the same commit. |
| S014 (feed journal fsync under owner, twice per member) | NOT CAUGHT; section 2 above. Add a native: a feed-journal device stall during START does not block a reader quantum. Or declare it out of the slice and say so. |
| r72 F4 (seal append and extension fdatasync under owner) | CONFLICT: the plan declares the seal under the owner as a deliberate exception; OWNER-OFFLOCK is assigned to move it off. Settle which, before the slice starts. |

## 5. Measurements (question 5)
- 92 unloaded files: CONFIRMED. `python3 tools/host_loaded_check.py` lists 92 "no build loads it" files and EXITS 1.
  It is in `make check` (Makefile:2509), so make check is RED on dev at this step today (that is B8). Not a plan error:
  a live red to route.
- The signature classifier (PRIM > COORD > GLUE by precedence, form boundary = a line starting with "(") is an honest
  ESTIMATE and labelled as one. Its 7,433 "none" lines versus about 1,800 real computation lines shows it over-counts.
  Land it as tools/host_signature_census.py only with a stated precision (spot-sample 50 forms against a reading) and
  never cite its counts as the TCB size; the 58k / 6-7k figures should cite host_loaded_check plus wc, not the
  classifier.

## 6. Appendix B (question 6), verified in source
- B1 CONFIRMED: `fnn-owner-admission-pending` is `(define-condition ... (serious-condition))` (owner.lisp:2048), signalled
  at 2058/2062, handled nowhere in host/ or books/. It reaches the shared-action catch-all and exits 4. Route to
  FAILURE-SCOPE (classification table).
- B4 CONFIRMED: fnn-log-parent (io.lisp:6398-6400) differs from fnn-parent (762-768). It does not trim trailing "/", so
  "/a/b/" gives "/a/b" against fnn-parent's "/a". A durable fsync-dir of the wrong directory if a trailing slash ever
  reaches it. Route: SWEEP-STORE (delete the twin).
- B7 PARTLY: tools/extract/world.py does not name lz4.lisp. tools/extract/gate.py:509 does, in a comment:
  "host/native/lz4.lisp ... not a second build", and that file does not exist. Comment-only; nit.
- B8 CONFIRMED as above: make check red at host_loaded_check. Route to the runner (wire, move or retire the 92 files,
  or baseline them by name, shrink-only).
- B2, B3, B5, B6: not verified by me (B5 overlaps r71 F16, which I did verify for fnn-owner-run-admission at 647).

## Must-fix summary
1. Add *inside-absstobj-update* (M1), the per-thread catch / hard-error path (M1b) and torn actor stobjs (M1c) to section
   2.3, with the design rule for each.
2. Close the definterface predefined-head raw-with gap before any actor step is raw-dispatched.
3. Committer acceptance: add the S003/r71 F5 forced schedule and the S014 stall case (or scope them out explicitly).
   Settle the seal-under-owner conflict with OWNER-OFFLOCK.
4. Route B8 (make check red) now.
