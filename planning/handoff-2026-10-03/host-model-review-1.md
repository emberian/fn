# Review 1 of the host-model plan (lanedumps/host-model.md), codex-liaison-11, 2026-10-03

Reviewed by me, not by Codex (usage limit) and not by a spawned agent (the session's agent limit). Source coordinate
origin/dev 4aa332295. Every file:line below was read. The plan is a sketch: nothing is built yet, so "the theorem" means
the statement as the plan writes it.

## Verdict
BUILD WITH THE MUST-FIXES BELOW.
- Theorem T1(b).1 (no unsettled read's incarnation is closed, over every schedule) is a real, non-vacuous invariant theorem
  and worth building first.
- Four of the seven theorems as written are definitional or near it. They are not keystones and must be named that way.
- The model has NO label for three real host preads, so the r31 F1 class is covered only for the issued-row path.
- Section 3's claim about P10's cuts is wrong in both directions.
- Section 2's "cannot be proved" is right in general, but a cheap special case is available.

## Must-fix

M1. Reads the model omits (question 1).
- The model's only read is :issue then :io-begin, which requires a row. Three host preads have no row:
  - fnn-extent-window-run (extent.lisp:276-290). It looks up the fd under the extent lock, then reads OFF the lock, with
    a page-ledger window lease as its only protection (fnn-extent-close's close-preview checks :read-file-held).
  - fn-pgs-fill-realize (extent.lisp:1145). It reads off the lock with no row and no lease; the plan names this one.
  - Checkpoint discovery fnn-extent-entry-fresh (extent.lisp:850-870). It reads UNDER the extent lock with a discovery
    lease.
- So theorem (2), "a request in flight reads its own incarnation", is silent on exactly the reads that look like r31 F1:
  the window run is an off-lock read whose safety rests on a lease the model does not have.
- Fix: add P/C labels for the lease-protected read, :window-acquire / :io-begin / :window-release, with :close also
  refused while a page-file lease names the incarnation (the host's close-preview :read-file-held). Then state theorem
  (1) over rows OR leases.
- Name fn-pgs-fill-realize in the book as an OPEN rowless reader, as the plan does, AND as a LOCK-CHECK R3 baseline
  entry, so the gap is counted rather than only prose.

M2. Definitional theorems are not keystones (AGENTS.md "Cite keystones").
- fn-hmc-close-is-refused-while-a-read-names-the-file is :close's own precondition. It holds because the step function
  was written to refuse. Name it -by-definition and cite T1(b).1 instead.
- fn-hmc-crash-forgets-every-request is the definition of :crash. Name it -by-definition. The real crash statement is
  T1(c), which v1 does not cover.
- fn-hmc-a-held-response-refuses-the-swap is NOT purely definitional: it needs the funded-owners conjunct of
  fn-hmc-invp, plus the pass holding its own pin. Keep it, but state that dependence in the theorem. The host twin is
  owner.lisp:5745-5748, which passes (1- (fnn-arena-reader-count)) and is correct only if the pass pinned first.
- fn-hmc-settle-publishes-only-its-own-token-once and fn-hmc-release-postdates-every-live-pin are lifts of existing
  keystones. They are fine as keystones, but only if the invariant (token uniqueness, arpn okp) does real work. The
  teeth must show a non-invariant state where they fail: a labelled corrupted-state witness.

M3. The realization is "stated, never a theorem", so the model catches only half of r31 F1 (question 4).
- The half it catches: :cancel calls the real fn-pio-cancel, and :close calls the real fn-pio-file-clear-p. A
  regression in those ACL2 functions (cancel settling the row, clear-p ignoring cancelled rows) breaks T1(b).1 at
  certification. The teeth schedule exercises that, which is good.
- The half it does not catch: r31 F1's actual host defect was a pread issued with NO row. Before the
  cold-read-ownership fix, the issue happened outside the owner mutex and without fn-pio-direct-admit. That is a host
  call site not matching the C-label, and the model cannot see it.
- Two more host-side regressions it cannot see: fnn-extent-close skipping fn-pio-file-clear-p, and the pending helper
  closing without fnn-arena-clear-p.
- Fix: give each C-label's realization a CHECKED row, not prose. Either LOCK-CHECK's R3/R1 rules name these exact call
  sites (the function, the locks held, the ACL2 function it must call before the primitive), or
  native_program_check-style source assertions compare each listed host function against the label table. The plan
  should say which, and the realization table should be a generated data file both read.

M4. P10's cut claim is wrong (question 6).
- The plan says fn-lg-open-program's "cuts are tests/campaign/native_cuts.py RECOVERY_CUTS". They are not the same set.
- fn-lg-open-program (books/store-log-route-programs.lisp:45-57) has 6 cut occurrences: log-truncated, log-recovered,
  recover-replayed, and recover-barrier x3.
- RECOVERY_CUTS (native_cuts.py:53-60) has 5 rows:
  - recover-replayed and recover-barrier 1-3, which ARE in the open program;
  - recovery-stage-unlinked, which belongs to fn-bs-recover-stage-cleanup-program, not the open program.
  log-truncated and log-recovered are LOG_CUTS rows.
- So "keeps the relation at every cut of fn-lg-open-program" must be cross-checked against LOG_CUTS' two recover rows
  plus RECOVERY_CUTS minus stage-unlinked. The stage cleanup needs its own theorem or an explicit exclusion.
- Missing from the open program entirely: fnn-log-complete-rotation (io.lisp:7236-7253). It runs BEFORE the open program
  on writable open: preallocate, fsync-file, fsync-dir. It has no cut and no model step, so a process death there is not
  a model crash point (AGENTS.md: "Every process-death cut is a model crash point").
- On #-linux that step also zero-fills over a misaligned committed segment (r72 F1, routed to SWEEP-STORE). P10's
  "every cut" claim is false for the host open until that step is either modelled or proved unreachable for committed
  segments.

## Should-fix

S1. C-label fidelity (question 2), checked call by call:
- :issue (owner+extent): MATCHES the direct route. fnn-extent-issue-direct holds the extent lock and its docstring says
  the owner is held (extent.lisp:988-1013), called from fnn-owner-cold-issue-locked (owner.lisp:4212-4225).
  BUT there is a SECOND issue route the model omits. When the pool is funded, the call goes to fnn-extent-issue-read
  (extent.lisp:890-910), which uses fn-owner-page-read-admit / fn-pio-own-admitted-token, a different ACL2 function. Its
  completion is fnn-extent-complete-read (:922), not fn-pio-direct-settle.
  Either model the funded route as its own labels, or prove it unreachable on the served build and say where
  fnn-extent-pool-funded-p is false (extent.lisp:230; owner.lisp:4219 branches on it).
- :io-begin binding time is wrong. The model has the ISSUING actor do :io-begin right after :issue, recording the
  incarnation bound "now". The host worker looks the fd up by FILE id under the extent lock when it RUNS
  (extent.lisp:942-944), possibly after a :cancel.
  The theorem still holds, because close stays refused while the row is unsettled. But the model should place
  :io-begin on the worker tid, enabled any time after :issue (including after :cancel), so the interleaving it proves
  over is the host's.
- :close (owner+extent+pins atomic): the host does NOT hold a pins lock across the close.
  - fnn-owner-release-pending-extents-locked tests fnn-arena-clear-p, then calls fnn-extent-close, which takes only the
    extent lock and rechecks fn-pio-file-clear-p (owner.lisp:4849-4859; extent.lisp:1225-1232).
  - This is sound only because new pins are taken under the owner mutex, which the closer holds. The reader pins and
    the response capture (owner.lisp:4549, inside handle-chunk) are taken that way; unpins off the owner only make
    clear-p more true.
  - Model the host's actual lock set (owner+extent), and make "every :pin/:capture runs under :owner" a stated
    realization obligation checked by LOCK-CHECK. Otherwise the model proves a stronger locking than the host has.
- :swap: host admission is fn-orcp-swap-word with readers = (1- (fnn-arena-reader-count)) under the owner gate
  (owner.lisp:5745-5748). That matches the model's "count <= 1 with the pass's own pin", provided the pass always
  pinned first (owner.lisp:5661). State it.
- :settle (owner+extent): matches (owner.lisp:4276-4282 takes the extent lock; the docstring at extent.lisp:1016 says
  both are held).

S2. P-label oracle generality (question 3).
- Covered: :io-complete "any time, any order, duplicated, after a cancel, after a crash" is the right generality. VERDICT
  must range over every host verdict:
  - :ok;
  - short read (got < elen);
  - :error/EIO;
  - EINTR, if the host retries it: show where;
  - the trailer-mismatch fault.
  The plan does not list them; the teeth should include a short read and an EIO completion.
- Missing: OS fd reuse is modelled only between extent incarnations. A FOREIGN close of an fd number that an extent
  incarnation still holds is not modelled at all: a double close in another subsystem, or the log fd swap's
  ignore-errors close (io.lisp:1119), would let the OS hand that number to a socket while the extent tables still bind
  it. Either add a P-label (:foreign-close FD) as an environment fault, under which theorem (2) must be weakened or
  guarded, or make "host code closes only fds it owns" a named A-PRIM-FD assumption plus a LOCK-CHECK rule.
- Missing: :crash clears FDS and CLOSED, but the host's state after a crash is a new process. Name the process
  boundary: crash ends the model run, and recovery is T1(c). Do not let schedules continue after :crash with a
  surviving device that delivers completions; that is a model artifact, made harmless only by the :stale answer.

S3. Section 2's "the bridge carried => static CANNOT be proved" (question 5): CONFIRMED in general, with a cheap special
case.
- fn-own-conn-okp (books/owner-invariants-relation.lisp:130-145) replays the prefix with the CURRENT groups and capacity
  (fn-own-prefix-archive groups capacity records version frontier).
- fn-ocl-conn-historyp (books/config-owner-live-complete.lisp:145-165) replays the PINNED config history (fn-cpr-replay
  config-prefix event-prefix, fn-cst-replay-node).
- After a reconfiguration that changes groups or capacity between the pin's generation and now, the two replays can
  differ. For example, a capacity cut re-refuses an article the historical replay admitted. So the static relation is
  false of a correct carried state, and no bridge exists in general. RESTATE is right.
- But the bridge DOES hold when the connection's pinned generation equals the current one (no reconfiguration since the
  pin), which is the common case. Prove that special case too:
  (implies (and (fn-ocl-conn-historyp oc conn) (equal generation (len configs))) (fn-own-conn-okp ...)).
  The existing static keystones then still cite something true on most of the served path, and the restatement is
  needed only for the reconfigured case. Cheap, and it keeps M6/P8's old citations meaningful during migration.

S4. Theorem (1)'s statement uses (nth 2 r) and (nth 6 r). Use fn-pio-row accessors (fn-pio-rowp field functions), so a
row-shape change cannot silently retarget the theorem.

## Notes
- N1. "A schedule is any list of labels from any actors; a refused label is a no-op." Good, and not a vacuity source here,
  with one exception: no theorem should hold only because the model REFUSES something the host DOES (refusal-by-model
  vacuity). Audit:
  - :issue refused unless INC is bound and not closed. The host faults in the same case (extent.lisp:1000-1002), so
    this is fidelity, not vacuity.
  - :close refused unless clear-p. The host does the same (1230). OK.
  - :settle refused without :return. The host settles only an observed-returned worker (extent.lisp:1016 docstring).
    OK, but :cancel then :settle before :return must be a refused label whose host twin is the deadline path that does
    NOT settle (owner.lisp:4366-4392 cold-await); check that it does not call settle.
- N2. The host-into-ACL2 decision (2026-10-03) makes the C-layer the code that will RUN. When FAILURE-SCOPE generates the
  :owner section wrapper, :issue/:settle/:close should be generated from these labels. Design the label table so
  FAILURE-SCOPE and TCB-SHRINK can consume it, so that realization becomes construction.
- N3. Effort (1-2 weeks, 800-1,200 lines) looks right for v1 with M1's lease labels; add about 2 days for the funded
  route (S1) if it is reachable.
