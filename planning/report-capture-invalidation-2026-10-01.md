# Bounded full-report capture without a catalog revision

Architectural handoff; source design only. No proof, image, or deployment claim.
This selects an additive owner-boundary scheme, not a change to the Cat stobj.

## Decision

Keep exactly one registered report preparation job in ACL2 STATE. Its captured
status is sticky: a report-relevant mutable-source write invalidates that job
before writing. No count, horizon, canonical epoch, host counter, or synthetic
transaction version stands in for this invalidation.

At BEGIN, under the existing owner serialization, retain the original immutable
OC, reader-view value, configuration, pins, Store/profile, record-octet carry,
exposure/limit values, scheduler/log values, request and cache values needed by
the existing report. Capture the fixed scalar observations once. Do not render
or traverse their lists at BEGIN. Later folds use these captured values, never
their newly published global replacements. Thus config, pins, reader-view,
profile and bookkeeping changes cannot silently change the report halfway
through. Their pointer captures and lifetime custody are part of the real
charged report operation; they are not an unlimited free retention grant.

Cat and arena remain mutable borrowed dependencies. Before every actual served
mutation/replacement of them, invalidate the registered job. Each bounded report
step tests the actual registered job and source phase before reading either
dependency. No borrowed child or raw pointer escapes a quantum. After a
mutation, the job ends with `:snapshot-changed`; it never resumes on the new Cat.
The completed immutable output buffer is installed only after the final check
in the same serialized turn. Subsequent writes do not invalidate that buffer or
its existing paginated cache. This preserves full report semantics at a captured
input tuple; it does not promise a continuously current report or completion
under unending writer churn. A changed attempt terminates explicitly, without
an unbounded internal retry loop or truncated successful report.

Runtime/OS observations retain their actual sampling coordinate. Retaining an
OBS value does not assert that an earlier external observation occurred at the
exact instant of the owner capture.

## Additive core API and identity

Reader owns a new `books/owner-report-capture.lisp`, with STATE globals for
source phase and the singleton registered job. Source phase is initially
`:unavailable`, then `:stable`, `:mutating`, or `:fault`. Cold successful owner
installation establishes stable only after its real publication/barriers.

* `fn-owner-report-write-begin(state) -> MV(word,state)` enters `:mutating`
  and marks any extant job invalid, retaining its payload and charges for
  cleanup. A nested call cannot acquire an independent right to end the scope.
* `fn-owner-report-write-complete(state) -> state` is internal to the ONE
  outer composed writer's successful completion branch. It restores source
  stability, never the invalidated job's validity. There is no public host
  success Boolean. Inner Cat/delta/install helpers never call this function.
* `fn-owner-report-write-fault(state) -> state` leaves source unavailable for
  a new capture until actual recovery has reestablished it. A raw escape while
  mutating already leaves the source closed; an unwind handler must not
  manufacture successful completion.
* `fn-owner-report-capture-begin(request,cached,capturedInputs,state)` is an
  INTERNAL composed entry after genuine request/BODY/retention admission.
  `capturedInputs` is produced by its actual owner getter in the same turn,
  not a native supplied snapshot. It refuses when source is not stable or any
  earlier job remains registered, including invalid/retiring jobs.
* `fn-owner-report-capture-step(...actual stobjs...,state)` and its cleanup
  fetch the actual registered job. They accept no caller-provided cursor,
  validity flag, snapshot or replacement job. The charged report driver alone
  schedules this continuation; a new incoming request receives busy while the
  job exists. An external resumable handle, if required by the final scheduler,
  must identify the real retained job reservation and its original caller.
  It cannot reuse an old ATS receipt as authority for later BODY work.

Bind original request/kind/cache and caller in the job. Do not use pointer
equality or equal on an entire report graph as a bounded identity test. Clear
the singleton only after the original continuation and temporary aliases have
retired through their actual cleanup. This prevents old-job/new-job confusion
without another monotonically growing number. Fresh steps obtain fresh actual
ATS BODY authority; report job updates and prepayment do not self-invalidate.

## Finite mutation cohort

Inspected actual `build/lanes/batch-be` owner path, not hypothetical exported
Cat helpers. Reader and owner must join the following source cohort together.

1. `host/owner-host.lisp`: `fn-owner-finish-submission-synced` and
   `fn-owner-finish-identity` call `fn-sca-finish`, which withdraws targets and
   commits. Start the outer report-write scope before the first owner/Cat
   publication in that composed completion. End only after successful complete
   publication; a Cat refusal after durable Store acceptance is a recovery
   fault, not stable. Nested owner installers do not end this scope.
2. `books/owner-recovery-retain.lisp`: `fn-owner-install-extended` publishes
   owner globals then calls `fn-sca-load-held-rows-keyed` (clear and commits).
   The actual cold/reset entry closes report capture before replacement begins;
   successful initialization establishes stable only after all barriers. An
   additive outer owner adapter is preferable to changing foundational Cat.
3. `host/native/owner.lisp`: the actual reclaim swap first installs the durable
   checkpoint, calls `fn-owner-orcp-swap`, replaces the live Cat/history stobjs,
   then runs reclaim barriers. Call the core begin BEFORE that durable install,
   and core complete only after replacement and barriers. The existing
   installed-but-not-swapped recovery fence also leaves reports unavailable.
   `fn-owner-orcp-load-columns` builds a FRESH private Cat off mutex; that build
   alone does not invalidate the served report. Its later swap does.
4. Arena lifecycle roots `fn-reader-use-seed`, `fn-xw-replay-begin`,
   `fn-xo-open-store`, and `fn-scka-load` clear arenas. Owner reset/recovery
   exclusion must close capture and invalidate before any served arena clear.
   Standalone offline invocations have no live report job. Arena append is
   permissible only under its existing old-handle preservation relation;
   reclaim/reuse/replacement requires the fence.
5. `books/catalog-delta.lisp` provides `fn-cat-apply-delta[-step]` and
   `fn-cat-recontext[-range]`, reaching withdrawal/redecision without a count
   or horizon change. No actual host/native callers were found in this cut.
   Any activated served caller must use the additive state-aware outer writer
   adapter. A yielded multi-step policy update keeps source mutating until the
   whole semantic update completes; per-row helpers never restore stable.
6. The new dense owner publisher must join the same boundary when its actual
   Cat publication is connected. Its source-only readiness packet is not
   evidence of Cat mutation coverage. Direct future live Cat calls are excluded
   from activation until covered; unchanged lower Cat functions remain usable
   for models and private/offline construction.

`fn-owner-install-ocfg` need not change: captured immutable configuration/pin
and owner values remain the report's inputs. In particular, do not add a new
global effect to this foundational book solely to invalidate reports on every
connection update. Any supposedly immutable retained input that actually
contains mutable backing must instead join the mutation/lifetime cohort above.

## Evidence and implementation boundary

Reader implements singleton capture, fixed input capture, bounded folds/render,
and final cache install. Owner implements the finite outer publication/reset/
swap wrappers and failure branches. Runner integrates their selected cohort.
No helper alone establishes coverage: the refinement subject is the actual
composed report driver under these actual writer entry points and serialization.

Necessary teeth: same-count redecision; two withdrawals at the same count and
horizon; clear/repopulate; reclaim replacement; writer failure after its first
write; nested writer attempts to reopen source early; changed config/pins after
capture still read as the old captured values; own report steps do not invalidate;
overlapping BEGIN refuses; an old continuation cannot operate on a replacement
job; and completed cached pages survive subsequent writes. A positive report
must equal the existing full report over the captured tuple, including every
existing health/status extra. Tests and source qualification remain separate
from a native activation claim.
