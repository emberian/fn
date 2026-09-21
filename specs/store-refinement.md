# Immutable-file store refinement contract

Status: executable file publication/allocator and live-node composition, with
conditional proofs and real adapter fault tests. The [file trace book](../books/store-files-traces.lisp)
extends step/crash preservation to arbitrary finite histories and retains prior
acknowledged records under its stated premises. The [live composition](store-node.md)
uses actual node completion and replay; its mixed-trace proof is now separately
certified. The [54-root checkpoint](../tests/evidence/2026-09-18-assurance.md)
records the frozen subset before that last mixed-trace addition. Actual adapter adoption passed the [75-root/67-test batch](../tests/evidence/2026-09-18-composed-store.md);
byte/effect correspondence and platform qualification remain work;
no checkpoint or experimental disk-format change follows from these proofs.
The 2026-09-19 crash-fidelity revision makes every process-death cut of
`tests/store_crash_child.py` a model crash point, states A-DURABILITY as the
hypothesis `fn-sf-crash-imagep` of the reopen theorems in
[`store-observed-traces`](../books/store-observed-traces.lisp) instead of as the crash
constructor, and roots every trace theorem at the host's process entry
`fn-sn-open-observed` as well as at `fn-sn-initial`; see
[store-node.md](store-node.md#observed-physical-image-entry).

## Why the isolated-slot journal is not the adapter model

`books/journal.lisp` is useful evidence for ordering and fail-closed scanning, but
it is not a faithful abstraction of `tools/run_store.py`:

- the journal stages separate object slots, barriers them, then stages and
  barriers a commit marker; the adapter barriers one complete framed transaction
  file and publishes it with a hard link;
- the journal permits independently torn, lost, and reordered volatile slots;
  after the staged file barrier, the adapter needs a namespace choice between no
  final link and a link to the whole immutable inode;
- the journal has a separately durable acknowledgement anchor; the adapter has
  none and cannot check whether an otherwise valid older store omitted a formerly
  acknowledged transaction;
- the adapter also persists a replace-in-place allocation frontier whose values
  may advance across known aborts. It is ordered before preparation and is not a
  journal commit sequence.

Mapping each transaction file to both an object slot and a commit slot would add
states the adapter cannot produce and would omit allocator replacement and
recovery rebarriers. Current journal theorems therefore do not establish adapter
recovery. The smallest extension is a dedicated immutable-file machine; do not
redesign the node, record codec, or `fn-replay`.

## Executable machine and composition

`books/store-files.lisp` is the logical file kernel, free of raw I/O. Its values
are records accepted by `fn-record-p`; byte/frame validation remains a separate
refinement premise.

The current kernel implements the publication/allocator phases below without
storing a live pending node or fixed configuration in its state. It uses the
existing replay functions for semantic admission/recovery, with groups/capacity
as parameters. A matching live core completion remains an explicit observation.
The separate `store-node` composition now carries fixed configuration and an
actual live node, closing that matching-completion premise through executable
node transitions. The [composition contract](store-node.md) describes its phase
relation and general trace proof; host adoption now sends physical observations through that composition.

The machine state contains:

```text
phase            : ready | reserved
                 | frontier-staged | frontier-data-durable | frontier-attempted
                 | record-staged | record-data-durable | aborting
                 | record-attempted | completing | completed
                 | replaying | recovering | fault
                 | fenced-frontier | fenced-record | fenced-recovery
config           : fixed groups, capacity, and bounds
stable-frontier  : next unused acceptance txid
frontier-update  : none | (old, new, staged | attempted | visible)
stable-records   : records in final-name sequence order
record-update    : none | (record, staged | data-durable | attempted | visible)
node             : composed node or diagnostic prefix
next-sequence    : len(stable-records)
successes        : ghost list of externally emitted (sequence . txid) pairs
barriers         : recovery prerequisite flags, cleared by crash
```

`successes` is trace state, not bytes claimed to exist in this adapter. It lets a
conditional crash theorem state what happened before the crash. A later external
freshness anchor would refine it; the current implementation does not. Because
no anchor exists, a reopened process starts with `successes = nil`; the
cross-restart guarantee is therefore stated over records
(`fn-sn-acknowledged-record-survives-observed-reopen`), not over a
reconstructed ghost list. Two phases, `aborting` and `completed`, are
transient: each is the intermediate state of one composed host call
(`fn-sn-known-abort`, `fn-sn-finish`) and is marked unreachable-in-composition
in the kernel book. The kernel has no phase for an uncertain refusal, an
uncertain known abort or a lost core-completion reply, because the host never
reports those results: it fences on its own side and reopens.

The physical crash image contains a configuration candidate, one frontier
candidate, final-name entries, and ignored staging entries. It contains no node,
mode, durability tags, acknowledgement flags, or diagnostic prefix.

### Observable events and transitions

Use explicit result events rather than an event called simply `commit`:

1. `open-exclusive(config)` obtains cooperative ownership and enters recovery.
2. `recover-scan(image)` checks bounded regular non-symlink files, configuration,
   frontier checksum/range, exact contiguous names `0..n-1`, frame integrity,
   exact record decoding, and filename/record sequence equality. Any failure
   returns `fault(reason, last-good-prefix)` and leaves `mode = fault`.
3. `recover-replay(records, frontier)` calls `fn-replay`, then
   `fn-replay-advance-txid`. A replay refusal or a frontier behind replayed
   history is a fault. Its prefix is diagnostic only.
4. `recover-barrier(name, ok | uncertain)` covers, in order, the config file,
   frontier file, transaction directory, store root, and store parent. Only five
   successful results produce `ready`; an error keeps the machine fenced.
5. `reserve-start(f)` is permitted only when ready, idle, and `f` equals both the
   node counter and stable frontier. It stages the checksummed value `f+1`.
6. `reserve-file-barrier(ok | known-fail)` precedes any replacement attempt. A
   known failure discards the staged candidate and changes no durable state.
7. `reserve-replace-attempt(result)` records the result of the replacement
   syscall. The syscall itself is issued before this event, so from
   `frontier-data-durable` onward a crash may already leave the new whole
   value (`fn-sf-frontier-new-visiblep`); every error from this event on is
   uncertain and fences.
8. `reserve-dir-barrier(ok | uncertain)` makes `f+1` the stable frontier only on
   success, and enters `reserved` with a one-use preparation token. Preparation
   is forbidden before this success and without that token.
9. `core-prepare(record | refused)` invokes the existing node. The record must
   have sequence `len(stable-records)`, txid `f`, generation `f`, and fields equal
   to the pending node proposal. Refusal is followed by the existing logical
   frontier advance to `f+1`; it creates no record or obligation. Refusal or
   abort consumes the reservation. Recovery returns ready without restoring it;
   another preparation requires a fresh durable allocator advance.

   The standalone live store wrapper calls `fn-spc-prepare` for this step.
   It retains the exact record, candidate-counter and pending-node binding
   checks but does not replay `append(stable-records, [record])` per prepare.
   `fn-spc-prepare-equals-specification-under-relation` equates it to
   `fn-sn-prepare` under `fn-snt-relation`. Successful `fn-sn-open-observed`
   establishes that relation by authoritative replay; `fn-spc-run` preserves
   it through the modeled prepare, I/O, finish, refusal, known abort, keyring
   and staging-sweep transitions. The relation is not a runtime flag or
   per-command recognizer. Shared-owner adoption remains a separate obligation.

10. `record-write(result)` creates an exclusive staging file. Write/create/file
    barrier failures before a final-name operation are known aborts. After a
    successful file barrier the candidate is `data-durable`.
11. `record-publish-attempt(result)` records the result of the hard-link
    invocation. The link is issued before this event, so from
    `record-data-durable` onward a crash may already leave the exact candidate
    as a final name (`fn-sf-record-present-visiblep`); from the moment the link
    starts, success, error, interruption, and process death are uncertain. An
    error does not become a known abort merely because the final name is absent
    when inspected. A known abort (`fn-sn-known-abort`) is the host's
    classification that no link was issued; it is a host claim under A-HOST,
    not something the kernel can check.
12. `record-dir-barrier(ok | uncertain)` appends the record to stable records on
    success. An error fences and requires recovery. Cleanup of the staging name
    is outside authority and cannot revoke a stable record.
13. `core-complete` is `fn-sn-finish`: a successful transaction directory
    barrier first enters `completing`, which blocks every new mutation
    (`fn-sf-completing-admits-only-matching-completion`); `fn-sn-finish` then
    performs the actual `fn-node-complete` with `:durable` for the exact
    pending txid and generation and the kernel's matching completion and
    acknowledgement in one host call. A rejected or lost reply to that call is
    a host-side fence with the kernel left in `completing`; the only route
    onward is crash and observed recovery, which retains the record. Abort
    resolution is `fn-sn-known-abort` and exists only before publication was
    attempted.
14. `emit-success(sequence, txid)` is allowed only after matching durable core
    completion and appends to the ghost success history. Socket delivery is not
    this event. Loss of the reply does not remove the record.
15. `crash(choice)` clears process state and barriers. Under the namespace
    atomicity hypotheses, a frontier replacement that may have been issued
    (from `frontier-data-durable` on) yields the old whole value or the new
    whole value, and a record link that may have been issued (from
    `record-data-durable` on) yields no final name or the exact data-durable
    file (`fn-sf-unobserved-frontier-replacement-crash-is-old-or-new`,
    `fn-sf-unobserved-record-link-crash-is-absent-or-present`). A completed
    directory barrier, not the crash constructor, removes the old or absent
    choice (`fn-sf-completed-frontier-barrier-removes-old-choice`,
    `fn-sf-completed-record-barrier-removes-absent-choice`). The set of images
    a crash may leave is the predicate `fn-sf-crash-imagep`; `fn-sf-crash` is
    one constructor that realizes every admissible image
    (`fn-sf-crash-realizes-every-admissible-image`). Malformed images are
    separate inputs to detected-fault tests, not normal crash outcomes under
    those hypotheses.

The model should make illegal transitions return the unchanged state plus
`reject`, rather than assume their preconditions. No mutation transition is
enabled in `fenced`, `recovering`, or `fault`.

### Durable order

Allocator and journal sequences are deliberately different:

```text
stable frontier F
    --barrier replacement to F+1-->
prepare txid F
    --known abort--> no record; frontier remains F+1
    --publish/barrier--> record sequence len(R), txid F; frontier remains F+1
```

Thus record sequences are exactly contiguous while record txids are strictly
increasing and may have gaps. Every final record txid is less than the recovered
frontier. A final record can survive publication uncertainty only because its
allocator advance crossed an earlier completed barrier.

Before a final-name publication attempt, an abort is known even if a staging
inode survives: staging is not recovery authority. At or after the attempted
hard link, absence, presence, or a failed directory barrier is uncertain. The
only next operation is recovery. The same rule applies to the allocator from
the attempted `replace` onward.

## Abstraction relation

For a usable physical image `P`, let `records(P)` be final files sorted by their
numeric names after bounded frame and exact codec validation, and let `F(P)` be
the validated allocation frontier. `P` represents logical node `N` exactly when:

1. names and record sequences are `0..len(records(P))-1`;
2. `fn-replay(config.groups, config.capacity, records(P))` returns
   `(:ok N0 len(records(P)))`;
3. `fn-replay-advance-okp(N0, F(P))` holds and advancing produces `N`;
4. every record txid is below `F(P)`, and replay establishes its article,
   complete group allocation, binding, archive pin, evidence, and charge in one
   node transition;
5. all recovery prerequisite barriers have succeeded since the latest crash or
   uncertain result.

Staging files, abandoned allocator candidates, caches, and the diagnostic node
inside a fault result are absent from the abstraction. A replay fault may carry
a valid invariant-preserving prefix for reporting; it does not satisfy the
relation and cannot authorize reads advertised as recovered or any mutation.

## First proof obligations

Implement these as general theorems over lists and natural numbers, not only as
single-record examples:

- **Transition preservation:** every permitted non-crash step preserves the file
  machine recognizer; ready states satisfy node validity, idle/unfenced state,
  `next-sequence = len(stable-records)`, and frontier dominance.
- **Replay abstraction:** successful scan/replay/rebarrier establishes the
  abstraction relation and returns exactly the node computed by existing
  `fn-replay` plus the frontier advance.
- **Known-abort safety:** a failure before either namespace-publication attempt
  cannot add a final record; a refused or aborted preparation may only increase
  the stable allocator frontier.
- **Atomic publication safety:** under the namespace and isolation hypotheses,
  every crash image has either the old record list or that list plus the exact
  candidate record. It never exposes a partial cross-post, pin, or charge.
- **Allocator-before-record:** every recoverable appended record has a txid below
  the recoverable frontier, including every allowed combination of allocator and
  record publication uncertainty.
- **Fence safety:** after any publication-attempt uncertainty or rejected core
  completion, no reserve, prepare, publish, complete, or success event is
  permitted until successful recovery and all rebarriers.
- **Acknowledged-prefix retention:** within one process, every pair in
  `successes` remains a stable record after any finite mixed trace
  (`fn-snrt-acknowledged-history-retained-through-mixed-trace`, hypotheses:
  `fn-snt-relation` of the start state and membership of the pair). Across a
  process death, for every image admissible under `fn-sf-crash-imagep`
  (A-DURABILITY and A-WRITE-ISOLATION as hypothesis), the host's reopen
  `fn-sn-open-observed` succeeds and the pair names a record of the reopened
  state, and it still does after any further mixed trace
  (`fn-sn-acknowledged-record-survives-observed-reopen`,
  `fn-snrt-acknowledged-record-retained-across-observed-reopen`). Neither is a
  recovery check implemented by the adapter, and neither reconstructs the
  acknowledgement list: a reopened process has `successes = nil`.
- **Unacknowledged survival:** recovery may include the exact candidate whose
  success was never emitted; replaying or retrying it preserves duplicate
  behavior and does not allocate a second article or pin.
- **Fault-prefix non-usability:** a fault result is never accepted by the ready
  recognizer even when its diagnostic prefix is a valid node.

These are safety obligations. Progress from fenced to ready requires a later
successful scan, sufficient resources, scheduling, and successful barriers.
Eventual acceptance or delivery additionally needs A-FAIRNESS and is not implied
by any theorem above.

## Assumptions and claim boundary

The refinement theorem must name these platform facts as hypotheses refining
A-DURABILITY, A-WRITE-ISOLATION, and A-HOST:

- a completed file barrier retains the staged bytes; completed directory
  barriers retain the named namespace changes and their required parents;
- frontier replacement is atomic old-or-new, and exclusive hard-link creation is
  atomic absent-or-linked-to-the-same-inode; neither overwrites an existing final
  name;
- linking a file after its completed data barrier cannot expose different or
  partial bytes, and later staging writes cannot damage stable files;
- one cooperating writer owns the stable lock, syscall results are associated
  with the correct operation, and no out-of-band actor mutates the store;
- stable data needed by earlier completed barriers remains retained across the
  modeled crash. Media corruption and whole-device loss are separate models.

These facts are the predicate `fn-sf-crash-imagep` in `books/store-files.lisp`:
an observed image is admissible for a kernel state when its frontier is the
stable value or, only while a replacement may have been issued, the candidate,
and its records are the stable list or, only while a link may have been issued,
that list plus the exact data-durable candidate. The reopen theorems in
`books/store-observed-traces.lisp` take that predicate as their premise. What remains
physical and is assumed by name: a torn write inside a staged file that a
completed `fsync` nevertheless reported durable (A-DURABILITY); a replacement
or link that is neither wholly old nor wholly new (A-WRITE-ISOLATION); a
directory barrier that returned without retaining the namespace change; the
drive cache behind `fsync(2)` on APFS (review D12); and whole-store rollback to
an older valid image, which no theorem here detects. The Python known-abort and
refusal classifications are host claims under A-HOST.

The frame checksum supplies only the predicate that damaged bytes in the stated
fault class are rejected. Do not assume SHA-256 is injective, that it authenticates
an attacker-controlled file, or that the experimental content label proves a
portable identity. Codec exactness and node replay remain separate obligations.

The present adapter has no independent acknowledgement or freshness anchor.
Consequently it cannot diagnose replacement by an older wholly valid config,
frontier, and transaction prefix. A future rollback claim needs an anchor outside
the store's rollback domain, binding a store identity, monotone generation or
frontier, acknowledged sequence, and a commitment to the acknowledged prefix.
Until then, acknowledged-history retention is conditional on the platform
retaining completed barriers; arbitrary-image recovery can claim validity and
replay consistency, not freshness.

## Existing and missing adapter traces

Current tests cover normal reopen, two-group atomic replay, duplicate/conflict,
known prepublication abort with a consumed txid, post-link uncertainty that
survives recovery, link `EIO` with no visible final name and fencing, allocator
replace error, frontier ahead/behind history, failed recovery barrier followed by
rebarrier, incomplete initialization recovery, staging orphans, bounds, sequence
gaps, truncation/checksum/schema faults, symlinks, and writer-lock contention.
An allocator directory-barrier failure after a successful replacement is also
covered: recovery through the same Store object reloads the observed on-disk
frontier, so the recovered core does not use its cached pre-error value.
An injected transaction-read I/O error also leaves the recovery gate closed
until a later complete scan/replay/rebarrier succeeds on the same object.
The completion-gate regression also covers rejection, a failed reply before core
completion, and a lost reply after actual core completion: each leaves the host
fenced and emits no success, while reopening retains the published article/pin.

### Native existing-store recovery (W15)

The native adapter's `fnn-acquire` checks the root, transaction, and staging
directories before taking its lock.  A missing `staging/` directory is therefore
a storage fault, rather than an empty staging observation.  After `fnn-recover`
has replayed the durable configuration and transactions and completed its five
existing recovery barriers, writable recovery supplies a bounded observation of
the staging namespace to ACL2 `fn-sn-sweep-staging`, through
`fn-store-sn-sweep-staging-list`.  It unlinks only names returned by that ACL2
subject; observed names outside the `.stage-` policy remain reported.  A
read-only open reports the bounded observation but does not mutate it.  More
than the ACL2-supplied limit of 64 entries faults before a larger host list is
built, so recovery does not turn an unbounded directory into a logical input.

The recovery cleanup is nonauthoritative: it does not alter the replayed
configuration, transaction history, or frontier.  Runtime evidence exercises a
selected process-death cut after one successful unlink and a separate injected
post-unlink error; each requires a new process to observe the remaining
namespace.  These tests establish the named adapter/model boundary and selected
restart behavior, not a claim about arbitrary filesystem races, power loss, or
every existing/retry opening path.

### Native immutable-initializer retry (W18)

Native `store init` distinguishes an immutable `link(2)` result of `EEXIST`
from another link error. The former retains and decodes the existing final
metadata file, then removes the newly staged candidate; the latter is
uncertain because the host cannot know whether the namespace operation was
issued. `fn-bsi-existing-init-program` models the valid existing-file branch
with an executable `:link-eexist` transition that continues only when
`fn-bs-link` actually returns `:eexist`. `fn-bsi-history-retry-program` models
the selected restart where configuration history was fenced and the frontier
is still absent. An external history entry appearing after an empty enumeration
remains uncertain. The runtime tests cover those branches and a held
writer-lock refusal; they do not qualify arbitrary existing layouts or
link-error platform behavior.

The [fault matrix](store-fault-matrix.md) covers before/after-effect
filesystem/completion rows, including partial/zero writes and all recovery
barriers, and tabulates the six process-death cuts against their model crash
points. The [bounded explorer](store-exploration.md) exhausts the two-record,
frontier-2 domain with a txid-gap record and reports states, applications and
state-changing transitions as distinct counts; the crash choices in the
data-durable phases and the recovery barrier counts are asserted covered.
The [corruption matrix](store-corruption-matrix.md)
adds malformed frontier/frame/namespace cases and multiple prior commits plus
an uncertain tail. Its independent targeted result is subsequent to the frozen
54-root checkpoint. Physical power-loss outcomes, freshness and all possible
host/namespace interleavings are not established by these finite tests.

For a rejected or lost durable completion, the adapter must close its mutation
gate before calling the core and clear it only after the exact matching success.
The durable file remains recovery authority; further mutation requires recovery.
