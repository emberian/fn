# Immutable-file store refinement contract

Status: refinement design with a first executable publication/allocator kernel
in [store-files.lisp](../books/store-files.lisp). The kernel uses actual
`fn-replay`, explicit crash choices, one-use reservations, completion gating,
and five recovery barriers. General start-frontier preservation and fence/gate
lemmas are proved; full transition/crash/acknowledged-history preservation and
the physical adapter correspondence remain open. It does not qualify a platform,
add checkpoints, or change the experimental disk format.

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

## Proposed executable machine

Add one logical book, provisionally `books/store-files.lisp`. Keep it free of raw
I/O. Its values are records already accepted by `fn-record-p`; byte/frame
validation remains a separate refinement premise.

The current kernel implements the publication/allocator phases below without
storing a live pending node or fixed configuration in its state. It uses the
existing replay functions for semantic admission/recovery, with groups/capacity
as parameters. A matching live core completion remains an explicit observation.
The complete state and correspondence below are therefore further work, not
properties implied by the kernel's initial certification.

The machine state contains:

```text
mode             : ready | reserved | preparing | completing | fenced | recovering | fault
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
freshness anchor would refine it; the current implementation does not.

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
7. `reserve-replace-attempt(result)` records that namespace publication was
   attempted. Every error from or after this event is uncertain and fences.
8. `reserve-dir-barrier(ok | uncertain)` makes `f+1` the stable frontier only on
   success, and enters `reserved` with a one-use preparation token. Preparation
   is forbidden before this success and without that token.
9. `core-prepare(record | refused)` invokes the existing node. The record must
   have sequence `len(stable-records)`, txid `f`, generation `f`, and fields equal
   to the pending node proposal. Refusal is followed by the existing logical
   frontier advance to `f+1`; it creates no record or obligation. Refusal or
   abort consumes the reservation. Recovery returns ready without restoring it;
   another preparation requires a fresh durable allocator advance.
10. `record-write(result)` creates an exclusive staging file. Write/create/file
    barrier failures before a final-name operation are known aborts. After a
    successful file barrier the candidate is `data-durable`.
11. `record-publish-attempt(result)` is the hard-link invocation. From the moment
    it starts, success, error, interruption, and process death are uncertain. An
    error does not become a known abort merely because the final name is absent
    when inspected.
12. `record-dir-barrier(ok | uncertain)` appends the record to stable records on
    success. An error fences and requires recovery. Cleanup of the staging name
    is outside authority and cannot revoke a stable record.
13. `core-complete(durable | aborted | indeterminate)` must match the exact
    pending txid and generation. A successful transaction directory barrier
    first enters `completing`, which blocks every new mutation while the adapter
    supplies `durable` to the core. Only its exact matching success returns to
    ready; a rejected or lost completion reply leaves the adapter fenced.
    `aborted` is allowed only before publication was attempted, and every
    indeterminate result fences.
14. `emit-success(sequence, txid)` is allowed only after matching durable core
    completion and appends to the ghost success history. Socket delivery is not
    this event. Loss of the reply does not remove the record.
15. `crash(choice)` clears process state and barriers. Under the namespace
    atomicity hypotheses, a pending frontier replacement yields the old whole
    value or the new whole value, and a pending record publication yields no
    final name or the exact data-durable file. Completed barriers remove the
    old/absent choice as specified below. Malformed images are separate inputs
    to detected-fault tests, not normal crash outcomes under those hypotheses.

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
- **Acknowledged-prefix retention:** given completed barriers, retained stable
  storage, and the crash constructor's platform hypotheses, every pair in
  `successes` occurs with the same record in recovered history. This is a trace
  safety theorem, not a recovery check implemented by the current adapter.
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
The completion-gate regression also covers rejection, a failed reply before core
completion, and a lost reply after actual core completion: each leaves the host
fenced and emits no success, while reopening retains the published article/pin.

The executable model and its tests still need crash choices at every allocator
and transaction step; transaction directory-barrier failure after a successful link; short
writes and staging-file barrier failures; final-name collision; frontier
truncation/checksum/symlink faults; filename/decoded-sequence mismatch; lost
success followed by duplicate retry; multiple prior commits plus one uncertain
tail; and general trace proofs for the tested completion failures.

For a rejected or lost durable completion, the adapter must close its mutation
gate before calling the core and clear it only after the exact matching success.
The durable file remains recovery authority; further mutation requires recovery.
