# Live node and immutable-file completion

Status: executable logical composition in [`books/store-node.lisp`](../books/store-node.lisp),
with correspondence theorems in
[`books/store-node-invariants.lisp`](../books/store-node-invariants.lisp).
This closes the file kernel's trusted `:matching` reply premise for the new
composition's acknowledgement operation. The experimental host now uses this composition. Proofs of logical transitions
remain conditional on the physical adapter faithfully supplying observations.

## State and submission

A composition state carries fixed configured groups, retention capacity, the
existing `fn-sf` file state, and the actual `fn-node` state. Transitions retain
the configuration; it is not resupplied to each publication or recovery call.
`fn-sn-statep` is the structural invariant: valid configuration, file state,
and node state. It does not assert full history/live-state equivalence for an
arbitrary hand-constructed composition state.

`fn-sn-prepare` operates only with the kernel's durable one-use reservation
and an idle live node. It calls `fn-replay-advance-txid` and the actual
`fn-node-prepare`, then requires the record to equal the record reconstructed
from the resulting pending acceptance and retention stage. This binds:

- transaction ID and generation;
- exact Message-ID, payload, and ordered requested groups;
- archive obligation ID, content subject, release evidence, and charge.

The file kernel additionally binds sequence to the existing history length,
generation to transaction ID, and transaction ID plus one to the durable
allocator frontier. It checks recoverability using the fixed configuration.
Speculative local calculation is discarded if either preparation gate refuses;
no partial node or record is installed. The unchanged reservation must
subsequently be used or abandoned through crash/recovery.

`fn-sn-prepare-installs-bound-candidate` proves the record/node and
sequence/transaction/frontier bindings for every successful preparation.
The existing node invariant establishes that the pending archive pin is true.
No field parsing, membership allocation, retention admission, or acceptance
rule has been duplicated in host code or in this composition.

## Existing article decision

The live duplicate decision is `fn-sn-existing-action` in `books/store-node`.
For a submitted exact Message-ID, payload octets and ordered selected groups,
it looks up the article in the composed Store's live node. It returns
`:duplicate` exactly when a held article has both equal payload and groups,
`:conflict` exactly when the ID is held and either differs, and `nil` when
the ID is missing. The standalone Store and configured owner host prepare
and query wrappers call this function after converting bounded octets and
group codes. The function does not infer a durable acceptance or allocate a
local article number. `books/store-node-existing-invariants.lisp` states the
three exact outcomes; `tests/acl2/store-node-existing-tests.lisp` exercises
them after a reachable commit and flips payload, groups and binding.

## Actual completion and acknowledgement


`fn-sn-io` supplies only file-kernel operations: allocator stages, record stages,
and recovery barriers. An operation named `:core-completion` or `:emit-success`
has no effect. File observations remain environmental inputs under the
[storage experiment's assumptions](store-experiment.md).

`fn-sn-finish` requires the file kernel to be in `:completing`, finds the exact
record identified by its completion pair, and checks every recorded field
against the actual still-pending node. It then calls the actual
`fn-node-complete` with the matching transaction ID, generation, and `:durable`.
Only this branch invokes kernel core completion and acknowledgement. No caller
supplies a string or token claiming that node completion matched.

The principal certified properties are:

- `fn-sn-actual-durable-completion-installs-record`: actual node completion
  installs the exact article payload and groups, true archive pin, archive
  binding, and retention obligation with the recorded subject, evidence, and
  charge.
- `fn-sn-finish-installs-exact-article-and-archive-pin`: the composed operation
  has that semantic result.
- `fn-sn-finish-acknowledges-exact-pair`: it appends exactly the file completion
  pair to the acknowledgement history.
- `fn-sn-new-success-requires-actual-matching-durable-node-completion`: any
  added success requires the actual matching pending node, equals its real
  durable transition, and has the exact committed article and archive pin.
- Preparation, I/O, crash, and recovery cannot create acknowledgements.

These are proofs of the actual transition definitions. There is no
post-completion content check used to assume the semantic result proved above.
Acknowledgement here means the logical kernel success event, not delivery of
socket bytes to a client.

## Replay and recovery correspondence

A crash discards the live process node. `fn-sn-recover` rebuilds it using the
existing `fn-sf-replay-node`, which calls the actual node preparation/completion
semantics for every accepted record and reconstructs the durable transaction
frontier. Recovery preserves the fixed configuration and creates no new
acknowledgement. All five file-kernel recovery barriers must still complete
before ordinary preparation can resume. Known prepublication absence also has the explicit resolution operations
described below; uncertain publication still requires recovery.

`fn-sn-replay-loop-append` proves sequential composition of the actual replay
interpreter. `fn-sn-extended-history-equals-live-completion` then proves that,
starting from a successful replayed prefix, appending one correctly sequenced,
admitted record yields exactly the actual live durable node. Hypotheses require
that advancing to the recorded transaction ID is admissible and the actual
preparation produces the matching proposal. Equality covers the entire node,
including memberships, watermarks, archive accounting/bindings, and transaction
ID; aborted transaction-ID gaps are permitted.

`fn-sn-fence-node` and `fn-sn-resolve-node` are unreachable-in-composition:
no host path calls them, and every uncertainty is resolved by reopening through
`fn-sn-open-observed`. They and their two correspondence theorems remain as
documentation of the in-process resolution primitives and are not evidence for
any host claim; the host-relevant statement of the same fact is
`fn-snt-pending-linkp`, which relates the pending node to replay of the current
and extended histories.

## Evidence and remaining boundary

Structural preservation is certified for initial state, prepare, I/O, finish,
crash, and recovery. The assertion book
[`tests/acl2/store-node-tests.lisp`](../tests/acl2/store-node-tests.lisp)
checks complete two-group publication, false host completion words, real but
mismatched pending payload/groups/archive metadata, repeated completion,
acknowledged reopen, both uncertain-link crash outcomes, and the same two
outcomes from `:record-data-durable`, where the link was issued but its result
never observed (the `final-link` process-death cut). Recovery of a present
record creates content without inventing an acknowledgement; recovery of an
absent record retains the consumed transaction frontier.

The global history/live-node induction is now certified in
[`books/store-node-traces.lisp`](../books/store-node-traces.lisp).
`fn-snt-relation` strengthens the structural invariant according to phase:

- Ready, allocator, and completed recovery phases have the exact replayed node
  at the live frontier. A newly reserved transaction still has the preceding
  frontier until actual preparation consumes its ID.
- Before record publication, the actual pending node's abort resolution equals
  current-history replay and its durable resolution equals extended-history
  replay. The pending record binds all acceptance and retention fields.
- After publication, actual durable completion equals replay of the now-durable
  history, and the exact matching completion gate is enabled.
- During `:replaying`, the process node is explicitly only a fresh diagnostic
  node; successful recovery replaces it with actual replay. Fenced allocator,
  record, and recovery states retain their corresponding relation. An
  unrecoverable `:fault` is unreachable from this invariant under the kernel's
  permitted crash model and admitted histories.

Every exposed wrapper operation separately preserves this relation.
`fn-snt-mixed-trace-preserves-live-history-relation` proves preservation by an
arbitrary finite mixed trace of those actual operations, and
`fn-snt-initialized-mixed-trace-has-live-history-relation` establishes the
initialized case. The dispatcher only chooses existing wrapper operations;
no transition tests the proposed relation of its output.

`fn-snt-mixed-trace-ready-node-is-exact-replay` identifies the actual ready or
recovered node with replay of its exact surviving history and frontier.
`fn-snt-acknowledged-history-retained-through-mixed-trace` proves that every
prior acknowledged pair remains acknowledged and has a covering durable record
after the trace. These statements cover arbitrary finite sequences, not only
the assertion vectors. The additional
[`mixed-trace tests`](../tests/acl2/store-node-traces-tests.lisp) exercise an
unused allocator ID, acknowledged reopen, and a later uncertain publication
that recovers content without inventing an acknowledgement.

The resolution operations in
[`books/store-node-resolution.lisp`](../books/store-node-resolution.lisp)
close the consumed-reservation paths. `fn-sn-refuse-reservation` resolves only
the exact reserved transaction and advances the actual idle node to the durable
frontier. `fn-sn-known-abort` derives the transaction and generation from the
bound candidate and calls actual aborted node completion. It applies only
before immutable publication is attempted, in the record-staged or
record-data-durable phases. Stale, repeated, and post-publication requests are
no-ops; publication uncertainty requires crash/recovery. Neither operation can
add an acknowledgement, and both preserve `fn-snt-relation`.

[`books/store-node-resolution.lisp` (the resolution traces were folded into it, 2026-09-19)](../books/store-node-resolution.lisp)
extends the actual trace dispatcher with these refusal and known-abort
operations. `fn-snrt-mixed-trace-preserves-live-history-relation` and its
initialized corollary cover arbitrary finite mixtures of preparation, exposed
file I/O, finish, refusal, known abort, crash, and recovery.
`fn-snrt-mixed-trace-ready-node-is-exact-replay` and
`fn-snrt-acknowledged-history-retained-through-mixed-trace` carry the exact replay
and acknowledged-record retention guarantees through this larger vocabulary.
`fn-snrt-new-success-is-actual-matching-durable-completion` additionally proves
that every step changing acknowledgement history is an actual matching durable
finish that installs the exact article and retention obligation. The
[resolution trace assertions](../tests/acl2/store-node-resolution-traces-tests.lisp)
exercise both abort phases, refusal and abort transaction-ID gaps before
publication, post-publication abort rejection, and later refusal/abort/recovery
that retains a prior acknowledgement.

These are logical refinement results. Semantic refusal and known prepublication
absence are host classifications at this layer; the proofs do not establish
that a physical adapter classified an error correctly or that OS, fsync, and
link behavior meets the model. Additional wrapper APIs require preservation
steps before joining the trace theorem. The observed-image loader and all 40 wrapper/loader guards are now certified
in targeted runs. The adopted adapter is being checked as a combined batch;
byte-to-image correspondence, POSIX refinement, physical storage accounting
and platform durability remain separate work. No signature or
content-hash correctness is asserted.

## Observed physical image entry

[`store-observed`](../books/store-observed.lisp) validates decoded configuration,
frontier and contiguous history before calling actual `fn-sn-recover`.
`fn-sn-open-observed-success-exact-history` establishes exact records/frontier,
actual replayed node and an empty fresh-process acknowledgement history.
The opening path creates no barrier observations. General theorems over the
actual `fn-sn-io` operation show zero through four successful recovery barriers
remain `:recovering`; the fifth reaches `:ready`. The host must supply those
results only after the corresponding physical fsync returns successfully.
Exact frame decoding and truthful physical observations remain adapter premises.

This entry is the root of every process (`host/store-node-host.lisp`,
`fn-store-sn-recover`), and the trace theorems are rooted there in
[`store-observed-traces`](../books/store-observed-traces.lisp), which includes
`store-observed` and `store-node-resolution`. The two books are
separate because the opening theorems above certify in the theory of
`store-node-invariants` and stall under the rewrite rules the trace books
export; the host includes only `store-observed`.

- `fn-sn-open-observed-success-has-live-history-relation`: a successful open
  satisfies `fn-snt-relation`, with the single hypothesis that the open
  succeeded (`fn-sn-open-okp`). Every trace theorem of the two trace books
  therefore applies to the state the host resumes from;
  `fn-snrt-observed-open-mixed-trace-preserves-live-history-relation` and
  `fn-snrt-observed-open-ready-node-is-exact-replay` restate preservation and
  exact replay from this root.
- `fn-sn-open-observed-succeeds-on-recoverable-image`: opening succeeds for
  every structurally valid image whose history replays at its frontier; with
  `fn-sn-open-observed-success-implies-recoverable-history` this makes the
  refusal codes exhaustive.
- `fn-sn-acknowledged-record-survives-observed-reopen`: for a live state
  satisfying `fn-snt-relation`, an image admissible under `fn-sf-crash-imagep`
  (A-DURABILITY and A-WRITE-ISOLATION as hypothesis) and a pair in its
  acknowledgement history, the open succeeds and the pair names a record of the
  reopened state. `fn-snrt-acknowledged-record-retained-across-observed-reopen`
  extends this through any later mixed trace of the reopened process. The
  acknowledgement list itself is not reconstructed; the adapter has no anchor
  from which to do so, and an image that rolled back the acknowledged record is
  not admissible under the hypothesis but is indistinguishable to the reopen
  entry from a valid one (the teeth in the test book exhibit exactly this).

The witnesses in [`store-observed-traces-tests`](../tests/acl2/store-observed-traces-tests.lisp)
open a two-record image with a consumed frontier gap, run refusal, known
abort, publication with acknowledgement, an uncertain link, crash and recovery,
then acknowledge a record, die at the `final-link` cut, and reopen on both
admissible images; each keystone has one refuting witness per hypothesis.
