# Live node and immutable-file completion

Status: executable logical composition in [`books/store-node.lisp`](../books/store-node.lisp),
with correspondence theorems in
[`books/store-node-invariants.lisp`](../books/store-node-invariants.lisp).
This closes the file kernel's trusted `:matching` reply premise for the new
composition's acknowledgement operation. It does not establish that the host
adapter uses this composition, or that physical file operations implement the
kernel's observations.

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
before ordinary preparation can resume. This narrow composition uses recovery
after a failed publication; it does not expose the kernel's optional in-process
prepublication-abort optimization.

`fn-sn-replay-loop-append` proves sequential composition of the actual replay
interpreter. `fn-sn-extended-history-equals-live-completion` then proves that,
starting from a successful replayed prefix, appending one correctly sequenced,
admitted record yields exactly the actual live durable node. Hypotheses require
that advancing to the recorded transaction ID is admissible and the actual
preparation produces the matching proposal. Equality covers the entire node,
including memberships, watermarks, archive accounting/bindings, and transaction
ID; aborted transaction-ID gaps are permitted.

For in-process resolution, `fn-sn-fence-node` and `fn-sn-resolve-node` call the
actual indeterminate completion and `fn-node-recover` primitives. General
correspondence theorems show committed resolution equals direct durable
completion and absent resolution equals direct abort. These helpers do not
claim that an unvalidated external committed/absent observation is trustworthy.
Crash recovery in the composition derives state from actual replay instead.

## Evidence and remaining boundary

Structural preservation is certified for initial state, prepare, I/O, finish,
crash, and recovery. The assertion book
[`tests/acl2/store-node-tests.lisp`](../tests/acl2/store-node-tests.lisp)
checks complete two-group publication, false host completion words, real but
mismatched pending payload/groups/archive metadata, repeated completion,
acknowledged reopen, and both uncertain-link crash outcomes. Recovery of a
present record creates content without inventing an acknowledgement; recovery
of an absent record retains the consumed transaction frontier.

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

The trace event vocabulary covers prepare, exposed file I/O, finish, crash,
and replay recovery. Additional wrapper APIs require their own preservation
steps before joining this theorem. Host adoption, observed-image loader
composition, byte codecs, POSIX refinement, guard verification, physical storage
accounting, and platform durability remain separate work. No signature or
content-hash correctness is asserted.
