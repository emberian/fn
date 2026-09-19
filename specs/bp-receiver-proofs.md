# Receiver journal proof scope

The receiver invariant books reason about the existing `fn-bpr` operations and
actual `fn-bprr-apply-record`, `fn-bprr-replay-rest`, and `fn-bprr-replay` journal
interpreters. They add proof predicates and record witnesses; they do not alter
receipt generation or filter outputs on a desired conclusion.

`fn-bprv-invariantp` combines receiver state shape with three relations: every
retained context has an exact accepted record in the fixed ready Store; each
committed or pending receipt entry is linked to the retained context and the
canonical receipt constructor; and each committed receipt has a matching typed
`:committed` decision in the supplied journal. Pending entries additionally
exclude an already committed receipt for the same work ID.

The combined public theorems are:

- `fn-bprv-initial-invariant`;
- `fn-bprv-actual-record-preserves-invariant`;
- `fn-bprv-actual-finite-replay-preserves-invariant`;
- `fn-bprv-successful-replay-has-invariant`.

Together they establish initialized state and preservation through the actual
journal transition and its finite recursive interpreter.
The finite theorem permits arbitrary records and includes the state returned
when replay stops at the first invalid, duplicate, or conflicting record. Its
journal-membership hypothesis records provenance; it is not a hypothesis that
the output satisfies the desired invariant.

Separate unconditional fresh-replay theorems establish the context/Store
relation and committed-decision provenance even for unsuccessful replay. With
no typed committed decision in the journal, the actual receipt encoder returns
no ADU. A nonempty replayed receipt implies an exact authoritative Store record,
ready Store phase, actual node article/subject/archive binding, exact request
payload and subject, retained committed entry, matching journal decision, and
canonical encoded receipt. Merely satisfying the original receiver state
recognizer is insufficient: typed orphan and changed-subject receipt states are
regression examples rejected by the stronger relation.

Existing context and committed receipt lookups survive every subsequent actual
journal operation and finite replay. A previously available receipt ADU remains
byte-identical after replaying an extension, including an extension that fails
and returns its accepted prefix. This supports duplicate handling and restart
regeneration from the retained journal; the interpreter does not skip invalid
records.

These are logical journal and fixed-Store theorems. `:committed` is the durable
decision observation supplied by the adapter; its physical fsync, filesystem,
BPA deletion, transport, and authentication behavior are not proved here. The
Store argument stays fixed across a receiver replay. Changes to Store retention
or a different recovered Store require their own compatibility argument. The
proofs do not establish cryptography, liveness, raw Lisp guard verification, or
an arbitrary concurrent disk execution trace. See [receiver semantics](bp-receipt.md)
and [adapter ordering](bp-receive.md).
