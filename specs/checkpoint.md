# Logical checkpoint experiment

Status: executable logical experiment for PRF-008. This does not select a disk
encoding, checksum, checkpoint-generation publication protocol, or recovery
winner after a crash.

`books/checkpoint.lisp` checkpoints the actual `fn-node` state produced by
`fn-replay`. A checkpoint retains the exact configured group list, retention
capacity, next journal sequence, consumed allocator frontier, and complete node
state. The complete node includes acceptance duplicate history and group
watermarks, articles, retention obligations and releases, article-to-obligation
bindings, and capacity accounting. The model never substitutes the visible
article list for this state.

The node is the exact result after replaying the checkpointed prefix. The
allocator frontier is stored separately because successfully reserved but
known-aborted transaction IDs leave no committed journal record. Thus the
frontier may be greater than the node's next transaction ID. Capture requires
that the node can advance to the frontier without changing committed content.

Restore accepts no prefix. It validates the checkpoint shape, exact group and
capacity binding, a natural next sequence derived by capture from actual replay,
and an idle unfenced node whose next transaction ID does not exceed the
checkpoint frontier. It
then requires the suffix to begin at the stored journal sequence, use only
transaction IDs at or above the consumed checkpoint frontier, remain strictly
ordered, and stay below the observed final durable frontier. It invokes
`fn-replay-loop` only on that suffix and finally advances the successful node to
the final frontier. Duplicate sequences and stale transaction IDs fail before
core replay; semantically inadmissible ordered records fail as replay errors.

`fn-checkpoint-plus-suffix-equals-full-replay` proves, for every executable
admissible prefix/suffix split, that capture followed by actual suffix restore
equals actual full-history replay normalized to the same final durable
frontier. The hypotheses require both journal intervals to satisfy the
immutable-file ordering rules and the actual prefix and full replays to
succeed. The theorem permits allocator gaps both before and after the
checkpoint. It does not assume the two results equal and restore does not call
full replay. That equivalence theorem is silent on rejection: both sides reduce
to the same replay-loop expression, so it does not by itself show the frontier
doing any rejecting work. `fn-checkpoint-restore-rejects-frontier-reuse` is the
companion result that does: for any checkpoint, matching configuration, and
valid persisted frontier, a suffix whose first record's transaction id reuses a
value below the checkpoint's consumed frontier is refused with `(:error
:suffix)` before any replay runs, regardless of the rest of the suffix.

The logical recognizer cannot detect substitution of one wholly well-formed
checkpoint for another. The logical checkpoint object is not a native or
durable byte format. A later
physical refinement must encode every field canonically, authenticate or
checksum the whole binding, publish a new generation with data and directory
barriers before selecting it, and retain the old authoritative generation until
that selection is durable. Checksums support corruption detection under their
algorithm assumptions; they do not prove storage durability or freshness.
Rollback of an otherwise valid checkpoint and suffix still needs an independent
freshness anchor. A detected invalid or mismatched checkpoint is a diagnostic
failure, not permission to discard acknowledged history or silently choose an
older usable state.
