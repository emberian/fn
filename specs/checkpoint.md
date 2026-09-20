# Checkpoints: logical value, canonical bytes, generation publication

Status: PRF-008 logical core (`books/checkpoint.lisp`), the canonical byte
encoding (`books/checkpoint-codec.lisp`, C1-10) and the generation
publication/selection machine (`books/checkpoint-publish.lisp`, C2-09) are
certified books; `tools/checkpoint.py` and the `recover` hook in
`tools/run_store.py` are the host adoption. Counts live in the generated
ledger; this page carries each keystone's property, hypotheses and covered
scope, and what the host still asserts.

## 1. The logical checkpoint (`books/checkpoint.lisp`)

A checkpoint is the seven-tuple `(:fn-checkpoint 1 groups capacity frontier
sequence node)`: the exact `fn-node` state after replaying `sequence`
records, the configured group list and retention capacity it binds, and the
consumed allocator frontier, which may be ahead of the node's next
transaction id because known-aborted reservations leave no record. Capture
replays the prefix once; restore takes no prefix and runs `fn-replay-loop`
only on the suffix, after checking the configuration binding, the stored
sequence, and that every suffix transaction id is at or above the consumed
frontier and below the observed final frontier.

- `fn-checkpoint-plus-suffix-equals-full-replay`: for every admissible split
  (`fn-checkpoint-admissible-splitp`: ordered journal intervals, successful
  prefix and full replays, both nodes reconcilable with their frontiers),
  capture followed by suffix restore equals full-history replay normalized to
  the same final frontier. Scope: the executable replay machine; allocator
  gaps before and after the checkpoint are permitted.
- `fn-checkpoint-restore-rejects-frontier-reuse`: for any checkpoint,
  matching configuration and valid frontier, a suffix whose first record
  reuses a transaction id below the consumed frontier is refused with
  `(:error :suffix)` before replay runs.

## 2. Canonical bytes (`books/checkpoint-codec.lisp`)

Layout, a concatenation of the records book's CBOR primitives: bytes
`"fn-c"`, uint schema 0, uint sequence, uint frontier, uint capacity, uint
group count, one bytes item per group, then `TREE(node)`. `TREE` is a tagged
encoding of the node's value universe (`fn-cpc-treep`: nil, naturals below
2^32, octet-domain strings, the symbols `t`, `:archive`, `:forward`,
non-empty octet lists, conses). An octet list is always one bytes item and
never a cons chain, so each value has one spelling; the decoder refuses the
cons spelling (`:noncanonical`), the empty bytes item under the octet tag, a
non-minimal CBOR head, an unknown tag or symbol code, and a cons deeper than
its depth fuel (the octets it has). The item reader has no per-item
whole-stream preflight: the frame bounds the payload once (4 MiB).

- `fn-cpc-decode-of-encode` (value direction): for an encodable checkpoint
  whose encoding fits the payload cap, decoding at its own groups and
  capacity and at any observed frontier and record-count bounds at or beyond
  its own yields `(:ok checkpoint)`. Hypotheses: `fn-cpc-encodablep` (a
  `fn-checkpointp` value with octet-domain group names, at most 16 groups,
  32-bit capacity and sequence, node in the universe), the two bounds.
- `fn-cpc-accepted-input-is-canonical` (byte direction): any accepted input
  is exactly the encoding of the value returned. Only hypothesis: acceptance.
  The decoder itself establishes the octet domain, cap, magic, version,
  bounds, configuration equality, absence of trailing octets and
  `fn-checkpointp` of the assembled value.
- `fn-cpc-decode-rejects-{mismatched-capacity, mismatched-groups,
  frontier-ahead, count-ahead}-before-node`: with the header's verdict fixed,
  the same refusal (`:configuration`, `:frontier`, `:sequence`) results for
  every octet tail in place of the node item, so the node is never parsed.
- `fn-cpc-valid-is-capture-value` (exact binding): a checkpoint that
  validates against a record prefix (`fn-cpc-validp`: recognizer, matching
  groups and capacity, and the actual replay of the prefix yields its
  sequence and node) is `fn-checkpoint-capture-value` of that prefix at the
  checkpoint's frontier, given the prefix is an ordered journal interval
  below that frontier. Every field is fixed by the prefix.
- The frame: `fn-cpc-frame-{encode,decode}` carry the payload in the generic
  `fn-frame` grammar under this book's magic `FNCP` and kind table
  `(:checkpoint :selection)`; `fn-cpc-frame-decode-of-encode`,
  `fn-cpc-frame-open-of-seal` (against A-CRYPTO),
  `fn-cpc-frame-accepted-is-canonical`, `fn-cpc-selection-decode-of-encode`.

Residual: a wholly well-formed checkpoint substituted for another under the
same name decodes; the frame trailer detects damage only under A-CRYPTO's
algorithm assumptions, never freshness or durability.

## 3. Generation publication and selection (`books/checkpoint-publish.lisp`)

A generation is published as the store publishes a record: candidate bytes
data-durable under a staged name, linked under `generation-N`, directory
barrier; then, and only then, selected by the same three steps on the
marker file (`selected`), whose namespace step is an atomic replacement.
Authority is the explicit marker, chosen over a newest-valid-generation
rule because the latter turns a corrupt newest generation into a silent
roll-back to its predecessor. Each generation entry carries its bytes and,
as ghost fields, the prefix, frontier and host digest that made them.
Crash images follow `fn-sf-crash`: marker `:old`/`:new` is live from
`:marker-data-durable`, generation `:absent`/`:present` from
`:candidate-data-durable`; a present generation is the exact data-durable
candidate (the store's A-WRITE-ISOLATION premise). That choice pair is the
K12 shape of [the byte-level crash model](crash-model-v2.md) §3.3; K12 stays
open there until its P8 programs are re-transcribed from the committed
`tools/checkpoint.py`, which is a successor lane's step, not this book's.

- `fn-cpp-crash-selects-old-authority-or-complete-candidate`: from any
  reachable state (`fn-cpp-statep`) and any choice, the image's marker is the
  previous authority, or it names the candidate and the image holds the
  candidate's complete entry. The `:new` choice exists only in marker phases,
  reachable only through `:candidate-published`.
- `fn-cpp-crash-marker-is-authority-before-selection-attempted`: before
  `os.replace` on the marker may have been issued, every image's marker is
  the old authority.
- `fn-cpp-recover-selects-complete-generation`: for a well-formed image
  (`fn-cpp-imagep`) whose marker names a generation, with the host's digest
  equal to the one that sealed it and the observed frontier and record count
  at or beyond the generation's, recovery is `(:ok name checkpoint)` with the
  checkpoint the capture of that generation's prefix.
- `fn-cpp-recover-reports-corruption`: replacing the selected generation's
  bytes by any bytes the codec refuses makes recovery `(:corrupt name
  reason)`: not `:ok` for any generation, not `:none`.
  `fn-cpp-corrupting-unselected-generation-is-invisible` is the other half:
  only the marker's generation is consulted.
- `fn-cpp-selected-plus-suffix-equals-full-replay`: under the recovery
  hypotheses and an admissible split of the generation's prefix with a
  suffix, `fn-checkpoint-restore` of the recovered checkpoint equals
  `fn-checkpoint-full-replay` of prefix plus suffix (composition with §1).
- `fn-cpp-authority-retained-until-selection-durable` and
  `fn-cpp-published-generations-retained`: no step but the marker's
  directory barrier changes the authority; no step or crash removes a
  published generation.

Outcomes stay distinct: `(:none)`, `(:ok name checkpoint)`, `(:corrupt name
reason)`, `(:missing name)`.

## 4. Host adoption (`tools/checkpoint.py`, `tools/run_store.py`)

`publish` asks ACL2 for the protected prefix of the capture of the durable
records at the durable frontier (`fn-store-checkpoint-protected`), seals it
with SHA-256 (A-CRYPTO), and issues the three publication steps; `select`
issues the three marker steps. The six `faults.at("checkpoint:<name>")`
sites are the cuts in `tests/campaign/cuts.py`. `Store.recover` replays the
journal as before (the journal remains the authority), then decodes the
selected generation through `fn-store-checkpoint-decode` at the observed
frontier and count, slices the suffix by the sequence ACL2 returned,
restores through `fn-store-checkpoint-restore` (the proved subject) and asks
`fn-store-checkpoint-differential` whether the restored node equals the node
full replay produced. The outcome (`none`, `ok`, `corrupt`) is printed by
`recover` and `checkpoint.py status`; `corrupt` exits 4.

What the host still asserts, outside the proofs:

- SHA-256 is a fixed function of the bytes (the digest the host supplies at
  recovery is the one it supplied at publication when the bytes are
  unchanged); ACL2 only compares it.
- `os.link` publishes the whole data-durable file or nothing, `os.replace`
  leaves the old or the new marker, and `fsync` orders them: the store's
  A-DURABILITY and A-WRITE-ISOLATION premises, exercised by process-death
  tests with the OS cache retained, not by power-loss qualification.
- The differential equality is a debug assertion under
  `FN_CHECKPOINT_DIFFERENTIAL`, not a production dependency; production
  recovery is the full replay.
- Rollback of a valid older generation together with a truncated journal
  still needs an external freshness anchor (C2-12); a detected invalid
  checkpoint is a diagnostic failure, never permission to discard history.
