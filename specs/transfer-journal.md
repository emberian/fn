# Fragment journal

Status: wave-3 laboratory profile (C2-04). The
[transfer kernel](transfer-experiment.md) stages fragments in memory and says
so. This specification adds the durable record that makes restart a theorem:
the journal is a sequence of kernel inputs with the kernel's own answer to
each, and replay is the kernel run again. The executable decisions are
`books/transfer-journal.lisp`; the theorems are
`books/transfer-journal-invariants.lisp`; the two-fragment restart trace and
the teeth are `tests/acl2/transfer-journal-tests.lisp`.

## Records

A journal begins with `(:profile capacity max-object max-chunk max-chunks
max-label max-reservations)`, the kernel profile that fixes the initial state.
Every later record is a transition record:

- `(:reserve label declared-length outcome)`, an input to
  `fn-transfer-reserve` and the outcome it returned;
- `(:chunk label offset octets outcome)`, an input to `fn-transfer-add-chunk`
  and the outcome it returned.

The host writes a record with `fn-tj-write` after the kernel answered and
before it adopts the new state; the outcome field is the kernel's, never the
host's. A refused arrival is journaled like any other: `:duplicate`,
`:covered`, `:overlap-conflict` and every resource refusal are evidence of
what arrived and what the kernel decided. Only `:reserved` and `:stored` can
move the state.

A written record has the input's kind, label, length or offset and (for a
chunk) octets in fixed positions, whatever the input was: a malformed input
is journaled with the refusal the kernel gave it and replays to that refusal.

Durable bytes are one frame per record under the
[frame grammar](../books/frame.lisp) in this book's own family: magic `FNTJ`,
version 1, kinds `:profile` = 1, `:reserve` = 2, `:chunk` = 3, field
specifications by `fn-tj-spec-for` (labels and chunk octets are `:blob`
fields, so the durable profile requires them nonempty; an empty arrival is an
`:empty-chunk` no-op and needs no record). `fn-tj-encode` and `fn-tj-decode`
take the host's digest of the protected prefix as `fn-frame-encode` and
`fn-frame-decode` do; `fn-tj-seal` and `fn-tj-open` state the same pair
against the constrained `fn-frame-digest` (A-CRYPTO).

## Replay

`fn-tj-apply` re-runs the record's transition on the record's own fields and
compares the kernel's outcome with the recorded one. `fn-tj-replay-records`
folds it over a record list; `fn-tj-replay-frames-with` (the host entry
point) first opens each frame with the host's digest, and
`fn-tj-replay-frames` is the same against A-CRYPTO. A replay answers
`(:ok state index)` or `(:fault reason state index)`, where the state is the
one before the faulting record and the index counts records consumed. The
faults are typed: `(:corrupt reason)` for a frame that does not open (the
frame decoder's reason: length, magic, trailer, field, trailing octets),
`:not-a-transition` for a decoded record of another kind, `:outcome-mismatch`
for a record the kernel contradicts, `:no-profile` for a journal that does not
begin with its profile.

## Keystones

Each sentence names the property, its hypotheses and the covered scope.

`fn-tj-replay-of-journal-is-run`: for any state `st`, any input list
whatsoever and any natural index, replaying the journal that a live run of
those inputs writes reproduces the fold of the kernel transitions,
`(list :ok (fn-tj-run st inputs) (+ (len inputs) index))`. The state is
reproduced exactly (gaps, retained bytes, reservations), because it is the
same function on the same inputs; nothing about durability of the write
itself is claimed (A-DURABILITY, host).

`fn-tj-replay-sealed-journal-is-run`: the same through sealed frames, under
the added hypothesis that every written record is encodable
(`fn-tj-records-okp`), against the constrained digest.
`fn-tj-decode-of-encode` and `fn-tj-open-of-seal` are the frame family's two
directions: an encodable record with a 32-octet digest decodes to itself, and
a sealed record opens to itself under A-CRYPTO.

`fn-tj-corrupt-frame-ends-replay-at-typed-fault`: under those hypotheses, a
sealed journal followed by any frame that does not open replays to
`(:fault (:corrupt reason) (fn-tj-run st inputs) (+ (len inputs) index))`,
whatever follows the bad frame. No partial chunk exists: the fault state is
the fold, and `fn-tj-run-preserves-statep` says the fold of any inputs over a
kernel state is a kernel state.

`fn-tj-refused-record-replays-to-same-state`: any record whose recorded
outcome is neither `:reserved` nor `:stored` replays to exactly the prior
state, with no hypothesis on the state. This covers duplicates, covered
arrivals, every overlap conflict and every resource refusal. Byte-identical
overlap is accepted as `:stored` and retains the union
(`fn-transfer-add-chunk-retains-union` in the kernel); a differing overlap is
`:overlap-conflict` and retains nothing. Reordering is a kernel property
(`fn-transfer-complete-entry-candidate-correct`): the witness shows two
arrival orders with different retained fragments and the same candidate.

`fn-tj-replay-frames-with-is-replay-frames`: with the digests a correct host
computes over the prefixes, the host entry point is the specification replay.

`fn-tj-restart-reproduces-missing-ranges` is a corollary of the first
keystone, stated because it is the form a scheduler uses.
`fn-tj-candidate-is-unverified-by-definition` records that the only export of
a complete entry is `(:unverified octets)`; the record kind table is exactly
`:profile`, `:reserve`, `:chunk`, and no result of this book has a receipt
shape. Validation and acceptance are [the container](container.md).

## Host work (proposals, not claims)

- `tools/run_transfer.py` (proposed): stage fragments by calling
  `fn-transfer-reserve`/`fn-transfer-add-chunk` through the host bridge,
  append `fn-tj-encode` of `fn-tj-write` to `transfer.fntj` with `fsync`
  before adopting the state, and on start replay with
  `fn-tj-replay-frames-with` over the frames split by their length fields.
  The split by length is host work exactly as for FNWF/FNRJ; the trailer
  comparison is ACL2's.
- BP side: `books/bp-fragment.lisp` reassembles bundle fragments; a bundle
  payload that is one fn object chunk is a `:chunk` input with the object's
  label as the transfer label and the fragment offset as the offset. The
  wiring is a proposal for C2-08.
- A `:progress` summary record (coalesced missing ranges) is not needed for
  correctness and is not defined; a scheduler reads
  `fn-transfer-missing-ranges` of the replayed state.
