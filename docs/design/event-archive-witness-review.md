# Canonical archive batch witness: format review

Proposal only. No new durable fields have been added. The actual source slice
through `40d8124d4` authenticates archive headers/pages and common cold reach;
it does not establish complete coverage, archived installation receipts or release.

## Current declarations and consumers

- `books/event-archive-schema.lisp`: internal schema20, key
  `(history, incarnation, event)`, value `(canonical (:octets 4096)), (leaf :digest)`.
- `books/event-archive-format.lisp`: root3 header binds the physical archive
  namespace, checkpoint, C/Cevent/Cseal and full schema10 manifest Ref.
- `books/event-archive-producer.lisp`: `fn2-event-archive-stage` takes the actual
  held journal LEAF/hash-phase3 range through the sole run builder.
- `books/event-archive-cold-header.lisp`, `-cold-cursor.lisp`, `-cold-reach.lisp`:
  real candidate page/layout verification, shared physical/run engine and typed reach.
- `books/format-storage.lisp`: the original `fn2-format-sealed-batch` layout.
  `books/format-physical.lisp`: original records/seal frame header and trailer.

The current producer keys schema20 with the checkpoint builder's physical
archive namespace. Its schema comment saying “journal's physical history” is
too strong: original journal namespace is separately decoded into
`fn2-event-read-journal-history` and `-journal-incarnation`. The proposed witness
preserves both words separately; it must not infer them from the archive key
or confuse them with semantic lineage/domain inside the canonical member.

## Existing commitment chain

1. `fn2-event-read-open-core` in `event-read-source.lisp` derives J, extent,
   epoch/allocation and expected event interval from actual held directory/catalog
   source (`fn2-event-proof-pack-entry`), not proposed witness arguments.
2. `fn2-event-read-format-step` in `event-read-verify.lisp` resolves expected J
   and J-1 semantic seals through `fn2-event-source-seal`, which checks actual
   source/holder identity. `fn2-event-read-format-core` uses `fn2-rec-context`
   (`recovery.lisp`) for the exact physical unit/extent/epoch/allocation/J context.
3. The existing `fn2-format-run :seal` checks the original sealed-batch bytes.
   `fn2-fc-identity` checks physical history/incarnation, extent, writer epoch,
   allocation, J and previous J. `fn2-fc-check-byte` compares predecessor-seal
   bytes. `fn2-fc-prefix-byte` and `fn2-fc-byte` hash the actual body under the
   existing sealed-batch domain and physical context, zeroing its final-seal
   field. No archive hash implementation is proposed.
4. On semantic-seal success, `fn2-event-read-format-core` additionally compares
   the computed result with the actual expected J seal, checks event-first/last,
   and fetches the sealed record-stream digest. The sealed-batch layout contains
   J, physical identity, predecessor seal, event interval and record-stream digest.
5. The records frame is checked under that record-stream digest and matching
   physical/J context. Only the successful records-frame branch begins the
   actual member scanner and enters MEMBERS. `fn2-journal-members-step` checks
   canonical record boundaries/event progression within the declared interval;
   `fn2-event-members-step` computes the canonical leaf through the shared hasher.

This chain binds the actual canonical member to J and its original physical
allocation. The leaf hash or event number alone does not bind J. Existing
`tests/event-read-verified-unit.lisp` drives actual producer/frame verification
and seal/records corruption controls; it is unexecuted under this lane's grant.

## Proposed source receipt and layout

Before copying durable witness fields, add a private verified-batch receipt
to the actual event reader. Proposed constructor names are new, not existing APIs:

- At actual semantic-seal success, capture immutable source owner/token, J,
  original physical namespace/identity, interval, expected J/J-1 seals and the
  verified record-stream digest; phase SEAL-CHECKED.
- At actual records-frame success, require the same captured source tuple and
  computed frame digest equal to that captured record-stream digest; phase MEMBERS.
- `fn2-event-read-verified-batch-receipt-p` checks that exact retained receipt
  against the current actual owner/source/member range. Archive staging requires
  it and serializes only its fields. A MEMBERS literal or scalar copy is insufficient.

Extend only schema20's value, keeping its key and existing canonical/leaf fields:

```lisp
(journal-history (:id history))
(journal-incarnation (:id incarnation))
(journal-extent (:id extent))
(journal-writer-epoch (:id writer-epoch))
(journal-allocation (:id allocation))
(journal-commit (:id commit))
(journal-first (:id event))
(journal-members :u32)
(journal-seal :digest)
(journal-previous-seal :digest)
```

Original records/seal unit addresses derive from this historical extent and
roles through existing `fn2-rec-context`; these inline values are not live
storage Refs. Both witness seals come from the frozen verified receipt. Window14
is the existing 64KiB held-entry workspace, so three digest slices fit without
a second working reservation. Generated MAX-entry/restart cost and the actual
named B envelope must still be checked after this declaration changes.

Repeating the bounded witness with each member avoids buffering every batch
while build1 emits the member run; no second unbounded catalog or schema22 run
builder is introduced. Schema21 remains reserved for actual shared carry outputs.

## Reader, semantic closure and transfer

The archive reader must authenticate descriptor→root3→schema10→schema20 first,
then check exact archive namespace/event key and original journal witness tuple.
For a full cold walk, events are contiguous; repeated J has identical witness;
the next J advances exactly once, joins the next event interval and names the
prior J seal. Last J/Cevent/seal match the authenticated root3 C/Cevent/Cseal.
Canonical bytes are copied to the existing 4KiB scanner scratch, scanned/hashed
with the shared member primitive, compared to the stored leaf before append,
and finally compared with the actual root4 frontier bound to this exact root3.

The RELEASE wire now supplies expected installation J and event. Point lookup
uses that event, checks witness J, then passes the actual authenticated typed
CHECKPOINT_INSTALLATION member to the shared codec matcher for cp+Ref6+hash and
C/Cevent<J/installation-event. It does not fabricate a resident rec-cand row.
The served proof source still needs real inclusion paths/carry nodes; peaks are
insufficient, and no complete point-proof API exists yet.

The retained-prefix semantic walk must also run the shared RELEASE constructor
to restore descriptor/self/installation-J outgoing obligations before orphan
disposal or epoch open. Page reach protects witness/member bytes, not those
outgoing objects. Codec owns this typed constructor and the exact transfer gate.
Old raw-source holds remain until actual publication/bank/query/peer contracts
and these typed obligations transfer. No FREE activation is proposed here.
