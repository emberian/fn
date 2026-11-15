# Canonical archive batch witness: revised format review

Proposal v2 only, superseding the ten-scalar-field proposal in `3d88a3f74`.
No new durable fields have been added. Source through `b75f244e4` repairs the
actual original seal reader's semantic boundary and budget continuation; its
ACL2 fixtures remain unrun. The archive still cannot establish COMPLETE-PREFIX,
serve an archived installation receipt, discharge old holds or authorize FREE.

## Existing declarations and exact shared engines

- `books/event-archive-schema.lisp`: internal schema20, key
  `(history, incarnation, event)`, value `(canonical (:octets 4096)), (leaf :digest)`.
- `books/event-archive-format.lisp`: generated root3 header binds physical
  archive namespace, checkpoint, C/Cevent/Cseal and full schema10 manifest Ref.
- `books/event-archive-producer.lisp`: `fn2-event-archive-stage` copies the actual
  held journal LEAF/hash-phase3 range through the sole run builder.
- `books/event-archive-cold-header.lisp`, `-cold-cursor.lisp`, `-cold-reach.lisp`:
  candidate page/layout verification, shared physical/run engine and typed reach.
- `books/format-physical.lisp`: original frame-header maximum95 and trailer33.
  `books/format-storage.lisp`: complete generated sealed-batch maximum942.
- `books/format-check.lisp`: `fn2-format-run`, `fn2-fc-identity`,
  `fn2-fc-prefix-byte`, `fn2-fc-check-byte`, `fn2-fc-byte`, `fn2-fc-decoded`.
- `books/recovery.lisp`: `fn2-rec-context` derives original role1/2 physical
  hash context from extent/epoch/allocation/J and both physical namespace words.
- `books/journal-members.lisp`, `journal-record-body.lisp`, `event-frontier.lisp`:
  sole canonical member scanner, zero-tail checker and member/Merkle hasher.

The actual schema20 key uses the checkpoint builder's physical archive pair.
The current schema comment calling this the journal namespace needs correction
with implementation. The original journal physical pair is distinct evidence
inside the original header/body. Semantic lineage/domain inside canonical
record headers remains distinct from both physical pairs.

## Why the scalar proposal was insufficient

Jseal hashes the complete semantic body, including INPUT-ROOT, DEPENDENCIES,
ALLOCATION-RETIREMENT, METADATA-EDITS, OUTPUT root recipe and EVENT-FRONTIER,
not only J/physical identity/event interval/record-stream/predecessor seal.
Copying selected fields into a newly committed checkpoint authenticates those
claims; it does not reconstruct their original J commitment. Event leaf hashes
also do not bind a member to J. The revised proposal preserves the exact
complete original generated body and reconstructs its records-frame commitment.
No omitted field is filled with zero or a default.

## Proposed schema20 value extension

Keep the existing key/canonical/leaf and append these fields, in this order:

```lisp
(batch-first (:id event))
(original-records-header (:octets GENERATED-FRAME-HEADER-MAX))
(original-sealed-batch (:octets GENERATED-SEALED-BATCH-MAX))
```

The bounds must come from the actual generated declarations (currently95/942),
not a copied second layout. The sole production assembly must see the updated
registered declaration before generating codecs, MAX-entry and restart costs.
Schema21 remains reserved; no portable inclusion-path/carry-node claim follows.

For the first member F of each original batch, both byte strings are nonempty.
Every later member names batch-first F and has both byte strings empty. The
reader checks these conditions using the decoded original sealed-batch's exact
positive event-first/last interval. The repeated F is a seek hint until the
whole batch is verified; it is never an authenticated J label by itself. All
entries in the reconstructed batch must name the same F and occur exactly once
in contiguous event order. Batch-first is unsigned60, positive and no greater
than the current event; all interval arithmetic must be checked for overflow.

Only the first member carries the bounded byte evidence, avoiding a repeated
complete seal per event. There is no second unbounded batch catalog or run
builder. A point reader can seek F and then stream this one original batch,
whose canonical bytes fit the original admitted records payload, to establish
its own actual membership relation before exposing the requested typed member.

## Actual producer receipt transition

Proposed receipt functions below are new interfaces, not implemented APIs.

1. Actual `fn2-event-read-open-core` derives J, physical identity, interval and
   owner/token from the HELD exact directory/catalog source. Its wrapper keeps
   checking the current source and resolves expected J/J-1 seals. No supplied
   batch-first/header/seal bytes can enter archive admission through a generic
   transaction, root1 catalog, peer or generic run-builder role.
2. The original full seal frame is physically verified first. SEAL-SPAN then
   resumes the same generated semantic decoder; SEAL-TAIL checks all remaining
   authenticated payload bytes. Semantic `fn2-format-run :seal nil` receives
   the exact body length, verifies final-seal and predecessor bytes and computes
   the actual Jseal. Event-read additionally matches the actual expected Jseal
   and event interval before fetching the original sealed record-stream digest.
3. At that exact success, before READ-RECORDS overwrites the read window,
   `fn2-event-read-capture-sealed-batch` copies the exact semantic body octets
   into a private receipt-owned slice. It binds source owner/token/J/interval,
   original physical pair/extent/epoch/allocation and both actual expected
   seals; it grants no member or archive completion by itself.
4. Actual records-frame verification uses role1 context and requires its
   computed digest to equal that retained record-stream digest. At this success,
   `fn2-event-read-capture-records-header` saves the exact generated header span
   from the same owned frame and closes the receipt. The member scanner starts
   only after this check. Header kind/ordinal/fragment/payload are checked too.
5. `fn2-event-read-verified-batch-receipt-p` rebinds this closed receipt to the
   actual current owner/source/read handle and frozen member range. Archive
   staging requires it plus the existing exact phase3 leaf/MK order. On the
   first member only it supplies the saved header/body slices to the same
   generated schema20 encoder; later entries use empty slices. A phase literal,
   copied digest, caller-ready flag or source-scanned state cannot close it.

Proposed live storage uses the already reserved 64KiB window14 scratch: its
first160 bytes retain current digest/small scratch uses; a named slice after
that prefix holds at most header95+body942 bytes. BEGIN must derive the actual
window14 owner/handle and validate the whole bound. Between capture and first
member emission, every scratch RESET/overwrite must respect receipt ownership:
notably current `fn2-event-archive-stage` unconditionally RESETs this scratch
and must be changed. Release is only after the actual run writer has copied
the complete first entry, or explicit uncertain teardown retaining source holds.
This lifetime change needs an exact write-class audit and refusal/interleaving
fixtures; existing capacity alone does not establish exclusivity.

## Cold/point reader reconstructs the original commitments

The reader first authenticates selected descriptor→root3→schema10→schema20,
exact namespace/fullRefs and the common current cold reach generation. For
each batch's first member it performs the following bounded resumable work:

1. Decode the exact archived records header and complete sealed body with their
   existing generated codecs, consuming each supplied span exactly. Require
   matching original physical pair/extent/epoch/allocation/J; records kind,
   ordinal0, fragment0 and actual producer payload3900; positive first/count,
   nonoverflowing interval; previous-J and seal-chain continuity. Fresh base0 begins at J1 with the
   actual genesis predecessor; append begins at the retained oldC+1 with its
   authenticated oldC seal and complete old-manifest authority. No arbitrary
   starting J/seal or missing prefix is accepted. Decode all body fields, not a flattened substitute.
2. Use `fn2-rec-context` role2 and `fn2-format-run :seal nil` over the archived
   body. This checks the preserved final-seal field and predecessor seal bytes
   and recomputes Jseal using the existing domain/context/hash-zeroing rules.
   Retain its actual record-stream digest and complete decoded batch interval.
3. Reconstruct the normalized original records frame in one owned4096-byte
   accumulator: exact archived header at0; concatenate the shared scanner's
   complete canonical member ranges in original order; zero the checked inner
   payload tail and outer pad; frame tag1 at4096−33; zero its final32 hash bytes.
   Header length plus payload must fit before that tag. No record can be
   skipped, duplicated, reassigned to J, or split outside its decoded interval.
4. Run the same `fn2-format-run :frame t` under role1 original context in that
   new accumulator, then compare its computed result with the sealed body's
   record-stream digest. Using sealp T writes only the reconstructed buffer's
   digest; the later digest comparison is the acceptance gate. No rec-cand row
   is fabricated and the historical physical tuple grants no old-storage read.
5. Independently use the shared canonical member hasher to compare each stored
   leaf before appending it to the private frontier. The full cold walk joins
   contiguous batches through J/Cevent and final root3 Cseal, then checks the
   existing root4 frontier bound to this exact root3 fullRef/hash.

The reconstruction relation has concrete premises: actual writer ZERO stages
initialize frames before bounded header/body writes; `fn2-fc-check-byte` checks
outer padding/tag and normalizes the trailer hash; the actual member scanner's
`fn2-journal-zero-tail` rejects nonzero inner payload suffix. Concatenating its
accepted complete ranges therefore recovers every committed payload byte,
including canonical zero padding. This relation and budget/crash/interleaving
fixtures are required before the receipt is claimed established. Source traces
and unexecuted fixtures are not that evidence. No new hash domain/implementation
or Python decision is proposed.

Cold storage proposes reusing boot's owned pool-slot4096 as the accumulator,
rx-slot4096 for transport/member scratch and root-slot65536 for the held archive
page. Parent must confirm no overlapping descriptor/root task remains during
this phase and thread exact handles/generations; otherwise an explicit supported
profile reservation is required. Every copy, decode, hash and tail operation
must obey budget1 progress and yield/resume. Generated restart cost changes must
fit the actual named boot envelope and reachable scheduler quantum; stored data
counts impose no ceiling.

## Complete-prefix authority, RELEASE and persistence cuts

Full cold coverage must restore every decoded prefix RELEASE's outgoing
self/descriptor/installation-J typed obligation through the codec owner's shared
constructor **before selected suffix current-source authority**, not only before
orphan disposal/epoch opening. Authenticated page reach does not imply those
objects are held. Missing original installation source remains refusal.

Proposed `fn2-event-archive-prefix-complete-p` must rebind same candidate,
checkpoint, descriptor32/root3fullRef, physical archive namespace and positive
common reach generation, exact contiguous event/batch/root4 coverage and actual
consumed prefix RELEASE constructors. Its final carrier signature depends on
that real constructor; no copied COMPLETE flag or cut-only substitute is valid.
Candidate disposal remains vetoed by either nonidle archive row until that
actual transfer/disposal contract is connected.

An internal installation point reader seeks the expected event/F, verifies its
whole bounded original batch as above under a current completed retained source,
checks exact original J/event, then reuses the shared CHECKPOINT_INSTALLATION
matcher for cp+Ref6+hash and C/Cevent<J/installation-event. No portable peer proof
exists until actual retained inclusion paths are implemented. Canonical records
also retain historical Message-ID/retry/peer semantics; event peaks cannot replace
them.

During witness copying, run completion, header/root4 construction, descriptor
persistence and each bank transition, old raw journal holds remain. Only the
composed persisted descriptor/bank/query/peer/typed-obligation transfer may
release them. Subsequent checkpoints must append old authenticated manifest
intervals plus the new suffix without full-prefix recopy. Fresh base0 is an
intermediate slice. The required two-successive-checkpoint physical reuse
control is still outstanding, and FREE remains off.
