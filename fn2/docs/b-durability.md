# fn2 layer B: the crash and log models, the formats, the commit batch, the allocator, recovery, checkpoint, cleaner

Present state, rewritten whole by the layer-B seat. The contract is
`build/coordinator/briefs/FN2-LAYER-B-DURABILITY.md`; the decisions it serves are
`build/coordinator/fn2/EXECUTION-MODEL.md` rule 8, `fn2/EXECUTION-MODEL-ROUND2-ASTRA.md` §E (the
durability protocol) and §F (checkers HISTORY, RECOVERY, RECLAIM; scenarios 13-17),
`fn2/STORAGE-DESIGN.md` (§4 as amended, §7 the decisive demonstration) and the concrete format of
`fn2/STORAGE-DESIGN-ASTRA.md` "The concrete storage format and root-selection algorithm with recovery
invariants" (§A-§J below means that section's lettered parts). Layer A's decisions
(`fn2/docs/a-pool-host-sim.md`) bind this layer too. A departure from a decision that is not
recorded here is a defect.

## 1. Where each piece lives
| piece | file(s) | quest |
|---|---|---|
| crash model (block device, the papers table's faults) | `fn2/books/crash-model.lisp` | B1 |
| log model (abstract history, acknowledgement, allowed recoveries) | `fn2/books/log-model.lisp` | B1 |
| encodings through the records DSL | `fn2/books/records.lisp` (DSL seed), `fn2/books/format.lisp` | B2 |
| commit-batch machine | `fn2/books/commit.lisp` | B3 |
| allocator with typed edges | `fn2/books/alloc.lisp` | B4 |
| recovery | `fn2/books/recovery.lisp` | B5 |
| checkpoint and cleaner machines | `fn2/books/checkpoint.lisp`, `fn2/books/cleaner.lisp` | B6 |
| HISTORY, RECOVERY, RECLAIM checkers | `fn2/sim/check-history.lisp`, `check-recovery.lisp`, `check-reclaim.lisp` | B3-B6 |
| acceptance | `fn2/tests/sim-layer-b.lisp` (+ driver `.lsp`) | B3-B7 |

## 2. Decisions inside the contract
- **B-BLOCK-DEVICE.** The crash model is a block-device model, not a POSIX one: fn2 has one
  preallocated data file or a raw device and no directories, rename, unlink or fsync(dirfd)
  (ENVELOPE §2.3 "What is absent"). The quarry's `books/byte-store.lisp` contributes its outcome
  vocabulary (every operation takes an environment-chosen outcome), its tear rule (a landing write
  cut into write units that land as written, as zeros, or as garbage) and its fsyncgate rule (a failed
  fence lands a torn selection and discards the rest); its inode and directory tables do not carry.
  The file backend is an implementation of the device (ENVELOPE §2.4 row "storage"); file growth is
  absent because the file is preallocated and zero-filled at format.
- **B-MODEL-IS-PREDICATE.** The crash model is ACL2 logic over lists (the list view exists only in
  the logic and in test/checker code; nothing on a served path executes it). It is stated as an
  *allowed-outcome predicate* (`given the trace so far, is this observed image / read result /
  completion allowed?`) rather than as an enumerator, so the simulator's concrete choice is checked
  by membership, trace by trace (ENVELOPE §2.6: "checked against it trace by trace").
- **B-ASSUMPTIONS-AS-PARAMETERS.** `A-PERSISTENCE-FENCE`, `A-INTEGRITY-EVIDENCE` and
  `A-INDEPENDENT-FRONTIER` (ROUND2 §E.5) are explicit fields of the fault profile passed to the
  model and to recovery; recovery's permitted conclusions are a function of them. Layer A's
  `fn2-a-integrity-evidence` (books/assumptions-integrity.lisp) is reused for the checksum premise.
- **B-IDENTITY-EXACT** (ember, 2026-10-28, via the coordinator): exact Message-ID octets are kept
  permanently in the identity metadata with content identity, acceptance binding and conflict
  state; erasure of identities is the operator's matter outside the node's contract; no digest-only
  identity and no aging window (STORAGE-DESIGN §4.6 updated). For this layer: the journal's identity
  records and the identity commitment of the checkpoint claim carry and commit to the exact octets.
- **B-WIDTHS.** As A-WIDTHS: in-memory counters are `u60`; persistent integers use the canonical
  unsigned base-128 encoding of §A (shortest form, numeric order, resumable decode), so no resident
  bignum and no fixed-width namespace ceiling.
- **B-GEOMETRY.** Format parameters, not ceilings: sector `S = 4096` (append and damage-isolation
  unit), tear unit 512 inside it, payload/page block `P = 65536`; the device's write-damage radius is
  a declared profile field of the crash model (default: a torn write damages only units of its own
  sectors; the broad profile admits damage to durable units within the radius of an in-flight
  write, papers table row 6).
