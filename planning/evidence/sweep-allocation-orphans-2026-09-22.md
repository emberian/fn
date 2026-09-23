# The staging sweep after campaign finding F2 (lane t5/sweep, 2026-09-22)

Finding F2 of [the campaign record](campaign-dabebb84-2026-09-22.md): a
death at `frontier-staged-durable` leaves the allocator's stage
`.allocation-<pid>-<hex>` in `staging/`. The sweep removed only `.stage-`
names, so each such death added one file for good. After 65 of them the
66th open failed with exit 4 at the 64-name observation bound, and the
store could not be opened again without someone deleting files by hand. The
host followed the model. The defect was the model's sweep policy.

## The decision, in the model

`books/store-sweep.lisp`:

- **What an orphan is.** A staging name is one beginning with a prefix that
  some host program stages under: `.stage-`, `.allocation-`, `.init-`,
  `.anchor-`, `.checkpoint-`, `.selection-` or `.pack-` (the last also
  covers `.pack-selection-`). In each program the rename or link out of
  `staging/` is the commit. A stage that was never renamed is therefore not
  authority, and one that was renamed is a second name for an inode that
  the final namespace already holds. The source test
  `test_every_prefix_the_host_stages_under_is_an_acl2_staging_prefix`
  checks that every `(fnn-join (fnn-staging store) (format nil ".x-~d…"))`
  in `host/native/` has a listed prefix.
- **The bound applies to a round, not to the directory.** The subject the
  host calls is `fn-sn-sweep-round (s observed overp held)`, which returns
  `(:done removals)`, `(:again removals)` with at least one removal, or
  `(:refused nil)`.
- The theorems:
  - `fn-sn-sweep-round-removes-only-unheld-staging-names`: a round removes
    only names that were observed, carry a staging prefix, and are not held.
  - `fn-sn-sweep-rounds-collect-every-orphan`: assume the kernel gate is
    open, every name is an unheld staging name, and the bound is positive.
    Then the host loop's model `fn-sn-sweep-rounds` ends `(:done nil)` for a
    directory of any length N.
  - `fn-sn-sweep-rounds-keep-every-name-they-may-not-remove`: every name
    that is not an unheld staging name survives, however many rounds run.
  - `fn-sn-sweep-rounds-end-done-or-refused`: the loop never stops
    mid-round. `:refused` means more than `limit` names remain and an
    observation of them removes nothing.
- **Exit codes.** Over the bound with only orphans, the store opens (exit
  0) after two or more rounds. Over the bound with more than one
  observation's worth of unrecognized names, the store is refused (exit 1,
  `staging namespace holds more than 64 names recovery may not remove`).
  Crashes alone cannot produce that state. It is never a fault (4). A
  shared-lock reader does not sweep: it reports one observation as
  `staging-orphans=64+ [...]` and opens.

## The keystone arm (K-sweep), `books/byte-store-keystones.lisp`

Neither `fn-bs-store-relation` nor `fn-bs-scan-store` reads `:staging`.

- `fn-bs-staging-unlink-keeps-relation-and-scan`: an unlink in `:staging`,
  at any name and with any outcome, keeps the byte state related to the
  *same* kernel state and leaves the scan unchanged. The scan covers the
  config, the frontier, the transaction namespace and the records, which
  is everything `fn-sn-open-observed` replays and everything
  `fn-sf-history-recoverablep` is evaluated over.
- `fn-bs-recover-sweep-keeps-relation-at-every-cut`: at every pair of the
  run of `fn-bs-recover-sweep-program` (one unlink and one
  `recovery-stage-unlinked` cut per name, in
  `books/byte-store-programs.lisp`), the kernel is unchanged, the byte
  state is related to it, and the scan is the original.
  These two are supporting lemmas. Their subjects are byte-model
  functions that no host line reaches (`reach_check`), so the registry
  cites only the next theorem.
- `fn-bs-sweep-round-keeps-every-cut-reopenable`: the same statement over
  the names returned by `fn-sn-sweep-round`. At every cut, every crash image
  whose identity history replays reopens through `fn-sn-open-observed`.

Host lines: `host/native/io.lisp` `fnn-sweep-staging` (the round loop),
`fnn-bridge-sweep-round` and `fnn-list-directory-window`, and
`host/store-node-host.lisp` `fn-store-sn-sweep-round`. `fnn-recover` calls
`fnn-sweep-staging` after the fifth recovery barrier, as before.

**Why the book was red, and what changed.** Commit `4857c648` added
`fn-sn-observed-identity-okp` to the kernel's reopen theorems, and
`fn-bs-crash-image-reopens` stopped proving. It and K4 now carry the same
condition over the scanned records. That makes them no weaker and no
stronger than the kernel theorems they stand on.

## Teeth

- `tests/acl2/store-sweep-tests.lisp`:
  - Every host prefix is recognized. `.operator-evidence`, `.incoming-` and
    `allocation-frontier.json` are not.
  - The F2 directory (65 `.allocation-` names) goes `:again`, then `:done`,
    then empty, and so does a directory of 200.
  - One violating value for each hypothesis of the collect theorem:
    - gate closed: `:refused` with all 65 names left;
    - a foreign name: it survives;
    - a held name: it survives;
    - bound 0: `:refused`.
  - The keep theorem's two teeth.
  - 65 foreign names give `:refused`. 64 give `:done` and are reported.
    100 orphans mixed with 10 foreign names end with only the 10.
- `tests/acl2/byte-store-sweep-tests.lisp`:
  - Witness: the `frontier-staged-durable` cut of the real allocator
    program over the concrete metadata seam. The stage is named in
    `:staging`, and the state is related and scans. Unlinking the stage
    removes the name, keeps the relation and keeps the scan, and the sweep
    program's run is related at every pair.
  - Separating tooth: the same unlink in `:root` at the frontier's name
    makes the scan fault and breaks the relation.
  - Relation tooth: an unrelated state stays unrelated.
- `tests/acl2/byte-store-scan-tests.lisp`: its frames are now functions.
  ACL2 ignores the digest attachment while it evaluates a `defconst`, and
  this was the book's own red.

## Tests outside ACL2

- `tests/test_native_recovery.py`:
  - `StagingSweepDecisionTests`: evaluates `fn-sn-sweep-rounds` and
    `fn-sn-sweep-round` through `frame_bridge`, without an image. It ran
    and passed locally.
  - The source-map tests: they now also cover the prefix check. They ran
    and passed locally.
  - `NativeRecoveryFidelityTests` builds the 65-orphan store from files.
    It writes the `.allocation-` names with the frontier's own bytes into a
    freshly initialized store, runs `status` and then `recover`, and adds
    three cases: every prefix, 65 foreign names refused with exit 1, and a
    mixed directory. **Not run.** No developer image exists on this laptop,
    and the class skips with `the developer image …/build/fn-host is
    absent`.

## Certification

The closure runs on persvati used `acl2-literal w25` and remote root
`/home/ember/fn-gates/t5-sweep`:

- `run-20260922T222703Z-1db3`: failed; `store-node` timed out at 300 s.
- `run-20260922T223519Z-2b86`: failed. `store-sweep` spent 439 s in one
  proof because an open 7-prefix recognizer multiplied every case split.
  The recognizer is now closed and the book certifies in 1.9 s.
- `run-20260922T232402Z-4691`: failed. It showed the pre-existing
  `fn-bs-crash-image-reopens` red.
- **`run-20260923T001123Z-0722`, passed**: the final run, without
  `--closure`, over the committed tree `fedcebc7`. It kept 60 cached
  certificates. Its roots were `books/store-sweep`,
  `tests/acl2/store-sweep-tests`, `books/byte-store-programs`,
  `books/byte-store-keystones`, `tests/acl2/byte-store-sweep-tests`,
  `tests/acl2/byte-store-scan-tests`, `books/store-prepare-correspondence`
  and `tests/acl2/store-prepare-correspondence-tests`. The manifest is
  `planning/evidence/manifests/certify-20260923T001126Z-1554636.json`.
  `tools/green_check.py --changed-since dev` reports the six changed books
  green, and every dependent green except
  `tests/acl2/owner-prepare-correspondence-tests`. That book is red in the
  cache from an earlier run; its closure needs nntp books that have no
  cached certificate at this head, so this lane did not certify it.
  The farm printed `unverified: books/byte-store-relation: closure changed
  since certification: books/byte-store-programs.lisp`; green_check counts
  it green at its bytes.

Provisional wave `run-20260922T233533Z-2973`
(`/home/ember/fn-gates/t5-sweep-triage`, budget 800 s) ran over the
earlier bytes. It named three reds in these books, all fixed since:
`fn-bs-staging-del-lookup-elsewhere`, the `defconst` in
`byte-store-scan-tests`, and an `mv-nth` in the new test book. It also
named two timeouts in books this lane did not edit, `store-node-resolution`
and `peer-inbound`, at 800 s. Fifteen books proved and were only waiting
on those, including `store-prepare-correspondence`,
`owner-prepare-correspondence` and `native-operator`.

## Open

- The image measurement: `NativeRecoveryFidelityTests` on a developer
  image built from this tree. Six of its tests (every one but the ACL2
  bridge fixture's) passed on the `da5fd8cb` developer image on 2026-09-23;
  see [the second campaign](campaign-da5fd8cb-2026-09-23.md).
- A byte-level tooth for the identity hypothesis of
  `fn-bs-crash-image-reopens`. The kernel-level tooth is store-observed's.
- `fn-sn-sweep-rounds` observes `(take limit dir)` in list order. The host
  observes the first `limit` readdir entries, and those may be reordered
  after unlinks. The collect theorem's hypothesis does not depend on
  order, but the model loop fixes one order.
- The bp and tcpcl stages (`.incoming-`, `.record-`, `.frontier-`,
  `.authored-`) live in their own directories, not `staging/`, and are not
  swept by this book. They may accumulate the same way.
- `owner-prepare-correspondence` and the image books above `store-sweep`
  were not certified by this lane. Their closure needs the nntp books,
  which have no cached certificate at this head.
