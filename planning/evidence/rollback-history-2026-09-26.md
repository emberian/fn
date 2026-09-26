# rollback-history: `store rollback-check --snapshot` compares history, not counters (PRF-141, SCN-076, PKT-327)

Lane `lane/rollback-history` from dev 8f5f9d0b, 2026-09-26. Brief:
`build/coordinator/queue/w3-rollback-history.txt`, on gpt-6's answers §7
("the rollback checker proves the wrong abstraction") and the mandate's §5.6.
Commits: 85f35331 (book, host, tests), 94579ffc (registry, docs, record, native evidence), b131fd0f (theorems over the host-called composition), 49df0c21 (manifest), and the final evidence commit. `make check-lane` green at 49df0c21 (green_check: 942 of 942 books green at their current digest).

## The misstep, reproduced natively first

Before any change, `tests/test_native_rollback_history.py` (written with the
corrected expectations) ran on hbox against the unrepaired tree (dev 8f5f9d0b
plus only the new test; `tools/hbox_native.sh --label red .`,
/tank/fn/scratch/rollback-history/native-red, developer image
`0b322356c57bc4ac3ea333d60bcc0f7eaf47f26b2725a78a9ca2b05306119186`, core
`8f26936035e2807b46a44dd13cd52e47670a3c071a6836b1d687a4b7a981a250`). Test log
[`red-test.log`](rollback-history-2026-09-26/red-test.log), SHA-256
`d751b651fc459c9b52576272a374e2134d8c9246817a724fb68a570ec2a5d053`
(all SHAs: [`red-SHA256SUMS`](rollback-history-2026-09-26/red-SHA256SUMS)).
Four failures, three of them defects:

| case | old verb | classification |
|---|---|---|
| snapshot: seq 0 `<article-a@...>`; store: seq 0 `<article-b@...>` (same file length, different octets), seq 1 another | `rollback snapshot loses transactions=1 snapshot-transactions=1 store-transactions=2`, exit 0 | implementation: gpt-6's counterexample, natively. The restore would also replace article B with A |
| store compacted after the snapshot was taken (4 records, all 4 files reclaimed into the pack) | `refused snapshot-not-a-prefix`, exit 1 | implementation: the pack was not read (PKT-287) |
| the store's writer lock held exclusively by another process | `accepted`, exit 0 | implementation: both stores were read with no lock |
| a true earlier state | `loses transactions=2`, the old sentence | expected (only the new wording was missing) |

## The repair

- `fnn-rollback-history` (host/native/io.lisp) now takes an acquired store
  and reads its committed history exactly as `fnn-recover-full-replay` does:
  `fnn-durable-records` from `*fnn-pack-lower-bound-callback*`'s lower bound,
  then `*fnn-pack-recover-callback*` (`fnn-pack-recover-records`, i.e. ACL2's
  `fn-store-checkpoint-compaction-observe` over the selected pack and the
  suffix), then `fnn-check-history-marker` over the count. Each element is a
  committed record's exact octets. No `stat-size`, no directory listing of
  lengths.
- `fnn-command-rollback-snapshot` acquires both stores with
  `make-fnn-store :writable nil` + `fnn-acquire` (shared, non-blocking
  `flock` on each `writer.lock`; a held store is refused `store is already
  locked`), holds both locks while reading and comparing, and releases them
  in `unwind-protect`. It calls ACL2 once per snapshot record
  (`fn-native-operator-host-history-step`, the record and the store's record
  at the same position, both octet lists built for that pair only) and then
  `fn-native-operator-host-history-verdict` with the store's record count.
- The sequence/size comparison is gone entirely: not kept as a filter nor as
  an approximate count. Exact comparison needs no collision assumption, so
  none was added to books/assumptions.lisp.
- The report: `loses` now says "the snapshot's committed records are this
  store's first S, compared record by record (packed records included)";
  the refusal says "this snapshot is not an earlier state of this store's
  history ... (equal transaction counts or file sizes do not make them so);
  restoring it would replace this history, not shorten it".

## Assurance chain

native entry `fn operator CONFIG store rollback-check --snapshot SNAP`
-> `fn-native-operator-run` plan `:rollback-snapshot` (unchanged, PRF-130's
parse) -> host/native/operator.lisp -> `fnn-command-rollback-snapshot`
-> observation: `fnn-rollback-history` of each store under its shared lock
(the open's reader, pack included, marker checked) -> executed ACL2 subject:
`fn-native-operator-history-start` / `-step` / `-verdict`, composed in the
host's order (V below; `fn-nop-history-run` is the loop)
-> behavioural theorem `fn-native-operator-history-loss-is-ancestry`
-> observed result: the two report lines and exit 0/1, natively below.
No relation is maintained across calls: the verb observes once under both
locks and decides once (operator commands are not a served path). The
correspondence "the host loop makes exactly these calls" is host code,
source-checked by `RollbackHistorySourceTests`, not proved (PKT-327 (3)).

## Theorems (books/native-operator.lisp, PRF-141)

- `fn-native-operator-history-loss-is-ancestry` (KEYSTONE), over
  V = `(fn-native-operator-history-verdict (fn-nop-history-run (fn-native-operator-history-start) snap cur) (len cur))`:
  ```
  (and (iff (equal (car V) :loses)
            (equal (append snap (nthcdr (len snap) cur)) cur))
       (implies (equal (append snap (nthcdr (len snap) cur)) cur)
                (equal (cadr V) (len (nthcdr (len snap) cur)))))
  ```
  The verb says `loses` exactly when the store's history is the snapshot's
  records followed by more records, and the count is the number of those
  records. Host line: `fnn-command-rollback-snapshot` (host/native/io.lisp)
  through `fn-native-operator-host-history-step` / `-verdict`
  (host/native-operator-host.lisp).
- `fn-native-operator-history-loss-is-snapshot-loss`: V equals
  `fn-native-operator-snapshot-loss` (PRF-130's list-level function; its
  lemma `fn-native-operator-snapshot-loss-counts-the-suffix` stays true and
  now describes records; PRF-130's statement is amended to say the
  descriptor reading was not a history comparison).
- Both theorems are stated over the composition itself, so the functions
  they mention are the host-called ones (`reach_check`); the first cut named
  a wrapper function `fn-native-operator-history-loss`, which no host line
  calls, and `make check-lane` flagged it as an unreachable subject; it is
  gone, and the test book spells V with a macro.
- Every executable function is guard-verified (`:common-lisp-compliant`,
  checked in the REPL: start, step, run, verdict, report).

Teeth (tests/acl2/native-operator-tests.lisp):
- Reachable positive witness: snapshot `(A)`, store `(A C D)`: the
  antecedent `(append snap (nthcdr 1 cur)) = cur` holds, `:loses`, and the
  count equals `(len (nthcdr 1 cur))` = 2; identical histories give 0; the
  host's call sequence (start, one step, verdict with 3) gives `(:loses 2)`.
- The removed sequence/size hypothesis (gpt-6's counterexample): `A` and `B`
  have the same length and leading octets; for snapshot `(A)`, store
  `(B C)` the `(sequence . length)` descriptors agree as a prefix and the old
  verdict over them is `(:loses 1)`, while the ancestry premise is false and
  the verb answers `(:refused :snapshot-not-a-prefix)`; plus a `must-fail`
  of "descriptor prefix implies `:loses`" (with `:do-not-induct`: a refusal
  of proof search is supplementary; the evaluated counterexample is the
  evidence).
- The count's premise removed: on the same pair the count is not the
  suffix's length (evaluated), and a `must-fail` of the unconditional count;
  the same for PRF-130's list lemma.
- A snapshot ahead of the store and one that diverges at a later record
  are refused.

## Certification

| run | box | what | result | manifest |
|---|---|---|---|---|
| run-20260926T064737Z-0e41 | persvati | `--affected-by books/native-operator.lisp` at 85f35331 | passed, 6 certified, 146 installed; native-operator 6.7 s, native-operator-tests 2.7 s, native-mission 2.0 s, native-operator-host 1.9 s; no book over 10 s | [`certify-20260926T064940Z-2305911.json`](manifests/certify-20260926T064940Z-2305911.json) |
| run-20260926T065645Z-3793 | persvati | the same at b131fd0f (the theorems restated over the host-called composition) | passed, 6 certified, 146 installed; no book over 10 s | [`certify-20260926T065706Z-2375300.json`](manifests/certify-20260926T065706Z-2375300.json) |

Proof development: an hbox `proof_repl.py` session over the qualified
w28 toolchain and /tank/fn/certcache (persvati's 16 slots were all held by
other lanes' idle REPL sessions, some over a day old; the laptop's ACL2 is
not a qualified toolchain). The first attempt's induction (on the fold with
a fixed accumulator) failed; a local induction scheme that increments the
matched count closed it. The test book's forms were evaluated in the same
session before the farm run.

## Native (hbox)

`tools/hbox_native.sh --label green 85f35331 tests.test_native_rollback_history`
(/tank/fn/scratch/rollback-history/native-green; developer image
`bb0655b4a81ded95a7ad1ea63179964d6467305ea023da908ba01bdc8ad9f70e`, core
`7ac3b4f6f35723776610806929ba136020bdc992821876d266bedd3d841c6123`): 5 tests
OK in 2.0 s. Test log [`green-test.log`](rollback-history-2026-09-26/green-test.log),
SHA-256 `53f4a11ce9f209336cb34eedaf9ec27dfed004a83db16ad8bd52d0412e50b51c`
(all: [`green-SHA256SUMS`](rollback-history-2026-09-26/green-SHA256SUMS)).

| case | now |
|---|---|
| the counterexample (equal names and file lengths, different first record) | `rollback snapshot refused snapshot-not-a-prefix` / "this snapshot is not an earlier state of this store's history ...", exit 1 |
| a true earlier copy, two posts later | `loses transactions=2 snapshot-transactions=1 store-transactions=3`, exit 0; the store against itself `loses transactions=0`; the reverse direction refused |
| compacted after the snapshot (all 4 files reclaimed into the pack) | `loses transactions=1 snapshot-transactions=3 store-transactions=4`, exit 0, counted through the pack; a same-shape other store (same message-ids, same lengths, different body) refused |
| the store's writer lock held exclusively | refused `store is already locked`, exit 1 |

Rerun at 49df0c21 (after b131fd0f changed the book's bytes: one uncalled
defun removed, the theorems restated; host code unchanged), so the green is
not transferred across changed bytes: /tank/fn/scratch/rollback-history/native-green2,
developer image `3a2cd363672d2aad20251a82ed051c0cc0e437eaafdefa266b6fac569043c332`,
core `031408b6ded340c93cb0b7de9668615e18f00e7b771aac561ff006f251907781`, 5
tests OK in 2.4 s, log [`green2-test.log`](rollback-history-2026-09-26/green2-test.log)
SHA-256 `2926fb6649276679a16587ef5d821ed35e860c756638e9dd38fd04cccc514fb8`
([`green2-SHA256SUMS`](rollback-history-2026-09-26/green2-SHA256SUMS)).

The expected answer of the red case changed from the old verb's `loses 1` to
the refusal because the old answer was the defect (gpt-6 §7); no behavioural
failure was turned green by changing an expectation the old code met.

## Not done (PKT-327)

1. The configuration history is not compared; a restore replaces it too.
   Default: compare the configuration records the same way and report a
   configuration divergence by name beside the transaction verdict.
2. Representation (D27): the compare builds octet lists one pair at a time,
   but the pack path it shares with the open's full replay builds the whole
   history's octet lists. Default: compare through the octet buffer when the
   representation wave gives the open that reader.
3. The host loop's correspondence with `fn-nop-history-run` is
   source-checked, not proved.
4. Chained packs are not on dev; the verb follows
   `*fnn-pack-recover-callback*`, so it reads whatever the open reads, but
   the chained case has no native row yet.
5. What the verb does not claim (docs/operator.md says so): that the
   snapshot is the newest earlier state, anything about the configuration,
   retention or peer state a restore brings back, or freshness (§5.6: a
   store-local comparison is not an anti-rollback witness).

PKT-287 (the pack undercount) is closed by this lane.
