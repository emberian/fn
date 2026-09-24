# Commit-path cost: the owner's commit finds its record by position, 2026-09-24

Lane `lane/commit-path-cost`, from dev `1b734868`. Commits `4f77af5b` (book,
teeth, host call, registry) and `e026414e` (the keystone's proof, 208 s to
0.01 s; no definition changed). This record and its files are in the
evidence commit that follows.

## What the cost was

The served-path lane's POST profile put 60 percent of commit CPU in
`fn-own-finish` (finding 2 of `served-path-cost-2026-09-24.md`). The
mechanism, read off the definitions:

- `fn-sn-completion-record` is `fn-sn-find-record` over the whole durable
  history (`books/store-node.lisp`). For every record it computes
  `fn-sf-record-pair`, and `fn-store-event-sequence` and
  `fn-store-event-txid` each dispatch on the event kind through
  `fn-record-p`, which walks the record's octets. That is O(L) per record,
  so O(N·L) per search.
- One `fn-own-finish` searches 14 times: 4 in its completion gate (2 in the
  core gate and 2 in the consumer/topic gate), 1 in
  `fn-own-completion-names-submission-p`, and 9 inside `fn-own-complete`
  (the gate again, then `fn-sn-finish`'s gate and its record).
- This is not a well-formedness check. It is a lookup whose key
  computation dispatches through the recognizer. The fact that makes it
  unnecessary is already in the invariant.

## The carried fact

`fn-sn-statep` conjoins `fn-sf-statep`, which conjoins
`(fn-sf-record-listp records 0 0 frontier)`. That says every record is a
store event and the record at position i has sequence number i. So the
record whose pair is P can only be at position `(car P)`.

`fn-ccar-seek` steps `(car P)` conses without looking at them and compares
one pair. Per commit that is 8 seeks, each N pointer steps plus one pair on
one record: O(N + L), against O(N·L)·14 before.

| Theorem (`books/owner-commit-carried.lisp`) | Statement | Host line |
| --- | --- | --- |
| `fn-ccar-own-finish-is-own-finish` (keystone) | `(fn-ccar-own-finish o cfg)` equals `(fn-own-finish o cfg)` for every `o` and `cfg`. No hypothesis. The copy has `fn-own-finish`'s guard, `(fn-sn-statep (fn-own-store o))`, and is guard-verified. | `host/owner-host.lisp` `fn-owner-finish-submission` (line 566) calls `fn-ccar-own-finish` at line 571 |
| `fn-ccar-seek-is-find-record` (keystone) | If `(fn-sf-record-listp records seq lower frontier)`, then `(fn-ccar-seek pair records seq)` equals `(fn-sn-find-record pair records)` for every `pair` | reached through `fn-ccar-completion-record` |
| `fn-ccar-completion-record-is-completion-record` | Under `(fn-sn-statep s)`, the carried completion record is `fn-sn-completion-record` | - |
| `fn-ccar-completion-core-enabledp-is-reference`, `fn-ccar-completion-enabledp-is-reference`, `fn-ccar-sn-finish-is-sn-finish`, `fn-ccar-own-complete-is-own-complete` | Each copy equals its reference, with no hypothesis | - |
| `fn-ccar-completion-names-submission-p-is-reference` | Equal under `(fn-sn-statep (fn-own-store o))` | - |
| `fn-ccar-relation-carries-sn-statep`, `fn-ccar-ocl-relation-carries-sn-statep` | `fn-own-relation`, and `fn-ocl-relation` of the configured owner, each imply the guard | - |
| `fn-ccar-own-finish-preserves-sn-statep` (preservation) | If the store satisfies `fn-sn-statep`, so does the store after the carried commit. Nothing else is assumed. | - |
| `fn-ccar-own-finish-preserves-relation` | `fn-own-relation` is preserved across the carried commit. This is a corollary of `fn-own-complete-preserves-relation` and is not registered. | - |

**Why the keystone has no hypothesis.** Both completion gates conjoin
`(mbe :logic (fn-sn-statep s) :exec t)`. Off the premise, both refuse in the
logic. On the premise, the record they find is the same. The premise buys
the executed code:
- The raw functions drop that conjunct, and the carried one runs the seek.
- Guard verification equates each raw function with its logical definition
  wherever the guard holds.
- The guard is `fn-own-finish`'s own. It is carried from open by both owner
  relations and kept by every commit.

No statement was weakened. Every theorem about `fn-own-finish` (among them
`fn-own-240-follows-consumed-completion`) is a theorem about the host's call.

## Teeth (`tests/acl2/owner-commit-carried-tests.lisp`)

- **Witness.** `*osi-completing*` (owner-served-invariants-tests) is reached
  by `fn-own-run` and satisfies `fn-own-relation`.
  - Its history has three records, and the completion pair is at sequence 2,
    so the seek skips two records.
  - The carried commit equals the reference and is `:durable`.
  - The found record is an article record: the last one.
  - The owner moves, and the relation and premise hold after.
- **Mismatch.** The `*osi-mismatch-completing*` witness is still `:fault`.
- **Guards.** All seven carried functions are `:common-lisp-compliant`.
- **The premise.** The same owner's history with its first record dropped:
  - Only `fn-sf-record-listp` fails; the node, the phase and the frontier
    are unchanged.
  - The reference search still finds the record, and the seek finds none.
  - One `must-fail` for each hypothesis:
    - the seek without `fn-sf-record-listp`;
    - the completion record without `fn-sn-statep`;
    - `-names-submission-p` without `fn-sn-statep` (the reference answers
      t on that state);
    - `-preserves-sn-statep` without its hypothesis;
    - `-preserves-relation` without its hypothesis.
- **No hypothesis on the keystone.** It holds on that state too, under
  `with-guard-checking :none`.

## Certification

- **Run.** persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s,
  `--affected-by books/owner-commit-carried`. Run
  `run-20260924T175948Z-c566`, manifest
  `manifests/certify-20260924T180005Z-3125113.json`, status passed.
  - `books/owner-commit-carried` 5.5 s.
  - `tests/acl2/owner-commit-carried-tests` 5.3 s.
- **Dependents.** `--affected-by` selects only these two roots. No other
  book includes the new one.
- **The first run.** `run-20260924T175347Z-3d37`, manifest
  `manifests/certify-20260924T175400Z-3070263.json`, at `4f77af5b`:
  - It passed, but the book took 212 s, of which 208 s was the keystone
    with both gates opened by `:use`.
  - `e026414e` proves the keystone from a forward-chaining fact (the gate
    implies `fn-sn-statep`) in minimal theory.
  - The same run certified `owner-served-invariants`, `owner-feed-subject`,
    `owner-tests` and `owner-served-invariants-tests` at dev bytes, because
    they were missing from the cache.
- **Host.** `host/owner-host.lisp` was translated by the after-image build
  on hbox (certify-20260924T175610Z-1746058 certified the new book in place;
  `proof_artifacts validate` loaded). `tools/host_shape_check.py`: 0
  findings.
- **`make check`.** It passes except `planning/ledger.*` stale. The lane
  does not regenerate the ledger; the coordinator does.

## Measurement (hbox, developer images, 2026-09-24 ~18:00 UTC)

- **Images.** Before: dev `1b734868` (launcher `59d398cb…`, core
  `b8e77938…`). After: lane `4f77af5b` (launcher `1dbf2ca5…`, core
  `bfbd8c65…`). `e026414e` changes only a proof hint, so its image runs
  the same code.
- **Build.** Both were built by `setup.sh`/`build.sh`:
  - roots certified in place from `/tank/fn/certcache`;
  - `proof_artifacts acquire`/`validate`;
  - `tools/build_native_host.sh` under `swarm-build`, with
    `w28/acl2-literal-4g` and OpenSSL 3.5.8.
- **Profiling twin.** Each image has a profiling twin with the served-path
  lane's scratch `sprof-raw.lisp` hook. Its entry is identical to
  `host/native/build.lisp`'s.

**CPU per POST at N = 120.** `prof_post.py`, SBCL sprof, CPU mode, 1 ms.
Samples ÷ profiled POSTs:

| run | before: CPU/POST | before: in `fn-own-finish` | after: CPU/POST | after: in `fn-ccar-own-finish` |
| --- | ---: | ---: | ---: | ---: |
| 24 POSTs (96→120) | 25.5 ms | 21.0 ms (82%) | 19.5 ms | 2.9 ms (15%) |
| 48 POSTs (72→120), r1 | 24.8 ms | 20.2 ms (82%) | 7.3 ms | 1.0 ms (13%) |
| r2 | 28.5 ms | 23.6 ms (83%) | 22.3 ms | 2.8 ms (13%) |
| r3 | 23.7 ms | 19.5 ms (82%) | 6.9 ms | 0.7 ms (11%) |

- **Noise.** The after runs differ by 3× in total samples, while the
  per-function proportions are the same (see the flat and graph files).
  The absolute sample rate is not reliable run to run; the shares are.
- **Before.** The commit took 82 to 83% of POST CPU, 19.5 to 23.6 ms.
- **After.** It takes 11 to 15%, 0.7 to 2.9 ms.
- **The served lane's figure.** It measured 45 ms CPU / 198 ms wall on
  `87846f9e`. dev has moved since, and this box's base measures 24 to
  28 ms.

**POST wall** (`msgid_measure.py`, median of the last quarter; 16 samples
per point):

| N | before | after | articles load before / after | RSS after load before / after |
| ---: | ---: | ---: | --- | --- |
| 16 | 42.2 ms | 50.1 ms | 0.76 / 0.94 s | 0.40 / 0.34 GB |
| 50 | 54.5 ms | 50.2 ms | 4.19 / 4.12 s | 1.02 / 0.43 GB |
| 120 | 58.9 ms | 42.0 ms | 10.01 / 8.77 s | 1.95 / 0.68 GB |

**The cost sentences, with their scope:**

- **Commit.**
  - Before: from the definitions, 14 whole-history searches, each O(N·L),
    with a `fn-record-p` per record. Measured at N = 120: 19.5 to 23.6 ms
    CPU per commit.
  - After: 8 seeks, each N pointer steps plus one pair on one record,
    O(N + L). Measured at N = 120: 0.7 to 2.9 ms.
  - This holds wherever the store satisfies `fn-sn-statep`, which the owner
    relation carries from open.
- **POST wall.** It is I/O bound: fsync and the round trip, about 50 ms at
  every N. Before, the median grew by 16.7 ms from N = 16 to 120. After, it
  is flat within the noise, and the p95 at N = 120 has outliers to 240 ms.
- **RSS after load at N = 120.** It fell from 1.95 to 0.68 GB. This is an
  observation, not a claim: the removed walk allocated octet lists per
  record per search.

## What remains on the commit path (after image, N = 120, share of CPU)

- **`fn-sf-candidatep` → `fn-sf-next-lower` (23 to 26%).**
  - Called by `fn-spc-stage-record` in the prepare (`fn-opc-prepare`), it
    computes the txid of every history record, through `fn-record-p`:
    O(N·L) per POST.
  - Under the same `fn-sf-record-listp`, it equals 1 + the txid of the last
    record, so it is carriable the same way. **Next.**
- **`fn-own-advance-result` → `fn-own-conn-boundedp` → `fn-auth-sessionp` →
  `fn-node-statep` (17%), plus `fn-nntp-projectionp` (5%).**
  - These run on the owner outcome after the 240.
  - This is the served-path lane's carried `fn-scar-conn-boundedp` pattern,
    not yet applied to advance. It is O(N²).
