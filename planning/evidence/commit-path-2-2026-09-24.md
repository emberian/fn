# Commit path, part 2: the prepare's txid fold and the advance's session check carried, 2026-09-24

Lane `lane/commit-path-2`, from dev `7bd50329`. Commits `f8c877c4` (books,
host calls), `02685354` (teeth, Makefile roots, prefixes, the staged premise
dropped), and the evidence commit that carries this record.

## What the cost was (from the commit-path lane's profile)

- **Prepare.** `fn-owner-prepare` installs `fn-sbud-prepare` →
  `fn-opc-prepare` → `fn-spc-prepare` → `fn-spc-stage-record` →
  `fn-sf-candidatep`. The candidate test compares the record's txid with
  `(fn-sf-next-lower records 0)`, a fold that computes
  `fn-store-event-txid` of every history record through `fn-record-p`:
  O(N·L) per POST.
- **Advance.** On a durable outcome, `fn-own-outcome` re-pins the posting
  connection through `fn-own-advance-result`, which tests the rebuilt
  connection with `fn-own-conn-boundedp` → `fn-auth-sessionp` →
  `fn-peer-sessionp` → `fn-node-statep` of the node the session carries:
  O(N²). The served-path lane's carried check compares that node with the
  store's live node, and that comparison would miss here. The session
  carries the node from when the connection last read, and the commit has
  since installed a new one (tests: `*acar-t-conn*`).

## The carried facts

- **The fold needs no invariant.** Each step of `fn-sf-next-lower` discards
  its accumulator. So from 0 the result is 1 + the txid of the last record,
  or 0 on an empty history. `fn-sf-record-listp` makes the value
  meaningful, because the txids increase. It is not what makes the two
  values equal.
- **The advance reuses a check the owner already made.** The rebuilt
  session is the held session with its innermost post session replaced.
  `fn-auth-with-base` over `fn-peer-with-base` keeps the peer, the node, the
  configuration, the transfer and the in-flight count.
  - The held session already satisfies `fn-auth-sessionp`, under both owner
    relations: `fn-ocl-conns-historyp` and `fn-own-conns-okp` each conjoin
    `fn-own-conn-boundedp`.
  - So `fn-scar-conn-boundedp` is passed the held session's node as `live`,
    and the node conjunct costs one pointer comparison.

## Theorems

| Theorem | Statement | Host line |
| --- | --- | --- |
| `fn-pcar-sbud-prepare-is-sbud-prepare` (keystone, `books/owner-prepare-carried.lisp`) | `(fn-pcar-sbud-prepare oc record budget)` equals `(fn-sbud-prepare oc record budget)` for every configured owner, record and budget. No hypothesis. It keeps the same guard and is guard-verified. | `host/owner-host.lisp` `fn-owner-prepare` (line 340) installs `(fn-pcar-sbud-prepare before record budget)` at line 386 |
| `fn-pcar-next-lower-is-next-lower` (keystone, same book) | `(fn-pcar-next-lower records)` equals `(fn-sf-next-lower records 0)` for every value. No hypothesis. | reached through `fn-pcar-candidatep` |
| `fn-pcar-candidatep-is-candidatep`, `-stage-record-is-stage-record`, `-spc-prepare-is-spc-prepare`, `-opc-owner-prepare-is-opc-owner-prepare`, `-opc-prepare-is-opc-prepare` | Each copy equals its reference. No hypothesis. | - |
| `fn-pcar-sbud-prepare-preserves-owner-relation` (corollary, not registered) | `fn-own-relation` of the owner is preserved across the carried prepare | - |
| `fn-acar-scar-auth-sessionp-of-rebuilt-session` (keystone, `books/owner-advance-carried.lisp`) | If `(fn-auth-sessionp as)`, then the session rebuilt from `as` with any new innermost base satisfies `fn-scar-auth-sessionp` at `as`'s node exactly when it satisfies `fn-auth-sessionp` | reached through `fn-acar-own-advance-result` |
| `fn-acar-own-advance-result-is-own-advance-result`, `fn-acar-own-outcome-is-own-outcome` | Each is equal to its reference when the connection the id names, if any, holds a session (`fn-acar-conn-sessionp o id`) | - |
| `fn-acar-own-outcome-is-reference-under-ocl-relation` (keystone for the host) | Under `(fn-ocl-relation oc)`, `(fn-acar-own-outcome (fn-ocfg-owner oc) id word)` equals `(fn-own-outcome (fn-ocfg-owner oc) id word)` for every id and word | `host/owner-host.lisp` `fn-owner-outcome` (line 1111) calls `(fn-acar-own-outcome owner id word)` at line 1127 |
| `fn-acar-own-outcome-after-commit-is-reference`, `fn-acar-own-outcome-is-reference-under-relation` | The same equation over the owner the commit installs (the commit keeps the connections, `fn-acar-own-finish-keeps-conns`), and under `fn-own-relation` | - |
| `fn-acar-ocl-relation-carries-conn-sessionp`, `fn-acar-relation-carries-conn-sessionp` | Each owner relation implies the premise | - |
| `fn-ocmt-sn-finish-preserves-cst-relation` (keystone, `books/owner-commit-ocl.lisp`) | `(fn-cst-relation s)` implies `(fn-cst-relation (fn-sn-finish s))`, on every arm of `fn-sn-finish` | - |
| `fn-ocmt-post-commit-preserves-ocl-relation` (keystone, finding 3) | `(fn-ocl-relation oc)` implies `(fn-ocl-relation (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg))))` for every `cfg`. A staged configuration record is carried through. | `fn-owner-finish-submission` (line 575) computes `(fn-ccar-own-finish (fn-ocfg-owner oc) (fn-ocfg-config oc))` at line 580 and installs `(fn-ocfg-with-owner oc (cdr result))` through `fn-owner-replace-core` at line 581 |

**Finding 3 is closed.**
- **The gap.** Before this lane, `books/config-store-traces.lisp` proved
  only that open establishes `fn-cst-relation`. No theorem said that any
  store step keeps it.
- **The store step.** The completing arm's `fn-cst-completion-linkp` is the
  equation between the node `fn-sn-finish` installs and the replay of the
  unchanged history:
  - the article arm, through `fn-sn-finish-is-actual-durable-completion`;
  - every other arm, through `fn-snt-finish-is-the-applied-event`.
- **The owner step.** It refreshes the view to the whole history, whose
  replay the store relation now names, and appends the committed pair to the
  ledger.

## Teeth

**`tests/acl2/owner-prepare-carried-tests.lisp`**
- **Witness.** `*own-taken*` after its POST's four frontier events.
  - The store is `:reserved` with 2 records.
  - The carried prepare equals the reference and stages the record.
  - At budget 2 it is the identity.
  - A record at the wrong txid is refused by both.
- **The fold.**
  - It equals 1 + the last record's txid.
  - It holds on a swapped list that `fn-sf-record-listp` refuses, which
    shows that no invariant is spent.
  - `must-fail`: with another start value on the empty history.
- **Guards.** All seven carried functions are `:common-lisp-compliant`, and
  their guards are the references' guards.
- **Preservation.** `must-fail`: the preservation corollary without its
  relation, on the owner with its first record dropped.

**`tests/acl2/owner-advance-carried-tests.lisp`**
- **Owner witness.** `*osi-completing*` committed through the carried
  commit. The carried outcome at connection 4 with `:durable` equals the
  reference and renders the 240.
- **Configured witness.** `*scar-t-oc*` driven through one POST's store
  events by `fn-ocfg-step`, to `:completing` with an article record, then
  committed.
  - `fn-ocl-relation` holds before and after.
  - Connection 1 carries the node from its open, not the post-commit node.
  - The carried advance equals the reference and is `:advanced`.
- **Guards.** The carried functions are guard-verified.
- **The premise.** Connection 1's session is given a non-node.
  - The connection no longer holds a session, and the relation fails.
  - The carried advance is `:advanced`; the reference is `:refused`.
  - `must-fail` for:
    - the advance equation without the premise;
    - the rebuilt-session keystone without `fn-auth-sessionp`;
    - the relation-carries-premise lemma without the relation;
    - the outcome equation without the relation (a submission of
      connection 1 in flight with a consumed completion).
- **Finding 3.**
  - On the witness, `fn-cst-relation` holds before and after
    `fn-sn-finish`, the completion record is an article, the phase returns
    to `:ready`, the 3 records are kept, and the node moves.
  - `must-fail` for:
    - `fn-cst-relation` after finish on the store with its node replaced;
    - `fn-ocl-relation` after the host's commit on the configured owner
      with that store.

## Certification (persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s)

- **Run 1.** `run-20260924T182719Z-0173`, manifest
  `manifests/certify-20260924T182731Z-3371907.json`, passed.
  - `books/owner-prepare-carried` 4.1 s and `books/owner-advance-carried`
    3.8 s, at their current bytes.
  - `books/owner-commit-ocl` 3.9 s, at `f8c877c4` bytes. These bytes are
    superseded.
- **Run 2.** `run-20260924T183305Z-9e1c`, manifest
  `manifests/certify-20260924T183317Z-3429911.json`, passed, with
  `--affected-by` for all three books.
  - `books/owner-commit-ocl` 4.1 s.
  - `tests/acl2/owner-prepare-carried-tests` 4.5 s.
  - `tests/acl2/owner-advance-carried-tests` 4.3 s.
  - `--affected-by` selected no other root.
- **Host.** `host/owner-host.lisp` was translated by both hbox image builds.
  `proof_artifacts acquire`/`validate` loaded the default profile, with 288
  books after.
- **`make check`.** Its only errors are `planning/ledger.*` stale. The
  coordinator regenerates the ledger.

## Measurement (hbox, developer images, 2026-09-24 ~18:37 UTC)

- **Images.**
  - Before: dev `7bd50329`, launcher `9fa992ef…`, core `c16ceb5e…`.
  - After: lane `02685354`, launcher `0c7c9ec1…`, core `aac590de…`.
- **Build.** Both were built by `setup2.sh` (default-profile roots certified
  in place from `/tank/fn/certcache`), `build.sh` and
  `tools/build_native_host.sh` under `swarm-build`, with
  `w28/acl2-literal-4g`.
- **Profiling twin.** Each image has a profiling twin with the served-path
  lane's sprof hook.
- **Scripts.** The commit-path lane's, in `commit-path-2-2026-09-24/`.

**CPU per POST at N = 120.** `prof_post.py`, 48 POSTs (72→120), SBCL sprof
at 1 ms. Samples ÷ 48, alternated base/after, 3 rounds:

| round | before: CPU/POST | after: CPU/POST |
| --- | ---: | ---: |
| r1 | 5.5 ms | 3.6 ms |
| r2 | 5.7 ms | 3.6 ms |
| r3 | 5.6 ms | 3.5 ms |

Shares of total samples (graph "Total" column):

| path | before | after |
| --- | --- | --- |
| prepare (`fn-spc-prepare` / `fn-pcar-spc-prepare`) | 23.0 to 23.9% | 2.9 to 5.4% |
| its candidate test | 21.2 to 22.0% (`fn-sf-next-lower` 20.4 to 20.9%) | 1.7 to 3.0% (`fn-pcar-next-lower` 0.6%) |
| advance (`fn-own-advance-result` / `fn-acar-...`) | 21.5 to 23.5% | 10.4 to 12.6% |
| its session check | 14.6 to 16.8% (`fn-node-statep`) | at most 1.7% (`fn-scar-conn-boundedp`) |
| its `fn-nntp-projectionp` | 4.7 to 8.0% | 10.4 to 12.6% (the whole remaining advance) |
| commit (`fn-ccar-own-finish`) | 9.1 to 12.3% | 18.4 to 18.6% |

In milliseconds at N = 120:
- The prepare fell from about 1.3 ms to about 0.1 to 0.2 ms.
- The advance's session check fell from about 0.9 ms to at most 0.06 ms.
- The advance is now about 0.4 ms, all of it `fn-nntp-projectionp`.

The sample totals were stable here, 264 to 274 before and 167 to 174 after.
The commit-path lane saw 3× swings, so the shares are the safer figure.

**The cost sentences, with their scope:**
- **Prepare's candidate test.**
  - Before: O(N·L), a `fn-record-p` per history record.
  - After: O(N + L), N pointer steps to the last cons and one txid.
  - This holds for every state; no invariant is used.
- **Advance's session check.**
  - Before: O(N²), `fn-node-statep` of the held session's node.
  - After: one pointer comparison plus shape checks, O(1) in N.
  - This holds under `fn-ocl-relation` of the configured owner, which open
    establishes and every transition keeps. The POST commit keeps it by this
    lane's `fn-ocmt-post-commit-preserves-ocl-relation`.
- **CPU per POST at N = 120.** It fell from 5.5 to 5.7 ms to 3.5 to 3.6 ms,
  about −36%.

**POST wall is not a CPU measure here.** `msgid_measure.py` reports 16
samples per point. Medians are for the first and last quarter.
- **Before.** 41.7 to 42.0 ms at every N. At N = 120 the p95 is 206 to
  208 ms.
- **After, run 1.** 41.8 ms at N = 120.
  - N = 16: the first quarter is 43.7 ms and the last quarter is 221 ms.
  - N = 50: the first quarter is 212.5 ms and the last quarter is 41.8 ms.
- **After, run 2.** N = 16 and N = 50 are 200 to 224 ms in both quarters;
  N = 120 is 41.8 ms.
- **Why this is not the lane's change.** The two modes, about 42 ms and
  about 200 ms, are the Linux delayed-ACK timer values. Before also shows
  the 200 ms mode, in its N = 120 p95. The CPU per POST is 3.5 ms. The wall
  is set by the TCP exchange with the one-connection client, not by the
  owner. The lane's change cannot add 160 ms of compute, and the profile
  shows none.
- **Consequence.** No wall figure is claimed. A client with `TCP_NODELAY`
  and quick-ack is what would make POST wall measure the server.

## What remains on the POST path (after image, N = 120, share of CPU)

- **`fn-ccar-own-finish`: 18.5%.** The commit's own seeks and the finish.
- **`fn-nntp-projectionp` in the advance: 10.4 to 12.6%.**
  - `fn-nntp-open-session` of the view archive runs `fn-statep` of the whole
    archive: `fn-articles-freshp` and `fn-article-listp`, O(N²) and O(N·L).
  - Under `fn-ocl-view-historyp` the view archive is `fn-node-acceptance`
    of a node that satisfies `fn-node-statep`. The whole-archive part of
    the projection recognizer is therefore carriable the same way. That is
    the next packet.
- **Not touched.** The peer arms' per-event `fn-node-statep`, as ember
  decided.
