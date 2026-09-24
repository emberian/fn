# The advance's projection recognizer carried, 2026-09-24

Lane `lane/advance-projection`, from dev `00d291d0`. Commits `be89edf8`
(book, teeth, host comment, prefixes, registry), `35414177` (the measuring
client: `TCP_NODELAY` and per-read `TCP_QUICKACK`), and the evidence commit
that carries this record.

## What the cost was

After commit-path-2, the whole remaining advance on a durable POST was
`fn-nntp-projectionp` (10.4 to 12.6 percent of POST CPU at N = 120). The
re-pin, `fn-acar-own-advance-result`, opens the reader session on the pinned
view's archive with `fn-nntp-open-session`, which records
`(fn-nntp-projectionp archive)`. Its first conjunct is `fn-statep` of the
whole archive:

- `fn-article-listp`: `fn-articlep` of every article, and for each article
  `member-equal` of its Message-ID in `fn-article-msgids` of the rest, which
  conses the rest's identifiers: O(N^2) comparisons and conses, plus O(N L)
  in the article size.
- `fn-articles-freshp`: each article's memberships against every later
  article: O(N^2 M).
- `fn-articles-below-nextsp` and the pending/fenced conjuncts: O(N M).

The other three conjuncts are `fn-nntp-safe-group-listp` of the groups,
`fn-nntp-nexts-boundedp` of the next-number table (both O(G) in the group
count, each group name bounded) and `(len articles)` against the RFC 3977
maximum (O(N) pointer steps).

## The carried fact

`fn-ocl-view-historyp` says the view archive IS `fn-node-acceptance` of a
node that satisfies `fn-node-statep`, and a node state's acceptance field
is an acceptance state. So under the configured owner's relation
`fn-statep` of the view archive is already known; the re-pin keeps the
three cheap conjuncts and drops the fourth.

## Theorems (`books/owner-advance-carried.lisp`)

| Theorem | Statement | Host line |
| --- | --- | --- |
| `fn-acar-nntp-projectionp-is-nntp-projectionp` (keystone, the recognizer) | If `(fn-statep archive)`, then `(fn-acar-nntp-projectionp archive)` equals `(fn-nntp-projectionp archive)` | reached through `fn-acar-open-session` in `fn-acar-own-advance-result` |
| `fn-acar-open-session-is-open-session` | If `(fn-statep archive)`, then `(fn-acar-open-session archive)` equals `(fn-nntp-open-session archive)` | same |
| `fn-acar-view-historyp-carries-view-statep` (keystone, the carried premise) | `(fn-ocl-view-historyp o)` implies `(fn-acar-view-statep o)`, that is `fn-statep` of the pinned view's archive | - |
| `fn-acar-ocl-relation-carries-view-statep` | `(fn-ocl-relation oc)` implies `(fn-acar-view-statep (fn-ocfg-owner oc))` | - |
| `fn-acar-own-advance-result-keeps-view`, `fn-acar-view-statep-after-advance` | the carried advance leaves `fn-own-view` unchanged, so the premise after it is the premise before it | - |
| `fn-acar-own-advance-result-is-own-advance-result`, `fn-acar-own-outcome-is-own-outcome` (hypotheses strengthened) | each equals its reference when the connection the id names holds a session (`fn-acar-conn-sessionp o id`) AND `(fn-acar-view-statep o)` | - |
| `fn-acar-own-outcome-is-reference-under-ocl-relation` (host keystone, statement unchanged) | Under `(fn-ocl-relation oc)`, `(fn-acar-own-outcome (fn-ocfg-owner oc) id word)` equals `(fn-own-outcome (fn-ocfg-owner oc) id word)` for every id and word; the relation now supplies both premises | `host/owner-host.lisp` `fn-owner-outcome` (line 1131) calls `(fn-acar-own-outcome owner id word)` at line 1150 |
| `fn-acar-own-outcome-after-commit-is-reference` (re-proved) | the same equation over `(cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg))`, under `(fn-ocl-relation oc)`: now through `fn-ocmt-post-commit-preserves-ocl-relation`, since the commit refreshes the view | the commit at `fn-owner-finish-submission` precedes the outcome |
| `fn-acar-own-outcome-is-reference-under-relation` (hypothesis added) | under `(fn-own-relation o)` AND `(fn-acar-view-statep o)`; the static owner's view is `fn-own-prefix-archive`, whose acceptance state needs prefix recoverability, which this lane did not prove | - |

The invariant and its life cycle:
- **Stated over** `fn-ocl-view-historyp`, the conjunct of `fn-ocl-relation`
  that pins the view; no new state field and no new recognizer on the path.
- **Advance**: keeps the view (`fn-acar-view-statep-after-advance`).
- **Commit**: `fn-ocmt-post-commit-preserves-ocl-relation` (commit-path-2)
  gives the relation, hence the premise, after the host's commit.
- **Other transitions**: `fn-ocl-open-`, `-close-`, `-observe-`, `-read-`,
  `-advance-` and `-complete-preserves-historical-relation`
  (`books/config-owner-live.lisp`, `config-owner-advance-invariants.lisp`).
- **Open (finding 1)**: no theorem says that the owner the host installs in
  `fn-owner-recover` (`fn-ocfg-make` over `fn-own-configure` of
  `fn-own-start`, owner-host.lisp:179) satisfies `fn-ocl-relation`.
  `fn-own-open-observed-start-relation` gives `fn-own-relation` of
  `fn-own-start`, not the configured relation. This gap is shared by every
  carried keystone stated under `fn-ocl-relation` (served-carried,
  commit-path-2, this lane); it is not introduced here.

## Teeth (`tests/acl2/owner-advance-carried-tests.lisp`)

- **Witness**: the committed configured owner `*acar-t-o*` (3 records, an
  article among them, reached by `fn-ocfg-step` and the host's commit).
  Its view archive satisfies `fn-acar-view-statep`, both recognizers are
  t, the carried and reference open sessions are equal, the re-pinned
  connection 1 records `projected = t`, the advance keeps the view, and
  the premise holds on the pre-commit owner too.
- **Guards**: `fn-acar-nntp-projectionp` and `fn-acar-open-session` are
  `:common-lisp-compliant`.
- **Separating value**: the same owner with a non-article (`junk`) prepended
  to its view archive. `fn-acar-conn-sessionp` still holds, the view
  premise fails, `fn-ocl-view-historyp` and `fn-ocl-relation` fail, the
  carried recognizer is t while `fn-nntp-projectionp` is nil (all three
  cheap conjuncts hold; only `fn-statep` separates), and the carried
  advance is `:advanced`.
- **must-fail, one per new hypothesis**:
  - the recognizer equation without `fn-statep`;
  - the open-session equation without `fn-statep`;
  - the advance equation without `fn-acar-view-statep` (its other
    hypothesis holds);
  - `fn-acar-view-statep` without `fn-ocl-view-historyp` / the relation;
  - the outcome equation without `fn-acar-view-statep`, with a submission
    of connection 1 in flight and its completion consumed.
- The earlier `fn-acar-conn-sessionp` must-fails are unchanged and still
  separate on that hypothesis alone (the view is untouched there).

## Certification (persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s)

- **Run 1** `run-20260924T212031Z-6f8f`, manifest
  `manifests/certify-20260924T212048Z-687123.json`, passed, at `be89edf8`
  bytes, `--affected-by books/owner-advance-carried`:
  `books/owner-advance-carried` 3.9 s, `tests/acl2/owner-advance-carried-tests`
  4.4 s, and the two uncached dependencies `books/owner-commit-carried`
  3.9 s and `books/owner-commit-ocl` 3.9 s.
- **Run 2** `run-20260924T212546Z-4373`, manifest
  `manifests/certify-20260924T212628Z-740206.json`, passed, at `48068356`
  bytes (the two equality rules withdrawn at the export),
  `--affected-by books/owner-advance-carried`: the book 3.9 s, the test
  4.4 s. `--affected-by` selected no other Makefile root.
- `tools/green_check.py --changed-since 00d291d0`: "2 changed books, 0 books
  include one; 0 not green at the bytes a merge would carry."
- **Host**: `host/owner-host.lisp` (comment only) was translated by the hbox
  after-image build; `proof_artifacts acquire`/`validate` passed for the
  default profile (hbox certified `books/owner-advance-carried` in place).
- **`make check`**: its only errors are `planning/ledger.*` and
  `planning/proofs.json` stale (the coordinator regenerates the ledger).

## Measurement (hbox, developer images, 2026-09-24 ~21:25 UTC)

- **Images** (`*-image.sha256` here): before = dev `00d291d0`, launcher
  `ab67fa88…`, core `90e36fec…`; after = lane `35414177`, launcher
  `b44c1d50…`, core `c9203881…`. `48068356` changes only the export
  theory, not a definition. Built by `setup2.sh`/`build.sh` (commit-path-2's
  scripts with this scratch path), with profiling twins.
- **Client**: both images are driven by the lane's `msgid_measure.py`
  (`TCP_NODELAY`, per-read `TCP_QUICKACK`); `prof.sh` imports it too.
- Box load average 4 to 7 during the runs.

**CPU per POST at N = 120** (`prof_post.py`, 48 POSTs from 72 to 120, SBCL
sprof at 1 ms, samples / 48, alternated base/after, 3 rounds):

| round | before | after |
| --- | ---: | ---: |
| r1 | 4.2 ms (200) | 4.1 ms (198) |
| r2 | 5.0 ms (241) | 4.2 ms (201) |
| r3 | 5.4 ms (257) | 4.6 ms (223) |

The absolute sample totals swing with box load (commit-path-2 read 3.5 ms
for its after image on a quieter box; the profiling twin's sampled time also
exceeds the plain image's wall, below). The shares are the stable figure:

| path (graph "Total") | before | after |
| --- | --- | --- |
| `fn-acar-own-outcome` | 10.1 to 11.2% | 0.5 to 0.9% |
| `fn-acar-own-advance-result` | 8.9 to 10.4% | 0 to 0.4% |
| its `fn-nntp-projectionp` / `fn-statep` | 8.9 to 10.0% (`fn-article-listp` 5 to 6%, `fn-articles-freshp` 3.5%) | absent from every graph |
| commit `fn-ccar-own-finish` | 13.3 to 15.5% | 17.9 to 20.2% |
| `fn-owner-submission-intent` | 10.0 to 13.6% | 9.0 to 17.7% |
| `fn-record-p` (all callers) | 16.6 to 17.5% | 19.9 to 21.1% |

At N = 120 the advance fell from 19 to 25 samples per 48 POSTs (0.4 to
0.5 ms per POST) to at most 1.

**Cost sentences, with scope:**
- **The re-pin's projection recognizer.** Before: `fn-statep` of the view
  archive, O(N^2) Message-ID and membership comparisons plus O(N L).
  After: O(N + G) (the article count by `len`, the group list and the
  next-number table). This holds under `fn-ocl-relation` of the
  configured owner (the premise comes from `fn-ocl-view-historyp`); the
  relation's establishment at recovery is finding 1.
- **The whole advance** is now O(N + G) in the archive: the `len` above
  and the connection-list walk; the session check is O(1) (commit-path-2).

**POST wall.** With `TCP_NODELAY` and quick-ack the store on `/tank`
(ZFS) still gives 41.8 ms medians at every N, with p95 196 to 217 ms at
N = 120, before and after (`base-n*.json`, `after-n*.json`). That mode is
not TCP: `phase.py` times POST→340 at 0.1 to 0.2 ms and body→240 at
41.4 to 41.8 ms on `/tank`, and body→240 at 2.42 ms with the store on
`/dev/shm` (same image, same client). The 42 ms is the durable publication
on this ZFS pool (fsync), and commit-path-2's delayed-ACK reading of it was
wrong (finding 2). The first wall figure that measures the server is
therefore the tmpfs one, where fsync is free, which is its scope:

| POST wall, store on tmpfs, median of the last quarter | N = 16 | N = 50 | N = 120 |
| --- | ---: | ---: | ---: |
| before, r1 / r2 | 2.67 / 2.69 ms | 2.65 / 2.57 ms | 3.03 / 2.99 ms |
| after, r1 / r2 | 2.69 / 2.67 ms | 2.64 / 2.55 ms | 2.73 / 2.63 ms |

Before grows by 0.3 to 0.4 ms from N = 16 to N = 120; after is flat within
0.1 ms, which matches the removed 0.4 to 0.5 ms of CPU. Durable POST wall
on the `/tank` store is about 42 ms, set by the medium.

## What remains on the POST path (after image, N = 120)

No whole-state recognizer remains in any after-image graph: no
`fn-statep`, `fn-node-statep`, `fn-sn-statep`, `fn-cst-relation`,
`fn-article-listp` or record-list fold appears. What remains:
- **`fn-ccar-own-finish`, 18 to 20%**: `fn-ccar-sn-finish` and
  `fn-ccar-completion-enabledp`, whose samples are `fn-store-event-p` /
  `fn-record-p` of the one record being completed (O(L)), plus an O(N)
  pointer walk in `fn-ccar-seek`.
- **`fn-owner-submission-intent`, 9 to 18%**: `fn-own-feed-intent-id` over
  the article's octets (O(L)), computed in `fn-own-submission-intent-result`
  and again in `fn-own-submission-intent-records`, which also calls the
  former (finding 3).
- **`fn-record-p` across callers, 20 to 21%**: the same record's
  `fn-record-metadata-bytes-p` recomputed by the prepare, the seek, the
  finish and the completion gate. These are per-article costs repeated,
  not N-dependent.

## Findings

1. **`fn-ocl-relation` is not proved established at recovery.** Every
   carried keystone under it assumes the host's owner satisfies it; the
   theorem for `fn-owner-recover`'s owner is missing.
2. **The 42 ms POST wall mode is the ZFS durable write, not delayed ACK.**
   Measured by phase split and by moving the store to tmpfs. The 200 ms
   tail at N = 120 on `/tank` also survives the client change; it is
   plausibly ZFS transaction-group latency, unmeasured.
3. **Repeated per-article work**: `fn-own-feed-intent-id` twice or more per
   POST, and `fn-record-p` of the same record on four paths.

## Not done

- The static owner's `fn-own-relation` does not carry the view premise
  here (stated as a hypothesis of
  `fn-acar-own-outcome-is-reference-under-relation`).
- The peer arms' per-event `fn-node-statep` is untouched (ember's decision).
- `planning/ledger.*` not regenerated.
