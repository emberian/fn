# Served-path cost: the node recognizer carried, not evaluated, 2026-09-24

Lane `lane/served-path-cost`, from dev `87846f9e`. Commit `6d6bbf34`
(books, host call, registry). This record and its files are in the evidence
commit that follows it.

## Profile: what the per-read cost was

- **How it was measured.** A developer image was built from dev `87846f9e`
  with one extra raw file, `sprof-raw.lisp`. It wraps the entry in SBCL's
  statistical profiler: CPU mode, 1 ms interval, every thread. It was built
  by `build-prof.sh`. The file is scratch only and not part of any image
  shipped. `prof_stat.py` posts 120 articles and then times 2000 `STAT` of
  present IDs on one reader connection. It profiles only that loop:
  5.47 ms per STAT and 10 566 samples.
- **Result** (`stat-n120-graph.txt`, cumulative share of samples):

| function | share |
| --- | ---: |
| `fn-owner-chunk` / `fn-ocfg-read-tls-prefix` | 99.3% |
| **`fn-node-statep`** (inside `fn-peer-sessionp` inside `fn-auth-sessionp`) | **90.9%** |
| `fn-own-finish-read` → `fn-own-conn-boundedp` (two calls per read) | 49.0% |
| `fn-served-dispatch` → `fn-auth-step-pinned` (20.5%), `fn-peer-step-pinned` (21.2%) | 41.5% |
| `fn-ocfg-observe`, `fn-own-observe-outcome` | < 0.1% |

- **Exponent from the definition** (`books/node.lisp` `fn-node-state`):
  - `fn-statep` of the acceptance state checks the article list for
    duplicate memberships. That is O(N²) in the article count N.
  - The binding conjuncts are O(B·N) (`fn-subsetp` of binding Message-IDs)
    and O(N·(B+P)) (`fn-node-articles-have-archive-bindingsp`).
  - B (bindings) and P (retention pins) grow with N. So one evaluation is
    O(N²), and a read made four of them.
- **Where the four evaluations came from.** On a connection that pins a
  node, which the owner's contextual readers and peers both do,
  `fn-own-conn-live-session` swaps the store's node in on every read. Then:
  1. `fn-auth-step-pinned` tests `fn-auth-sessionp`, which evaluates
     `fn-peer-sessionp` and so `fn-node-statep`.
  2. `fn-peer-step-pinned` tests `fn-peer-sessionp` again.
  3. `fn-own-finish-read` tests `fn-own-conn-boundedp` against the store's
     groups and against the archive's groups. Both evaluate `fn-auth-sessionp`.

## The carried premise

The owner already carries the fact. `fn-ocl-relation`
(`books/config-owner-live.lisp`), the configured owner's relation, conjoins
`fn-cst-relation`, which conjoins `fn-sn-statep`, which conjoins
`fn-node-statep` of the store's node. The static owner's `fn-own-relation`
carries it the same way, through `fn-snt-relation`.

| Theorem | Statement | Host line |
| --- | --- | --- |
| `fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation` (keystone, `books/owner-served-carried.lisp`) | If `(fn-ocl-relation oc)`, then `(fn-scar-ocfg-read-tls-prefix oc id octets)` equals `(fn-ocfg-read-tls-prefix oc id octets)` for every `id` and `octets` | `host/owner-host.lisp` `fn-owner-chunk` calls `fn-scar-ocfg-read-tls-prefix` |
| `fn-scar-ocfg-read-tls-prefix-is-reference-under-relation` | The same equality under `fn-own-relation` of the owner | same |
| `fn-scar-ocfg-read-tls-prefix-is-ocfg-read-tls-prefix` | The same equality under `(fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))` alone | same |
| `fn-scar-ocl-relation-carries-node-statep`, `fn-scar-relation-carries-node-statep` | Each relation implies `fn-node-statep` of the store's node | - |
| `fn-scar-ocfg-read-keeps-store` (preservation) | With no hypothesis, the carried read leaves the configured owner's store equal to what it was, so the premise holds after every read. Across commits, the existing `fn-ocl-*-preserves-historical-relation` theorems (open, close, observe, read, advance, complete) carry it. | `fn-owner-chunk` |
| `fn-scar-auth-step-pinned-is-auth-step-pinned` (`books/served-carried.lisp`) | If `(fn-node-statep live)`, then the carried AUTHINFO/STARTTLS step equals `fn-auth-step-pinned` for every session, archive, index, verdicts, config, observation, injection and event | reached from `fn-owner-chunk` through `fn-scar-dispatch` |
| the served chain in `books/served-carried.lisp` | `fn-scar-{peer,auth}-sessionp`, `-peer-step-pinned`, `-auth-delegate-pinned`, `-dispatch`, `-dispatch-events`, `-feed-byte`, `-feed-counted`, `-step-counted-core`, `-step-counted-fast` and `fn-scar-{conn-boundedp,finish-read,own-read-tls-prefix}`. Each equals its reference under `(fn-node-statep live)` and nothing else. | - |

**What changed in the carried functions.** Each copy differs from its
reference in one place, the node conjunct of the session recognizer. The
reference `(fn-node-statep node)` becomes `(or (equal node live)
(fn-node-statep node))`, where `live` is the store's node. No branch is
removed, and no statement is weakened. Every theorem about the reference
functions is a theorem about the host's call on states where the relation
holds. SBCL's `equal` tests `eq` first, and the session holds the very
node `fn-own-conn-live-session` installed, so the conjunct costs one pointer
comparison.

**Where the node premise cannot be carried (finding).** A peer session with
a peer name still goes to `fn-peer-step-pinned` itself, which evaluates
`fn-peer-sessionp` once per event. The reason:
- `fn-peer-command`'s guard is `fn-peer-sessionp`, and
  `fn-peer-decide-offer`'s guard is `(fn-node-statep node)`.
- The host enters ACL2 through the executable counterpart with
  guard-checking `t` (`host/native/io.lisp` `fnn-call`).
- So a guard-verified copy must either evaluate the recognizer or fail guard
  verification. Its top-level guard would also be evaluated on every call.

Removing this evaluation would need one of two changes. Each is a
trust-boundary decision for ember, not a lane's:
- the host calls the raw function under a guard carried from open;
- ACL2 `memoize` of `fn-node-statep`, which is `eq`-keyed per node object.

The IHAVE/CHECK history scan (`fn-peer-history-hasp`) is also untouched. It
is T17's open item 1.

## Teeth (`tests/acl2/owner-served-carried-tests.lisp`)

- **Reachable witness.** `*ocl-t-new-open*` from `config-owner-live-tests`
  satisfies `fn-ocl-relation`. On connection 1, `GROUP fn.live` gives:
  - carried result equal to the reference result;
  - a non-empty reply;
  - the connection kept;
  - the store unchanged.
- **The shortcut is exercised.** The live session's node is non-nil and is
  the store's node.
- **Guards.** All four host-reached carried functions are
  `:common-lisp-compliant`.
- **The hypothesis.** The same owner has its store node replaced by
  `(:not-a-node-state)`. Then `fn-ocl-relation` fails and the carried read
  differs from the reference:
  - the carried read answers `GROUP`;
  - the reference refuses the session, answers nothing and drops the
    connection.
  A ground `must-fail` records the inequality.
- **Session level.** A session holding that node is accepted by
  `fn-scar-auth-sessionp` given that node and rejected by
  `fn-auth-sessionp`. This also has a ground `must-fail`.
- **Store-keeping is not trivial.** The read changes the owner, but not its
  store.

## Measurement (hbox, `tools/msgid_measure.py`, 16 samples per point)

- **Before:** dev `87846f9e` developer image, `base-tree`. Launcher
  `28e63624…`, core `c8471dd2…`.
- **After:** lane commit `6d6bbf34`, `after-tree`. Launcher `eb65fa4f…`,
  core `eede6fcc…`.
- **Build.** Both were built by `build.sh`: certificates from
  `/tank/fn/certcache` (the missing books certified in place), then
  `proof_artifacts acquire`/`validate --profile default`
  (`result=loaded`), then `tools/build_native_host.sh` under `swarm-build`
  with `w28/acl2-literal-4g` and OpenSSL 3.5.8.
- **Runtime environment.** `FN_OPENSSL_PREFIX` and `LD_LIBRARY_PATH`, set by
  `measure.sh`.
- **What the A/B differs by.** This lane's commit only.

Median per command in ms (T17's "after" column is its own image,
`b4dc77d7` plus `9a021560`):

| N | STAT present: T17 after / before / **after** | STAT absent: before / after | IHAVE dup: before / after | CHECK dup: before / after | CHECK absent: before / after |
| ---: | --- | --- | --- | --- | --- |
| 16 | 0.483 / 0.236 / **0.180** | 0.223 / 0.078 | 0.248 / 0.265 | 0.265 / 0.289 | 0.269 / 0.301 |
| 50 | 1.356 / 1.280 / **0.179** | 1.217 / 0.158 | 1.191 / 1.858 | 1.200 / 0.586 | 1.188 / 0.405 |
| 120 | 5.059 / 5.062 / **0.080** | 4.890 / 0.071 | 4.986 / 2.005 | 5.064 / 1.497 | 4.915 / 1.389 |

**The cost sentences, with their scope:**

- **Reader STAT.** From N = 16 to N = 120 (7.5× the articles), STAT went
  from 21.4× (exponent 1.5; T17's image 10.5×) to flat. It was 0.18, 0.18
  and 0.08 ms, exponent about 0 within the ±20% load drift. At N = 120 the
  median fell from 5.06 ms to 0.08 ms.
  - The pessimistic bound by definition is independent of N on the served
    read: trie lookup (T17: at most 64 507 branch probes) and pointer
    comparison. This holds while the session holds the node the owner
    installed, which `fn-own-conn-live-session` does on every read.
  - A session holding any other node falls back to one `fn-node-statep`,
    which is O(N²).
- **Peer IHAVE/CHECK.** At N = 120, 5.0 ms fell to 1.4 to 2.0 ms. The
  measured exponent over 16 → 120 is 0.8 to 1.0.
  - The pessimistic bound stays O(N²): one `fn-node-statep` per event in
    `fn-peer-step-pinned` (the finding above).
  - Add O((N+B)·L) for the history scan.
- **POST.** The medians over the last quarter were 106.6 / 226.8 / 108.8 ms
  before and 113.1 / 152.7 / 128.5 ms after, with no trend. POST is I/O
  bound (below).
- **Memory.** RSS after load is unchanged: 0.40, 1.02 and 1.95 GB at
  N = 16, 50 and 120.

## The other candidates the T17 lane named

- **`fn-own-conn-boundedp` per read.** Carried: it is
  `fn-scar-conn-boundedp` inside `fn-scar-finish-read`.
- **Commit-path owner events through `fn-ocfg-step`'s unverified guard.**
  Profiled on 24 POSTs at N = 120 (`post-n120-graph.txt`, CPU samples only;
  198 ms per POST wall, about 45 ms CPU):
  - `fn-owner-step` has 1.0% of samples. Not a cost at this N.
  - The CPU is in `fn-owner-finish-submission` → `fn-own-finish` (59.6%),
    which calls `fn-sn-completion-enabledp`, then `fn-sn-find-record`, then
    `fn-record-p` on each record of the history (`fn-record-metadata-bytes-p`,
    `fn-record-string-octets-aux`).
  - This is a whole-history recognizer per commit: O(N·L) per POST.
    **Finding, not fixed here.**
  - The remaining 18.5% is POST's command and body lines through
    `fn-owner-chunk` before this change.
- **`fn-gidx-build` of the whole archive on each `fn-own-refresh`.** 0.1% of
  the POST samples. O(N) per commit. Not a cost at this N.

## Certification

- **Farm run.** persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s.
  Run `run-20260924T163520Z-006d`, manifest
  `manifests/certify-20260924T163534Z-2387827.json`, status passed.
  - The three roots: `books/served-carried` 3.0 s,
    `books/owner-served-carried` 3.9 s,
    `tests/acl2/owner-served-carried-tests` 3.8 s.
  - Also certified at dev bytes, because they were missing from that cache:
    `config-owner-live` (8.1 s), `owner-tls-prefix`, `served-tls-prefix`,
    `config-store-traces` and two test books.
  - The remote-root label reads `served-path-cost-65cfb85e`. The label was
    typed before the commit hash was known; the run is of `6d6bbf34`.
- **Dependents.** `--affected-by` on both new books finds only the three
  roots. `green_check --changed-since 87846f9e` shows 3 changed books,
  0 dependents and 0 not green.
- **Host.** The host file was translated by the after-image build (hbox,
  certified in place, `certify-20260924T163600Z-1625136`).
