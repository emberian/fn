# T17 (b) second half: IHAVE/CHECK duplicate test from the trie, 2026-09-24

Lane `lane/t17-ihave-check`, from dev `00d291d0`. Commits `02b2e455`
(books, host comment, registry), `23949539` (`tools/msgid_measure.py
--nodelay`), `beb52854` (the premise over every owner the host installs).
This record and its files are in the evidence commit that follows them.

## What the peer path did before this lane

- On a peer connection, `IHAVE <id>` and `CHECK <id>` reach
  `fn-peer-command` (`books/peer-inbound.lisp`) through
  `fn-scar-peer-step-pinned` → `fn-peer-step-pinned`. The offer decision
  `fn-peer-decide-offer` answers "have" with `fn-peer-history-hasp`:
  `fn-acceptedp`, a scan of the node's article list, then
  `fn-node-find-binding`, a scan of its bindings. That is O((N + B) · L) per
  offer, N articles and B bindings, L the Message-ID length.
- The node is the store's, swapped into the session on every read by
  `fn-own-conn-live-session`.
- Every peer event also evaluates `fn-peer-sessionp`, and so
  `fn-node-statep` (O(N²)), in `fn-peer-step-pinned`'s first branch. That
  is ember's decision (served-path-cost finding 1) and this lane does not
  touch it.

## Design

The brief's design put a seventh field in the peer session. That changes
`books/peer-inbound.lisp`, which has 166 dependent roots
(`certify_books.py --affected-by books/peer-inbound --dry-run`). The owner
already maintains a trie over its committed view (`fn-own-view-index`,
refreshed by `fn-own-refresh` through `fn-midx-refresh`). This lane passes
that trie and the view's article list down the carried served chain
instead, and leaves the session and `peer-inbound` unchanged.

- `fn-pix-history-hasp msgid node trie arts`: when `msgid` is a nonempty
  string and the node's article list is `equal` to `arts`, the answer is
  `(fn-midx-lookup msgid trie)`. Otherwise it is `fn-peer-history-hasp`.
  `fn-own-refresh` stores the store node's own acceptance in the view, so
  after a refresh the two lists are the same object. SBCL's `equal` then
  answers on its first pointer comparison.
- `fn-pix-decide-offer`, `fn-pix-peer-command` and `fn-pix-peer-step-pinned`
  are the references with that one call changed. All are guard-verified.
- The `fn-scar-` step chain (`books/served-carried.lisp`) takes `trie arts`
  and hands them to `fn-pix-peer-step-pinned`.
  `fn-scar-own-read-tls-prefix` (`books/owner-served-carried.lisp`) passes
  `(fn-own-view-index (fn-own-view o))` and the view archive's articles.
- The host line is unchanged: `host/owner-host.lisp:1367` in
  `fn-owner-chunk` calls `fn-scar-ocfg-read-tls-prefix`. The native host
  reaches it at `host/native/owner.lisp:1446`.

## Theorems (all in certified books; manifests below)

| Name | Statement | Host line |
| --- | --- | --- |
| `fn-pix-history-hasp-is-peer-history-hasp` (keystone, `books/peer-offer-indexed.lisp`) | If `(fn-node-statep node)` and `(fn-midx-correspondencep trie arts)`, then `(fn-pix-history-hasp msgid node trie arts)` equals `(fn-peer-history-hasp msgid node)` for every `msgid`. It rests on `fn-midx-lookup-of-build-is-find-article-for-nonempty` and on `fn-pix-peer-history-hasp-is-acceptedp`: under `fn-node-statep` every binding names an article, so the binding scan adds nothing. | reached from `fn-owner-chunk` through `fn-scar-dispatch` → `fn-scar-peer-step-pinned` |
| `fn-pix-decide-offer-is-peer-decide-offer`, `fn-pix-peer-command-is-peer-command`, `fn-pix-peer-step-pinned-is-peer-step-pinned` | Each copy equals its reference. The step needs only the correspondence, because its own `fn-peer-sessionp` test supplies `fn-node-statep`. | same |
| `fn-scar-*-is-*` (`books/served-carried.lisp`, statements changed) | The nine step functions equal their `fn-served-*`/`fn-auth-*` references under `(fn-node-statep live)` and `(fn-midx-correspondencep trie arts)`. | same |
| `fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation` (statement changed) | Under `fn-ocl-relation` and `(fn-scar-view-indexedp (fn-ocfg-owner oc))`, the carried read equals `fn-ocfg-read-tls-prefix`. `-under-relation` needs `fn-own-relation` alone: it carries the trie (`fn-scar-relation-carries-view-indexedp`, from `fn-own-view-okp`). | `fn-owner-chunk` |
| `fn-oix-ocfg-step-keeps-view-indexed` (preservation, `books/owner-offer-indexed.lisp`) | `fn-scar-view-indexedp` of the owner is kept by `fn-ocfg-step` for every event. The only step that changes the trie is `fn-own-refresh` (`fn-oix-refresh-keeps-correspondence`, over `fn-midx-refresh-preserves-correspondence`). | `fn-owner-step` |
| `fn-oix-own-start-is-view-indexed` and the host-direct lemmas | The premise holds at `fn-own-start` and is kept by every owner `host/owner-host.lisp` installs without `fn-ocfg-step`: `fn-ocfg-observe`, the carried read, `fn-ocfg-open`/`-open-peer`/`-read-step`/`-fault`/`-with-owner`, `fn-pcar-sbud-prepare`, `fn-ccar-own-finish`, `fn-acar-own-outcome`, `fn-own-with-feeds`, `fn-own-configure`, `fn-own-transit-outcome` and `fn-ocl-publish`. | each install site |

The T4 precedent is `fn-sn-finish-preserves-indexedp`
(`books/store-node-invariants.lisp`). The store's statement index follows
the same pattern: an index carried beside the state, the guard of nothing,
and kept by every transition. The Message-ID trie's maintenance is
`fn-midx-refresh`, and here it is proved over the owner's transitions.

## Teeth (`tests/acl2/peer-offer-indexed-tests.lisp`)

- **Reachable witness.** `*pt-node1*` from `peer-inbound-tests` is the node
  after one transit transfer and its durable completion. The session is
  `*pt-ps1*`, and the trie is `fn-midx-build` of its articles.
  - IHAVE of the held id gives `435 duplicate`. CHECK gives `438 <id>`.
  - IHAVE of an absent id gives `335` plus begin-article. CHECK gives
    `238 <id>`.
  - Each result equals `fn-peer-step-pinned`'s.
  - The fast path is the one taken: the lists are equal and the trie finds
    the held id.
  - The four copies are `:common-lisp-compliant`.
- **Correspondence hypothesis.** The empty trie is keyed to the same list.
  The history test answers "absent" where the scan answers "held" (ground
  `must-fail`). At the step, the wrong trie answers 335 where the reference
  answers 435 (`must-fail`).
- **Node hypothesis.** A node has a binding whose Message-ID no article
  has, and `(fn-node-statep ...)` is false. The trie and list agree (both
  empty). The trie answers "absent", and the scan, through the binding,
  answers "held" (`must-fail`).
- **Fallback.** With a list the trie is not keyed to, the answer is the
  scan's.
- **Owner premise.** It holds on `*scar-t-o*` (the reachable configured
  owner of `owner-served-carried-tests`), after its served read, after an
  `fn-ocfg-step :close`, and at `fn-own-start`. A view whose trie is not the
  build of its articles violates it (`must-fail`).

## Certification (persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s)

- `run-20260924T213008Z-d15c` (source `02b2e455`), manifest
  `manifests/certify-20260924T213026Z-777833.json`: status passed, 8 roots.
  - This is `--affected-by` of `served-carried`, `peer-offer-indexed` and
    `owner-served-carried`.
  - Times: `peer-offer-indexed` 4.7 s, `served-carried` 3.8 s,
    `owner-served-carried` 3.9 s, `owner-offer-indexed` 4.7 s,
    `owner-advance-carried` 3.8 s, and tests `owner-served-carried-tests`
    3.9 s, `peer-offer-indexed-tests` 4.0 s,
    `owner-advance-carried-tests` 4.6 s.
  - Wall 24.9 s.
- `run-20260924T213631Z-3119` (source `beb52854`), manifest
  `manifests/certify-20260924T213652Z-841509.json`: status passed, the same
  8 roots plus `owner-offer-indexed`'s new includes.
  - Certified at new bytes: `owner-offer-indexed` 5.1 s and
    `peer-offer-indexed-tests` 4.3 s.
  - `owner-prepare-carried` (4.0 s) was certified at dev bytes because it
    was missing from the cache.
  - The other five roots were installed at bytes the first run certified.
  - Wall 13.4 s.
- `books/peer-inbound.lisp` is unchanged, so its 166 dependents need no
  recertification.

## Measurement

### Served (hbox, `tools/msgid_measure.py --nodelay`, 16 samples per point)

- **Images.** Both are developer images, built by `build.sh` in this
  directory under `swarm-build`: certify the default roots in place from
  `/tank/fn/certcache`, `proof_artifacts validate` (`result=loaded`), then
  `tools/build_native_host.sh`.
  - Base: dev `00d291d0`. Launcher `518a152f…`, core `0b8a0760…`.
  - After: `23949539`. Launcher `01271407…`, core `e539ae56…`.
- **What the A/B differs by.** This lane's first two commits. Both images
  are measured by the after tree's `msgid_measure.py`, so both get
  TCP_NODELAY.
- Load average was 3 to 4.

Median per command, in ms (base / after):

| N | IHAVE dup | CHECK dup | CHECK absent | STAT present |
| ---: | --- | --- | --- | --- |
| 16 | 0.283 / 0.264 | 0.157 / 0.166 | 0.165 / 0.171 | 0.091 / 0.232 |
| 50 | 0.500 / 0.404 | 0.412 / 0.413 | 0.422 / 0.420 | 0.178 / 0.188 |
| 120 | 1.551 / 1.624 | 1.657 / 1.508 | 1.671 / 1.510 | 0.092 / 0.091 |

- **No measurable change on the served path.** Every IHAVE/CHECK point
  differs by at most 20%, in both directions, within the ±20% load drift
  of `planning/scale-profile.md`.
- **What the per-offer cost is.** From N = 16 to N = 120, IHAVE/CHECK grows
  6 to 10× (exponent 0.9 to 1.2) on both images, while STAT stays flat.
  That cost is the per-event `fn-peer-sessionp` → `fn-node-statep` in
  `fn-peer-step-pinned`, O(N²) by definition. It is ember's decision and
  out of this lane's scope.

### The history test alone (persvati ACL2 session, compiled SBCL)

`b1.lisp` and `b3.lisp` build synthetic nodes: N articles and N bindings,
with Message-IDs `<t17-i@example.invalid>`. Loops time each function
(`history-test-repl-timing.txt`). The timer resolution is 0.01 s against
totals of 0.03 to 0.18 s, so the scan figures carry about ±30%.

| N | scan, absent id (articles + bindings) | scan, held id at the end | trie, absent | trie, held at the end |
| ---: | ---: | ---: | ---: | ---: |
| 120 | 2.4 µs | 0.9 µs | 0.25 µs | 0.43 µs |
| 1 000 | 15 µs | 7.5 µs | 0.30 µs | 0.45 µs |
| 10 000 | 150 µs | 75 µs | 0.25 µs | 0.45 µs |

**The cost sentences, with their scope:**

- **Scan, the bound by definition.** `fn-acceptedp` plus
  `fn-node-find-binding` is (N + B) comparisons of up to L octets,
  O((N + B) · L). Measured: linear, exponent 1.0 from N = 1 000 to 10 000.
- **Trie, the bound by definition** (`fn-midx-lookup` over a builder trie,
  `fn-midx-build-has-unique-branches`). At most (L + 1) levels × 257 keys.
  With the 250-octet ceiling that is 64 507 branch probes, independent of N
  (exponent 0). The pointer-equal test on the article list adds one
  comparison.
  - The bound holds while the session node's article list is the view's.
    `fn-own-refresh` makes it the same object at every idle phase.
  - Between a finish and its refresh, the lists differ and the answer is the
    scan's.
  - A structurally equal but unshared list would cost one `equal` walk,
    O(total article size). No owner transition builds one; this is not
    proved.
  - Measured: flat, 0.25 to 0.45 µs, at N = 120, 1 000 and 10 000.
- **Served IHAVE/CHECK.** At N = 120 the history scan is about 2 µs of a
  1.5 ms command, so removing it does not show. The pessimistic per-offer
  bound is still O(N²): one `fn-node-statep` per event in
  `fn-peer-step-pinned`.

## Findings

1. The IHAVE/CHECK history scan was not the served cost at any N the native
   CLI reaches (N ≤ 120 on the development profile). The per-event
   `fn-peer-sessionp` evaluation is. Removing it is ember's decision
   (`served-path-cost-2026-09-24.md`, "Where the node premise cannot be
   carried").
2. `fn-ocl-relation` does not carry the view trie; `fn-own-relation` does.
   The configured owner's keystone now has two premises:
   `fn-ocl-relation` and `fn-scar-view-indexedp`. The second is proved kept
   by every owner the host installs (`books/owner-offer-indexed.lisp`).
   Folding it into `fn-ocl-relation` would touch `config-owner-live` and its
   dependents; it was not done.
3. The fast path's "same object after refresh" is an implementation fact of
   the compiled code, not a theorem. The keystone does not depend on it, but
   the O(L) cost sentence does.
