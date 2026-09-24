# T17: Message-ID lookup on the served path, 2026-09-24

Lane `lane/t17-msgid-index`, from dev `a35ce928`. Commits `9a021560`
(observe transition), `44d85b44` (dispatcher keystone), `66e87d69` (registry).

## What the served path did before this lane

- **Reader `ARTICLE`/`HEAD`/`BODY`/`STAT <msgid>`** were already indexed. The
  host line is `host/owner-host.lisp` `fn-owner-chunk`, which calls
  `fn-ocfg-read-tls-prefix`. That equals `fn-ocfg-read` by
  `fn-ocfg-read-tls-prefix-is-full-read`, and the chain continues through
  `fn-own-read`, `fn-served-step` and `fn-nntp-archive-command-pinned`
  (`books/nntp.lisp`) to `fn-nntp-msgid-retrieval-indexed`, which calls
  `fn-midx-lookup` on the connection's pinned trie. The trie correspondence is
  a conjunct of `fn-own-conn-okp` and `fn-own-view-okp` inside
  `fn-own-relation`, and `fn-own-step-preserves-relation` preserves it. Nothing
  evaluates it per command. This came from `w28/nntp-msgid-index` and
  `implement/served-msgid-index` through `df60790c`.
- **`IHAVE`/`CHECK` on a peer connection** decide duplicates with
  `fn-peer-history-hasp` (`books/peer-inbound.lisp`). That is `fn-acceptedp`,
  a linear scan of the live node's article list, followed by
  `fn-node-find-binding`, a linear scan of its bindings. The node is swapped in
  on every read by `fn-own-conn-live-session`. **This lane leaves it
  unindexed** (see "Open").
- **Every read, whatever the command,** first went through
  `fnn-owner-handle-chunk`, then `fnn-owner-advance-clock` and
  `fn-owner-observe`, and from there to `fn-owner-step` and `fn-ocfg-step`.
  `fn-ocfg-step` is not guard-verified. Its guard is
  `(fn-sn-statep (fn-own-store ...))`. The saved image runs with
  guard-checking `t` (`host/native/io.lisp`), so the executable counterpart
  evaluates that guard and then the logic body. Tracing one `(:observe obs)`
  call in a live ACL2 session found 2 top-level `fn-sn-statep` calls, 3 raw
  `fn-sn-statep` calls and 3 `fn-node-statep` calls. `fn-node-statep`
  includes `fn-article-listp`'s duplicate check, which is O(N²) in the article
  count N, and the binding/pin cross-checks, which are O(N·B) and O(N·P). So
  every served command paid a whole-store revalidation before it was framed.
  The same trace on `fn-ocfg-observe` finds 0 such calls.

## Theorems

| Name | Statement | Host line |
| --- | --- | --- |
| `fn-ocfg-step-observe-is-fn-ocfg-observe` (`books/owner-config-observe.lisp`) | `(equal (fn-ocfg-step oc (list :observe obs)) (fn-ocfg-observe oc obs))`. No hypothesis. `fn-ocfg-observe` has guard `t` and is guard-verified. This is a subject equation proved by unfolding, not a keystone. | `host/owner-host.lisp` `fn-owner-observe` installs `(fn-ocfg-observe (fn-owner-ocfg state) obs)` |
| `fn-nntp-archive-command-pinned-msgid-arms-are-the-scan` (`books/nntp-pinned-msgid.lisp`) | If `(fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))` and the keyword is ARTICLE, HEAD, BODY or STAT, then `fn-nntp-archive-command-pinned` equals the scanning `fn-nntp-archive-command` for every argument list | reached from `fn-owner-chunk` through the chain above |
| `fn-nntp-message-id-token-is-not-a-number-token` (same book) | A Message-ID token is never a number token. Helper lemma. | - |
| keystone it rests on: `fn-midx-lookup-of-build-is-find-article-for-nonempty` (`books/msgid-index.lisp`, existing) | For a string msgid with a nonempty key, looking it up in the trie built from any article list gives the same result as `fn-find-article` | - |

## Teeth

- `tests/acl2/owner-config-observe-tests.lisp`: a reachable witness, the owner
  after a live group creation (`*ocl-t-created*`). A later reading becomes the
  clock, and the store, configuration and pins are unchanged. The test also
  evaluates the equation on that witness and checks that `fn-ocfg-observe` is
  `:common-lisp-compliant`. A must-fail shows the reading is not ignored. The
  equation has no hypothesis to remove.
- `tests/acl2/nntp-pinned-msgid-tests.lisp`: one accepted article. STAT and
  ARTICLE by its Message-ID give the same answer through the trie as through
  the scan, and a present ID is separated from an absent one. Correspondence
  hypothesis: the empty trie answers 430 where the scan answers 223, plus a
  must-fail. Keyword hypothesis: HDR `:fn-verified` differs between pinned and
  scan, plus a must-fail.

## Certification (persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s)

- `run-20260924T154244Z-3534`, manifest
  `manifests/certify-20260924T154258Z-1926862.json`: status passed, 13 books.
  - Both new books passed: `owner-config-observe` in 3.6 s and its tests in
    3.7 s.
  - Also certified at dev bytes, because they were missing from the cache:
    `nntp-post`, `nntp-pinned-effects`, `peer-inbound`, `nntp-auth`,
    `served`, `owner`, `owner-invariants` (9.5 s), `owner-fault`,
    `owner-config`, `config-owner-live` and its tests.
- `run-20260924T154846Z-3a8d`, manifest
  `manifests/certify-20260924T154857Z-1980701.json`: status passed.
  `nntp-pinned-msgid` took 1.6 s and its tests 2.0 s.
- Dependents: `--affected-by` found no further Makefile roots for either new
  book. Only their test books and the host file include them. The host file
  was translated by the image build below.

## Measurement (hbox, `tools/msgid_measure.py`)

The harness does the following:
- It creates one scratch store and runs `operator run` on a kernel port.
- It posts N articles through one reader connection with POST.
- On a reader connection, it times 16 `STAT` of present IDs spread over the
  store and 16 of absent IDs.
- It then runs a live `peer add` with source address 127.0.0.1 and times 16
  `IHAVE` duplicates (435), 16 `CHECK` duplicates (438) and 16 `CHECK`
  absents on one peer connection.

Each timing is one command line written and one status line read on an open
loopback socket. Process startup is not included.

- **Before:** the p2-wire developer image at `b4dc77d7`
  (`/tank/fn/scratch/p2-wire/tree/build/fn-host-developer`, launcher
  `50092191…`, core `09ed86fa…`).
- **After:** `b4dc77d7` plus this lane's commit `9a021560`, with its Makefile
  and prefixes hunks left out. It was built at `/tank/fn/scratch/t17/after-tree`
  (launcher `5ace0bd4…`, core `3a2aaab2…`).
  - Certificates: 278 of 279 books installed from `/tank/fn/certcache`, and
    `owner-config-observe` certified in place.
  - `proof_artifacts validate --profile default`: `result=loaded`.
  - The developer image was built by `tools/build_native_host.sh` under
    `swarm-build` with the same toolchain (`w28/acl2-literal-4g`) and
    OpenSSL 3.5.8 as before. The scripts are in `t17-msgid-index-2026-09-24/`.
- The A/B differs only by this lane's change. It was not built from the lane
  branch head, which would have mixed in the crash-replay merge.

Median per command, in ms:

| N articles | image | STAT present | STAT absent | IHAVE dup | CHECK dup | CHECK absent |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 16 | before | 0.614 | 0.564 | 0.603 | 0.659 | 0.670 |
| 16 | after | 0.483 | 0.470 | 0.482 | 0.520 | 0.512 |
| 50 | before | 1.345 | 1.274 | 1.264 | 1.298 | 2.077 |
| 50 | after | 1.356 | 1.272 | 1.272 | 1.314 | 1.418 |
| 120 | before | 11.767 | 12.166 | 11.398 | 11.537 | 11.726 |
| 120 | after | 5.059 | 5.000 | 5.038 | 5.132 | 5.277 |

Logs and JSON are in `t17-msgid-index-2026-09-24/`, with these SHA-256
values:

| file | .log | .json |
| --- | --- | --- |
| before-n16 | `bff6d42b…` | `b347c084…` |
| before-n50 | `5a8abba9…` | `70673474…` |
| before-n120 | `a175d222…` | `da297518…` |
| after-n16 | `47bbc74d…` | `98afb993…` |
| after-n50 | `494f60b7…` | `86f1c8d5…` |
| after-n120 | `891cc8c1…` | `850b466e…` |

Load average was 8.5 during the after runs and about 4 during the before
N=120 run. The between-load drift in `planning/scale-profile.md` (about ±20%)
applies.

**The cost sentences, with their scope:**

- **Per-command cost:** at N = 120, the largest store the native CLI can make,
  the change cut every served command's median from about 11.8 ms to about
  5.0 ms. This is 16 samples per point, with an A/B that differs only in
  `fn-owner-observe`.
- **It is still super-linear.** From N = 16 to N = 120 (7.5× the articles),
  per-command time rises about 10.5× after the change (19× before). Some other
  per-read cost remains.
- **The Message-ID lookup is not that cost.** STAT and IHAVE/CHECK stay within
  about 5% of each other at every point.
- **Trie lookup bound** (`fn-midx-lookup` over a builder trie,
  `fn-midx-build-has-unique-branches`): at most (L+1) levels × 257 keys. With
  the 250-octet token ceiling that is 64,507 branch probes, independent of N
  (exponent 0).
- **Scan bound:** the scan it replaces, `fn-find-article`, is N comparisons of
  up to L octets, O(N·L).
- **The IHAVE/CHECK history test is still a scan.** It is O((N+B)·L). On a peer
  connection, `fn-auth-step-pinned` and `fn-own-conn-boundedp` also evaluate
  `fn-auth-sessionp`, and so `fn-node-statep`, on the live node for every
  command and read. That is O(N² + N·B + N·P), with B and P growing with N, so
  the pessimistic per-IHAVE cost is quadratic in N.

**Not measured at N = 1000 or 10000.** The native `store init` writes the
`:development` profile (`books/byte-store-frame.lisp`
`*fn-bs-meta-development-values*`), which caps a store at 128 transactions.
The 4096-transaction `:scale` profile is unreachable from the native CLI. The
first N = 1000 attempt refused article 129 with `441 ... no capacity`. RSS
after load was 0.40 GB at N = 16, 1.02 GB at N = 50 and 1.95 GB at N = 120,
on both images. POST time also grows with N; the owner's commit steps still
run through the unverified `fn-ocfg-step`.

## Open

1. **IHAVE/CHECK through the index.**
   - Design: carry a trie with the live node in the peer session (a seventh
     field, set by `fn-own-conn-live-session` from `fn-midx-refresh` of the
     owner view).
   - `fn-peer-history-hasp` reduces to `fn-acceptedp` under `fn-node-statep`,
     because binding msgids ⊆ article msgids. So the indexed test is one
     `fn-midx-lookup`.
   - Cost: 149 dependents of `peer-inbound` to recertify, plus the wire
     theorems of `peer-inbound-invariants`.
   - It changes no measured number until the per-command `fn-node-statep` in
     `fn-auth-sessionp` is carried rather than evaluated.
2. **The remaining super-linear per-read cost** after this change needs a
   profile of the native owner. Candidates:
   - `fn-own-conn-boundedp`/`fn-auth-sessionp` on every read;
   - the commit-path owner events through `fn-ocfg-step`;
   - `fn-gidx-build` of the whole archive on each `fn-own-refresh`.
3. **Native store profile:** the capacity ceiling makes the plan's
   N = 1000/10000 image measurement impossible until a larger profile is
   reachable from `store init`.
