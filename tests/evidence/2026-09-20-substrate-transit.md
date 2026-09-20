# Substrate transit: the lace projected, the index, policy on transit, epochs

Tool: ACL2 8.7 (`/tank/fn/acl2-8.7/saved_acl2`) on hbox, via
`python3 tools/farm.py submit hbox --remote-root /tank/fn/lanes/w9-substrate`.
Environment on every invocation: `ACL2_CUSTOMIZATION=NONE`,
`ACL2_BOOK_HASH_ALISTP=NIL`. Input revision: branch `w9/substrate`, from
`dev` `52eb0db` with `w7/substrate-s1-2`'s three stx fixes cherry-picked.

The first run of this lane went to persvati (`run-20260920T180143Z-de7b`)
before the coordinator moved the lane to hbox; it certified the dependency
closure and is why hbox's `installed`/`kept` counts are high from the second
run on. Every result below is hbox's.

| Root | Run | Evidence directory | Result |
| --- | --- | --- | --- |
| `books/stx-lace` | `run-20260920T181308Z-0b1b` | `build/acl2/certify-20260920T181311Z-1023611` | certified |
| `books/stx-index` | `run-20260920T183034Z-b081` | `build/acl2/certify-20260920T183037Z-1057241` | **open** at `(defthm fn-stx-index-equivocators-agree ...)`; every form before it, including `fn-stx-index-bindings-agree` and `fn-stx-index-slots-agree`, is admitted in that run |
| `books/stx-policy` | `run-20260920T182629Z-333c` | `build/acl2/certify-20260920T182632Z-1047438` | certified |
| `books/stx-epochs` | `run-20260920T183034Z-b081` | same | **open** at `(defthm fn-stx-commit-decode-is-a-commit ...)`; the codec and its guards are admitted |
| `books/stx-authority` | `run-20260920T183034Z-b081` | same | not reached: cascade from `stx-index` |
| `tests/acl2/stx-transit-tests` | `run-20260920T183034Z-b081` | same | not reached: cascade from `stx-epochs` and `stx-authority` |

## w10/substrate-2 closed the four open roots (2026-09-20)

Tool: ACL2 8.7 (`/home/ember/fn-tools/acl2-8.7/saved_acl2`, SHA-256
`c8a7a804d9cc80e2...`) on persvati, via `python3 tools/farm.py submit persvati
--jobs 4 --remote-root /home/ember/fn-lanes/w10-substrate-2 --affected-by
books/stx-index.lisp --affected-by books/stx-epochs.lisp --closure`, then
`wait`. Per-invocation environment `ACL2_CUSTOMIZATION=NONE`,
`ACL2_BOOK_HASH_ALISTP=NIL`, `ACL2_SYSTEM_BOOKS` unset; per-book timeout
1800 s. Input revision: branch `w10/substrate-2` at `976f0e0`, from `dev`
`c6ebc68` merged with `dev` `f730c24`.

Run `run-20260920T211342Z-aa20`, evidence
`build/acl2/certify-20260920T211346Z-3327395`,
**31 of 31 roots certified, exit code 0**, 128 s wall at `--jobs 4`.

| Root | Result | Source SHA-256 (first 16) | Seconds |
| --- | --- | --- | --- |
| `books/stx-index` | **certified** | `f059904ee7f4deeb` | 0.73 |
| `books/stx-epochs` | **certified** | `0c9becdc14fdfe52` | 0.52 |
| `books/stx-authority` | **certified** | `a11fc976e952bcfb` | 0.65 |
| `tests/acl2/stx-transit-tests` | **certified** | `0dfa13a083b55479` | 0.72 |

The whole include closure certified in the same run: `stx-carrier`,
`stx-verify`, `stx-lace`, `stx-policy`, `statement`, `statement-invariants`,
`lace`, `lace-invariants`, `principal`, `principal-invariants`, `policy`,
`policy-invariants`, `membership-epochs`, `membership-epochs-invariants`,
`article`, `cbor`, `cbor-invariants`, `records`, `records-invariants`,
`crypto-seam`, `defrecord`, `node`, `acceptance`, `acceptance-alloc`,
`retention`, `provenance` and `tests/acl2/crypto-seam-tests`.

Corroborated locally on the laptop (ACL2 8.7, `/opt/homebrew/bin/acl2`,
`tools/certify_books.py`, one root at a time):
`build/acl2/certify-20260920T205912Z-79933` (`stx-epochs`),
`certify-20260920T210944Z-90380` (`stx-index`),
`certify-20260920T211000Z-90581` (`stx-authority`),
`certify-20260920T211258Z-93549` (`stx-transit-tests`).

New limitations this run introduces, beyond those listed below:

- **The S4-1 and S5-1 witnesses in `tests/acl2/stx-transit-tests` were
  vacuous before this run and had never executed.** A statement whose kind
  is not `:article` carries its payload as the article body in base64
  (`fn-stx-payload-for`, `fn-stx-body-payload`), and both carrier articles
  had a prose body, so `fn-stx-delta` was `nil` and every assertion about
  the hostile batch held of an empty delta. Repaired, and the two deltas are
  now pinned by assertions of their own. Any earlier reading of those rows
  should be re-taken from this run.
- **Neither keystone has a host line.** `fn-stx-index-lookup` and
  `fn-stx-commits-of-batch` have no caller outside their books; the
  theorem-subject rule of `AGENTS.md` is not met for PRF-023 or PRF-025 and
  both stay `in-progress`.

Limitations, and they are the point of reading this file next to the claim:

- **Two roots are open and their witnesses have therefore not run.** The
  teeth in `tests/acl2/stx-transit-tests.lisp` are written and committed but
  unexecuted; nothing in this lane's claims may lean on them until that book
  certifies. The two open forms and what each needs are in
  `specs/substrate-transport.md` section 10.
- Every witness runs under the **toy realisers** of
  `tests/acl2/crypto-seam-tests.lisp` (a polynomial mix digest and a
  sign-by-public-key scheme). Nothing here is evidence about unforgeability
  or collision resistance; those are A-CRYPTO. What is evidenced is the
  projection, the merge, the index and the confinement.
- The A-CRYPTO edge is **not** assumed away in the fork witness: the two
  forks are asserted to have distinct content ids under the toy digest,
  which is the hypothesis `fn-lace-merge-drops-at-collision` says the
  detection needs.
- `fn-stx-acceptedp` is an **observation** of the node pair (the store of the
  next node is the store of this one with the accepted article at its head),
  not a theorem derived from `fn-peer-transfer` and `fn-node-complete`. The
  test book exhibits stores in that relation; deriving it from the machine is
  the open obligation recorded in `specs/substrate-transport.md` section 10.
- **No two-node run was made by this lane.** SCN-019's legs (post a signed
  statement on A, relay through a peer that ignores the field, verify on B by
  bytes) are unexecuted; `tools/twonode_gate.py` gained no scenario. The
  reason is budget, and the gap is recorded rather than papered over: the
  single-node fork witness in `tests/acl2/stx-transit-tests.lisp` exhibits
  both forks at one node and says nothing about two.
- Independent verification "with no fn code" (S6's acceptance criterion) is
  not achievable under the toy realiser without a second implementation of
  the digest in Python, which the one-owner rule forbids. It is blocked on
  D09, the deployed realiser.
