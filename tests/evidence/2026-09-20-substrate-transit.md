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
