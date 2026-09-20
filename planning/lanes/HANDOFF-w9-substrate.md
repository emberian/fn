# w9/substrate — the lace projected, the index, policy on transit, epochs

Branch `w9/substrate`, worktree `build/lanes/w9-substrate`, from `dev`
`52eb0db` with `w7/substrate-s1-2`'s three stx fixes cherry-picked (that
lane's work is not merged to `dev` yet; this lane builds on its names and
its certificates, and its registry commit `79cb367` is left to it).

Packets S2 to S5 of [substrate transport](../../specs/substrate-transport.md);
SUB-002 to SUB-005; PRF-021 to PRF-025. The status table is
[section 10 of the spec](../../specs/substrate-transport.md#10-status-packets-s2-to-s5-lane-w9substrate)
and it is where every open obligation is written with its exact shape.
Certification evidence: `tests/evidence/2026-09-20-substrate-transit.md`.

## Certification, hbox, ACL2 8.7

`books/stx-lace` and `books/stx-policy` are **certified**
(`run-20260920T181308Z-0b1b` and `run-20260920T182629Z-333c`); so is the
whole dependency closure, cached on hbox at `/tank/fn/certcache`.
`books/stx-index` is **open** at `fn-stx-index-equivocators-agree`,
`books/stx-epochs` is **open** at `fn-stx-commit-decode-is-a-commit`, and
`books/stx-authority` and `tests/acl2/stx-transit-tests` are cascades of
those two. **The teeth have therefore not run**: they are written and
committed and nothing here may lean on them until the test book certifies.
PRF-019 to PRF-022 and PRF-024 are `in-progress` citing only certified
roots; PRF-023, PRF-025 and PRF-026 stay `planned`.

The first submission of this lane went to persvati before the coordinator
moved the lane to hbox; everything after it is hbox's.

## What landed

- **`books/stx-lace.lisp`** — the lace as the store projected. `fn-stx-parse`
  (the syntax article behind stored octets), `fn-stx-verifiedp` with
  `fn-stx-verifiedp-is-the-verified-verdict` tying it to the verdict the
  evidence slot records, `fn-stx-delta` (a singleton exactly when the
  article's own octets verify under this node's keyring, nil otherwise),
  `fn-stx-store`, `fn-stx-lace` as the oldest-first projection, and the
  bridge `fn-stx-lace-of-accept-is-merge`. S3-1 and S3-2 follow as labelled
  corollaries, including the two membership conjuncts that say neither fork
  is dropped, and `fn-stx-transit-equivocation-survives-later-merges`.
- **`books/stx-index.lisp`** — the incremental twin: three alists, at most one
  cons per accepted article, with `fn-stx-index-agrees-with-lace` (lookup and
  the equivocator predicate) and `fn-stx-index-invariant-preserved-by-accept`.
  The `(:equivocation creator incarnation sequence id-held id-new)` records
  are the third list and `fn-stx-recorded-equivocation-agrees-with-lace` is
  what stops them becoming a second authority. The cost shadow is
  `fn-stx-index-lookup-cost-is-index-bounded` and
  `fn-stx-index-grows-by-at-most-one-binding`.
- **`books/stx-policy.lisp`** — `fn-stx-transit-authority-ok`, the batch
  vocabulary (`fn-stx-accept-batch`, `fn-stx-batch-delta`,
  `fn-stx-lace-of-accept-batch`), the append forms of the three confinement
  lemmas, `fn-stx-peer-batch-cannot-change-policy`,
  `fn-stx-peer-batch-cannot-change-admission`, the constructive
  `fn-stx-batch-policy-change-needs-authority-signature`,
  `fn-stx-transit-admission-is-grounded`, and
  `fn-stx-policy-statement-propagates`. The two typed authority outcomes are
  `*fn-stx-authority-outcomes*`, deliberately not in `*fn-peer-reasons*`.
- **`books/stx-epochs.lisp`** — the commit codec over the `fn-stmt-` item
  vocabulary (five items, bounded before any is parsed),
  `fn-stx-commits-of-batch`, the carrier obligation
  `fn-stx-commits-of-batch-are-verified-and-well-formed`, and the three
  membership-epoch corollaries, each labelled with the keystone it restates.
- **`tests/acl2/stx-transit-tests.lisp`** — the witnesses and teeth.
- **`bin/fn`, `tools/stx.py`** — `fn statement sign|attach|show|verify` and
  `fn principal new|list`; `tools/stx.py` gained `show` and `principal-new`.
  Every value is computed by an ACL2 session; the CLI derives nothing.

## Three departures, each recorded in the spec's status table

1. The two typed reasons do **not** join `*fn-peer-reasons*`: a member of
   that enumeration is a reason to refuse bytes, and an equivocating article
   must be accepted.
2. The bridge lemma carries a freshness hypothesis, because two Message-IDs
   can carry one statement.
3. `fn-inj-prefix` is not edited: a node holds no principal's signing key.

## Open, recorded rather than weakened

- **The host-line equations** (`fn-stx-transit-verdict-is-fn-stx-verdict`,
  and the same obligation standing behind S4-1's renamed
  `-by-definition` row). `fn-peer-transfer` records provenance as a string,
  not as a structured value, so there is nowhere for `(:statement ...)` to
  go. Owner: this lane with the peering cluster; the interface change is a
  structured evidence value carried beside the node, as the index is.
- **`fn-stx-acceptedp` is an observation**, not derived from
  `fn-node-complete`.
- **S6-1 / PRF-026 is not wired**, and deliberately not half-wired: there is
  no slot in which acceptance records a verdict, so `fn-nntp-hdr-content`
  cannot reach one. The three steps to close it are in the status table; the
  nntp chain is independently red at `books/nntp-effects.lisp:971`.
- **`fn-stx-reissue-detected-after-peering`** needs a two-node system model
  (`fn-sys-run`) that does not exist on this tree.
- **SCN-019 was not run.** No scenario was added to `tools/twonode_gate.py`.
- **Independent verification with no fn code** is blocked on D09.
