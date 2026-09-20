# Deputy report: owner-relation (2026-09-20)

HEAD `4ef13d3` on `w10/owner-relation`, from `dev` `99a348c`, merged `dev`
at `9396a86` and `5dbd745`. Full detail:
[`planning/lanes/HANDOFF-w10-owner-relation.md`](../lanes/HANDOFF-w10-owner-relation.md).

## Per root

persvati `run-20260920T224103Z-7c59` on the merged tree (`--jobs 4`,
`--closure`, evidence
`build/acl2/certify-20260920T224106Z-4192084/manifest.json`; the same
verdicts as `run-20260920T222128Z-eedc` and `run-20260920T222651Z-97fc`
before the merge of `w10/dtn-3` and `w10/session-depth`). 73 roots, 72
certified.

| root | verdict |
| --- | --- |
| `books/owner-invariants` | certified, 7.6 s (prove 6.3 s) |
| `tests/acl2/owner-tests` | certified, 166 of 166 `assert-event` |
| `books/owner-config` | OPEN at `fn-ocfg-statep` (`fn-own-relation`'s guards) |
| `books/provenance-codec`, `books/peer-inbound`, `books/nntp-auth`, `books/served`, `books/owner` | certified; none of them was, at `dev` HEAD, before this lane |
| `tests/test_feed.py` | 4 of 4, 9.4 s, laptop |

## Ledger, `dev` `5dbd745` to HEAD

Theorems 5548 -> 5551 (three new `local` lemmas); suspects 45 -> 45;
export-hygiene warnings 72 -> 72; enabled-projection warnings 26 -> 26;
`assert-event` count 5275 -> 5275, of which 166 now execute that never
had. `books/owner-invariants` closure certify wall time: 7.6 s for the
book, the whole 73-root closure under 6 min at `--jobs 4` with 34
installed from the box cache.

## What changed and why

1. `1019c97` merged auth-served's three-wrapper session STATEMENTS over
   peering-inbound-2's two-wrapper HINTS and CITATIONS. Four sites in
   `books/owner-invariants.lisp`; `certify-book` stops at the first, so
   only one was ever seen. No statement changed.
2. `fn-own-auth-base-of-fn-auth-with-base`, `local`: the auth wrapper has
   no exported accessor-of-update lemma where the peer wrapper does.
3. `books/provenance-codec` was the single gate on the whole owner chain
   and no lane held it. Two `local` lemmas, no statement changed.
4. `books/owner-config`'s four accessors were `(car x)` at `:guard t`,
   false at `x = 3`, since the commit that created the book. Repaired to
   the tree's `mbe` idiom; two further defects recorded open.
5. `tests/acl2/owner-tests` was inert (a `deftheory` over a dead name is a
   hard error) and three arity changes behind. No assertion weakened.
6. `tests/test_feed.py` and `tools/run_feed.py`: four never-run defects,
   all host-side.
7. After merging dev: `books/provenance-codec` takes `w10/dtn-3`'s fix
   (deeper cause, subsumes this lane's two lemmas); `tools/session_depth.py`'s
   two `OPEN_DEFECTS` entries for `books/owner-invariants.lisp` are deleted
   because the sites are fixed; and `w10/session-depth`'s 403 fourth
   outcome killed the witness for
   `fn-own-durable-reply-names-a-durable-record`'s
   `(fn-own-find-conn id (fn-own-conns o))`, so that hypothesis has no
   violating value and is deleted from the theorem
   (docs/proof-style.md section 5). The theorem is strictly stronger.

## Proposal (cross-cluster; each with its owner)

1. **auth/served**: export `fn-auth-session-base-of-fn-auth-with-base`
   from `books/nntp-auth.lisp`, beside
   `fn-peer-session-base-of-fn-peer-with-base`.
2. **store/kernel**: guard-verify `fn-snt-relation`
   (`books/store-node-traces.lisp:159`). It is the only thing between
   `books/owner-config` and green.
3. **owner-config's next holder**: `fn-ocfg-reconfig-record`'s generation
   needs an `nfix` and the rewrite that keeps `fn-ocfg-statep`'s staged
   clause true.
4. **tooling**: `tools/certs.py install` accepted 250 pairs whose content
   is not this tree's; re-verify after installing, or hold none in the
   main checkout.
5. **feed**: retire `tools/run_feed.py` for the owner's driver.
