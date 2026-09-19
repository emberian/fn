# HANDOFF w2/bp-guards (partial — stopped at tool-call budget)

Packet: review §8 C1-01, guard closure without semantic change, on
`books/bp-ingress.lisp`, `books/bp-outbound.lisp`, `books/bp-workflow-records.lisp`.
`books/bp-receipt.lisp` / `books/bp-receipt-records.lisp` not touched (another
lane owns them; `bp-receipt.lisp` includes `bp-ingress`, so its certification
is downstream of this lane's book but no file of its own was edited).

## Method (source is committed; see per-book status below for what is confirmed)

Every function's `:logic` value is byte-identical to its pre-existing body.
Two techniques, both already established in `books/acceptance.lisp` /
`books/store-node.lisp`:
1. Body only applies `car`/`cdr` inside a branch already gated by
   `(consp ...)` on that expression, or only calls guard-`t` functions: plain
   `(declare (xargs :guard t))` + `(verify-guards f)`, no body change.
2. Body applies `car`/`cdr`/`member-equal`/`append`/`1-` to a value not known
   to be a proper list/number: `(mbe :logic <original-body> :exec <same-shape
   body with fn-ag-car/fn-ag-cdr/fn-ag-member/fn-ag-append/fn-bpi-ag-dec>)`,
   `:guard t :verify-guards nil` plus a separate `(verify-guards f)`.

New local helpers in `bp-ingress.lisp` (each proved equal to the function it
substitutes for, by enabling that function's own non-recursive definition —
needed because `fn-record-msgid`/`-payload`/`-groups`/`-obligation-id`/
`-content-subject` and `fn-article-result-article` carry a `(true-listp x)`
guard, not `t`): `fn-bpi-ag-dec`, `fn-bpi-ag-result-article`,
`fn-bpi-ag-record-msgid`, `-payload`, `-groups`, `-obligation-id`,
`-content-subject`.

`bp-ingress.lisp` gained `(include-book "article-properties")` for the
existing theorem `fn-article-successful-parse-syntax-p` (a successful
`fn-article-parse` result satisfies `fn-article-syntax-p`, the guard of
`fn-af-proto-article-check`), cited via `:guard-hints` on
`fn-bpi-ingress-prepare` and `fn-bpi-adu-durably-acceptedp`. No new theorem
proved from scratch.

## Per-book status

- **`books/bp-workflow-records.lisp`**: source edited for all 10 declared-off
  functions (`fn-bp-journal-textp`, `fn-bp-u64p`, `fn-bp-config-recordp`,
  `fn-bp-config-from-record`, `fn-bp-journal-recordp`, `fn-bp-record-event`,
  `fn-bp-record-contextp` plain; `fn-bp-apply-journal-record`,
  `fn-bp-replay-records`, `fn-bp-replay-journal` via mbe). Ledger shows
  `10/0/1/0` (10 verified, 1 pre-existing `fn-bp-journal-nth` left
  `default-guarded`, untouched). **Not independently re-certified after the
  bp-ingress hint fix below** — in the one full-chain run
  (`build/acl2/certify-20260919T100931Z-86942/books--bp-workflow-records.certify.log`)
  the `FN-BP-REPLAY-JOURNAL` guard goal was mid-proof (`Goal'`) when the run
  ended; unclear whether that is a real defect or contention from concurrent
  lanes on this shared box. **Needs a clean, isolated
  `python3 tools/certify_books.py books/bp-workflow-records` run to confirm.**

- **`books/bp-outbound.lisp`**: source edited for both declared-off functions
  (`fn-bpo-decode-receipt` plain, `fn-bpo-receipt-intent-record` via mbe for
  `(car applied)`). Ledger shows `2/0/9/0`. **Not independently certified**:
  in the full-chain run it failed only because it includes
  `bp-workflow-records`, which hadn't produced a `.cert` yet (cascade, not an
  `bp-outbound`-specific defect). Needs its own isolated certify after
  `bp-workflow-records` is confirmed.

- **`books/bp-ingress.lisp`**: source edited for all 35 previously-unguarded
  functions. Ledger shows `35/0/7/0` (7 new `fn-bpi-ag-*` helpers left
  `default-guarded`, same treatment as `fn-ag-car` etc. in `acceptance.lisp`).
  First full-chain attempt failed: `VERIFY-GUARDS FN-BPI-INGRESS-PREPARE`
  hit ACL2's own warning ("using-enabled-rules" — `:use`-ing the already-
  enabled rewrite rule `fn-article-successful-parse-syntax-p`) and the proof
  did not finish within the run
  (`build/acl2/certify-20260919T100931Z-86942/books--bp-ingress.certify.log`,
  truncated at `Goal''`). **Fix applied**: `:guard-hints` on both
  `fn-bpi-ingress-prepare` and `fn-bpi-adu-durably-acceptedp` now disable
  `fn-article-successful-parse-syntax-p` while `:use`-ing it
  (`:in-theory (e/d (fn-article-result-article) (fn-article-successful-parse-syntax-p))`).
  A targeted `python3 tools/certify_books.py books/bp-ingress` was launched
  to check this fix (`build/certify-bpi-only.log`) but had not finished
  before the tool-call budget ran out. **This is the one form most likely to
  still need attention**; re-run that command in isolation first.

## Test books / Makefile

`tests/acl2/bp-ingress-guards-tests.lisp`, `bp-outbound-guards-tests.lisp`,
`bp-workflow-records-guards-tests.lisp` added, each asserting
`:common-lisp-compliant` symbol-class and guard `t` for every function in its
book (including the new helpers), plus malformed-input `assert-event`s, in
the style of `tests/acl2/acceptance-guards-tests.lisp`. Added to the Makefile
right after each book's existing test book. **These three new test books have
not yet been certified at all** (blocked on the books above certifying
first).

## Evidence

`build/certify-baseline.log` + `build/acl2/certify-20260919T100931Z-86942/`
(full-chain attempt, pre-fix); `build/certify-bpi-only.log` (targeted
bp-ingress retry, in flight / outcome unknown at handoff time).
`python3 tools/ledger.py --write` was run after the source edits and its
output is committed.

## What's left for the next lane/session

1. Check `build/certify-bpi-only.log` / re-run
   `python3 tools/certify_books.py books/bp-ingress` alone.
2. If green, `python3 tools/certify_books.py books/bp-workflow-records`
   alone, then `books/bp-outbound` alone (each one-at-a-time, per AGENTS.md).
3. Then the three new guards-tests books, then `make check`.
4. No definition's logic was changed anywhere in this commit; if a guard
   proof still fails, the fix is a hint/lemma adjustment, not a body change.
