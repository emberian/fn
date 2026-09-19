# Deputy report: NNTP surface (wire, article, wildmat, nntp, transfer)

HEAD `a31ed5f` (dev), lane branch `dep/nntp`, worktree `build/lanes/dep-nntp`.

## What certifies

| Root | Before (farm) | After (laptop) |
| --- | --- | --- |
| `books/wire` | 5.5 s | **1.3 s** |
| `books/wire-invariants` | 0.8 s | **0.7 s** |
| `tests/acl2/wire-tests` | 0.1 s | **0.1 s** |
| `books/nntp-syntax` | — | **0.3 s** |
| `books/nntp-session` | — | **0.3 s** |
| `books/nntp-projection` | — | **0.5 s** |
| `books/nntp-responses` | — | **0.4 s** |
| `books/nntp` | 0.8 s (whole file) | **0.3 s** (dispatcher only; 1.8 s for the five) |
| `books/nntp-invariants` | 393.5 s | PENDING |
| `books/nntp-effects` | 62.5 s | PENDING |
| `books/transfer-reservation` / `-union` / `-invariants` | 2.8 s (one book) | PENDING |

**`books/nntp.lisp` did not certify on `dev` before this lane touched it.** The
pre-split file, taken from `a31ed5f` and certified unchanged as
`books/nntp-probe`, fails at `fn-nntp-group-low-is-available` exactly as the
split chain did. The cause is core's record opacity: when `fn-article-msgid`
was `(car x)`, `(stringp (fn-article-msgid a))` forced `(consp a)` by type
reasoning, and withdrawing the definition rune takes that inference away, so
every projection proof that needed an article to be a cons lost it.
`books/nntp-projection.lisp` now states that bridge once, locally, as a
forward-chaining rule on `(fn-article-msgid article)`. **core owns the general
fix**: export the shape-to-`consp` fact alongside the record lemmas, or every
includer of an opaque record will re-derive it.

## Wall times

Before, from `~/fn-gates/dev-0a16592/build/acl2/certify-20260919T183731Z-1508473/manifest.json`
on persvati (Linux, ACL2 8.7, 16 jobs): the two the brief asked for are
`books/article-properties` **577.3 s** (the tree's slowest book) and
`books/nntp-invariants` **393.5 s**; then `article-invariants` 136.4,
`article-work` 93.7, `nntp-effects` 62.5, `article-work-scanners` 47.8,
`wire` 5.5, `nntp` 0.8, `wire-invariants` 0.8. The row's 39 books total
**1418.2 s**.

After, on this laptop (ACL2 8.7, SBCL 2.6.8, one job, so not comparable to the
farm in absolute terms): `books/wire` 5.5 s -> **1.3 s**, `books/wire-invariants`
**0.7 s**, `tests/acl2/wire-tests` **0.1 s**; closure **2.1 s**.

## What changed

- **`books/wire.lisp`: three opaque records.** `fn-wire-state-shapep`,
  `fn-wire-result-shapep` and `fn-wire-next-shapep` are new; every accessor is
  now total (`:guard t`) over the two `fn-wire-ag-` selectors, which are their
  logical primitives by `mbe`, so no caller incurs a `true-listp` obligation to
  read a field. Each record has its shape lemma and one
  `fn-<field>-of-fn-wire-make-<rec>` per field, and then
  `(in-theory (disable (:d ...)))`. `fn-wire-statep` is written over the shape
  predicate instead of `(and (true-listp x) (equal (len x) 8))`, so it is no
  longer a `len`-backchaining invitation. Hints no longer enable a constructor:
  enabling it turns the record into a `list` term and the record lemmas stop
  firing (that is what broke `fn-wire-close-is-statep` first).
- **`books/wire.lisp` export theory.** `fn-wire-step-vocabulary` withdraws the
  recognizer, the initial state and every transition. Keystones, record lemmas,
  the list-recursive vocabulary and the `fn-wire-ag-` selectors stay enabled.
- **One new guard fact, `:rule-classes nil`**:
  `fn-wire-result-events-of-a-true-list-is-a-true-list`, cited by `:use` from
  `(verify-guards fn-wire-continue)`. It exists only to discharge a guard.
- **`books/wire-invariants.lisp`** opens the step vocabulary and the three
  records *locally*, and says so: it is the one book that reasons about how a
  step's pairing splits across a chunk boundary. It ends with an export theory
  that withdraws `fn-wire-drive` and the suffix vocabulary under
  `fn-wire-invariants-vocabulary`.
- **`books/nntp.lisp` split** (1506 lines) into `nntp-syntax` (497),
  `nntp-session` (345), `nntp-projection` (375), `nntp-responses` (316) and
  `nntp` (121, the dispatcher: `fn-nntp-archive-keywordp`,
  `fn-nntp-session-command`, `fn-nntp-archive-command`, `fn-nntp-command`,
  `fn-nntp-step`). All 286 events are preserved with their order and their
  `verify-guards`; each part ends with a `fn-<book>-vocabulary` export theory
  and `nntp-invariants`, `nntp-index` and the three test books re-enable all
  five in one line. `nntp.lisp` is still the top: an includer sees every name.
- **`books/transfer-invariants.lisp` split** (1058 lines) into
  `transfer-reservation` (212), `transfer-union` (467) and
  `transfer-invariants` (383), at the banner seams; `transfer-invariants` stays
  the top of the chain.
- **Eight bare general `must-fail` teeth deleted** from
  `tests/acl2/nntp-tests.lisp` and `tests/acl2/nntp-index-tests.lisp`. Each one
  sat directly beneath a concrete `assert-event` on a specific violating value
  that does the actual work; a general negated `must-fail` refutes nothing in
  particular, and `tools/check_scaffold.py` says so in its own words. No
  concrete witness was removed. `make check` is green.

## Open, not weakened

- `books/nntp*` and `books/transfer*-invariants` have not been through ACL2
  since the split. They must be certified before the convergence merge.
- `books/article*`, `books/wildmat*` and the rest of `books/transfer*` were not
  realigned: records are still open, no book has an export theory, and
  `books/transfer-public-bound.lisp` (1062 lines) is unsplit. The budget went
  to diagnosing the certificate cache and to the wire closure.
- `books/transfer.lisp` exports eleven `fn-transfer-guard-*-is-*` equalities as
  global rewrite rules -- the `fn-ag-*-is-*` cautionary case of
  `docs/proof-style.md` §3, one book above every transfer consumer. The fix is
  the same one core applied: make each `fn-transfer-guard-*` an `mbe` over its
  logical primitive, so opening the definition *is* the equality, and keep the
  twins only as `:rule-classes nil` names. It is a theory change inside two
  1000-line proof books, so it is recorded here rather than attempted blind.

## Proposal (cross-cluster)

1. **tooling / root.** `tools/certs.py publish` must refuse a certificate that
   was not produced from the source it is keyed by. Root is doing this; the
   report above has the evidence. Until then `make certs-install` can hand a
   lane a green-looking worktree that cannot certify anything.
2. **core.** `books/nntp*` locally enable `fn-statep`, `fn-articlep` and
   `fn-pendingp` where core opened them; after the split that local enable now
   lives in `books/nntp-projection.lisp` rather than `books/nntp.lisp`. No
   statement changed.
3. **bp (`books/bp-ingress.lisp`) and the host.** `fn-article-parse` and the
   fields view are unchanged; `books/article*` was not touched. Nothing to do.
