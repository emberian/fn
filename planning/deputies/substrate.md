# Deputy report: substrate (crypto-seam, statement, principal, lace, policy, membership-epochs, assumptions)

HEAD: `dep/substrate` at f943d92, branched from `dev` a31ed5f. Conventions:
[`docs/proof-style.md`](../../docs/proof-style.md). Board entries: 2026-09-19 substrate.

## Certification state

**Not re-certified in this lane.** The root withdrew the certificate cache
mid-lane (a publisher had pushed stale certificates under new content hashes)
and instructed every deputy to delete `books/*.cert` and `tests/acl2/*.cert`
and stop certifying until "CACHE READY", which had not arrived when this
lane's budget ran out. Every source change below is committed and
paren-balanced; none of it has been through ACL2 in this worktree. The next
owner runs, in this order, one root at a time with
`FN_ACL2_TIMEOUT_SECONDS=1800`:

    crypto-seam, statement, statement-invariants, principal,
    principal-invariants, lace, lace-invariants, policy, policy-invariants,
    membership-epochs, membership-epochs-invariants, assumptions,
    then the six test books.

The change is shaped so that this is cheap to repair if it is not green: every
export event is the LAST form in its book, and every book inside the cluster
that includes another opens the withdrawn definitions again in one local line
(`(local (in-theory (enable fn-<x>-internals)))`, placed directly after the
`include-book` forms). So the theory each proof runs in is the theory it ran
in before, and a failure means a theory name is missing or misspelled, not
that a proof moved.

### Wall times measured before the cache was withdrawn

Evidence `build/acl2/certify-20260919T193314Z-57040` (ACL2 8.7, SBCL 2.6.8,
this laptop). Only four books certified from source in that run; the rest were
cache hits at 0.00 s and are not measurements.

| Book | Before |
| --- | --- |
| `tests/acl2/membership-epochs-tests` | **221.0 s** (prove 219.5) |
| `books/membership-epochs-invariants` | 1.80 s (prove 1.31) |
| `books/membership-epochs` | 0.27 s |
| `books/assumptions` | 0.02 s |

The 219.5 s is the whole finding of this lane's teeth work: eighteen general
negated `must-fail` forms, each of which is the prover failing to find a proof
rather than a counterexample, and three of which explore induction until the
step limit. After the change that book contains no `must-fail` and no `thm`.

## Cluster ledger numbers (`tools/ledger.py --write`, before → after)

- Theorems in the closure 305 → 340 (35 new accessor-of-constructor lemmas).
- `assert-event` teeth 275 → 326; `must-fail` forms 29 → 11, and all eleven
  remaining are in `tests/acl2/assumptions-tests.lisp`, which the lint already
  accepts as concrete-bodied.
- Ledger teeth-form lints for the cluster 9 → 0.
- SUSPECT 2 → 2, unchanged and both honest:
  `fn-lace-cross-canonical-self` (true by definition —
  `fn-lace-canonicalp` IS `fn-lace-cross-canonicalp lace lace`) and
  `fn-prin-apply-succession-when-not-acceptable` (a branch restatement).
  Both should be renamed `-by-definition` and given `:rule-classes nil`; that
  is a statement change and is left for the next cycle.
- Export-hygiene lints 7 → 7: the lint reads `defthm` rule classes only and
  does not yet see a book-final `deftheory` withdrawal, so three of the seven
  (`fn-stmt-content-id-unfolds`, `fn-stmt-of-items-of-items`,
  `fn-stmt-encode-bytes-item-consp`) are now withdrawn but still flagged, and
  four are the round-trip keystones, which are equalities by their nature.
  This is exactly item 6 of the core deputy's proposal to tooling.
- Definition runes withdrawn at export: 151 across the six definition books
  (crypto-seam 9, statement 58, principal 19, lace 8, policy 24,
  membership-epochs 33) — accessors, constructors, recognizers, codec entry
  points and transitions — plus ten `true-listp`/`consp` backchaining rules
  and the five properties books' non-keystone lemmas.

## What changed and why

1. **Export theory at every book end** (style §2). Each definition book ends
   with `(deftheory fn-<x>-internals '(...))` and `(in-theory (disable
   fn-<x>-internals))`; `books/assumptions.lisp` ends with
   `(in-theory (current-theory :here))` because it withdraws nothing — every
   event in it is a constraint, and a theorem that takes an assumption as a
   hypothesis needs its constraints. Only `(:d name)` runes are withdrawn, so
   type prescriptions and executable counterparts survive and the test books'
   ground evaluation is untouched.
2. **Record lemmas** (style §1). 35 accessor-of-constructor theorems for the
   eight records in the cluster: the statement header, the statement, the
   receipt, the principal key state, the policy statement, and the commit,
   message and site records. With the accessors and constructors withdrawn,
   these are the only way above the cluster to relate a field to a
   constructed record. Names follow `fn-<field>-of-fn-<make>`.
3. **Properties books export keystones only.** The five `-invariants` books
   withdraw their proof vocabulary under
   `fn-{stmt,prin,lace,pol,me}-invariants-vocabulary`. Every keystone named in
   the packet keeps its name AND its statement.
4. **`true-listp` backchaining withdrawn** (style §8): `fn-lace-p-implies-
   true-listp`, `fn-lace-ids-is-true-list`, `fn-lace-stmt-preds-are-true-list`,
   `fn-stmt-id-listp-implies-true-listp`, `fn-stmt-encode-items-is-true-list`,
   `fn-stmt-header-items-is-true-list`, `fn-stmt-take-id-items-value-is-true-
   list`, `fn-pol-authorized-set-is-true-list`, `fn-me-commitsp-implies-true-
   listp`, `fn-me-messagesp-implies-true-listp`.
5. **Teeth as concrete witnesses** (style §5). The eighteen `must-fail` forms
   in `tests/acl2/membership-epochs-tests.lisp` are replaced by ground
   `assert-event` witnesses, one per dropped hypothesis, built from the sites
   and letters the book already defines plus three new ones (`*me-site-early*`
   with no revocations, `*me-site-over*` whose held list already exceeds its
   limit, `*me-site-far*` five epochs on with a zero-epoch window). The two in
   `tests/acl2/crypto-seam-tests.lisp` are replaced by the colliding-digest
   and forged-signature witnesses that already sat directly above them.
6. **The constrained functions were not touched.** `fn-digest`,
   `fn-sig-public-key`, `fn-sig-sign`, `fn-sig-verify` and the seven
   `fn-assume-*` encapsulates keep exactly the constraints they had. Nothing
   in this lane needed a stronger one.

### Open, recorded rather than weakened

- `fn-me-merge-exposes-the-partition` has a hypothesis with no violating
  value: `(not (equal (fn-me-commit-id ca) (fn-me-commit-id cb)))` follows
  from `(member-equal ca a)` and `(not (member-equal (fn-me-commit-id cb)
  (fn-me-commit-ids a)))`. Per style §5 it should be deleted from the theorem;
  deleting it re-proves the keystone, which needs an ACL2 run this lane could
  not make. The derivation is written at the end of the test book.
- The two SUSPECT rows above want `:rule-classes nil` and a `-by-definition`
  name. Statement changes; next cycle.
- `-invariants` books were NOT folded into their definition books. The seam
  does not allow it under style §6: `statement` + `statement-invariants` is
  1174 lines and `membership-epochs` + its properties book 840, both over the
  800-line split rule, and unlike `replay-invariants` these books do not
  discharge the definition books' guards — they are the properties layer the
  style document prescribes. Folding them would trade one lint for a worse one.

## FTY: measured on the statement header, not migrated

`fty::defprod` with `:layout :list` for the six-field header, over two
`fty::deflist` types, admits in 0.9 s wall (ACL2 8.7, SBCL 2.6.8, this laptop;
`centaur/fty/top` is already certified and includes in 0.50 s). Three findings:

1. **The representation would not move.** The constructor evaluates to the
   positional list `((1 2) 3 4 ((5)) :ARTICLE (6 7))` — byte-for-byte the
   shape `fn-stmt-make-header` builds, so `books/records.lisp`, the CBOR
   record codec and every host loader are unaffected.
2. **Every keystone statement would grow fixing functions.** The
   accessor-of-constructor lemma this lane just wrote 35 times,
   `(equal (h->creator (h c i s p k r)) c)`, is NOT a theorem under `defprod`:
   it fails, and the provable form is `(equal ... (fnat-list-fix c))`. So
   `fn-stmt-content-id`, the round trips and the canonicality theorems would
   each acquire `-fix` normal forms in their statements — which is precisely
   the thing the packet says must not change.
3. **The include cost is enabled rules, not seconds.** One `defprod` plus its
   two list types generated 78 theorems, all enabled on include, into every
   book above — the pollution `docs/proof-style.md` exists to stop.

**Settled by the root, 2026-09-19:** no migration; opaque raw-list records
are the discipline, this lane's measurement and core's independent one
agreeing on both the `-fix` normal forms and the 78 enabled theorems per
prod pushed into every includer.

Recommendation as measured: **do not migrate**, and in particular do not
migrate the statement header, the future portable object, until there is a
concrete need for congruence reasoning over record equivalences. If that need
appears, the cheapest shape is a local `statement-fty.lisp` behind the
existing accessor names with `-fix`-free corollaries exported, so no keystone
statement moves. The measurement scripts are
`/private/tmp/claude-501/.../fty/d2.lsp` and its log; the numbers above are
the whole of the evidence.

## Proposal: cross-cluster steps (exact edit, owner)

1. **tooling.** `tools/ledger.py` export-hygiene should read a book-final
   `deftheory` + `(in-theory (disable <theory>))` and stop flagging a theorem
   that is withdrawn there; today it flags three withdrawn statement lemmas
   and four round-trip keystones. This is core's proposal 6, seen again here.
2. **tooling.** The teeth lint should also flag a `must-fail` whose *cost* is
   pathological: 219.5 s in one book was invisible until this lane timed it.
   A per-form prove-time budget in the certify runner would have caught it.
3. **bp (bp-release).** The policy-term placeholder now sees `fn-pol-term`,
   `fn-pol-make-receipt` and `fn-stmt-receipt-term` withdrawn. When it is
   wired to the real term, it needs `(local (in-theory (enable
   fn-pol-internals fn-stmt-internals)))` or, better, to go through
   `fn-stmt-receipt-term-of-fn-stmt-make-receipt`.
4. **codecs.** `books/statement.lisp` builds its own item-sequence codec over
   `fn-cbor` rather than adding arrays/maps to `cbor.lisp`. If codecs adds a
   map item, the statement codec should be restated over it and the
   canonicality theorems re-derived; that is a statement change and needs both
   deputies in one batch.
5. **root.** Certify this closure once the cache is rebuilt (order above), and
   record the after times against the four before times in this report.
