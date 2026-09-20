# w10/substrate-2 — the four red substrate roots are certified

Branch `w10/substrate-2`, worktree `build/lanes/w10-substrate-2`, from `dev`
`c6ebc68`, with `dev` `f730c24` merged mid-lane (the `tools/proof_profile.py`
fix). Packets S3 and S5 of
[substrate transport](../../specs/substrate-transport.md); PRF-023 and
PRF-025. Evidence summary and its limits:
[`tests/evidence/2026-09-20-substrate-transit.md`](../../tests/evidence/2026-09-20-substrate-transit.md),
section "w10/substrate-2 closed the four open roots".

## Certification

persvati, ACL2 8.7 (`$HOME/fn-tools/acl2-8.7/saved_acl2`),
`run-20260920T211342Z-aa20`, evidence
`build/acl2/certify-20260920T211346Z-3327395`, `--jobs 4`, **31 of 31 roots,
exit code 0**, 128 s wall.

| Root | State | Run | Evidence | Log |
| --- | --- | --- | --- | --- |
| `books/stx-index` | **certified** | `run-20260920T211342Z-aa20` | `build/acl2/certify-20260920T211346Z-3327395` | `books--stx-index.certify.log` |
| `books/stx-epochs` | **certified** | `run-20260920T211342Z-aa20` | same | `books--stx-epochs.certify.log` |
| `books/stx-authority` | **certified** | `run-20260920T211342Z-aa20` | same | `books--stx-authority.certify.log` |
| `tests/acl2/stx-transit-tests` | **certified** | `run-20260920T211342Z-aa20` | same | `tests--acl2--stx-transit-tests.certify.log` |

Local corroboration, one root at a time, laptop ACL2 8.7:
`build/acl2/certify-20260920T205912Z-79933` (`stx-epochs`),
`certify-20260920T210944Z-90380` (`stx-index`),
`certify-20260920T211000Z-90581` (`stx-authority`),
`certify-20260920T211258Z-93549` (`stx-transit-tests`).

Baseline for comparison, same box, same command, before any edit:
`run-20260920T204626Z-b9b3`, `build/acl2/certify-20260920T204819Z-3079633`,
27 of 31, the four roots above red.

## The two theorems, closed with their statements unchanged

### `fn-stx-index-equivocators-agree` (books/stx-index.lisp)

The gap was one equality the goal could not see:
`(cdr (fn-stx-alist-get (fn-stx-slot-key s) (fn-stx-index-slots index)))` is
`(fn-stx-lace-slot-first lace (fn-stx-slot-key s))`. `fn-stx-index-slots-agree`
says it, but its first conjunct is stated over `fn-stx-index-slot-first`,
which the goal never contained, and its second is an `iff` that cannot rewrite
inside `(consp ...)`. Without it the prover reached
`Subgoal *1/1.12'''`: a record written (`(consp prev)`, `(cdr prev) ≠ s`) with
`(not (fn-lace-slot-conflictp s lace))` still assumed.

The profile ran first, on the pre-change form, with the fixed
`tools/proof_profile.py` (`--host persvati`; log kept at
`/private/tmp/.../profile-equivocators-baseline.log`). It named **fifteen
runes with zero useful applications**, headed by `fn-stx-index-stmt-is-consp`
18,651 frames, `(:type-prescription fn-stmt-p)` 8,540,
`(:definition fn-lace-p)` 6,996, `(:definition fn-stx-alist-get)` 5,880,
`fn-prin-acceptablep-implies-shapes` 5,036, `fn-lace-member-is-stmt` 4,270,
`fn-stx-lace-slot-first-of-member` 3,668. They are withdrawn together as the
local `deftheory fn-stx-index-equivocator-fan`, and the two forms that used to
fight them now re-enable `(:d fn-lace-p)` for exactly one case split.

The proof is four local steps:

- `fn-stx-slot-fork-is-equivocation` — the slot already holds THIS statement
  and the lace forks it anyway, so the lace was an equivocator before the
  step and no new record is owed.
- `fn-stx-slot-first-differs-is-conflict` — the converse: a slot whose first
  statement is not `s` is a fork of `s`.
- `fn-stx-index-equivocatorp-of-add1` — one more statement, stated over an
  arbitrary index and lace, with the three hypotheses the induction supplies.
- `fn-stx-index-equivocatorp-of-add` — the same over a nil-or-singleton delta,
  which is the shape `fn-stx-index-of-store` hands the induction.

Both bridges carry every hypothesis explicitly. That is not decoration: the
first attempt cited `fn-stx-slot-partner-elim` and
`fn-lace-distinct-same-slot-is-equivocation` directly inside the step, and
the clausifier's cross product put the same-slot conjunct of the first in a
different clause from the branch of the second that needed it — one surviving
checkpoint, `Subgoal 9'`, whose only defect was
`(NOT (EQUAL (FN-STMT-CREATOR S) (FN-STMT-CREATOR (FN-STX-SLOT-PARTNER LACE S))))`.
Neither bridge mentions the partner, so that cross product does not arise.

Cost: the keystone is **1,778 prover steps, 0.01 s**, against **108,917 steps
failing**; the two bridges are 7,303 and 14,644 steps; the whole book is 0.73 s.

### `fn-stx-commit-decode-is-a-commit` (books/stx-epochs.lisp)

The checkpoint was `Subgoal 38`, ending
`(TRUE-LISTP (FN-STMT-VALUE (FN-STMT-OK (LIST :FN-ME-COMMIT ...))))`. The
prompt's guess — a `:rule-classes nil` shape lemma about
`fn-stmt-decode-items` at count 5 — is **not what it needed and no such lemma
was added**. `books/statement` withdraws `fn-stmt-ok`, `fn-stmt-okp` and
`fn-stmt-value`, and `books/statement-invariants` withdraws the result algebra
that relates them; nothing in this book's include chain re-opens either. So
the accepting branch built the commit and the conclusion could not see it.
Two rewrites about `fn-stmt-ok` alone, `fn-stmt-okp-of-ok` and
`fn-stmt-value-of-ok`, are enabled AT THAT ONE FORM. Every field the
conclusion constrains is constrained by `fn-stx-commit-of-items`' own branch
tests — the base by `fn-stmt-uint-item-p` hence `fn-record-uint32p` hence
`natp`, the op by `fn-stx-op-of-code-is-an-op` — so `fn-stmt-decode-items`
stays disabled and no shape fact about it exists.

## Four further defects, all in forms no run had ever reached

A failed certification stops at the first bad form, so everything below
`books/stx-index.lisp:494` and `books/stx-epochs.lisp:109` had never been
admitted by anything. Four of those forms were wrong.

1. **`fn-stx-commits-of-lace-have-witnesses` was FALSE** (local,
   `books/stx-epochs.lisp`). It asked only `(fn-lace-p delta)`; the witness
   scan's disjunct needs `(fn-prin-verifiedp (car delta) keyring)`, and ACL2's
   checkpoint was exactly
   `(IMPLIES (FN-STMT-P DELTA1) (FN-PRIN-VERIFIEDP DELTA1 KEYRING))`.
   Repaired with the hypothesis that holds on every reachable delta — every
   statement of the lace verifies — carried as a recursive predicate because
   the scan walks the list while `fn-stx-batch-delta-members-are-verified` is
   member-shaped, and proved of `fn-stx-batch-delta` from `fn-stx-delta`'s own
   definition. No exported statement changed.
2. **`fn-stx-every-commit-by-sublist`'s `:use` sat on the wrong subgoal.** The
   scheme is three-way (base, no witness, witness); the case that needs the
   witness is `*1/2`. It also needed `subsetp-equal` reflexivity, which ACL2
   ground zero does not supply.
3. **`fn-stx-index-lookup-cost-is-index-bounded` suggested no induction
   scheme**: `(fn-stx-index-bindings index)` is not a variable. It is now the
   instance of a walk lemma, `fn-stx-alist-steps-is-len-bounded`; the
   statement is unchanged. **This is the D3 cost shadow and it had never been
   proved.**
4. **The S4-1 and S5-1 witnesses were VACUOUS.** A statement whose kind is not
   `:article` carries its payload as the article body in base64
   (`fn-stx-payload-for` / `fn-stx-body-payload`), and both carrier articles
   in `tests/acl2/stx-transit-tests.lisp` were built with a prose body ("p").
   The reconstructed statement therefore carried the wrong payload, no
   signature verified, `fn-stx-delta` was `nil`, and every assertion about the
   hostile batch held of an **empty delta**. The tooth that caught it is the
   non-degeneracy line the previous lane wrote for exactly this purpose:
   `(not (fn-pol-delta-without-authority-p (fn-stx-batch-delta *stxt-real-batch* ...) ...))`.
   Both carriers now carry `fn-stx-b64-encode` of their own signed payload,
   and two new assertions pin the deltas themselves
   (`(equal (fn-stx-batch-delta *stxt-hostile-batch* *stxt-keyring*) (list *stxt-pol-stmt-b*))`
   and the same for the real batch) so the vacuity cannot return silently.

## Registries

- **PRF-023 `in-progress`**, events curated in `planning/proof-events.json`:
  `fn-stx-index-bindings-agree`, `fn-stx-index-slots-agree`,
  `fn-stx-index-equivocators-agree`, `fn-stx-index-invariant-preserved-by-accept`.
  `fn-stx-index-agrees-with-lace` is their `:rule-classes nil` corollary and
  is cited as one, not as the event.
- **PRF-025 `in-progress`**, events `fn-stx-commit-decode-is-a-commit` and
  `fn-stx-commits-of-batch-are-verified-and-well-formed`. The three
  reconnection rows are labelled corollaries of the
  `books/membership-epochs-invariants` keystones they name.
- PRF-021, PRF-022 and PRF-024 keep their `planned` status — they are not this
  lane's rows — but each gained a note that the test book now certifies, so
  their witnesses have run, and that S4-1's were vacuous until now.
- `specs/substrate-transport.md` section 10: the S3-3, S4-1, S5-1-carrier and
  S5-1-corollaries rows are rewritten to what is now proved, each with what
  is still open.

## Open, recorded rather than weakened

- **Neither keystone has a host line.** `fn-stx-index-lookup` and
  `fn-stx-index-equivocatorp` have no caller: `fn-node-statep` is
  `(acceptance retention stage bindings)` and has no index slot, so the D3
  claim "the served query walks the index, never the store" is about a query
  the served path does not carry. `fn-stx-commits-of-batch` likewise has no
  caller on any reconnection path. Both are recorded as `pending_subject` in
  `planning/proof-events.json`; PRF-023 and PRF-025 are `in-progress`, not
  closed, for exactly this reason.
- **The `:policy` carrier's body wrapping is still not implemented.** The
  witnesses above encode the payload as unwrapped base64 because
  `fn-stx-strip-wsp` removes WSP and CRLF is not WSP, so a 76-column wrapped
  body — which is what RFC 4648 §4 and §1.3 of the design call for, and what
  any real transport will produce — is refused. w7/substrate-s1 recorded this;
  it is now load-bearing for every non-`:article` statement that crosses a
  wire, not just for large payloads.
- **`books/stx-index.lisp:23`** still enables `(:d fn-lace-same-slotp)`,
  `(:d fn-lace-slot-conflictp)` and `(:d fn-lace-equivocatorp)` book-wide
  (locally). Every theorem below it that must not see them disables them in
  its own hint. That is the inversion the proof-style guide warns about and
  it is what made the fan measurable; narrowing it to the forms that want it
  is a clean follow-up, not attempted here.
- A-CRYPTO stands behind every verification in the test book: the toy
  realisers of `tests/acl2/crypto-seam-tests.lisp`, a polynomial mix digest
  and a sign-by-public-key scheme.
