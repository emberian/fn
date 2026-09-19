# LANEDUMP: hygiene lane

Handed off mid-session to a Codex root. Full detail (verbatim rewritten
sentences, complete rationale) is also in `HANDOFF.md` in this worktree;
this file is the structured summary the coordinator asked for.

## Packet as I understood it

Repair the hygiene/registry findings from `planning/review-2026-09-18-independent.md`
(§4 tautologies/uncalled-API/ghost-only citations) in files owned by this
lane: `books/index.lisp`, `books/checkpoint.lisp`, `books/journal.lisp`
(header comments only), the matching test books, specs/index.md,
specs/checkpoint.md, docs/*, planning/now.md (→ ≤40 lines + new
evidence-index.md), planning/assurance-closure.md, planning/swarm-cycles.md
(Roles + review §8 C1 table), planning/milestones.md, README.md,
tests/evidence/*.md (prose only). Standard: every keystone theorem
satisfiable, has teeth (must-fail or negated assert-event per hypothesis),
named for what it proves; no skip-proofs/defaxiom/defttag; no counts in
prose (point at planning/ledger.md, plain text since it doesn't exist yet).
GATE: `make check` + full `make certify` green.

## DONE

### `books/index.lisp` — real soundness/completeness theorems

Replaced the `X ⊆ X` tautologies (`:128-131`/`:204-207` in the original)
by **redefining** `fn-index-soundp`/`fn-index-completep` to scan
`fn-article-memberships` directly (never calling `fn-index-build`), so the
theorem names `fn-index-build-sound`/`fn-index-build-complete` are unchanged
but now prove real facts — no vacuous theorem survives under either name.
Deleted the one purely-redundant lemma, `fn-index-build-subset-self`.

Verbatim keystones (both now CERTIFIED, confirmed by `certify_books.py`):

```lisp
(defthm fn-index-build-sound
  (implies (fn-article-listp configured articles)
           (fn-index-soundp (fn-index-build articles) articles)))

(defthm fn-index-build-complete
  (implies (fn-article-listp configured articles)
           (fn-index-completep (fn-index-build articles) articles)))
```

New predicate definitions backing them:

```lisp
(defun fn-index-membership-hasp (group number memberships)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (or (and (equal group (fn-ag-car (fn-ag-car memberships)))
               (equal number (fn-ag-cdr (fn-ag-car memberships))))
          (fn-index-membership-hasp group number (fn-ag-cdr memberships)))
    nil))

(defun fn-index-entry-sourcedp (entry articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (or (and (equal (fn-index-entry-msgid entry)
                      (fn-article-msgid (fn-ag-car articles)))
               (fn-index-membership-hasp (fn-index-entry-group entry)
                                         (fn-index-entry-number entry)
                                         (fn-article-memberships (fn-ag-car articles))))
          (fn-index-entry-sourcedp entry (fn-ag-cdr articles)))
    nil))

(defun fn-index-soundp (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp index)
      (and (fn-index-entry-sourcedp (fn-ag-car index) articles)
           (fn-index-soundp (fn-ag-cdr index) articles))
    t))

(defun fn-index-memberships-completep (msgid memberships index)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (and (fn-ag-member
            (fn-index-entry (fn-ag-car (fn-ag-car memberships))
                            (fn-ag-cdr (fn-ag-car memberships))
                            msgid)
            index)
           (fn-index-memberships-completep msgid (fn-ag-cdr memberships) index))
    t))

(defun fn-index-completep (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (and (fn-index-memberships-completep
            (fn-article-msgid (fn-ag-car articles))
            (fn-article-memberships (fn-ag-car articles))
            index)
           (fn-index-completep index (fn-ag-cdr articles)))
    t))
```

Supporting proof chain (all in `books/index.lisp`, all CERTIFIED): induction
lemmas `member-equal-append-{left,right}`, `fn-index-membership-hasp-of-member`
(uses raw `car`/`cdr`, NOT `fn-ag-car`/`fn-ag-cdr` — see Design decisions),
`fn-index-entry-sourcedp-cons`, `fn-index-soundp-{cons-articles,append-index}`,
`fn-index-membership-entries-sourced`, `fn-index-article-entries-self-sourced`
(soundness side); `fn-index-memberships-completep-{cons-index,self,append-left,
append-right}`, `fn-index-completep-append-left` (completeness side); plus a
guard-listp chain `fn-index-membership-entries-listp` (needs `fn-string-listp
groups`, not just `fn-membership-listp` — see Design decisions),
`fn-index-article-entries-listp`, `fn-index-listp-append`,
`fn-index-build-listp`, used to remove the unnecessary `fn-index-listp
(fn-index-build articles)` hypothesis from the pre-existing
`fn-index-range-query-correct` (kept, otherwise unchanged).

Teeth: unchanged `tests/acl2/index-tests.lisp` already had both required
witnesses (`*index-omitted*` fails completeness while staying sound;
`*index-invented*` fails soundness) — verified by hand they still evaluate
correctly under the new definitions (extensionally equivalent to the old
ones on any real `fn-article-listp` input); no test edit needed.

**Confirmed CERTIFIED**: `books/index` + `tests/acl2/index-tests`, scoped run,
`build/acl2/certify-20260919T063633Z-34181`.

### `books/checkpoint.lisp` — guards + frontier-rejection keystone

All 13 functions now `(verify-guards ...)`. Three real guard bugs found and
fixed (not mechanical) — see Design decisions for the exact mechanism. New
keystone (CERTIFIED):

```lisp
(defthm fn-checkpoint-restore-rejects-frontier-reuse
  (implies
   (and (fn-checkpointp checkpoint)
        (equal groups (fn-checkpoint-groups checkpoint))
        (equal capacity (fn-checkpoint-capacity checkpoint))
        (fn-record-uint32p frontier)
        (<= (fn-checkpoint-frontier checkpoint) frontier)
        (< (fn-record-txid record) (fn-checkpoint-frontier checkpoint)))
   (equal
    (fn-checkpoint-restore checkpoint groups capacity
                           (cons record more) frontier)
    (list :error :suffix)))
  :hints (("Goal" :in-theory (enable fn-checkpoint-restore fn-sf-record-listp))))
```

Every hypothesis independently exercised in `tests/acl2/checkpoint-tests.lisp`
(drop `fn-checkpointp` → `:error :checkpoint`; drop groups/capacity → `:error
:configuration`; drop frontier validity/ordering → `:error :frontier`; drop
the reuse condition, using `*cp-r1*` (txid 4 ≥ frontier 3) → `:ok`). Reachable
witness: `*cp-stale-txid*` (txid 2 < frontier 3), already present; added one
more assertion with `(list *cp-stale-txid* *cp-r1*)` for "regardless of the
rest of the suffix."

Bridging lemmas added (all non-recursive, all CERTIFIED):
```lisp
(defthm fn-replay-okp-implies-node-statep
  (implies (fn-replay-okp answer)
           (fn-node-statep (fn-replay-result-node answer)))
  :hints (("Goal" :in-theory (enable fn-replay-okp))))

(defthm fn-record-uint32p-implies-natp
  (implies (fn-record-uint32p n) (natp n))
  :hints (("Goal" :in-theory (enable fn-record-uint32p))))

(defthm fn-node-statep-implies-retention-true-listp
  (implies (fn-node-statep node)
           (true-listp (fn-node-retention node)))
  :hints (("Goal" :in-theory (enable fn-node-statep fn-retain-statep))))
```

`fn-checkpoint-make`'s guard was strengthened from `t` to `(fn-node-statep
node)` (true at both call sites — see file). NOT dropped: the
`fn-replay-okp` hypotheses in `fn-checkpoint-admissible-splitp` (packet asked
to drop them "if the review says they're unnecessary" — I read the full
review and found no such passage; my own check says they are NOT redundant,
see Design decisions).

**Confirmed CERTIFIED**: `books/checkpoint` + `tests/acl2/checkpoint-tests`,
scoped run, same evidence dir as index above.

### `books/journal.lisp` header (comments only, lines ~444-447)

Old: "Certified local recovery facts. These are logical properties of the
scanner, conditional on the crash constructor's stated platform assumptions."

New: "Certified local facts about the scanner and completion-action helper
defined above. Each is a definition unfolding or a fact about a single
physical commit image (one sequence/txid pair); none mentions
FN-JOURNAL-CRASH and none is conditioned on the crash constructor's platform
assumptions. This book is the historical isolated-slot journal experiment
named in docs/prefixes.md, not the adapter model the host runs."

### Prose files (all edited, `make check` passing throughout)

`specs/index.md`, `specs/checkpoint.md`, `docs/implementation.md`,
`docs/README.md`, `planning/now.md` (rewritten to exactly 40 lines: What
runs / What is proved with scope / Next), `planning/evidence-index.md` (NEW —
16 rows, one per `tests/evidence/*.md`, columns: record, source revision,
covers, does-not-show), `planning/milestones.md`, `planning/assurance-closure.md`
(rows 26/32/33/34/36 corrected with theorem names + review citations),
`planning/swarm-cycles.md` (new "Roles" section; C1 table replaced with
review §8's Order/Packet/Change/Tier table verbatim, 0-14; C2/C3 tables kept
unchanged), `README.md` (count removal), `tests/evidence/2026-09-18-integrated.md`,
`tests/evidence/2026-09-18-article-work.md`, `tests/evidence/2026-09-18-fields-transfer.md`
(prose only; no `.json` touched). See "Sentences rewritten" below for the
exact old→new table; `HANDOFF.md` §4 has the same table plus more context.

## IN-PROGRESS

**Full-tree `make certify` (the GATE run) — running, left running per
instruction, do not restart/kill.** Log: `build/certify-final2.log` in this
worktree. Evidence dir at handoff time: `build/acl2/certify-20260919T064436Z-39951`,
about 10-20 books in (through roughly `books/wire`), no errors seen so far.
This is the THIRD attempt at a full run:
- Attempt 1 and 2 (before my source fixes): killed by external session
  resets, not proof failures — never reached checkpoint/index.
- Attempt 3 (`build/certify-final.log`, evidence
  `build/acl2/certify-20260919T054140Z-2837`): ran to completion, **found two
  real bugs** (see Design decisions) — this is how they were caught.
- After fixing, a **scoped** run of just `books/checkpoint
  tests/acl2/checkpoint-tests books/index tests/acl2/index-tests` (reusing
  the `.cert`s attempt 3 produced for every other book) went green after 3
  iterations (2 more bugs found and fixed along the way — see Design
  decisions). Evidence: `build/acl2/certify-20260919T063633Z-34181`,
  "ACL2 certification passed".
- Attempt 4, the current one (`build/certify-final2.log`), is the first FULL
  run since the fixes; it was launched to satisfy the packet's explicit "run
  the full command anyway" gate requirement. A prior attempt at this
  (`build/certify-final.log`, evidence `build/acl2/certify-20260919T063721Z-34711`)
  reached book ~20 cleanly then was also killed by an external reset
  (`make: *** [certify] Terminated: 15`), not a proof failure.

**When you pick this up**: check `tail -5 build/certify-final2.log` and
`ls build/acl2/certify-20260919T064436Z-39951/*.log | xargs grep -L
FN_CERTIFY_SUCCESS` to see what's left. If it's still running, either wait or
kill it and re-run — no source edit is pending on it; `books/checkpoint` and
`books/index` are independently *already proven* to certify clean (scoped
run above), so a full-run failure elsewhere would be pre-existing or a fresh
regression unrelated to this lane's edits. Always set
`FN_ACL2_TIMEOUT_SECONDS=1800` per the coordinator's box-contention notice,
and check `lsof -a -p <pid> -d cwd` on any `certify_books.py`/`saved_acl2.core`
process before assuming it's yours — nine other lanes share this box and can
have byte-identical command lines.

## NOT STARTED

- No further ACL2 work is planned by me; index.lisp and checkpoint.lisp are
  functionally complete for this packet pending only the full-tree gate
  confirmation above.
- The non-owned-file proposals below are text proposals only — I did not
  (and per OWNED/NOT-OWNED scope, should not) apply them myself.
- I did not attempt to prove `fn-checkpoint-admissible-splitp`'s
  `fn-replay-okp` hypotheses redundant (see Design decisions — I believe
  they are not redundant, but did not exhaustively try).

## Design decisions and why (so Codex does not redo this work)

1. **Index tautology fix = redefine the predicates, not just reprove.**
   `fn-index-soundp`/`fn-index-completep` used to be defined via `fn-subsetp`
   against `fn-index-build`'s own output, so instantiating the theorem with
   `index := (fn-index-build articles)` was definitionally `X ⊆ X`. The fix
   is NOT a cleverer proof of the old statement — it's redefining the
   predicates to scan `fn-article-memberships` directly (never mentioning
   `fn-index-build`), so the SAME theorem names now state a genuine
   induction (build's append-recursion vs. the membership-scan predicates).
2. **`fn-ag-car`/`fn-ag-cdr` in a lemma's CONCLUSION never matches later
   goals.** `fn-ag-car-is-car` (already in `acceptance.lisp`) is a rewrite
   rule `(fn-ag-car x) = (car x)`, so ACL2 normalizes *away* from
   `fn-ag-car` everywhere. A lemma whose own trigger term still says
   `fn-ag-car` (like my first `fn-index-membership-hasp-of-member`) will
   never fire against an already-normalized goal that says `car`. Any new
   lemma meant to fire against normal-form goals must be stated with raw
   `car`/`cdr`, not the `fn-ag-*` helpers (those are for *guard*
   satisfiability inside a `defun` body, not for lemma statements).
3. **`fn-membership-listp` does not type group names as strings** — only
   `fn-selection-validp` does (via `fn-articlep`). A lemma that needs
   `(stringp (car groups))` from a `fn-membership-listp groups memberships`
   hypothesis alone will fail; you need `fn-string-listp groups` as an
   explicit extra hypothesis, sourced from `fn-selection-validp`.
4. **Several codebase functions are NOT guard-`T`** despite most of the
   surrounding style being guard-`T`-with-`mbe`: `fn-retain-{capacity,
   reserved,pins,releases}` all have guard `(true-listp s)`
   (`retention.lisp:159-169`), and raw `member-equal`/`append` (as opposed to
   `fn-ag-member`/`fn-ag-append`) need `(true-listp ...)` on their list
   argument. A NEW guard-`T` function that calls one of these on an
   unconstrained parameter will fail `verify-guards` even though the
   surrounding style looks uniformly guard-`T`. Two fixes depending on
   shape: (a) if the value is a genuine precondition of the function (e.g.
   `fn-checkpoint-make` needs a real `fn-node-statep node` to make sense at
   all), strengthen the `:guard`; (b) if it's incidental (e.g.
   `fn-index-memberships-completep` calling `member-equal` on an arbitrary
   `index` it's supposed to accept universally), swap to the `fn-ag-*`
   guard-`T` equivalent instead of narrowing the guard.
5. **Never `:in-theory (enable X)` a predicate whose definition can reach
   `FN-REPLAY`/`FN-REPLAY-LOOP`** when trying to extract one fact from it at
   a call site where a `LET` binds a variable to `(FN-REPLAY ...)`. Both are
   enabled *by default* (nothing in `checkpoint.lisp` disables them before
   my new code), and `FN-REPLAY-LOOP` recurses over an unconstrained
   `records`/`prefix` list — ACL2 will burn minutes (I measured 656s once)
   attempting induction and still fail. The fix pattern: prove a tiny
   standalone lemma about the opaque predicate applied to a *free variable*
   (so ITS proof can't reach `fn-replay`), then at the real call site
   `:use` that specific instance while `:in-theory (disable fn-replay
   fn-replay-loop <predicate-being-bridged>)`. See the three bridging
   lemmas above; reuse this pattern for any future guard proof shaped like
   "extract fact from `fn-replay-okp`/`fn-node-statep` of a `fn-replay`
   result."
6. **`fn-checkpoint-admissible-splitp`'s `(append prefix suffix)` also
   needed `fn-ag-append`** (same class of bug as #4b) — `append`'s guard
   needs `(true-listp prefix)`, not implied by the function's own guard `t`.
7. **Ten lanes share this box; `ps aux` cannot distinguish them** when
   command lines are identical (unmodified `Makefile`). Use `lsof -a -p
   <pid> -d cwd` to check a candidate ACL2/`certify_books.py` process's
   working directory before concluding it's (or isn't) yours.
8. **Prose "counts" ban vs. AGENTS.md's "quote the pessimistic number"
   rule are different rules for different things.** Root/function/test/edge
   *ledger* counts (things `tools/ledger.py` will generate) get replaced
   with a plain-text `planning/ledger.md` pointer (not a Markdown link — the
   file doesn't exist yet in this worktree; a Markdown link would fail
   `make check`'s missing-target scan, confirmed by hitting this once on
   `HANDOFF.md` itself). A *work-bound number* (like the 17,450,479,652-unit
   article-parser ceiling) is the opposite: AGENTS.md says quote it exactly,
   paired with its covered scope, in the same sentence — don't hide it.
9. **`fn-checkpoint-admissible-splitp`'s `fn-replay-okp` hypotheses are not
   provably redundant** (my own read, not found stated in the review): the
   only other structural hypothesis, `fn-sf-record-listp`, constrains
   sequence/txid ordering only — it says nothing about whether `fn-replay`
   actually succeeds (group/capacity/duplicate/content validity can still
   fail independent of ordering). Left them in place.

## Sentences rewritten (owned files) — old → new

See `HANDOFF.md` §4 for the full table with exact quotes; short version:
`specs/index.md` (both-directions overclaim → real induction description),
`specs/checkpoint.md` (added the frontier-rejection keystone description),
`docs/implementation.md` retention row ("evidence-gated release" →
admit-string equality), replay row (diagnostic-only overclaim → "by
convention, not proof"), article-syntax row (split value/cost bound claim),
object-assembly row (named the uncalled transfer bound + its gaps), NNTP
bullet (effect typing loosened), `tests/evidence/2026-09-18-integrated.md`
(node binding relation), `tests/evidence/2026-09-18-article-work.md`
(value/cost split + pessimistic-number-with-scope), `tests/evidence/2026-09-18-fields-transfer.md`
(historical digest annotation), `planning/assurance-closure.md` rows
26/32/33/34/36 (see HANDOFF.md for exact new text), `planning/milestones.md`
(stale scaffold count → ledger pointer), and count removal across
`README.md`/`docs/implementation.md`/`planning/milestones.md`.

## Proposals for files I do not own (exact replacement text)

- `specs/article-fields.md:51` — see HANDOFF.md, proposes clarifying
  `fn-af-message-id-equalp`'s theorem is a direct definitional unfolding.
- `specs/bp-ingress.md:73` — proposes "exercises... as 25 assert-event
  examples" instead of "certifies" (book has 0 `defthm`).
- `specs/store-refinement.md:270` — proposes removing the "9,038 edges
  including allocator/record crash choices" overclaim (no D4 crash points,
  no txid-gap record, includes self-loops).
- `docs/prefixes.md:12` — proposes "release gated on a stored evidence-string
  match" instead of "evidence-gated release".
- `planning/proofs.json` (PRF-002) — proposes retargeting its citation to
  `fn-install-preserves-state`/`fn-watermark-does-not-conflict` instead of
  the six `inv⇒inv` corollaries.
- `tests/acl2/bp-workflow-binding-invariants-tests.lisp:78-90` — proposes a
  second fabricated-work witness separating subject/archive equality (did
  not read exact predicate names, outside ownership).
- `specs/article-parser.md:88` — proposes reconciling with
  `specs/article-work.md` (currently contradicts it).

## Gate commands and last results

- `python3 tools/check_scaffold.py` — **PASSED**, last run "Scaffold OK: 78
  Markdown files, 49 requirements, 18 proof targets, 18 scenario
  specifications." (re-run any time, no ACL2 needed, cheap)
- Scoped `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py
  books/checkpoint tests/acl2/checkpoint-tests books/index
  tests/acl2/index-tests` — **PASSED** (3rd iteration), evidence
  `build/acl2/certify-20260919T063633Z-34181`.
- Full `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` — **IN PROGRESS** (4th
  attempt), see "IN-PROGRESS" above. Not yet confirmed green end-to-end.

## Known defects / remaining gaps

- Full-tree gate run not yet confirmed complete (in progress at handoff).
- `fn-checkpoint-admissible-splitp`'s `fn-replay-okp` hypotheses not proven
  redundant (design decision #9) — not a regression, just not attempted.
- Non-owned-file review findings listed above remain unfixed (proposals
  only).
- `books/README.md` (not in OWNED or NOT-OWNED lists) mentions
  `node`/`node-invariants` article-to-pin bindings; left untouched, ambiguous
  ownership.
- `tests/README.md` still has some historical counts (e.g. "54 passing
  certification roots") — NOT in the packet's explicit count-removal file
  list (only README.md/docs/*.md/now.md/milestones.md were named), so left
  as-is deliberately, not an oversight.

## Dirty and untracked files at handoff (no commit yet)

```
 M README.md
 M books/checkpoint.lisp
 M books/index.lisp
 M books/journal.lisp
 M docs/README.md
 M docs/implementation.md
 M planning/assurance-closure.md
 M planning/milestones.md
 M planning/now.md
 M planning/swarm-cycles.md
 M specs/checkpoint.md
 M specs/index.md
 M tests/acl2/checkpoint-tests.lisp
 M tests/evidence/2026-09-18-article-work.md
 M tests/evidence/2026-09-18-fields-transfer.md
 M tests/evidence/2026-09-18-integrated.md
?? HANDOFF.md
?? planning/evidence-index.md
?? LANEDUMP-hygiene.md (this file)
```

`tests/acl2/index-tests.lisp` is intentionally NOT modified (see DONE above
— existing tests already cover the new definitions correctly).
