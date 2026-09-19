# hygiene lane handoff

`git rev-parse HEAD`: PENDING — filled in after the final commit (see bottom).

## Box safety

Ran at most one ACL2 process of my own at a time. The initial `make certify`
baseline was killed twice by session/shell resets outside my control (not by
me running a second ACL2 process); each time I confirmed no `certify_books.py`
process remained before restarting, and never edited `books/index.lisp` or
`books/checkpoint.lisp` while a certify run was in flight past the point where
it could reach them uncertified with old content. Ten lanes share this box, so
`ps aux` alone is not enough to tell my ACL2/`certify_books.py` processes from
the other nine lanes' (their command lines can be byte-identical to mine when
a lane hasn't touched the Makefile) — before every certify invocation after I
noticed this, I checked `lsof -a -p <pid> -d cwd` on each live match and
confirmed none had this worktree as its cwd before proceeding. When the scoped
debug cycle (§ Commands run) found real bugs in my own new code, I fixed the
source and re-ran the scoped 4-book command rather than the full tree, per
AGENTS.md's "certify only owned roots" guidance, then ran the full
`make certify` once at the end as the GATE. No `git stash`, no `git add -A`;
commits are of named files via `git commit -F`.

## Files changed

Owned files edited this lane:

- `books/index.lisp` — real soundness/completeness theorems, guard-clean.
- `books/checkpoint.lisp` — all 13 functions guard verified; new keystone
  `fn-checkpoint-restore-rejects-frontier-reuse`.
- `books/journal.lisp` — header/comment rewrite only (lines ~444-447), no code.
- `tests/acl2/index-tests.lisp` — unchanged (existing tests already exercise
  the new predicates correctly; see "Teeth" below for why no edit was needed).
- `tests/acl2/checkpoint-tests.lisp` — added an explicit teeth block for the
  new keystone, reusing existing witnesses plus one new multi-record suffix
  assertion.
- `specs/index.md`, `specs/checkpoint.md` — rewritten to describe the real
  theorems.
- `docs/implementation.md`, `docs/README.md` — prose repairs, count removal,
  evidence-index link.
- `planning/now.md` — rewritten to 40 lines.
- `planning/evidence-index.md` — new; one row per `tests/evidence/*.md`.
- `planning/milestones.md`, `planning/assurance-closure.md`,
  `planning/swarm-cycles.md` — prose repairs, count removal, Roles paragraph,
  C1 table replacement (assurance-closure.md rows 26/32/33/34/36 corrected
  with theorem names and review item numbers).
- `README.md` — count removal.
- `tests/evidence/2026-09-18-integrated.md`, `tests/evidence/2026-09-18-article-work.md`,
  `tests/evidence/2026-09-18-fields-transfer.md` — prose corrections; no `.json`
  touched.

## 1. index.lisp — verbatim new theorems

The tautologies at `:128-131` (`fn-index-completep`/`fn-index-soundp` defined
via `fn-subsetp` against `fn-index-build`'s own output) and `:204-207`
(`fn-index-build-sound`/`fn-index-build-complete` instantiating that build
against itself, `X ⊆ X`) are gone. Fix mechanism: **the predicates
`fn-index-soundp` and `fn-index-completep` were redefined** to scan
`fn-article-memberships` directly, never calling `fn-index-build`, so the
theorem *names* `fn-index-build-sound`/`fn-index-build-complete` are unchanged
but now prove real facts (no vacuous theorem is left under either name — the
"never keep both" rule is satisfied by replacement, not duplication). The one
truly-redundant lemma, `fn-index-build-subset-self`, is deleted outright (no
longer needed).

New/changed definitions (`books/index.lisp`):

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

Keystone theorems, hypothesis stacks verbatim:

```lisp
(defthm fn-index-build-sound
  (implies (fn-article-listp configured articles)
           (fn-index-soundp (fn-index-build articles) articles)))

(defthm fn-index-build-complete
  (implies (fn-article-listp configured articles)
           (fn-index-completep (fn-index-build articles) articles)))
```

Each is proved by induction on `fn-index-build`'s own append recursion,
connected to the membership-level predicates by a chain of helper lemmas
(`member-equal-append-{left,right}`, `fn-index-membership-hasp-of-member`,
`fn-index-entry-sourcedp-cons`, `fn-index-soundp-{cons-articles,append-index}`,
`fn-index-membership-entries-sourced`, `fn-index-article-entries-self-sourced`
for soundness; `fn-index-memberships-completep-{cons-index,self,append-left,append-right}`,
`fn-index-completep-append-left` for completeness) — none of which cites
`fn-index-build` in its own statement, so the connection is a real induction,
not a restatement.

`fn-index-range-query-correct` (`:183` originally) is kept; its unnecessary
`fn-index-listp (fn-index-build articles)` hypothesis is removed and instead
derived from a new `fn-index-build-listp` (itself built from
`fn-index-membership-entries-listp` — which needed an extra hypothesis,
`fn-string-listp groups`, that I initially missed: `fn-membership-listp`
alone does not type the group names as strings, only `fn-selection-validp`
does, via `fn-articlep`).

**Teeth**: unchanged `tests/acl2/index-tests.lisp` already has both: an
omitted-entry index (`*index-omitted*`) fails `fn-index-completep` while
remaining `fn-index-soundp` (line ~78-82, negated `assert-event`), and a
fabricated entry (`*index-invented*`) fails `fn-index-soundp` (line ~109-115,
negated `assert-event`). I verified by hand that these concrete witnesses
evaluate identically under the new definitions (both predicates are
extensionally equivalent to the old ones on every article list that is
actually `fn-article-listp`; they differ only in *why* they're true, no
longer through self-reference) — no test edit was needed.

## 2. checkpoint.lisp — guards and the frontier-rejection keystone

All 13 functions (`fn-checkpoint-{groups,capacity,frontier,sequence,node,make,
capture,capture-value,finish,restore,full-replay,admissible-splitp}` and
`fn-checkpointp`) now have `(verify-guards ...)` calls; none was previously
verified. This was not mechanical — three real, distinct guard gaps surfaced
during actual certification (below), each fixed with a targeted, non-recursive
bridging lemma rather than a blanket `:in-theory (enable ...)`, because the
naive enable triggered a 656-second failed guard proof by pulling
`FN-REPLAY`/`FN-REPLAY-LOOP` (both enabled by default, both recursive over an
unconstrained `records`/`prefix` list) into the simplification of a
`LET`-bound `(FN-REPLAY GROUPS CAPACITY PREFIX)` term. The fix pattern used
throughout: prove a tiny standalone fact about the *opaque* predicate applied
to a free variable (so its own proof never touches `FN-REPLAY`), then `:use`
that specific instance while *disabling* `FN-REPLAY`/`FN-REPLAY-LOOP` (and the
predicates being bridged) at the call site, so the guard prover gets exactly
the fact it needs without a path back into the recursive definitions:

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

The three gaps these close:

1. **`FN-CHECKPOINT-MAKE`'s guard was `T`** but its body calls
   `(fn-retain-capacity (fn-node-retention node))`, and `FN-RETAIN-CAPACITY`'s
   own guard is `(true-listp s)`, not `T` (`retention.lisp:159-161`) — an
   arbitrary guard-`T` `node` carries no such promise. Fixed by strengthening
   the guard to `(fn-node-statep node)` (true at both call sites: inside
   `fn-checkpoint-capture`, guarded by `fn-replay-okp`; in the test book, from
   an already-`fn-checkpointp` value) plus `:hints (("Goal" :in-theory (enable
   fn-node-statep fn-retain-statep)))` — safe to enable directly here because
   `node` is a bare parameter, not something computed via `fn-replay`.
2. **The same `FN-RETAIN-CAPACITY` gap recurs inside `FN-CHECKPOINTP`
   itself** (it destructures its own `node` the same way) and again inside
   `FN-CHECKPOINT-ADMISSIBLE-SPLITP` (on `(fn-node-retention
   (fn-replay-result-node prefix-answer))`), where enabling `fn-node-statep`
   directly would have re-triggered the same `fn-replay` runaway; fixed there
   via `:use (:instance fn-node-statep-implies-retention-true-listp (node
   (fn-replay-result-node (fn-replay groups capacity prefix))))` with
   `fn-node-statep`/`fn-retain-statep` disabled.
3. **`FN-INDEX-MEMBERSHIPS-COMPLETEP`** (in `books/index.lisp`, not
   checkpoint.lisp) called raw `MEMBER-EQUAL` on its `INDEX` parameter, and
   `MEMBER-EQUAL`'s guard needs `(true-listp index)` — again not implied by a
   bare guard-`T` parameter. Fixed by swapping to `FN-AG-MEMBER` (the
   guard-`T` equivalent `FN-SUBSETP`'s own `:exec` branch already uses, proved
   equal to `MEMBER-EQUAL` unconditionally by `FN-AG-MEMBER-IS-MEMBER` in
   `acceptance.lisp`), not by adding a hypothesis — this function's guard
   stays `T`, matching its siblings.

A fourth, purely logical (non-guard) bug also surfaced: my first
`FN-INDEX-MEMBERSHIP-HASP-OF-MEMBER` stated its conclusion with
`FN-AG-CAR`/`FN-AG-CDR`, but `FN-AG-CAR-IS-CAR` rewrites *away* from
`FN-AG-CAR` by default, so every goal that could actually use the rule had
already been normalized to raw `CAR`/`CDR` and the rule's trigger never
matched — `fn-index-membership-entries-sourced`'s proof fell through to an
unprovable fallback branch as a result. Fixed by restating the lemma with
`CAR`/`CDR` to match the normal form ACL2 actually produces.

New keystone, verbatim, hypothesis stack included:

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

Every hypothesis is necessary and independently exercised elsewhere in
`tests/acl2/checkpoint-tests.lisp`: drop `fn-checkpointp` → `:error
:checkpoint` (line ~51-56); drop groups/capacity match → `:error
:configuration` (line ~42-47); drop the frontier-validity/ordering hypotheses
→ `:error :frontier` (line ~48-50); drop the txid-reuse condition (use
`*cp-r1*`, txid 4 ≥ frontier 3 instead) → `:ok`, not `:error :suffix` (the
main restore assertion, line ~23-26). The keystone's own reachable
non-degenerate witness is `*cp-stale-txid*` (txid 2, below `*cp-value*`'s
frontier 3), already present; I added one more assertion using
`(list *cp-stale-txid* *cp-r1*)` to witness "regardless of the rest of the
suffix."

**`fn-replay-okp` hypotheses in `fn-checkpoint-admissible-splitp` — NOT
dropped.** The packet asked me to drop "the `fn-replay-okp` hypotheses the
review says are unnecessary if the equality holds without them." I read the
full independent review (all 274 lines) and could not find a passage stating
these hypotheses are unnecessary — the only nearby finding is about
`checkpoint.lisp:293` not exhibiting the frontier's rejecting role (addressed
above), not about redundant hypotheses. My own check: `fn-sf-record-listp`
(the other structural hypothesis already present) only constrains
sequence/txid ordering; it says nothing about whether `fn-replay` actually
*succeeds* on those records (group/capacity/duplicate/content validity can
still fail). So `(fn-replay-okp prefix-answer)` and `(fn-replay-okp
full-answer)` are not implied by the surrounding hypotheses, and I left them
in place rather than remove something I could not prove redundant without
breaking `fn-checkpoint-plus-suffix-equals-full-replay`.

## 3. journal.lisp header

Replaced the `:444-446` comment block (only comments; no code touched):

Old: "Certified local recovery facts. These are logical properties of the
scanner, conditional on the crash constructor's stated platform assumptions."

New: "Certified local facts about the scanner and completion-action helper
defined above. Each is a definition unfolding or a fact about a single
physical commit image (one sequence/txid pair); none mentions
FN-JOURNAL-CRASH and none is conditioned on the crash constructor's platform
assumptions. This book is the historical isolated-slot journal experiment
named in docs/prefixes.md, not the adapter model the host runs."

## 4. Sentences rewritten (owned files)

| File | Old | New (summary — see diff for exact text) |
| --- | --- | --- |
| `specs/index.md` | "The certified `fn-index-build-sound`, `fn-index-build-complete`, and `fn-index-build-correspondence` theorems establish both directions for rebuilds." | Describes soundp/completep as scanning `fn-article-memberships` directly, never `fn-index-build`; states the induction, and that an omitted/fabricated entry fails completeness/soundness independent of the rest of the index. |
| `specs/checkpoint.md` | Ended at "...restore does not call full replay." | Adds: the equivalence theorem is silent on rejection (both sides reduce to the same expression); names `fn-checkpoint-restore-rejects-frontier-reuse` as the theorem that exhibits the frontier's rejecting role, states its exact conclusion. |
| `docs/implementation.md` (Retention row) | "...evidence-gated release..." | "...release gated on an exact stored evidence string match..." + boundary column: "Evidence is a single admit-string equality, not an issuer/nonce/incarnation/authorization check." |
| `docs/implementation.md` (Replay row) | "A last-good prefix on fault is diagnostic only; no checkpoint, rollback detection, or disk refinement claim" | "...is *meant* as diagnostic only, but no theorem forbids a caller adopting it; every current consumer honors that by convention, not proof. No checkpoint..." |
| `docs/implementation.md` (Article syntax row) | "...unconditional public parser structural-work bounds are certified..." | Splits value vs. cost: value exact, cost a separate instrumented shadow ~16,000x above measured cost, with citation. |
| `docs/implementation.md` (Object assembly row) | "...full public validation/lookup/missing-range work bound certified in a targeted run..." | Names `fn-transfer-missing-ranges`/`transfer-public-bound.lisp:1041`; states it has no caller outside the transfer books, `reserve`/`add-chunk` uncosted, overlap conflict has no byte comparison. |
| `docs/implementation.md` (NNTP bullet) | "Implemented NNTP session/cursor preservation and effect typing are certified" | Splits: session/cursor certified; effect typing loose (2-list shape, not a bounded reply-line grammar). |
| `tests/evidence/2026-09-18-integrated.md` | "committed article-to-archive-pin relation" | "article-to-pin binding as a `(msgid subject pin-id)` string triple... the binding proof does not relate `subject` to the article payload; see `node.lisp:139-157`." |
| `tests/evidence/2026-09-18-article-work.md` | "proves exact correspondence with the actual parser for every ACL2 input" (unqualified) + bare exponent | Splits value/cost; states the ~16,000x gap next to the 17,450,479,652-unit ceiling in the same sentence (per AGENTS.md's "quote the pessimistic number with its scope" rule — this was **not** a count-removal case, it's the *opposite* rule: keep the number, add scope). |
| `tests/evidence/2026-09-18-fields-transfer.md` | (no annotation) | Added historical note: the recorded `transfer.lisp` digest predates a rewrite of that book; JSON untouched. |
| `planning/assurance-closure.md` row 26 | "...preserves all article-to-membership-to-pin bindings" / cites corollaries for PRF-002 / "rejects stale generations" | States `node-traces.lisp:329` is real-but-trivial (no transition removes a binding); names the real keystone (`fn-install-preserves-state`/`fn-watermark-does-not-conflict`) PRF-002 should cite instead of the six `inv⇒inv` corollaries; states `fn-durable-completion-*`'s stale-generation rejection is unreachable from the live path today (production passes `next-txid` for both fields). |
| `planning/assurance-closure.md` row 32 | "Wire book proves partition behavior" / "effect typing...certified" | States the wire partition theorem is scoped to `fn-wire-feed-proper`, not the host's `fn-wire-next`; states effect typing accepts `(:reply (65))` and an unconditional NIL cursor, not yet RFC-bounded. |
| `planning/assurance-closure.md` row 33 | "evidence-gated release" | "release is gated on one stored string match, not authorized evidence"; downgrades the closure-state cell to **not Certified** as an authorization property. |
| `planning/assurance-closure.md` row 34 | "full public validation/lookup/missing-range work bound certified" counted for REP-003 | States the bound is real but has no caller and excludes reserve/add-chunk cost; REP-003's wider claim is **not Certified**. |
| `planning/assurance-closure.md` row 36 | "Certified logical artifacts for checkpoint/suffix replay and rebuilt index queries" | Names the concrete fixes (index against authoritative memberships; new frontier-rejection theorem; all 12 checkpoint functions guard verified). |
| `planning/milestones.md` | "`make check` passed for 22 Markdown files, 49 requirements..." (stale — review's own re-run found 74) | Points to planning/ledger.md instead of repeating a count that had already drifted. |
| `README.md`, `docs/implementation.md`, `planning/milestones.md` | assorted root/function/test counts (75-root/67-test, 533 functions, 678 functions, 41-function codec + 97 remaining, etc.) | Replaced with qualitative property statements plus a plain-text `planning/ledger.md` pointer (not a Markdown link — that file does not exist in this worktree yet; `make check` was run and still passes). |

## Proposals for files I do not own

- **`specs/article-fields.md:51`** — current: `` `fn-af-message-id-equalp` is exact octet equality when both operands are valid, as required by RFC 3977 Appendix A.2 and OBJ-002.`` Proposed: "`fn-af-message-id-equalp` is exact octet equality when both operands are valid; RFC 3977 Appendix A.2 requires exactly this case-sensitive, no-folding comparison. The certified theorem for this equality is a direct unfolding of `fn-af-message-id-equalp`'s definition (`article-fields.lisp:311-314`), not an independent structural proof: it shows the function does what it is defined to do, not a separate RFC-compliance argument beyond the definition itself."
- **`specs/bp-ingress.md:73`** — current: `` `tests/acl2/bp-ingress-tests.lisp` certifies a complete exact-byte ingress, actual Store finish, duplicate refusal, crash/recovery reconstruction, malformed article rejection, destination-policy rejection, missing/duplicate critical field rejection, and unknown-group rejection.`` Proposed: replace "certifies" with "exercises... as 25 `assert-event` executable examples over the same parser and acceptance definitions — `bp-ingress.lisp` itself has no `defthm`, so this is example coverage, not a general theorem; 35 of the book's functions remain unguarded."
- **`specs/store-refinement.md:270`** — current: "...exhausts 211 states and 9,038 edges, including allocator/record crash choices and recovery barrier counts." Proposed: "The bounded explorer exhausts a fixed state/event product (see planning/ledger.md for the exact counts) over two fixed records and no txid-gap record; it does not include the two syscall-returned-unobserved crash points the independent review's D4 finding identifies, and its edge count includes no-op self-loops rather than only meaningful transitions."
- **`docs/prefixes.md:12`** — current tag description "Abstract retention accounting: pins, charges, evidence-gated release." Proposed: "...pins, charges, release gated on a stored evidence-string match."
- **`planning/proofs.json` (PRF-002)** — proposed: retarget its cited events from the six `node-invariants.lisp`/`acceptance-invariants.lisp` `*-preserves-*` corollaries to the keystone `fn-install-preserves-state` with `fn-watermark-does-not-conflict` (`acceptance-invariants.lisp:65-192`).
- **`tests/acl2/bp-workflow-binding-invariants-tests.lisp:78-90`** — proposed: add a second fabricated-work witness that separates subject-equality from archive-equality (the existing witness only exercises the missing-msgid clause); I did not read this book's exact predicate names since it is outside my ownership and I did not want to guess signatures without ground truth.
- **`specs/article-parser.md:88`** — current: "Full parser work/allocation proofs and other semantic fields remain open." This contradicts `specs/article-work.md`, which exists specifically to close the structural-work part of PRF-016. Proposed: "Parser structural-work correspondence and bounds are closed for `fn-article-parse` by the work specification (`article-work.md`, same directory), subject to its own scope (value-side exact correspondence; cost-side is a separate instrumented shadow, not measured real cost — see tests/evidence/2026-09-18-article-work.md); other semantic fields remain open."

## 5. planning/now.md and planning/evidence-index.md

`now.md` is 40 lines (checked with `wc -l`), structured as What runs / What is
proved with scope / Next, with no counts. `planning/evidence-index.md` is new,
one row per file in `tests/evidence/*.md` (16 rows) with date, source
revision (or "no git revision recorded" for the two pre-revision-tracking
records), what it covers, and what it explicitly does not show. Linked from
`now.md` (line 3) and `docs/README.md` (new "Sources of truth" row).

## 6. planning/swarm-cycles.md

Added a "Roles" section (Terra=`gpt-5.6-terra`, Sol=`gpt-5.6-sol`,
Luna=`gpt-5.6-luna`, Astra=the Codex root; names are allocations, not
correctness claims). Replaced the C1 packet table with review §8's Order/
Packet/Change/Tier table verbatim (0-14, six new/reshaped packets), kept the
C2 and C3 tables unchanged, and kept the review's "non-negotiable prompt
content" list as a bullet paragraph.

## 7. planning/assurance-closure.md

Rows 26, 32, 33, 34, 36 corrected — see the sentence table in §4 above; each
names the actual theorem and cites the review's finding (either by file:line
or by "review §4 row N").

## 8. tests/evidence/*.md

`2026-09-18-fields-transfer.md` now has a historical annotation that its
`transfer.lisp` digest predates a rewrite of that book. No `.json` file was
opened for writing (only read, to extract revision hashes for
evidence-index.md).

## Commands run and results

- `python3 tools/check_scaffold.py` (`make check`): PASSED, run repeatedly
  after edits, last at "Scaffold OK: 78 Markdown files, 49 requirements, 18
  proof targets, 18 scenario specifications."
- Full `make certify` (unfiltered `ACL2_BOOKS` list), attempt 1 (background,
  killed by an external session reset before completion) and attempt 2 (same
  cause): both confirmed dead (no `certify_books.py` process left) before I
  restarted; neither reached `books/checkpoint`/`books/index`, so no edit ever
  raced a live certification of those two files.
- Full `make certify` attempt 3: ran to completion, **FAILED** at
  `books/checkpoint` (`FN-CHECKPOINT-MAKE` guard) and `books/index`
  (`FN-INDEX-MEMBERSHIPS-COMPLETEP` guard) — real bugs in my own new code, not
  a box/timeout artifact. Root cause and fixes are in §2 and §1 above.
- Root/coordinator notice mid-run 3: with ten lanes sharing the box,
  `books/article-properties` can exceed the certify runner's default 600s
  per-book timeout; going forward, set `FN_ACL2_TIMEOUT_SECONDS=1800`. Attempt
  3 had already certified `books/article-properties` successfully without the
  variable, so I let it finish rather than restart; its failure was a real
  proof/guard bug, not a timeout, so I fixed the bugs rather than just
  retrying with the variable.
- Scoped `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py
  books/checkpoint tests/acl2/checkpoint-tests books/index
  tests/acl2/index-tests` (using the still-valid `.cert`s attempt 3 produced
  for every earlier book), iterated three times while fixing the guard/proof
  bugs in §1/§2:
  - Attempt 1: FAILED — `FN-CHECKPOINT-MAKE` guard (fixed), and separately
    `FN-INDEX-MEMBERSHIP-ENTRIES-SOURCED`'s proof (the `FN-AG-CAR`/`CAR`
    rewrite-matching bug, fixed) — `books/index` failed on that proof, not a
    guard.
  - Attempt 2: `books/index` and `tests/acl2/index-tests` **PASSED**.
    `books/checkpoint` FAILED — `FN-CHECKPOINT-ADMISSIBLE-SPLITP` guard, a
    second occurrence of the `FN-RETAIN-CAPACITY` gap, this time behind a
    `FN-REPLAY`-computed `prefix-answer` (fixed with the third bridging
    lemma, `:use`d rather than enabled, to avoid the runaway).
  - Attempt 3: **ALL FOUR PASSED** — `build/acl2/certify-20260919T063633Z-34181`,
    "ACL2 certification passed: books/checkpoint, tests/acl2/checkpoint-tests,
    books/index, tests/acl2/index-tests".
- Full `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` (the GATE run, all 113
  roots, run after the scoped run above went green): see the addendum at the
  bottom of this file, appended after it completed, for the final result.
  Before launching each certify invocation above I checked `lsof -a -p <pid>
  -d cwd` on every live `certify_books.py`/`saved_acl2.core` process to
  confirm none had a hygiene-worktree cwd, since `ps aux` alone does not
  distinguish this lane's ACL2 process from the other nine lanes sharing the
  box.

## Known defects / remaining gaps

- `fn-checkpoint-admissible-splitp`'s `fn-replay-okp` hypotheses were not
  dropped (see §2); if a future lane can prove them redundant, that is new
  work, not a hygiene-lane gap.
- Several §4 review findings in files I do not own remain unfixed; exact
  replacement text is proposed above for the next lane/root to apply.
- `books/README.md` and `planning/proofs.json` contain material relevant to
  this packet (a `node`/`node-invariants` binding description, and PRF-002's
  citation) but are outside my explicit OWNED list; I left them untouched and
  proposed the proofs.json change above instead of guessing at edit rights.
