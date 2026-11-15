# Budgeted digest fetch: current-source proof packet

SOURCE-ONLY successor to the frozen6a5 author check described below. The current structural-theory
proof boundary has not run in ACL2. Archive authority and hold
release remain unfinished; this packet grants neither.

The base is `a1dba5a1c7bd303ba6085c589b9020c357624079`. The entire original
`fn2-rec-fetch` definition, `fn2-rec-byte-at` definition and two byte theorems,
and `fn2-rec-fetch-shape` theorem are byte-identical to the base. The original
pool-digest blob is `d1e67d1c69ed93f48841082bb5517fe8193e9f87`, SHA256
`f7d2dd9f1687703d8df34e771925515c32998325d844bbc05d316e63191c1096`.
No pool/layout/column/BLAKE3 source is changed. In particular, the qualified
layout SHA256 stays `2060684efd33bb23e0c426275edc9a3dc6c47b50ceda0b80207c84ec7fd89d48`.

`fn2-rec-fetch-step` consumes at most its byte budget, returning the absolute
next byte and a width-constrained partial U32 accumulator. It calls the existing
`fn2-layout-byte :u32` transition and writes a digest word only after all four
bytes succeed. Budget zero preserves the complete carrier and continuation. The public
`fn2-rec-fetch-step-result-state` theorem exports validity of the returned
next/partial state for valid input/budget/offset, including source errors;
invalid-input `:bounds` continues to echo its arbitrary input state.
An owner/stale/bounds error preserves the partial word and all previously
committed words. The pool is read-only. The unchanged old fetch remains the
reference for code and complete digest-carrier effects.

`fn2-rec-fetch-exec-refines` states exact two-result equality under the original
typed guard. Local proof support supplies a full four-result worker composition
statement, extracts the aligned four-byte reads/store from the original fetch,
and splits the remaining worker at that word. The final hint inducts the
original fetch. These statements and guard events are authored, UNRUN proof
obligations, not established equalities. Source controls cannot discharge them. Independent source review found no
guarded code/effects mismatch and identified the exported result-state theorem
needed by downstream continuation guards; its hint uses the same local bound.
The first refuting gate must admit the new definitions, invariant/composition
lemmas and guard events before reaching the final equality; a failure there
must be fixed before importing the event-reader continuation.

`tests/pool-digest-budget-unit.lisp` uses the actual U32 encoder and independent
boundary words including high-bit/all-one values. It checks all aligned starts
0..8 against the unchanged API with complete carrier copies and the whole
refinement premise, 32 budget-one visits, budget-zero effects, wrong owner,
stale generation, stale after a partial word (byte5/acc255), and a fill10
failure with identical complete-carrier effects. The expected values are not
derived by decoding the writer output. These executable controls are UNRUN.

The mechanical transformations and their before fixtures are in
`tools/pool_digest_budget_rewrite.py` and `tools/pool_digest_proof_rewrite.py`.
Ten Python source controls pass. Lisp structural checks, secrets and diff
checks pass. No whole-book proof or executable fixture success is claimed.

## Exact dependency/cache cut

`digest-fetch-current-inventory.json` records the plain-world v4 closure keys,
source/form hashes and candidate cache metadata for exactly ten local books.
The nine unchanged dependencies have compiled candidates at
`fn@forge:/home/fn/.cache/fn-certs` for toolchain
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`;
only the changed `books/pool-digest` key misses. Candidate integrity/origin
selection used the existing `certs.cached_entries`/`choose_entry` recipe from
`/build/lanes/ticket-frontier-3b62`. This is metadata and payload-integrity
inventory, not ACL2 core/pair compatibility or certification. The earlier
hbox default-cache query is superseded and supplies no miss evidence.

Reproduce the read-only inventory with:

```
python3 tools/digest_fetch_current_inventory.py --remote --output /tmp/digest-fetch-current.json
```

The shared launcher coordinate supplied by the integrator is
`/tank/fn/toolchains/w28/acl2-literal-4g-tls64k`. No launcher was invoked. Any
later gate requires a named root compute grant and must reuse the nine cached
candidates without silently certifying dependencies. The broader cold archive
reader/boot closure is deliberately excluded from this prerequisite packet.

## Frozen6a5 first refusal and proposed local boundary

Root granted one author-only exact ten-book check of `6a5ab24a0`, using nine
cached dependencies, 2 GiB external MemoryMax, zero swap, 600 total seconds,
and fresh 2 million steps/20 seconds per original event. Client preflight
accepted all 42 forms. The source range began at the local system include so
its arithmetic theory remained inside the source encapsulate. The original
byte reader/theorems and new state predicate admitted, then worker definition
form14 refused during termination: rewrite call-depth1000, 1,515 steps and
0.04 ACL2 seconds (the enclosing source attempt reported 0.27 seconds). The
final equality, worker guards and all fixture assertions were unreached.
This is a proof-engine refusal, not a counterexample or certification.

`digest-fetch-6a5-author-refusal.json` binds the raw input/refusal hashes and
scope. Raw artifacts remain under the owned lane's
`build/coordinator/evidence/digest-fetch-6a5/` and remote `/tmp/digest-fetch-6a5-*`.
Explicit release stopped only the recorded own session: outer1395116,
wrapper1395117, server1395153 and ACL2 group1395157 were all absent, and
`run-p1395116-i30751807.scope` was absent before ledger release was reported.

The displayed termination goal is `(o-p (nfix left))` plus decrease of
`(nfix (- left 1))` under `(not (zp left))`; all source/codec branch facts are
irrelevant to that measure. The refusal's rule summary shows the enabled
state predicate opening unsigned-byte/integer-range/exponent arithmetic in
those branch facts. No gstack was captured, so this source diagnosis does not
claim to identify a unique repeated rewrite rune.

The proposed fix adds only local `fn2-rec-fetch-left-measure`, stating that
scalar natural-measure fact, and a worker termination hint that uses it under
`minimal-theory`. The unchanged worker measure, guard and executable body do
not depend on semantic state normalization. A source control checks the exact
helper formula, absence of codec/pool arguments, the explicit minimal theory,
and byte-identical worker body; the old fetch remains entirely byte-identical.
No rewrite depth, step/time allowance, runtime data domain or error behavior
changes. The minimal next question is whether this local natural-measure
boundary admits, and then which next original event is first to refuse.
The successor requires a new named root scope; no retry has run.

## Frozen734 next refusal and structural boundary

A separately granted author check of `7349fa4fa` used the same limits and a
fresh owned worktree/session. The scalar LEFT lemma and worker termination
admitted within the source encapsulate. The next first refusal was local
`fn2-rec-fetch-bytes-shape`: rewrite call-depth1000, 8,129 steps and 0.07 ACL2
seconds (enclosing source attempt 0.33 seconds). No final equality or worker
guard event was reached. The entire attempted encapsulate subsequently failed;
these event admissions do not constitute a certified or exported book.

`digest-fetch-734-author-refusal.json` binds that unchanged source/input and raw
refusal. Explicit cleanup removed outer1404825, wrapper1404826, server1404866,
ACL2 group1404870 and `run-p1404825-i30761516.scope` before release was reported.
Raw artifacts remain in the owned ignored `build/coordinator/evidence/` and
remote `/tmp/digest-fetch-734-*`; no fixture or record job ran.

The structural carrier theorem requires only the original carrier recognizer,
row validity, and actual `fn2-digest-set-word-shape` after a whole-word write.
The worker explicitly tests `unsigned-byte-p 32 word` before that write. It
need not establish the decoded value or partial-state arithmetic to preserve
carrier shape. Its former hint enabled the worker/row predicate but left the
semantic state and width definitions enabled; the raw refusal again shows
integer-range/exponent arithmetic opening in the induction branches.

The successor changes only that local hint to enable worker/row reasoning
while keeping `fn2-rec-fetch-state-p` and `unsigned-byte-p` opaque. Existing
setter-shape rules can consume the explicit width hypothesis without decoding
it. The exact theorem, recursive body, measures, guards and public contracts
remain unchanged. A source control checks the full carrier-shape conclusion
and these theory boundaries. This is an unrun source proposal, not an argument
that the next proof succeeds; it requires a fresh named root scope.
