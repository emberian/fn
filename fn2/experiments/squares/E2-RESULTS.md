| Consumer / shared machinery | Declaration lines | Other new handwritten lines | Copied support lines | Admitted rows | Generated correspondence events |
|---|---:|---:|---:|---:|---:|
| Q1 reference vs concrete | 6 (5 form + 1 wrapper) | 347 physical / 295 code | 0 | 39 cases + 1 composition, all owed | 40 statements + 40 rows + 1 coverage |
| Q4 read-state fold/summary | 8 (7 form + 1 wrapper) | 361 physical / 304 code | 631 physical / 393 code | 3 event cases + composition + G0, all proved | 5 statements + 5 rows + 1 coverage + 5 proof theorems |
| Shared envelope, evidence driver and loading | — | 392 physical / 349 code | 0 | — | — |
| Envelope controls and standalone controls | — | 171 physical / 160 code | 0 | test rows excluded above | — |
| Sequential runner and inventory tool | — | 169 physical | 0 | — | — |

# Experiment E2 pass 3 — declared roles bind generated statements

**COHERENCE §5.2 / decision 2: SHARE this public envelope, with specialized
statement templates.** Both consumers generate their case statements from
role constants, and the common envelope refuses absent declared roles unless
the row explicitly names an unused-role exception. The measured cost includes
those exceptions, proof bridges and checker adapters; it establishes neither a
universal semantic template nor a net code-size saving.

**DSL-METATHEORY §9 item 1: share declarations, keep independent semantic
judgments.** Q1's bounded correspondence checks can pass a shared-handler
defect such as M4 while the client oracle catches it; Q4 proves preservation
of its chosen relation and observations, not a shared event interpretation's
conformance to an external protocol. Neither generated statements nor role
occurrence checks replace that independent judgment.

All 14 books pass local ACL2 `certify-book` below 60 seconds each. The table
contains 45 rows, 40 owed and five proved, with 83 separate evidence records.
Fresh ORIGINAL campaigns complete 10,004 G1 checks across 19/39 cases;
**20/39 remain unexercised**. [Acceptance](e2/acceptance.txt),
[author check](e2/author-check.txt), [report](../../../build/REPORT.md).

## Binding the declared roles

`sq-q1-case-formula(case, contract, sides)` obtains every named semantic call
from `*sq-q1-contract*` and `*sq-q1-sides*`. The same constants reach the
`defsquare` declaration through its `make-event` wrapper and reach the binder
as arguments. Structural Lisp operators and variable names belong to the
specialized template; they are not additional semantic implementations.

| Q1 role | Function(s) | Position in the iteration formula |
|---|---|---|
| contract `:pre` | `sq-q1-loop-invp` | Antecedent invariant |
| contract `:enabled` | `sq-q1-continuep` | Continuation premise |
| contract `:casep` | `sq-q1-casep` | Registry-label premise |
| contract `:relation` | `sq-q1-loop-invp` | Successor invariant/relation |
| contract `:observation` | `sq-q1-effects-agreep` | Before/after effect agreement |
| contract `:budget` | `sq-q1-budget` | Both transition calls |
| contract `:advance` | `sq-q1-advance` | Successor context |
| sides `:concrete` | `fn2-transition`, `fn2-exec-account-work` | Transition then accounting |
| sides `:reference` | `fn2-ref-transition` | Reference transition |

`:relation` denotes the full successor invariant, including admissibility.
That is the function occurring in the preserved statement, and is also the
precondition function. The narrower `sq-q1-loop-relatedp` remains inside the
invariant's definition; it is not advertised as a direct row role or excused
as unused. This role choice permits the requested direct occurrence check
without unfolding arbitrary helpers or changing any Q1 proposition.

The runner asserts that all **39 translated iteration bodies are exactly
unchanged from pass 2**, using SHA-256 of the canonical printed list of
`(row-id . translated-body)` pairs in catalogue index order:

```text
c2b514f22e46ffa58a15fa4c247605feb25ef21ac2409f652fa89eb2ab2dec78
```

The baseline was extracted from the pass-2 TABLE snapshot at
`c134ae187d2fb53904075fad57ef58fab46e0d74+E2-sha256:f6b0636f6a6f4fad908cda1a93bb9b88dd81f2309a3b8ab71492811beb8382c7`
before editing Q1. `q1-pass2-translated.sha256` pins it; the driver serializes
current admitted bodies to `q1-translated.sexp`, and `run.py` compares the hash
and fails the author check on any difference. Printing uses ACL2's package,
readable output, no pretty printing, no length/level truncation, and a final
newline. The baseline file is included in the run's source identity. The
composition row separately continues importing the existing owed
`fn2-turn-refinement` formula and its original antecedent unchanged.

The generic envelope runs `all-fnnames` on each translated statement after
removing guard holders. For each effective contract/side role, **every named
function must occur**, including calls inside lambda bodies, unless that role
is explicitly listed in `:unused-roles`. Payload `:contract` and `:sides`
overrides are applied before this check. Exceptions are qualified pairs such
as `(:contract :step)`; they must equal the missing-role set, so unknown,
duplicate or redundant exceptions are rejected. The actual list is stored in
the row. Function resolution, proof-formula equality, coverage and separate
proof/evidence status remain in force. There is no Q1/Q4 branch in the macro.

| Rows | Explicit unused roles | Why absent from this statement |
|---|---|---|
| All 39 Q1 cases; Q1 composition | None | All effective roles occur directly |
| Q4 read, catchup, malformed | contract observation, fold, converter | Event preservation calls steps and relation, not queries, folds or conversion |
| Q4 composition | contract step, recognizer, converter | Suffix statement calls folds and observations; it does not spell out single-event steps or conversion |
| Q4 converter | contract step, recognizer, observation, fold; sides source, target | G0 asserts target admissibility and the relation after conversion; observation functions remain inside that relation's semantics |
| Count-only step test (not a store row) | contract observation, fold | Same event-statement boundary as above |

Q4 event sides now name just the steps, composition sides just the folds;
converter sides name source/target observations and the converter, with those
two observation roles explicitly unused. This is meaningful boundary metadata
with visible exceptions, not a claim that every boundary uses every contract
role. These exception lists and per-boundary side adapters are measured strain.
The role constant and wrapper avoid a second copy of the contract itself.

This is a syntactic occurrence condition, not a theorem that a named function
has the intended meaning, occurs at the intended argument position, or affects
the result. An author can explicitly exempt a role; that is a reviewable waiver,
not evidence for it. The specialized builders, proof obligations and semantic
teeth remain necessary. The full store is still not a case-partition proof.

## Controls and proved Q4 claims

Both consumers have an output-enabled `must-fail` role-divergence control.
Q1 keeps its generated statement but declares `sq-q1-loop-relatedp` as the
relation instead of the full invariant; Q4 keeps its generated statement but
declares `rs-count2-rel` instead of `rs-same-reads`. Both substitute existing
functions, use fresh row/owner names and `:proof (:owed)`, and are refused
specifically for the unlisted absent `(:contract :relation)`. Assertions check
that neither the row nor the owner survives. [Refusal output](e2/role-refusals.txt)
is extracted verbatim from certification, not inferred from a failed search.

The original `defsquare-tests` controls, Q1 per-case checker teeth, Q4 count
contract and incorrect-summary `(2)` fixture all still pass their expected
outcomes. The count-only template's complete step and composition implications
evaluate NIL with full true antecedents at the tooth-1 witness. The strong
proof cannot be attached to that weak generated step: its genuine unused
observation/fold roles are explicitly listed, leaving the exact proof-formula
check as the independent refusal. The original off-by-one summary tooth runs.

Q4's accepted `sq-fs-formula` is unchanged. It replaces pass 1's circular
copying of a theorem formula followed by comparison with that same theorem. It generates relation plus both
post-admissibility claims for each recognized event kind and the malformed
complement, admissibility plus relation for G0, and relation plus observation
equality after arbitrary suffixes for composition. Event tags come from the
admitted recognizer; no second event catalogue is written.

| New proved theorem | Original formula matches? | Proof bridge |
|---|---|---|
| `sq-q4-generated-read` | No | `rs-same-reads-of-read` plus both step-admissibility lemmas |
| `sq-q4-generated-catchup` | No | `rs-same-reads-of-catchup` plus both step-admissibility lemmas |
| `sq-q4-generated-malformed` | No | `rs-same-reads-of-other` plus both step-admissibility lemmas |
| `sq-q4-generated-converter` | No | `rs-summarize-related` plus `rs-s-ok-of-summarize` |
| `sq-q4-generated-composition` | Yes | `rs-summary-adequate` by `:use` |

All five bridges instantiate one eight-line `defthm` skeleton within the
14-line proof emitter, with a five-line support selector. There are zero
separately handwritten per-kind bridge bodies, but the emitter, selector,
source-lemma naming, invocation and copied lemmas are all counted. Composition
is generated from roles; its proof reuses the theorem whose functional
instances are `fc-rel-fold` and `fc-obs-fold`. Functional instantiation constrains
the mathematical premises, not the use of theorem introspection to construct
the statement. No new induction was needed beyond the copied support.

## Measurements and covered scope

The pessimistic package count is **2,085 physical source lines: 1,454 new +
631 copied**. Fourteen lines are wrapped consumer declarations; 2,071 are
other source. Bare declaration forms total 12 lines. The table above includes
both consumer controls, generic envelope, evidence adapters and reporting of
checks; it excludes generated evidence/import events, baseline/output data,
JSON, prose, logs and unchanged layer-A/E1 dependencies. Physical lines include
comments/blanks; Lisp code lines exclude those. No implemented hand-registration
baseline exists, so this is a cost inventory, not a measured net LOC saving.
Each declaration also emits one diagnostic `value-triple`; negative controls
leave no additional accepted correspondence rows.

The generic envelope is 208 physical / 182 code lines. Q1's role constants
cost seven form lines; Q4's role constant costs five, all charged to support.
The named inventories below give every helper, contract function, copied lemma,
fixture and adapter by name. Exception declarations and the Q1 hash check are
included in these source costs.

| Book | ACL2 seconds | Wall seconds (rounded up) |
|---|---:|---:|
| `defsquare.lisp` | 0.13 | 0.531 |
| `defsquare-tests.lisp` | 0.41 | 0.794 |
| `fold-contract.lisp` | 0.05 | 0.573 |
| `read-state-history.lisp` | 0.03 | 0.316 |
| `read-state-summary.lisp` | 0.20 | 0.429 |
| `read-state-transport.lisp` | 0.09 | 1.145 |
| `read-state-teeth.lisp` | 0.48 | 1.260 |
| `q4-checker.lisp` | 0.43 | 1.042 |
| `q4-template.lisp` | 0.03 | 0.392 |
| `q4-square.lisp` | 0.57 | 1.092 |
| `q4-template-tests.lisp` | 0.42 | 0.947 |
| `q1-contract.lisp` | 2.24 | 2.697 |
| `q1-bindings.lisp` | 2.69 | 3.577 |
| `q1-template-tests.lisp` | 2.29 | 3.144 |

All 14 books were certified serially with warm dependencies. The slowest was
**3.577 seconds wall, rounded upward, / 2.69 seconds ACL2** for
`q1-bindings`. Triage reports zero real/cascade/limit/killed/other failures,
three intentionally caught must-fail logs and 11 clean logs. These are local
laptop author certificates, not farm/record-toolchain certification.

| Fresh ORIGINAL campaign | Charged transitions | Entered G1 | Completed G1 | Cases / 39 | Trials / prefixes | Seconds | Result |
|---|---:|---:|---:|---:|---:|---:|---|
| random, seed 1 | 20,000 | 5,004 | 5,004 | 19 | 22 trials | 0.214641 | transition cap |
| enumeration, requested depth 4 | 20,000 | 5,001 | 5,000 | 9 | 601 prefixes | 0.392816 | transition cap; depth 4 not exhausted |

Across both runs, 10,004 completed G1 checks pass; 19/39 distinct cases are
exercised and **20/39 unexercised**. No outside-catalogue label occurs. One
enumeration call enters but is interrupted before completion, so it is not
exercised. E1 charges transitions before its cap check; charged calls are not
all completed calls. Per-row G1 counts are reconciled with E1's own counters.
The full acceptance process took 5.845 seconds as reported by the runner;
campaign-only times exclude loading. All five Q4 fixtures pass. Evidence
import leaves 40 Q1 rows owed and five Q4 rows proved, with 83 scoped records.

Q1 checks the existing G1 projection: five return values, normalized concrete/
reference correspondence and shape. It does not evaluate every conjunct of
the stronger proof-only invariant, and its 19 pairs of executed runtime teeth
are G1 checker witnesses. The original seven-fault/two-word domain, random
choices, client oracle, allocator and latency monitors are unchanged. Q1 is
reference-vs-concrete; no fused dispatcher exists. Fusion would add the
fused-vs-unfused E square composed vertically, plus TRACE on common runs.

`fn2-work-certificate` independently folds records into five additive totals;
per-turn comparisons and across-turn concatenation do not furnish a stronger
future-sensitive relation. Q4 therefore uses the authorized read-state fallback.
Its relation quantifies over all article queries; its count-only tooth uses
one fixed bound. Equality of counts at every bound already identifies the read
set, so strict strength is relative to the chosen observation; future step
closure is the composition condition. The five copied books retain exact
source contents after provenance headers for acl2aiguide commit
`2283433658784eb4767192508f0e5135a8c939b1`, with only local includes.

## What this does not show

No Q1 theorem is discharged. Entry, exit, termination, partition and accounting
remain named missing obligations. Twenty Q1 rows remain unexercised and their
teeth unimplemented; the composition also has no checker and its teeth remain
unimplemented. G1 evidence is not proof of the full invariant. Q4 fixture
queries cover only articles through 5; its proved composition is unbounded
under its hypotheses. Proof-only functions include unverified guards.

There is no universal semantic template, net code-size saving, production
coverage or performance conclusion, served-path summary replacement, historical
availability theorem, fusion implementation, new client oracle or farm green
claim. M4 is prior E1 evidence, not rerun here: both sides share the wrong send
offset while the independent client oracle detects the defect. Sharing does
not make the precise refinement proposition vacuous, and role occurrence does
not prove the shared semantics correct. No commit or push was made.

## Per-case G1 evidence

Counts are completed calls, not reached calls. Zero means unexercised, not
passing. All 39 cases retain `:proof (:owed)`; empty-principal enumeration
reached 1,810 calls and completed 1,809.

| Case | Random | Enumeration |
|---|---:|---:|
| `(:run fn2-listener :accepting)` | 270 | 584 |
| `(:run fn2-listener :closing)` | 39 | 0 |
| `(:observe fn2-listener :accept-result)` | 160 | 20 |
| `(:observe fn2-listener :close-result)` | 37 | 0 |
| `(:run fn2-echo :free)` | 0 | 0 |
| `(:run fn2-echo :command)` | 70 | 0 |
| `(:run fn2-echo :reply)` | 73 | 0 |
| `(:run fn2-echo :closing)` | 42 | 0 |
| `(:run fn2-echo :draining)` | 40 | 0 |
| `(:run fn2-echo :retired)` | 0 | 0 |
| `(:observe fn2-echo :receive-result)` | 68 | 0 |
| `(:observe fn2-echo :send-result)` | 50 | 0 |
| `(:observe fn2-echo :borrow-released)` | 50 | 0 |
| `(:observe fn2-echo :close-result)` | 41 | 0 |
| `(:run fn2-scribe :free)` | 0 | 0 |
| `(:run fn2-scribe :reserve)` | 22 | 147 |
| `(:run fn2-scribe :fill)` | 0 | 0 |
| `(:run fn2-scribe :patch)` | 0 | 0 |
| `(:run fn2-scribe :write)` | 0 | 0 |
| `(:run fn2-scribe :write-result)` | 0 | 0 |
| `(:run fn2-scribe :fence)` | 0 | 0 |
| `(:run fn2-scribe :fence-result)` | 0 | 0 |
| `(:run fn2-scribe :reset)` | 0 | 0 |
| `(:run fn2-scribe :read)` | 0 | 0 |
| `(:run fn2-scribe :read-result)` | 0 | 0 |
| `(:run fn2-scribe :verify)` | 0 | 0 |
| `(:run fn2-scribe :next)` | 0 | 0 |
| `(:run fn2-scribe :stopped)` | 0 | 0 |
| `(:observe fn2-scribe :write-result)` | 0 | 0 |
| `(:observe fn2-scribe :fence-result)` | 0 | 0 |
| `(:observe fn2-scribe :read-result)` | 0 | 0 |
| `(:router :fallback)` | 0 | 0 |
| `(:executor :clock)` | 304 | 28 |
| `(:executor :signal)` | 0 | 0 |
| `(:executor :service 0)` | 534 | 603 |
| `(:executor :service 1)` | 534 | 603 |
| `(:executor :service 2)` | 534 | 603 |
| `(:executor :service 3)` | 534 | 603 |
| `(:executor :empty-principal)` | 1602 | 1809 |

## Named handwritten inventory

Regenerated by `e2/inventory.py`. Form spans may overlap for nested generated
controls and are not summed as file costs. Includes, assertions, comments and
blanks are included in file totals. Existing E1 reuse remains 658 physical
lines: checks 119, choices 80, runner 371, fixtures 88; excluded from new source.

### Q1 named support

`q1-bindings.lisp` — 57 physical / 50 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `sq-q1-case-origin` | `defun` | 3 |
| `sq-q1-id` | `defun` | 2 |
| `sq-q1-bind-cases` | `defun` | 18 |
| `sq-q1-bindings` | `defun` | 18 |

`q1-contract.lisp` — 110 physical / 89 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `sq-q1-fuel` | `defun` | 1 |
| `sq-q1-h` | `defun` | 1 |
| `sq-q1-k` | `defun` | 1 |
| `sq-q1-a` | `defun` | 1 |
| `sq-q1-obs` | `defun` | 1 |
| `sq-q1-visits` | `defun` | 1 |
| `sq-q1-actions` | `defun` | 1 |
| `sq-q1-ref-bytes` | `defun` | 1 |
| `sq-q1-ref-steps` | `defun` | 1 |
| `sq-q1-budget` | `defun` | 1 |
| `sq-q1-advance` | `defun` | 6 |
| `sq-q1-normalize-reference-work` | `defun-nx` | 2 |
| `sq-q1-loop-relatedp` | `defun-nx` | 4 |
| `sq-q1-nat-listp` | `defun` | 3 |
| `sq-q1-loop-invp` | `defun-nx` | 18 |
| `sq-q1-continuep` | `defun-nx` | 8 |
| `sq-q1-casep` | `defun-nx` | 3 |
| `sq-q1-effects-agreep` | `defun-nx` | 10 |
| `*sq-q1-contract*` | `defconst` | 4 |
| `*sq-q1-sides*` | `defconst` | 3 |
| `sq-q1-case-formula` | `defun` | 15 |

`q1-template-tests.lisp` — 24 physical / 21 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `sq-q1-role-divergence` | `defsquare` | 9 |

`q1-campaigns.lsp` — 162 physical / 141 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `*sq-q1-g1-original*` | `defvar` | 1 |
| `*sq-q1-scope*` | `defvar` | 1 |
| `*sq-q1-outside-catalogue*` | `defvar` | 1 |
| `*sq-q1-tooth-cases*` | `defvar` | 1 |
| `*sq-q1-campaign-results*` | `defvar` | 1 |
| `sq-q1-copy-core` | `defun` | 4 |
| `sq-q1-fresh-sample` | `defun` | 4 |
| `sq-q1-install-teeth` | `defun` | 17 |
| `sq-q1-check-sample` | `defun` | 16 |
| `sq-q1-install-attribution` | `defun` | 19 |
| `sq-q1-attribution-counts` | `defun` | 15 |
| `sq-q1-restore-hooks` | `defun` | 3 |
| `sq-q1-run-one-campaign` | `defun` | 39 |
| `sq-q1-run-campaigns` | `defun` | 16 |

### Q4 named support

`fold-contract.lisp` — 100 physical / 58 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `fc1-init` | `defun` | 1 |
| `fc2-init` | `defun` | 1 |
| `fc1-step` | `defun` | 1 |
| `fc2-step` | `defun` | 1 |
| `fc1-obs` | `defun` | 1 |
| `fc2-obs` | `defun` | 1 |
| `fc1-ok` | `defun` | 1 |
| `fc2-ok` | `defun` | 1 |
| `fc-rel` | `defun` | 1 |
| `fc-init-ok` | `defthm` | 3 |
| `fc-rel-init` | `defthm` | 2 |
| `fc-rel-step` | `defthm` | 5 |
| `fc-rel-obs` | `defthm` | 3 |
| `fc1-fold` | `defun` | 2 |
| `fc2-fold` | `defun` | 2 |
| `fc-fold2-induct` | `defun` | 4 |
| `fc-ok-fold` | `defthm` | 5 |
| `fc-rel-fold` | `defthm` | 4 |
| `fc-obs-fold` | `defthm` | 6 |

`q4-checker.lisp` — 99 physical / 83 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `sq-q4-field` | `defun` | 3 |
| `sq-q4-queries-agree` | `defun` | 6 |
| `sq-q4-event-case` | `defun` | 3 |
| `sq-q4-positive` | `defun` | 8 |
| `sq-q4-count-only-refused` | `defun` | 6 |
| `sq-q4-off-by-one-refused` | `defun` | 9 |
| `sq-q4-negative` | `defun` | 3 |
| `sq-q4-checker` | `defun` | 25 |

`q4-square.lisp` — 148 physical / 128 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `sq-q4-quoted-keywords` | `defun` | 7 |
| `sq-q4-cases` | `defun` | 5 |
| `sq-q4-theorem` | `defun` | 8 |
| `*sq-q4-contract*` | `defconst` | 5 |
| `sq-q4-proof-name` | `defun` | 4 |
| `sq-q4-proof-support` | `defun` | 5 |
| `sq-q4-proof-events` | `defun` | 14 |
| `sq-q4-evidence` | `defun` | 14 |
| `sq-q4-requires` | `defun` | 12 |
| `sq-q4-bindings` | `defun` | 39 |

`q4-template-tests.lisp` — 81 physical / 65 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `*sq-q4-count-contract*` | `defconst` | 5 |
| `sq-q4-count-generated-step` | `defun` | 3 |
| `sq-q4-count-generated-composition` | `defun` | 3 |
| `sq-q4-template-negative` | `defun` | 8 |
| `sq-q4-count-control` | `defsquare` | 14 |
| `sq-q4-role-divergence` | `defsquare` | 9 |

`q4-template.lisp` — 41 physical / 36 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `sq-fs-kind-formula` | `defun` | 4 |
| `sq-fs-formula` | `defun` | 26 |
| `sq-fs-vars` | `defun` | 4 |

`read-state-history.lisp` — 71 physical / 43 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `rs-eventp` | `defun` | 5 |
| `rs-event-covers` | `defun` | 6 |
| `rs-h-init` | `defun` | 1 |
| `rs-h-ok` | `defun` | 1 |
| `rs-h-step` | `defun` | 1 |
| `rs-h-fold` | `defun` | 3 |
| `rs-h-obs-read` | `defun` | 5 |
| `rs-h-obs-count` | `defun` | 6 |
| `rs-h-obs` | `defun` | 5 |
| `rs-h-obs-read-of-step` | `defthm` | 3 |
| `rs-h-ok-of-step` | `defthm` | 2 |

`read-state-summary.lisp` — 173 physical / 117 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `rs-above-okp` | `defun` | 8 |
| `rs-s-ok` | `defun` | 6 |
| `rs-insert` | `defun` | 6 |
| `rs-drop-upto` | `defun` | 5 |
| `rs-compact` | `defun` | 6 |
| `rs-s-init` | `defun` | 1 |
| `rs-s-step` | `defun` | 8 |
| `rs-s-fold` | `defun` | 3 |
| `rs-summarize` | `defun` | 3 |
| `rs-memberp` | `defun` | 5 |
| `rs-covered` | `defun` | 7 |
| `rs-s-obs-read` | `defun` | 3 |
| `rs-s-obs-count` | `defun` | 6 |
| `rs-s-obs` | `defun` | 5 |
| `rs-above-okp-of-insert` | `defthm` | 3 |
| `rs-above-okp-of-drop-upto` | `defthm` | 3 |
| `rs-s-ok-of-compact` | `defthm` | 3 |
| `rs-s-ok-of-step` | `defthm` | 2 |
| `rs-s-ok-of-init` | `defthm` | 1 |
| `rs-s-ok-of-summarize` | `defthm` | 1 |
| `rs-memberp-of-insert` | `defthm` | 3 |
| `rs-covered-of-drop-upto` | `defthm` | 4 |
| `rs-covered-of-compact` | `defthm` | 6 |
| `rs-s-obs-read-of-read-step` | `defthm` | 4 |
| `rs-s-obs-read-of-catchup-step` | `defthm` | 4 |
| `rs-s-obs-read-of-other-step` | `defthm` | 4 |

`read-state-teeth.lisp` — 146 physical / 83 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `rs-count2-rel` | `defun` | 2 |
| `rs-h-count2-obs` | `defun` | 3 |
| `*rs-s1*` | `defconst` | 1 |
| `*rs-s2*` | `defconst` | 1 |
| `*rs-suffix*` | `defconst` | 1 |
| `rs-count2-rel-not-step-closed` | `defthm` | 5 |
| `rs-count2-rel-step-obligation-false` | `defthm` | 6 |
| `rs-count2-rel-fold` | `defthm` | 12 |
| `rs-bad-compact` | `defun` | 7 |
| `rs-s-bad-step` | `defun` | 7 |
| `rs-s-bad-fold` | `defun` | 2 |
| `rs-bad-step-breaks-relation` | `defthm` | 11 |
| `rs-s-bad-same-reads-of-read` | `defthm` | 9 |

`read-state-transport.lisp` — 141 physical / 92 code lines.

| Name | Kind | Form lines |
|---|---|---:|
| `rs-same-reads` | `defun-sk` | 2 |
| `rs-same-reads-of-read` | `defthm` | 9 |
| `rs-same-reads-of-catchup` | `defthm` | 9 |
| `rs-same-reads-of-other` | `defthm` | 8 |
| `rs-same-reads-of-step` | `defthm` | 8 |
| `rs-obs-count-agree` | `defthm` | 5 |
| `rs-obs-agree` | `defthm` | 6 |
| `rs-same-reads-init` | `defthm` | 3 |
| `rs-summary-adequate` | `defthm` | 21 |
| `rs-summarize-related` | `defthm` | 9 |
| `rs-summarize-adequate` | `defthm` | 7 |

