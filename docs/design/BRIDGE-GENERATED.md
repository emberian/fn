# Generated served certificates

`emit.sh` now exports the complete served closure and emits a contract for every
live arm, subarm and handler. The denominator comes from ACL2's declaration
registry, including late declarations and narrowed child signatures. It is not
an emitter allowlist. A child subarm has its actual child function and complete
child tuple; the generator does not invent a core wrapper for it.

`build/served-certificate-coverage.json` is the machine-readable result.
Its `.txt` companion lists every unvalidated root by function name and concrete
remaining proof obligation. Printing a contract does not count as validation.
The generated files are reproducible artifacts, excluded from version control.

The checked 2026-11-13 snapshot has **12,039/12,039 canonical exports** and
**57/263 whole-arm interpretation roots** validated across 14 served kinds.
All 263 contracts compile. [The coverage snapshot](BRIDGE-GENERATED-COVERAGE.txt)
lists the other 206 roots by name and reason; [the statement snapshot](BRIDGE-GENERATED-STATEMENTS.txt)
quotes all 57 validated contracts and theorem signatures verbatim. Both are bound
to the canonical packet hash, rather than promising coverage for later declarations.

The final bb2 gate reported `certify summary: 3 built, 0 failed` in
`build/bridge-final-certify.log`. The record runner also passed all three books in
`build/acl2/certify-20261108T102032Z-1763634`; the coverage join completed with
`DONE 0`. All 57 proofs passed their three theorem censuses (`0 sorryAx`, axioms
`⊆ {propext, Classical.choice, Quot.sound}`). Fifteen focused Python controls and
the raw Lisp printer controls passed. ACL2 iteration admitted the final 38 helper,
22 isolated control and 1,658 export forms without refusal.

Remaining red: the generated export book takes 103.137 seconds in the mandated
gate (about 105 seconds in the record runner), exceeding D26. The 206 remaining
interpretation proofs and closure-wide body-evaluation/primitive-domain proofs
are not certified by this snapshot. No live durable word is present in this
assembly, so the incoming consumer `:commit` instance still needs its live gates.

## Gates and scope

The canonical gate compares every exported record against the live ACL2 world:
function name, formals, logical body, guard, justification, stobj inputs and
outputs, and attachment. It also checks the complete call closure through bodies,
guards, measures and attachments, rooted at `fn2-turn`, every `FN2-HOST-*` function,
and every declared arm/handler. Missing callees, false refusals and duplicate
names are errors. Metadata checks bind original declarations, layout, signatures,
operation declarations, constants and waits to that same world.

The canonical transport is version 2: one header followed by one exact function
record per line. The single generated `meta/emit/served-export.lisp` book packs
symbol package/name strings to reduce certification memory. ACL2 expands one
record at a time before comparing the original canonical objects. The admitted
statement is:

```lisp
(defthm fn2-tv-matches-packed-function-exact
  (implies (fn2-tv-matches-packed-function entry fn world)
           (equal (fn2-tv-unpack entry) (fn2-tv-function fn world)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-tv-matches-function-exact
                                  (entry (fn2-tv-unpack entry)))))))
```

The Lean gate checks original declarations and layout against the emitted kind
presentation, then checks each generated proof and its named axiom census. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. Successful interpretation
must exist for every input and every represented core: all children are quantified,
without a core well-formedness hypothesis. Refused entry is included. Every counted
proof also has an accepted-entry witness and an omitted-child control quantified
over every fuel and result; all three named theorem censuses must pass. For example,
the echo root's contract is emitted verbatim as:

```lean
def contract (id : Val) (budget : Val) (kids : Fin 57 → Val) : Prop :=
  ∃ fuel result, runCore world coreTuple kind arm false [id, budget, image kids] fuel = .ok result ∧
    world.fns "FN2-ECHO-RUN-FREE" [id, budget, image kids] = some result
```

The shared schemas and compositional combinators (`meta/Fn2/Arms/Combinators.lean`
and `meta/emit/served_proof_gen.py`) currently discharge complete `(:idle)` arm
declarations, complete `(:wake)` handler declarations, and 31 additional `:CORE`
and `:CHILDREN` run, observe, and child-subarm roots across pending-write/flush,
operation-result/child-writeback, branch-join, stop/reclamation, and `:goto`
subarm composition. Other roots retain their full contracts
and explicit missing proof obligations. This interpretation count is the third
bridge equality; canonical identity is **not** a substitute for the first two
exported-body evaluation equalities or reachable primitive-domain obligations.
The earlier body/loop certificates remain documented in `BRIDGE-CORE.md` and
`BRIDGE-LOOPS.md`; this report does not inflate their scope to the entire closure.

The checker rebuilds the whole local Lean import graph. Its reusable cache binds
source, local dependencies, selected compiler/runtime, toolchain/manifest and
actual import artifacts (including private/server sidecars and IR). It also binds
the ordered effective Lean search path and a conservative inventory of external
library artifacts, including transitive imports and directory shadowing. A
changed external inventory during a gate discards its cache and rejects the run.
Each compilation exposes only its declared transitive local imports through a
private `Fn2` search root. Batches contain only proofs with identical transitive
local import scopes, so a sibling cannot lend an undeclared dependency to another
proof. An external package cannot silently import another stale local artifact;
that missing dependency is refused. Standalone closure
checks use the same final external-world recheck as complete gates. Cache keys
also bind the checking-policy version. This intentionally invalidates earlier
cache keys; copied warm artifacts alone are not evidence. Coverage is invalidated by a change
to the canonical packet or any recorded input. A whole root is counted only after
both its Lean proof/census and the current ACL2 record-cache gate pass.

## Durable word

The independent Lean reader understands `:commit` in both submitting and settling
contexts, retaining the original declaration. The printer emits each live word's
ACL2 expansion; generated checks compare that expansion in ACL2 and Lean. An
independent ACL2 traversal of the live declarations checks the complete word
inventory, so omitting a word cannot improve its coverage count. Subarms
use the generator's NIL tag rather than their name as the settling context.
Only statement positions are traversed: a phase named `:commit`, a case label,
or quoted data is not a durable word. The incoming consumer declarations must
still pass these live-word gates once merged into the served assembly.

## Reproduction

Run print/emission on bb2 using the lane's certified reference/probe books and
record launcher. The normal `meta/emit/emit.sh` includes the served package and
certificate generation. To regenerate only proposals from an existing packet:

```sh
python3 meta/emit/emit_embed.py --served-certificate meta/emit/served-certificate.sexp
```

Iterate ACL2 through `tools/bb2_repl`, then use the mandated gate:

```sh
tools/box_certify_bb2.sh bridge-certificate -j 8 books/translation-validation.lisp tests/translation-inventory-unit.lisp meta/emit/served-export.lisp > build/bridge-packed-certify.log 2>&1
```

The legacy box script produces certificates but no record-cache manifest. On bb2,
under `swarm-build`, produce that evidence with the narrow record runner:

```sh
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k python3 tools/certify_books.py --jobs 8 --timeout-seconds 240 --images off books/translation-validation tests/translation-inventory-unit meta/emit/served-export
```

Under bb2 `swarm-build` and the pinned Lake environment, with this lane's
`build/lean-lib` first in `LEAN_PATH`, run:

```sh
python3 meta/emit/check_served_certificate.py --lean --acl2 /tank/fn/toolchains/w28/acl2-literal-4g-tls64k --lib build/lean-lib -j 4 --timeout 120
```

Use a timeout and recorded PID/DONE wrapper for detached jobs. Keep the generated
packet and source book synchronized before the box helper's full rsync.

## Open assurance work owned by the Lean recovery lane

Owner: `recover_lean` / `lane/stride-lean-reflect`. These are implementation and
proof obligations, not conclusions supplied by the 57-root historical snapshot
or the later recovered-package 58-candidate Lean-only regression. The current
checker has no closure-wide canonical-body-evaluation or primitive-domain gate.
`Translation.BodyCorrect` defines an interface; defining it does not instantiate
it for the served closure. The echo FREE certificate is a scoped precedent.

The new `ACL2/CanonicalEvaluation.lean` foundation evaluates every user call
through its decoded canonical body, without an arbitrary function-dispatch
oracle. It requires explicit domains at reached calls and separates primitive
object correspondence from body evaluation. Its integer bump/twice-bump fixture
checks concrete emitted dispatch as well as this closed evaluation, including a
callee-only mutation of the composed caller and a primitive-domain-removal
counterexample. All seven Lean theorem censuses passed with the allowed axioms.
`tests/translation-domain-unit.lisp` independently checks the exact admitted
bodies and integer guards; its record certification passed and published under
qualified toolchain `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`
in run `certify-20261114T004844Z-3462921`. This is a two-function foundation
fixture, not a served-root certificate. Binding supported input domains to the
current served guards, handling canonical symbol identity, and joining every
required closure obligation remain owned work.

1. **Current package and closure.** Once integration supplies a coherent source
   revision, regenerate registry, canonical packet and LayerA bodies from the
   same current ACL2 world. Qualify `reference`, `translation-validation` and
   `meta-probe` prerequisites with current record-cache keys, then certify the
   generated served-export book. Derive required functions from the complete
   served call graph, retaining recursion, guards, measures and selected
   attachments. No root is end-to-end qualified from a recovered packet.
2. **Canonical body evaluation.** Extend the shared body generator used by the
   echo certificate to emit, for each required function, the ACL2 equation
   between evaluation of its exported logical body and its admitted function,
   plus Lean decoding and `canonical_body`/`BodyCorrect` evidence against the
   emitted function. Compose callee evidence by dependency order. Recursive
   components need measure induction and a proved evaluation-fuel bound; a
   fixed fuel constant or assumed callee equation is not a replacement. A
   constrained function's selected attachment needs its own named refinement
   obligation; preserve the logical body and the exact attachment pair.
3. **Representable domain and primitive correspondence.** Introduce named
   per-root input-domain predicates derived from the actual served guards and
   representation invariants, and prove initialization, external admission,
   callee arguments and returned state preserve them. Preserve the existing
   unconditional interpreter equalities: the new domain predicates qualify the
   additional ACL2-to-Lean semantic claim. Relate canonical integers, supported
   package-qualified symbols, byte characters/strings and recursive cons values
   to `Val`; prove the relation is unambiguous on the admitted domain. Inventory
   every reachable primitive call and discharge its domain and correspondence
   obligations. Check attachments and executable `:logic`/`:exec` agreement too.
4. **First arithmetic slice.** Start with served `EXPT` sites: literal natural
   exponents, `NFIX` exponents, the integer/nonnegative branch of `UNSIGNED-BYTE-P`,
   the `0 < LEFT < 4` branch of `B3-BLOCK-WORD`, and non-`ZP` `N` in
   `CODEC-EMIT-BE` before computing `N-1`. Prove these conditions at each actual
   call, then compose `expt_nonnegative` under the root domain. If a served call
   admits negative/rational exponents, extend the semantic representation there;
   do not silently lower rational results to integers. Connect the existing
   rational floor/ceiling and negative-ASH contracts to their actual call sites,
   and include `PrimitiveContracts` in the checked import closure before counting
   them. The twelve sites observed in the old packet are leads; recompute the
   inventory from the current packet.
5. **Gate and controls.** Add separate machine-readable denominators for canonical
   record identity, ACL2 body equations, Lean body evaluation, reachable primitive
   obligations and whole-arm interpretation. Join them by exact function/record
   and root dependency closure, never by a successful global count. A root's new
   semantic status requires all its dependency obligations and its named input
   domain; missing obligations remain failures. Controls must reject a changed
   valid body, wrong callee/attachment, missing dependency, a removed domain
   premise admitting `2^-1`, and negative division/ASH truncation. Include a
   reachable positive input satisfying the whole new domain and conclusion.

The next served semantic slice is `FN2-CNS-RUN-DRAINING` on the fresh composed
source, with all five evidence dimensions joined. Recompute its closure, including
new timer-clear behavior; do not inherit the old package's closure count. Use echo
FREE as a small reference/control and reuse the core body/lambda generator rather
than create a second emitter. The shared foundation owns `Translation`, recursion
fuel lemmas and body-emitter helpers; family work supplies declarations/templates.
Then extend to the guarded arithmetic families and recursive components. This
sequence does not reduce the destination: all served roots and their executable
dependencies remain required.

`canonical_call_correct` now composes a callee's `CanonicalBodyCorrect` at the
actual evaluated arguments and returns one shared result with closed evaluation,
the actual emitted interpreter equation, and the callee postcondition.
`canonical_lambda_correct` carries that same result through the translated
lambda continuation with an explicit arity premise. Qualified Lean author checks
compile these rules and a two-call control whose first result establishes the
second call's domain. Native dispatch shadowing and a missing lambda formal are
concrete negative controls; all three theorem censuses use only the allowed
`propext`, `Classical.choice`, and `Quot.sound` axioms. This is composition support,
not a current CNS body certificate.

The next executable instantiation is the fresh canonical
`FN2-CNS-CLEAR-WAIT-TIMER` record. Reuse the existing core emitter's exact record
reader and actual LayerAWorld dispatch, obtain its definition/guard/helper closure
from the current qualified callback packet, and prove its `CanonicalBodyCorrect` with the whole
result `(:ok, cleared-core)`. Its independent ACL2 postcondition requires
`fn2-corep`, `fn2-core-wfp`, natural ID, and ID below scheduler rows; retain each
premise and the complete core frame. Apply `canonical_call_correct` at the actual
arm call, then use `canonical_lambda_correct` for its result destructuring and
continuation. Establish reclamation's domain from the returned core plus the
preexisting partition reservation invariant. Do not assume that timer clearance
establishes ownership or a positive partition active count. The required artifact
is a typed current helper certificate consumed by the actual root continuation;
another isolated successful fixture cannot substitute for it.

The timer producer is now `meta/emit/print-cns-timer-certificate.lsp`. After the
current `assembly-callbacks-e-cns` and `translation-validation` prefixes qualify,
run `tools/acl2 --timeout 180 < meta/emit/print-cns-timer-certificate.lsp` in the
owned derived source tree and require its `FN2-META-CERTIFICATE PASS` marker.
Record that tree's identity and packet digest. The printer's optional context
flag is false here, so it adds no unrelated arm readers; the existing closure
walker still includes every reached logical body, guard and measure dependency.
Inspect with `python3 meta/emit/emit_core_certificate.py --inspect --root
FN2-CNS-CLEAR-WAIT-TIMER meta/emit/cns-timer-certificate.sexp` (one shell line).
That command reports only body-proof selection and retains existing refusal
checks; it does not discharge guard or primitive obligations. Explicit root
selection currently requires inspection mode, preventing accidental default arm
emission. A raw-printer fixture checks both the smaller root set and retained
guard/measure dependencies, while six inspection controls preserve refusal and
no-write behavior. These source controls are not evidence from a live ACL2 world.

`CanonicalGuardEval` now names the separate canonical guard record, requires its
formals to match the logical definition, and proves a finite closed evaluation to
a truthy value. `DomainRespectsGuards` requires this for every admitted function
call. These predicates use no emitted-function oracle; guard callees and primitives
carry the same explicit domain obligations as body evaluation. Root admission must
still have a reachable witness, and domain preservation remains separate. The
INTEGERP fixture uses the exact COMMON-LISP symbol and ACL2 X formal from the
qualified two-function ACL2 fixture; wrong formals and a changed false guard are
negative controls. Its guard primitive domain is deliberately separate from the
arithmetic body fixture, so these controls do not claim a composed semantic root
or primitive correspondence. Production emitters must bind guard and body tables
to the same freshly qualified canonical records before using these predicates.

## Recursive closed-evaluation pilot

`Fn2.ACL2.MemberExecEvaluation.closed_adequate_emitted` connects the actual
`MEMBER-EQ-EXEC` emitted function to a finite canonical body derivation, with
symbol keys and proper lists. Its logical closure contains `NOT`, `ATOM`, `ENDP`,
and `EQ`; no recursive call is answered by an arbitrary dispatch oracle. Every
recursive transition preserves the domain and strictly decreases `ACL2-COUNT`
of the list. For every fuel greater than this measure, the transition evaluator
returns the same successful result. This strengthens fuel stability to success.

The positive witness searches past a nonmatching element. Controls exhibit
insufficient fuel and a mutated transition that keeps its input forever. The
module and all nine theorem censuses passed the bounded forge Lean author check
using only `propext`, `Classical.choice`, and `Quot.sound` (2026-11-14). The generic
`Countdown` module now imports only `Init`; its statements and proofs do not need
the former whole-world `Fuel` dependency. Two emitted leaf modules were compiled
from the frozen `6e07e62f3` source for this check.

`tests/member-exec-domain-unit` checks the live ACL2 logical bodies, formals,
guard, admitted measure, decrease, domain preservation, and positive witness.
Its qualified source probe admitted all six forms (242 steps). Single-book record
`certify-20261114T020835Z-3549888` passed in 0.115 seconds with a qualified published
cache entry at closure key
`74a7e7f4d487615f9893005e30de487577504aea47b4cbf2345bc0168fef9d35`.
This pilot does not
establish fresh served-packet coverage, complete guard reflection, or canonical
object/primitive and symbol-package correspondence. Those remain separate bridge
obligations.

## Required semantic inventory

The generated served report now contains a `semantic_inventory` of required
obligations, always marked pending. It binds raw canonical records and fields,
walks logical bodies, guards and selected attachments, and names primitive sites
separately. Recursive components require termination evidence; an undecoded
justification remains a frontier, even when its known function symbols supply
conservative dependency hints. Missing metadata and unresolved callees remain
frontiers. This inventory accepts no proof-status flags and does not increase any
validated denominator. A strict checker must regenerate it from the canonical
packet and check typed Lean wrappers and current ACL2 body records; consuming the
JSON as evidence would bypass that obligation. Ten focused inventory controls
cover these boundaries, including altered constructor subjects/fields and forged
completion flags; the existing 25 checker controls also pass. No new current-world
packet or semantic proof is claimed by this tooling change.
PoolCompare's current Lean source now checks without Mathlib or the aggregate
Fuel import. The template proves the exact NFIX scalar identity privately and
uses explicit finite branch cases. Its public theorem statements and generated
function bodies are unchanged. The world-body generator's opt-in `public; scan`
mode supplies only the selected public names and their bodies; ordinary private
body imports retain their previous behavior. This removes an accidental reliance
on Fuel re-exporting the entire world.

The bounded Forge diagnosis distinguished three stages: imports passed,
definitions/private scalar lemmas passed, and the old repeated-splitting decrease
proof exited 137. Finite branch proofs then passed for decreases, emitted-loop
agreement and the body equation, followed by the full PoolCompare module at
`/tmp/stride-pool-final.log` (PID 530557, exit 0, 2Gi, `lean -j1`). Both the
adequacy certificate and canonical-body theorem census contain only `propext`,
`Classical.choice` and `Quot.sound`. Thirty-two public declaration statements were
compared unchanged against the integrated source. These are Lean author checks
on the current committed generated source, not a fresh ACL2 packet qualification
or an increase in served semantic coverage.

Canonical recursive proofs can now be reused inside a larger canonical program
without replacing their logical subjects. `canonical_eval_extend`,
`canonical_args_extend` and `canonical_export_extend` preserve every resolved
`CanonicalDefinition` exactly and require explicit inclusion of the call and
primitive domains. They transport a finite derivation at its original arguments
and result; they do not widen the inputs quantified by a body certificate or
identify an executable dispatcher.

`MemberExecEvaluation.closed_in_program` consumes this transport for the actual
emitted `MEMBER-EQ-EXEC` result on a symbol key and proper list. Its controls accept
an additional unrelated definition, reject a changed body with the original ABI,
and reject exclusion of the actual entry input. The two-module Forge author gate
passed at `/tmp/stride-extension.log` (PID 620008, exit 0, 2Gi, Lean 4.30 `-j1`,
120-second bound); all thirteen member axiom censuses contain only `propext`,
`Classical.choice` and `Quot.sound`. Existing imported source closure is unchanged
between the earlier qualified recursive author check and integrated `d486cbe80`;
only these two edited modules were compiled. Source hashes are
`b9c2e3176adc4b5bc8b83e4b422be15607fb8180aa24fd929889600b1d23211c`
and `726cae242ec7dd8cff5b57893cb7fc6e942dc0dd1e97cb60fa225dafd3d958c7`.

The CNS consumer must still establish those exact lookup/domain premises from
its current qualified packet, prove the selected logical/executable MBE relation
under its guard, and connect primitive correspondence and selected attachments.
This author check discharges none of those current served-site obligations.

The existing core emitter now accepts an opt-in packet-bound recursive consumer:

```
python3 meta/emit/emit_core_certificate.py --root FN2-CNS-RUN-DRAINING \
  --closed-member-output /tmp/CnsMember.lean CURRENT-SCOPED-PACKET.sexp
```

This selects the actual root body closure, retains its exact canonical Object
bodies, rejects duplicate decoded subjects and missing/attached callees, and emits
five kernel-checked lookup equations into `MemberExecEvaluation`'s definitions.
The resulting `member_closed` theorem consumes those equations through
`program_extension_of_lookups` and `closed_in_program`. Call-domain and
primitive-domain inclusion remain explicit theorem premises. Generation itself
is a proposal; the packet's live-world qualification and the generated Lean
module's successful check are both required. No current packet is substituted
by the test fixtures.

A six-record fixture (the five membership definitions and a synthetic caller)
passed the bounded Forge generator-composition gate at
`/tmp/stride-member-packet.log` (PID 625826, 2Gi, 120 seconds, Lean 4.30 `-j1`).
The generated lookup and closed-evaluation censuses contain only the allowed
three axioms. Changing only the recursive CDR argument to the unchanged list
kept the ABI and closure but failed exactly at the `memberLookup` equality
(exit 1, raw output `/tmp/stride-member-packet-mutant.log`). Successful generated
source SHA is `585fa7c59fa8179b5dce6ab2923a65af16a15386ae803c283a48a7b546a5e296`;
mutant SHA is `bb2bd939d56cf453d5e5180d7ce165dab05114cb45e9a59a0d0dcb626dfb49fc`.
Four new packet controls and six existing inspection controls pass directly.
A unittest-discovery invocation unexpectedly loaded unrelated surface tests and
failed on their missing `hypothesis` dependency; the named files were then run
directly, without that unrelated suite.

The actual draining membership site is generated `:do` acceptance routing for
`:ok`/`:retired`; core release uses OR/EQ and timer clearing has no source MEMBER
call. Therefore this consumer must bind the current draining closure rather
than label a timer-only export as membership coverage. Current branch-domain,
MBE, primitive/object and attachment obligations remain open.

The scoped printer `meta/emit/print-cns-member-certificate.lsp` requests only
DRAINING as a root (`include-context nil`, no operation roots). The printer
still collects body, guard and measure dependencies. Once the current callback
closure is qualified, produce the packet in that world and generate both sides:

```sh
python3 meta/emit/emit_core_certificate.py --root FN2-CNS-RUN-DRAINING \
  --closed-member-output /tmp/CnsMember.lean \
  --closed-member-book meta/emit/cns-member-packet.lisp \
  meta/emit/cns-member-certificate.sexp
```

The companion ACL2 book checks the manifest and every exact function record,
including records outside the Lean body selection, then checks the live
body/guard/measure/attachment closure and native boundary. Its root census must
exactly match the requested roots; malformed, duplicate or extra roots refuse
before either output is written. Both outputs and all their selectors consume
one immutable packet-text snapshot; replacing the source pathname between
stages cannot pair different packets. It uses existing translation-validation
checks and does not add a dependency to the shared callback prefix.

This is an unadmitted qualification-book proposal, not new served evidence.
Its current closure-key qualification and the corresponding Lean module check
are separate gates. Even both gates would establish only packet identity and
the stated membership theorem with domain premises: reached caller domains,
primitive correspondence, MBE and the selected-dispatch/host binding chain
still need their own proofs. This printer does not substitute the proposed
selected dispatcher for the production dispatcher or treat defattach as an
ACL2 equality. Fourteen Python source-generation controls and six existing
inspection controls pass; no current packet or ACL2 admission was obtained by
those controls.

The Lean consumer now retains the complete packet definition inventory and
emits `guards : CanonicalGuards` from each same function record's exact guard
and formals. Previously it kept only the root body closure and discarded all
guards; a guard-only nonnative helper consequently had no definition available
to `CanonicalGuardEval`. The root body still must actually reach the membership
closure. Missing body/guard callees and attachment-backed helpers refuse
emission; attachment selection is not a logical-body substitution. The ACL2
companion remains responsible for exact live measures and full live closure.

A seven-record generation control has a root guard that calls a helper absent
from the root body. Both its canonical body and guard now appear in the emitted
program. Changing only the root guard leaves the emitted body program identical
but changes the guard table. Removing the helper or attaching it refuses. These
are source-generation controls, not proofs of `DomainRespectsGuards` or guard
satisfaction. The authorized warm-import Lean gate subsequently passed both
emissions and rejected the changed-body and changed-guard controls at their
respective exact equations. It used 2 GiB, one job and a 120-second timeout;
peak memory was 108,294,144 bytes, memory events were zero and the scope was
released. The six positive theorem censuses contain only the allowed axioms.
The bounded fixture receipt is
`docs/design/receipts/canonical-member-guards-fixture-record.json` (Forge
PID 1157213, `/tmp/audit-bridge-guards-0e9b5f9ac/run.log`). No imports were
rebuilt and no ACL2 admission was run. The current served CNS packet still
waits for its qualified callback world; these fixture results do not qualify it.
