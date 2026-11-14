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
Its qualified probe and record certification remain pending. This pilot does not
establish fresh served-packet coverage, complete guard reflection, or canonical
object/primitive and symbol-package correspondence. Those remain separate bridge
obligations.
