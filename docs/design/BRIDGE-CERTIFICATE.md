# Canonical export and echo FREE certificate

The echo `:FREE` core face has all three bridge equalities checked, including
refused entry and every one of the assembly's 57 children. ACL2 checks 95 body
equations against its admitted world. Lean checks the same canonical bodies
against the emitted functions, then proves successful whole-core interpretation
of the independently read `((:idle))` declaration. This is one arm, not all echo
arms or the served node.

## Statements

The root ACL2 theorem in `meta/emit/bridge-body.lisp`, verbatim:

```lisp
(defthm FN2-ECHO-RUN-FREE-EXPORT-BODY
  (equal (FN2-EXPORT-EVAL *FN2-ECHO-RUN-FREE-EXPORTED-BODY* (list (cons 'ID ID) (cons 'BUDGET BUDGET) (cons 'FN2-CORE FN2-CORE)))
         (FN2-ECHO-RUN-FREE ID BUDGET FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable FN2-ECHO-RUN-FREE))))
```

The root canonical-body theorem in `Fn2.Instances.BridgeWorld`, verbatim:

```lean
theorem «FN2-ECHO-RUN-FREE».canonical_body («ID» : Val) («BUDGET» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-ECHO-RUN-FREE».canonicalBody fns [("ID", «ID»), ("BUDGET", «BUDGET»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-ECHO-RUN-FREE» «ID» «BUDGET» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-ECHO-RUN-FREE».decoded]
  exact «FN2-ECHO-RUN-FREE».export_body «ID» «BUDGET» «FN2-CORE»
```

The whole-core certificate in `Fn2.Arms.Validation`, verbatim:

```lean
theorem echo_free_certificate (id budget : Val) (kids : CoreImage) :
    ∃ fuel result,
      runCore world coreTuple echoKind echoFree false [id, budget, image kids] fuel = .ok result ∧
      result = «FN2-ECHO-RUN-FREE» id budget (image kids) :=
  ⟨1, _, echo_free_whole_core id budget kids, rfl⟩
```

`CoreImage = Fin 57 → Val`; `image` constructs the complete ordered child list.
The result includes all four answers and the entire returned core. Every input
and child value is quantified, with no guard premise: successful entry returns
the unchanged core; refused entry returns the exact `FN2-CORE-STOP` result.
`echo_free_positive` exhibits live entry and the entire result. The independently
checked signature is takes `[FN2-ECHO, FN2-MACHINES]`, returns `[]`, answers `4`.

## Checked boundary

`books/translation-validation.lisp` preserves package names, character codes,
cons structure, integers, rational/complex objects, guards, justification data,
stobj signatures and attachment pairs. Missing properties remain `:MISSING`.
The manifest contains the complete core layout, core instance, registered
children, original and late declarations, and narrowed signatures. Logical
bodies are never replaced by selected attachments.

The generated ACL2 book compares each claimed function's canonical record and
the entire manifest against the live admitted world. It also checks the FREE
declaration directly with `fn2-machine-declared`. One shared `defevaluator`
provides actual ACL2 callee semantics for the 95 unconditional body equations.
The nonrecursive body dependency graph is closed; recursive and attached roots
require different certificates and are refused by this proposer.

Lean's `Translation.readTerm` independently reads each canonical body. Its
kernel checks decoding, evaluation and absence of attachments for every emitted
function, using the canonical attachment fields checked by ACL2. The generic
syntax lemmas compose those proofs without expanding the entire dispatch table.
`BridgeKinds.canonical_layout` reads the canonical complete layout and checks its
order; `canonical_free_declaration` decodes the original arm data. `Arms.read`
then interprets that data. The whole-core proof schema lives in
`meta/emit/echo_validation.lean.in`; the emitter generates every child binder and
row reader from the canonical package. Python proposes these equations; neither
Python's exit status nor a matching hash establishes them.

`meta/Fn2/Instances/bridge-identity.json` records source-file and dependency
hashes, package hash, Lean/Mathlib identities, ACL2/SBCL versions and the checked
ACL2 image hash. It lists the 95 candidates, 2,588 other exported functions,
missing guard properties and primitive correspondence obligations. Its status
deliberately remains `PROPOSED`: kernel gate evidence is separate. The raw
canonical package is regenerated, ignored by git, and its exact objects occur
in the checked ACL2/Lean artifacts.

The correspondence still crosses two kernels. It is not ACL2 proof replay in
Lean. `Val` represents integer arithmetic, imported ACL2/Common Lisp names and
keyword names; rational/complex lowering is refused. The primitive basis is
`CONS`, `EQUAL`, `INTEGERP`, `<`, `NTH`, `MV-NTH`, `UPDATE-NTH`, with the existing
ACL2/Val primitive correspondence explicit. This arm introduces no ASH,
division, string conversion, recursive operation or attachment contract.
Other arms, handlers, genesis and executable `:logic`/`:exec` agreement retain
their separate obligations and differential campaigns.

## Controls and gates (bb2, 2026-11-07)

Both kernels reject a valid body changed to `(quote nil)`, reversal of the
complete child layout, and an injected echo-to-scribe attachment. ACL2 uses
`must-fail` around the same live-world checks used by the package; positive
checks use the unchanged world. Lean proves `altered_body_rejected`,
`altered_child_layout_rejected`, and `wrong_attachment_rejected`. The body
control is a semantic result inequality, not a syntax error.

Commands run from the lane clone:

```sh
tools/bb2_repl load bridge-body --no-sync
tools/bb2_repl load bridge-controls --no-sync
tools/box_certify_bb2.sh bridge-certificate -j 8 meta/emit/bridge-body.lisp tests/translation-validation-unit.lisp
tools/box_certify_bb2.sh bridge-certificate -j 2 meta/emit/bridge-body.lisp tests/translation-validation-unit.lisp
python3 tests/test_translation_export.py
```

The final warm REPL admitted 197/197 forms with zero refusals in 7.30 seconds;
the controls admitted 12/12 with zero refusals. Certification reported
`2 built, 0 failed`; an earlier affected assembly closure reported
`49 built, 0 failed`. The final two targets took 18.057 and 17.939 seconds at
`-j 8`. The shared evaluator replaced 95 separate evaluators, reducing warm
admission from 11.71 to 7.30 seconds without splitting a book. The remaining
certification cost, including assembly loading, exceeds the ten-second target.
The explicit two-job control rebuilt the same targets with `2 built, 0 failed`:
20.364 seconds for the body book and 20.866 for the controls. ACL2 attributed
2.52/0.59 seconds to proving and 17.65/20.05 to other work respectively. This
D26 cost defect remains open; the proof search itself is not the dominant cost.

The final Lean chain (`Translation`, `BridgeWorld`, `BridgeKinds`,
`BridgeTranslation`, `Arms.Validation`) built under `swarm-build`, and the
ordinary `Fn2` root imports the certificate. The eight new census subjects use
only `propext`, `Classical.choice`, `Quot.sound` (some use none). The four direct
Python transport tests pass. An attempted unittest discovery also invoked the
repository's unrelated surface loader and failed for missing `hypothesis`;
that is not a gate for this change and was replaced by the direct file command.

Local evidence is under `build/bridge-shared-repl.log`,
`build/bridge-final-certify.log`, `build/bridge-final-lean2.log`,
`build/bridge-controls-load3.log`, and `build/bridge-two-job-certify.log`.
No native, host, full-node green or new differential campaign is claimed.
