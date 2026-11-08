# Canonical CNS core certificates

The package exports the live ACL2 bodies of `FN2-CNS-RUN-DRAINING` and
`FN2-CNS-ON-READ-RESULT`, their 408-function body/reader/setter/operation-child
closure, the complete 57-child core layout, the original CNS declarations,
operation rows and constants. `meta/emit/emit.sh` proposes both kernel checks.
Printing a proposal does not mark it certified.

`meta/emit/core-body.lisp` checks the manifest, original declarations, selected
operation rows and each function's exact body and attachment against ACL2's live
world. Its evaluator theorems equate each actual ACL2 function with evaluation of
that body over arbitrary formal values. The four selected operations are CNS
reclaim, CNS lease-release, machine free-head and machine generation-limit. The
printer includes each operation's child in the function closure: free-head's core
wrapper directly reads FREE-HEADI, whereas its declared child is FREE-HEAD-OF.

`CoreTranslation.lean` checks decoding of each canonical body and its evaluation
against the existing `LayerAWorld` function. `CoreWorld` reuses that emitted world
and its checked dispatch equations. Lambda bodies are checked once over fresh
formals, with explicit congruence to their occurrence in the emitted function.
`RETURN-LAST` uses its logical final argument through `Translation.eval_return_last`.
These proof steps preserve the complete statements; they avoid normalizing the
concrete interpreter during unification. Every body theorem prints its axioms.

The independently read `:READ-RESULT` declaration has a complete whole-core
certificate in `CoreValidation.lean`. `coreImage` includes all 57 arbitrary child
values; no well-formedness or successful-entry hypothesis is imposed:

```lean
theorem cns_read_result_certificate (id event outcome reason count aux0 aux1 : Val)
    (kids : Fin 57 → Val) :
    ∃ fuel result,
      runCore world coreTuple cns readResult true
        [id,event,outcome,reason,count,aux0,aux1,coreImage kids] fuel = .ok result ∧
      result = «FN2-CNS-ON-READ-RESULT» id event outcome reason count aux0 aux1 (coreImage kids)
```

The accepted branch includes both valid and refused writes. The entry-refused
branch reproduces the observation stop and NONE wake value. The positive witness
asserts the whole core arity, accepted snapshot, wake result, all four changed
fields and a result different from returning the old core. Both kernels reject
an omitted child and moving wake before the pending write. ACL2 checks the altered
manifest/declaration against the live world; Lean also checks the changed execution.

The `:DRAINING` declaration has the same three equalities, including a complete
whole-core interpreter certificate over every input and all 57 child values:

```lean
theorem cns_draining_certificate (id budget : Val) (kids : Fin 57 → Val) :
    ∃ fuel result,
      runCore world coreTuple cns draining false [id,budget,coreImage kids] fuel = .ok result ∧
      result = «FN2-CNS-RUN-DRAINING» id budget (coreImage kids)
```

Accepted entry uses seven interpreter steps. A held lease calls the declared
release child and either clears its three ownership fields or records the
phase stop. Without a lease, the arm computes the generation and free-list link,
flushes cleanup fields and phase, then calls the declared reclaim child. Both
write-fit outcomes are covered; a refused cleanup write records stop 13 and
still follows the emitted reclaim continuation. Refused entry records stop 15.
Distinct array-field writes commute even on incomplete logical lists; no
representation hypothesis hides malformed-input behavior. Generic stop and
accepted-operation lemmas keep the concrete world out of kernel normalization.

The mutation witness asserts the complete core arity, accepted snapshot and
DRAINING phase, then the exact charge, FREE phase, incremented generation,
cleared CTL, old free-list link, new free-list head, decremented active count,
restored admission credit and unchanged control child. Both kernels prove it.
No other CNS arm is claimed.

Cross-kernel object/primitive correspondence has the explicit scope recorded in
BRIDGE-CERTIFICATE and BRIDGE-LOOPS. The equations do not import ACL2 proofs as Lean
axioms and do not certify unselected emitted functions.

Gates for the 408-function package: bb2 REPL 827/827 forms admitted, zero refused;
`tools/box_certify_bb2.sh bridge-certificate -j 8 meta/emit/core-body.lisp tests/core-certificate-unit.lisp`
reported `certify summary: 2 built, 0 failed` in `build/bridge-core-finalcert2.log`.
The full Lean body/axiom check under bb2 `swarm-build` completed with `DONE 0` in
`build/bridge-core-complete.log`; only propext, Classical.choice and Quot.sound.
D26 remains red: ACL2 body 33.542s and controls 22.373s at eight jobs.
The integrated Fn2 root and full AxiomCensus completed with `DONE 0` and no
sorryAx in `build/bridge-core-root.log`. Normal regeneration reproduced all six
canonical artifacts byte-for-byte (`build/bridge-core-reproduce.log`).

The completed DRAINING certificate and mutation witness pass bb2 `swarm-build`
in `build/bridge-drain-checked.log` (`DONE 0`), with only propext, Classical.choice
and Quot.sound. Its controls replay admitted 12/12 forms, zero refused, in 0.38s.
`tools/box_certify_bb2.sh bridge-certificate -j 8 tests/core-certificate-unit.lisp`
reported `certify summary: 1 built, 0 failed` in `build/bridge-drain-certify.log`.
The wrapper exited without its final marker after reporting success; scoped
rsync subsequently copied its certificate, cert.out and port. The updated
controls took 20.167s at eight jobs, so D26 remains red. Normal regeneration
reproduced all six artifacts in `build/bridge-drain-reproduce.log` (`DONE 0`).
The completed Fn2 root and full axiom census pass in
`build/bridge-drain-root.log` (`DONE 0`), including both whole-core certificates,
the generic control-flow lemmas and the mutation witness. The census contains
no sorryAx; the mutation witness requires only propext.
