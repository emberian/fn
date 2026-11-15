# CNS enum no-op controls

`tools/cns_enum_controls.py` compares the actual three changed PUT fragments,
covering four conditional enum self-writes. It reads the old source from git,
the repaired source from `--source-root`, and the complete actual
`fn2-cns-sources` declaration. It does not substitute a boolean model of the
source table. Its closed interpreter models the declaration's column arrays and
rows scalar and compares the entire returned carrier, including the sibling row.
Unknown expression forms are errors. This is assurance tooling, never a served
implementation of an ACL2 decision.

The narrow source check run against `lane/assurance-current-cns-row@969065e2f`
and baseline `4c46607449f33dc604d944d81ea614661eba04e3` passed 9,216 comparisons.
Each named phase and manifest-stage tag and storage tag 255 participates;
manifest/data/raw/done/index-match branches are exercised. Four negative mutants
remove the actual conditional update at each repaired site; all four are caught
by a whole-table difference. A separate missing-row negative retains a typed,
WFP zero-row table: writing its absent enum element back extends the column,
whereas skipping the write leaves it empty. Thus removing the row premise is
unsound, independently of the unnamed-tag guard defect.

The emitter writes 225 closed positive ACL2 theorem witnesses and one missing-row
negative witness. Each positive witness asserts actual table P, WFP, valid row,
and whole-carrier equality together; it is not an implication that can pass with
a false antecedent. Witnesses retain all declared columns and an unrelated second
row. They include 255 and every named tag, every real enum transition in the four
sites, and both matching/nonmatching next-index branches. They use the original
and repaired source expressions verbatim as parsed S-expressions. ACL2 will
expand the actual PUT macro and call the actual accessors and setters.

Reproduce after composing the runtime donor:

```sh
python3 tools/cns_enum_controls.py --source-root . --emit tests/cns-enum-noop-generated.lisp
python3 tools/lisp_source.py tests/cns-enum-noop-generated.lisp
```

The emitted file belongs under `tests/` so its relative include resolves.
Generation against an unrelated or unlowered tree fails closed on source shape.
The baseline git object must be available. This lane intentionally does not
commit a 430 KB generated artifact or modify the runtime donor.

**Remaining obligations:** record certification of the generated witnesses
(author admission passed below); record certification of the [three author-admitted universal whole-fragment
equalities](cns-enum-universal-author-25186111.json); composed return-value/effect equivalence of the three
served functions; repaired-book guard verification and record certification.
The local source check and lexical parse establish none of these. The fragment
controls intentionally include branch combinations that may be unreachable in
the composed machine; they are not claims about reachability or keystones.
No ACL2 or build process was started by this lane.

## Logical-only kernel gate proposal

Every emitted ground theorem now carries a proof-only local computed hint. It
selects `:executable-counterpart` runes from the actual ACL2 world and excludes
all whose `stobjs-in` or `stobjs-out` contains `fn2-cns-sources`. The remaining
function definitions and ordinary executable counterparts provide reduction.
This is the same signature-metadata method as
`tests/checkpoint-member-guarded-evidence-unit.lisp`; no frozen accessor list or
raw SBCL array operation is used. The formulas and their positive hypotheses are
unchanged. Old PUT terms intentionally contain enum setter applications to 255;
their logical definitions must be reduced, never raw-executed on the quoted
logical carriers. The missing-row witness uses logical `update-nth` directly.

Frozen source inputs:

- old raw source: git `4c46607449f33dc604d944d81ea614661eba04e3`
- repaired raw source SHA256: `8aa01d1a7d7ddb15ce9f6bcd110dfca0df66f1798f6c1e2cdbf645e963433981`
- state declaration SHA256: `01056705c1c63fff3b196bf743b838deca04ea1a938c823105574728d9d2192e`
- emitted logical fixture SHA256: `a7a717e212d49359786865ec58344eff5e012b610c49db55ab3892591cd94ed8`

Proposed next gate, pending the coordinator's compute grant: one isolated
2 GiB memory / zero swap job, 180 seconds CPU / 240 seconds wall. Reuse the
existing qualified 135-book world, whose receipt includes `cns-source-state`
closure key `2ed934279cd42e6b845b38bf3cca2fa5d81b2da2f8c871f09f379b2e1ac0ef84`.
Preflight the exact source hashes and qualified cache payloads, place the frozen
fixture under that isolated tree's `tests/`, and admit only that fixture with
stop-on-first-error. No `cns-source-raw` include or requalification is necessary:
all formulas use its copied PUT fragments and the state book's actual macros,
logical functions, types, and enum constants. Record the ACL2 exit, all 226 event
names, and a fresh success marker; a timeout or first refusal is diagnostic,
never certification. This is a proposal, not an authorized or completed run.

## First kernel admission attempt

The coordinator granted the frozen `a7a717e2` fixture a single 2 GiB / zero swap,
240-second outer / 180-second internal wall job on forge. In the isolated
`/build/lanes/assurance-enum-controls-kernel` tree at `3e4d2b7cb`, all 135 source
hashes and qualified cert/FASL payloads passed preflight, as did the exact repaired
raw, state, and fixture hashes. The state-only compiled entry loaded in 11.06
ACL2 seconds. No raw consumer book was included.

Admission stopped at the first theorem,
`FN2-CNS-ENUM-CONTROL-0-0-0-0-0-1-1`: ACL2 translation rejects its unused LET
binding `N`. The shared ground environment binds variables used by the other
fragments, and needs lexical `IGNORABLE` declarations or fragment-specific
binding selection. Neither the theorem nor a proof was admitted: **0/226
witnesses, zero prover steps**. This was a translation failure, not a failed
logical equality or a counterexample.

The exact output is retained on forge at `/tmp/enum-controls-first-refusal.txt`,
with `/tmp/enum-controls-{campaign,start,author,stop}.log` and the frozen fixture
in the isolated tree. Owned outer PID 1838571, driver 1838577, serve 1838643, and
ACL2 process group 1838647 were all absent after cleanup; their scope
`run-p1838571-i31195260.scope` was gone. The compute grant was released. The
approved frozen source and fixture remain unchanged; a repair requires a new
frozen fixture and a separate admission grant.

The source-only successor adds `(declare (ignorable ...))` to each positive
witness's shared constant LET bindings. A parsed comparison verifies all 226
theorem names and formulas are exactly identical after stripping the declarations;
no actual constructor, premise, or result term changes. The source comparisons,
mutation checks, missing-row check, and 230-form lexical parse pass again.
Successor fixture `/tmp/assurance-enum-controls-ignorable.lisp` SHA256:
`848c6934bfe163081287d69e7d9a8950e6cdf7abae4673f2a2898b8b6fb78e00`.
Emitter SHA256:
`b73a015423837f2fa9fbf605bf6ff6996930f0fe161c73e2d06892b1621d90fe`.
This successor has not been submitted to ACL2. Its existing state-only dependency,
metadata-based raw-executable exclusion, and all outstanding proof obligations
remain the same.

The granted successor attempt also admitted **0/226 witnesses**: its internal
90-second wall timer ended the job with exit 124 while the first theorem's
computed hint was still the last output. The genuine 131-book state closure
loaded in 9.83 ACL2 seconds, and exact input/payload preflight passed again.
No first-theorem proof summary or logical refutation was produced. Its terminal
raw output is `/tmp/enum-controls-848-terminal-raw.txt` on forge, SHA256
`9e37993a89f16bc9c5b7f33898a045f5e0042051bc4eaed7b325dc452a30ff17`.
All owned handles (1845377, 1845380, 1845426, process group 1845430) and scope
`run-p1845377-i31202066.scope` were absent after cleanup. The ledger slot was
released under its lock, recalculating both unassigned fields from current slots.

## Narrow theory source candidate

The broad computed hint performed nested `union-equal` over the entire loaded
world's function and executable theories for each witness. Those list-set unions
perform quadratic membership work before the prover emits its summary. The
terminal log is consistent with that setup cost; it does not measure which
subexpression consumed the wall budget.

The source-only candidate constructs `fn2-cns-enum-logical-theory` once. Its seeds
come from actual fragment getter calls and PUT-generated setters, plus the actual
table P/WFP/ROWS functions and ground addition/comparison/equality/NATP primitives.
It follows the live world's stored `unnormalized-body` dependencies with
`all-fnnames`, selects only corresponding definition/executable runes from the
world, then subtracts actual stobj executable counterparts using their signature
metadata. A world-sized fuel bound fails hard if exhausted. It never silently
truncates a dependency closure. Each witness references that named small theory;
there is no whole-world `union-equal` and no per-witness closure construction.

A parsed comparison confirms all 226 names/formulas, including the IGNORABLE
declarations, are exactly unchanged. Source controls still pass. The candidate
fixture `/tmp/assurance-enum-controls-narrow.lisp` SHA256 is
`61bbea7a3030a9a7abe49ec13cb6cb1326b19d0bd2cfec532d10e9d26bcbbf21`;
emitter SHA256 is
`539194c4c64a95f9b0ffc77c0d8f0279c524a8ecab9f02be50d580ae8da956ff`.
This support code and its named theory are unadmitted; no new compute was started.


## Narrow fixture author admission

The frozen `61bbea7a` fixture passed author admission of **all 226 named closed
witnesses** under the unchanged original 2M-step / 20-second per-event limits.
The state-only 131-book compiled closure loaded in 10.48 ACL2 seconds. Constructing
the named theory took 0.06 ACL2 seconds (`DEFTHEORY` itself rounded to 0.00); the
fixture command took 1.6 seconds wall. Its outer encapsulate summary reports 1.54
ACL2 seconds and 1,045 steps, which excludes child proof work and is not a total
proof-cost claim. There were zero refused events and campaign exit was zero.

The [scoped receipt](cns-enum-fragment-author-61bbea7a.json) records all 226 exact
admitted names, parsed-formula hashes, all three fixture hashes, qualified warm
world provenance, retained raw-log hash, resource limits, and terminal cleanup.
It establishes logical whole-carrier equality for the recorded concrete witnesses,
including 255, named transitions, and the missing-row negative. It is author
admission rather than a record-toolchain certificate or runtime qualification;
the universal fragment and composed served-function obligations remain open.
All owned handles and their exact scope were absent before the actual ledger
slot was released under lock, recalculating both unassigned fields. No additional
compute or runtime consumer replay was performed.
