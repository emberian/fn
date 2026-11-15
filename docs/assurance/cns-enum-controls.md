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

**Unrun obligations:** ACL2 admission of the generated witnesses; an actual
P+WFP+valid-row universal whole-fragment equality proof with the cached stage
bound to the actual getter; composed return-value/effect equivalence of the three
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
