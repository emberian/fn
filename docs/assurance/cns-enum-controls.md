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
