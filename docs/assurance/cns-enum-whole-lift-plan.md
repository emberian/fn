# Whole-function CNS enum lift — source proposal

`tools/cns_enum_whole_lift.py` generates three complete logical MV-result equality
proposals in `tests/cns-enum-whole-result-controls.lisp`. The new side is the
actual served function. The old side is a mechanically extracted function from
`4c46607449f33dc604d944d81ea614661eba04e3`, renamed with `-enum-frozen-old`.
Its formals, original guard, stobj declarations and entire body are preserved;
only its name and proof-only `:verify-guards nil` setting change. No production
function or guard is modified, and these old clones have no runtime qualification
claim.

The fixture depends on the actual qualified `cns-source-raw` book and qualified
universal fragment book. It does not create an alternate raw loader or replay an
author-only prefix. The runtime owner currently has a qualified 136-book parent
but the complete RAW book's frame proofs remain pending. That qualification is a
concrete prerequisite for this fixture's next kernel gate. No ACL2/build was
started for this candidate.

The [source audit](cns-enum-whole-source-audit.json) verifies that the latest runtime
lane's three bodies, guard formulas, arguments and stobj declarations match frozen
`969065e2f`. The universal generator independently confirms that all other B*
bindings and return expressions are unchanged old/new. On the continuing path,
there is exactly one sources carrier binding: the changed fragment. Earlier
continuing MV bindings never return sources, so its input P/WFP remains precisely
the original input carrier's property. No arbitrary TYPE/P premise on an I/O
prefix result is introduced.

The lift uses three local rewrite aliases whose formulas are parsed identical
to the admitted universal fragment laws, each justified `:by` that original law.
It unfolds only the mechanically extracted old function and actual new function.
Public setter/getter and I/O definitions stay opaque, keeping the actual nested
PUT expression available to match the fragment rewrite. The shared pool/block
I/O prefix and other carrier updates are identical terms on both sides. This
avoids additional factored full-function twins or an independent interpreter.

ISSUE and NEXT/COPY obtain valid row from the actual owner predicate. One local
forward rule derives NATP row and row < ROWS directly from that predicate's
actual definition, without opening its field getters. Their whole-result
statements require only input sources P/WFP; invalid-row refusal branches are
unchanged and do not reach the fragment.

HARVEST additionally requires actual input source-operations P/WFP. Its checked
NATP op and op < operations ROWS supply the public typed
`fn2-cns-source-operations-source-row-natp` theorem's guard; the actual continuing
source-row bound supplies the remaining fragment premise. The cached stage
binding immediately precedes the fragment. This is an input recognizer already
owned by the actual stobj representation, not a fabricated post-prefix invariant.
The other two functions do not require an operations type premise to justify
their source row.

Each conclusion equates the whole function call, including every scalar and
returned stobj in its complete MV list. The audit records each actual continuing
return tuple. Thus the proposed scope includes all ACL2 carrier changes and
modeled request/result effects represented by these returns; it does not claim
host/native side-effect correspondence or physical process-death behavior.
The actual RAW functions' guard qualification remains independently owned.

The small proof theory contains the two full function definitions, exact local
fragment rewrite, owner-row forward rule, and (for HARVEST) the public typed row
getter, plus pure list/boolean rules. No raw stobj executable counterpart is
selected. No callee I/O definition or executable counterpart is enabled.
Whether this rewrite orientation suffices through ACL2's B* normalization is the
next concrete proof question; source audit is not its answer.

Frozen fixture SHA256:
`f893333a374057f38bb29c052bc16c413869ea5b8b3e83f18fc8e4933bad12eb`.
Emitter SHA256:
`11965005a714ce41c6856a56bb943d1b6f1741d8e62fae6a3954267b203f9830`.
The generated fixture has 13 top-level forms. Its three whole-function statements
and support have not been admitted. The existing three universal fragment proofs
and ground 226 witnesses are not counted as these new obligations.

Reproduce in a tree containing the runtime sources and relevant git revisions:

```sh
python3 tools/cns_enum_whole_lift.py --source-root . --emit tests/cns-enum-whole-result-controls.lisp --audit docs/assurance/cns-enum-whole-source-audit.json
```
