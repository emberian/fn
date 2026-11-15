# Universal CNS enum fragment equalities — proposed, unadmitted

`tools/cns_enum_universal.py` emits the three actual old/new PUT fragment
equalities in `tests/cns-enum-universal-controls.lisp`. Its source target is
baseline `4c46607449f33dc604d944d81ea614661eba04e3` versus repaired runtime
`969065e2f`. The current runtime lane's fragments must match the frozen target;
proof-hint-only changes elsewhere do not alter the extracted terms. No ACL2 or
build was started for this candidate.

All three conclusions equate the complete returned `fn2-cns-sources` carrier,
under actual SOURCESP, WFP, NATP row and row < ROWS. They are universal in every
other free parameter. ISSUE adds its actual cached `phase` and `stage` getter
equalities; HARVEST adds only its actual cached `stage` getter equality. NEXT/COPY
has neither cached enum binding, so it adds neither hypothesis. Branch booleans
and numeric write values remain arbitrary; no enum COUNT premise or assumed
post-prefix P preservation is introduced.

The [source audit](cns-enum-universal-source-audit.json) checks each actual
continuing B* binding sequence. There is one sources carrier binding, containing
the extracted replacement. Actual cached getters precede it, no preceding
continuing MV output contains the sources carrier, and every other binding and
the return expression are identical as parsed syntax between old and new.
ISSUE's pool/block I/O and operation-table update do not return sources, HARVEST
caches stage immediately before its fragment, and NEXT/COPY reads its enum values
inside the fragment. Early refusal arms return before this continuing update.
This audits the connection; it does not replace a theorem about the full function.

The proposed proof has four parts:

1. One local bounded list law states that `(update-nth i (nth i xs) xs)` equals
   `xs` when `nfix(i) < len(xs)`. This matches the existing proved
   `fn2-ctf-update-nth-nth-same` statement/proof pattern, without importing its
   unrelated commit book. In particular the law is bounded; it is false on a
   missing row.
2. One local actual-table shape fact derives the two enum column bounds and their
   row bounds from actual P/WFP/valid row. It opens only P, WFP, ROWS and the two
   generated target array-length definitions. Element-recognizer definitions
   remain opaque. It assumes no named enum cardinality.
3. A small named universal theory reuses the ground fixture's actual-definition
   dependency closure and actual stobj executable exclusions, adds the bounded
   law and existing `nth-update-nth`, `len-update-nth` and
   `fn2-columns-len-update-nth` frame facts, and leaves recursive NTH/UPDATE-NTH
   and P/WFP definitions opaque. Other-column writes preserve the target column
   and outer record bounds even when the other written values are arbitrary.
   Cached stage reads then agree through the prefix; the unchanged enum setter
   disappears by the bounded law. Actual transitions and later writes remain.
4. The already admitted actual-table missing-row negative is retained with
   precisely the same name and formula. The 226 admitted concrete witnesses remain
   the positive/transition controls; this new fixture does not replay them.

The generated fixture SHA256 is
`24c655ac0a970bfe175f8ae7197e499cbe9ad02a7347287ec99ab5105c1f00a0`.
It has 14 top-level forms: existing proof-only theory setup, local proof support,
three universal equality proposals and the unchanged missing-row negative.
Its local support, hints and universal formulas have not been admitted. A next
kernel gate should reuse the qualified state-only closure, send only this file
under the original per-event budget, stop at the first refusal, and record actual
per-event outcomes. Source generation and lexical parsing pass; this does not
establish universal equality.

After admission, connecting the three laws to their complete served function
return/effect tuples still requires showing actual entry shape hypotheses and
lifting equality through the unchanged B* context. These fragments themselves
write only sources, and their whole-carrier equalities preserve every sources
array and row. This candidate claims neither equivalence of the full I/O path nor
runtime guard qualification, record certification, or composed crash behavior.

Reproduce in a tree containing both source revisions and the runtime donor:

```sh
python3 tools/cns_enum_universal.py --source-root . --emit tests/cns-enum-universal-controls.lisp --audit docs/assurance/cns-enum-universal-source-audit.json
```

## First author gate and lexical-world successor

The frozen `24c655ac` fixture reached a setup refusal in the shape-theory
MAKE-EVENT: `(theory ...)` expands using lexical WORLD, which that LET omitted.
Before that refusal, the three local helper DEFUNs and initial logical DEFTHEORY
were admitted, and the new bounded list law was proved in 0.13 ACL2 seconds /
1,371 steps. The enclosing encapsulate then failed: **0/3 universal equalities**
were admitted, and the actual shape theorem and negative were not reached. The
state-only 131-book closure loaded in 9.66 ACL2 seconds. The
[setup receipt](cns-enum-universal-24c-setup-receipt.json) preserves exact event
names, refusal output hash, the separate initial staging failure before ACL2,
and verified terminal handles/scope and actual ledger release.

The source successor binds `(world (w state))` in that MAKE-EVENT. A structural
check verifies both generated MAKE-EVENT theory expressions now bind WORLD;
DEFTHEORY and theorem theory expressions use their ordinary ACL2 event context.
All three universal theorem names/formulas and the missing-row negative remain
exactly identical. The new frozen fixture SHA256 is
`79040a36f2811a6d9bfbba9b4d5429af3a2d29997099c327591a1035db0368da`;
its emitter SHA256 is
`2c58df94e9015c016fa4d66fab9ba550042955f576a7922e160472478a9d83a4`.
No successor ACL2 run or other compute was started.
