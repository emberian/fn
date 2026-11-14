# Issue wrapper contracts

An arm's `:issue` result must agree with actual queue and issuance-history
changes. A declared descriptor cost alone does not establish that agreement.
The block-read wrapper was opaque at this boundary: its type and well-formedness
contracts did not supply either effect relation to its cursor/CNS callers.

The shared wrapper producers now locate `fn2-ops` in the admitted result ABI.
They require the three scalar issue results followed by a unique operation
carrier, and refuse a missing or incompatible carrier. The resulting contracts
preserve operation rows and establish queued/issued deltas of one exactly on
`:ok`, zero on refusal. These remain separate relations: queue length does not
in general determine issuance history.

The action-wrapper defining macro registers its actual declarations for both
producers. This removes duplicate handwritten proof lists and includes TLS-start,
which those lists omitted. The custom block-read wrapper invokes the same
producers beside its owning definition. Runtime bodies and guards are unchanged.

For an arm without an operation carrier, both public effect statements reduce
to the same complete statement about reporting zero descriptors. The generator
checks their AST equality and proves the second by the first. Carrier-bearing
arms retain their separate effect proofs.

## Qualification

The prototype used the authenticated `0be7f6d51` baseline, 87 cached dependencies
with no misses, and fresh producer names from `bf65c01a6`. Before the effect
claims, it checked the actual original block-read/read body, guard, formals and
stobj ABI against fresh definitions from the candidate. Those clones were audit
controls only; the caller and effect theorems named the original functions.
A final assertion checked that ART-READ calls the original block-read function.

| Control | ACL2 seconds | Prover steps |
|---|---:|---:|
| Original block-read and fresh-wrapper effect family | 1.11 | 38,711 |
| Original ART-READ body/guard/shape/quantities | 6.02 | 354,322 |
| Old opaque-boundary strategy refusal | 4.19 | 39,157 |
| Unchanged ART-READ descriptor effect | 12.60 | 136,216 |
| Unchanged ART-READ issued effect | 21.40 | 214,704 |
| Shifted six-result ABI and missing-carrier refusals | 0.27 | 1,226 |
| Retired-arm setup and descriptor proof | 0.65 | 8,530 |
| Identical retired-arm issued theorem by prior proof | 0.00 | 0 |

The first prototype selection included TLS-start, which is absent in the older
baseline, and correctly refused its missing ABI. A subsequent staging check
caught a missing cursor declaration needed for extra-child discovery. Both were
corrected in prototype setup; no theorem, body or guard changed. The original
automated runner retained that initial refusal exit status, while the corrected
individual proof receipts above passed. The session then stopped and released
its 4 GiB allocation.

This is not current-source certification. TLS-start's current boundary and the
complete changed-source fixtures remain pending a coherent record gate. The
smallest fixture roots are `tests/issue-wrapper-boundary-unit` (49 books) and
`tests/machine-arms-unit` (36 books). Remaining ART-READ proof costs above ten
seconds are still proof-engineering work; the full cursor book was not replayed.
