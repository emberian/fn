# Live handoff donor against current parent

Parent `072b8b316`; preserved source donor `52ebabd0b`. The full live handoff
remains the objective. This is an integration cut, not execution qualification.
No historical pool/columns/allocator/boot file should replace current parent
source. The current application baseline takes execution priority.

Six actual donor roots were inspected: `checkpoint-live-adoption`, its `-rearm`
book, `checkpoint-directory-consume`, `checkpoint-master-arms`,
`checkpoint-summary-authority-live`, and `checkpoint-summary-live-close`.
Their literal project union is 250 books: 157 byte-identical to parent, 23 absent,
70 different. Different does not mean required replacement. The exact inventory
is `/tmp/reclamation-live-donor-provider-map.json`. This separates the actual
lower adoption closure (206 books) from master/rebase continuations.

## Ordered source cuts

| Cut | Named donor source | Current-parent integration |
| --- | --- | --- |
| 1. Resident conservation | `aba3acc01`, based exactly on current072 | Four production books; actual query API retained; independent 132-book fixture. This can be qualified before live adoption. |
| 2. Canonical catalog/holds | `afe8923d3`, `eac0a89a2`, `0e5308162`, `3040b9696`, `58225f63d`, terminal wake `b4113f25f` | Parameterize the current canonical summary, descriptor and hold bodies over active0/pending1; preserve current cold fields/owner checks/bank protection. Keep active0 wrappers. Descriptor storage is per row; source catalog stays extent-indexed and tag-bound. Row release must notify existing protection-dirty on actual terminal availability. |
| 3. Actual physical source reader | Root1 driver `22eccc907` / coherent provider `a27ff7737`, canonical geometry `197cc3118`, profile leaf `6753ec344` | Export only actual source/load/IO/verified handback and driver bindings onto current qualified pool/columns. Keep current primitive bounds and callbacks. Root1 may encounter installed physical roots after C1, so this is required for C2. No second parser or loader. |
| 4. Typed source observers | Protocol `51e2d87b6` / `e162` and actual D/C/sealer hook providers | Add actual machine-generation-bound READ admission/release and writer preference to current actors. Every old-source reader must join this protocol; raw writer EXCLUSIVE with no connected readers is insufficient. Retain actual query/catalog handles through IO or owned materialization. Drain before HELD; never relax closed-phase mutation guards. |
| 5. Producer/candidate authority | `8131d6053`, `4d5b23ca0`, actual live promise `bf7dae8fc` | Actual root1 BEGIN captures pending1; successful manifest EMIT immediately records its typed Ref/hash, preserving current binder and callback ABI. Publication completion closes catalog against complete pending authority. Exact live candidate/descriptor/cuts/token/owner joins precede actual source-edge promise acquisition. Keep active0 authority unchanged until real consume. |
| 6. Bounded source transfer | `a357c39a0`, `5d54cbe79` | Add monotone installed version floor to current declaration/installers and checked successor above actual priorities/ID/sealer bounds. Separate wire-run/query priority already exists in parent. Apply new roots through the shared cold/live source installer; exact typed writer EXCLUSIVE and old leases0 required. Advance versions before retiring old cache/rows. Use the separate canonical-metadata row-swap extension; do not replace columns. |
| 7. Real consume and release | `5d54cbe79`, phase helper `d7090f8d7`, current master body | Project only the ADOPTED predicate/read-only carriers and ordered new phases onto the current consume/master bodies. Preserve current archive, bank, seal, suffix and physical-map conditions. Actual base/authority commit must happen before old C-process promises drop. Keep old bank/archive/debt obligations independent. Final writer/snapshot close requires actual resource release/thaw/rearm and immutable consumed identity. Do not change current cold boot states. |

These cuts are not safely replaced by cherry-picking a historical broad merge.
The original `5d54` handoff body is the transfer implementation; the current
projection must compose it with the current representations and real reader
hooks. Closure admission and the full positive publication/hold/adoption witness
remain unrun. The new component fixture proves no such positive antecedent.

## Missing lower provider books (exact inventory)

- Source observer: `c-source-observer`, `c-source-observer-state`.
- Catalog and hold: `checkpoint-summary-entry`, `checkpoint-summary-live-catalog`,
  `checkpoint-summary-live-close`, `checkpoint-cbase-start`,
  `checkpoint-cbase-live-acquire`.
- Source transfer: `checkpoint-live-adoption-state`, `checkpoint-live-adoption`,
  `checkpoint-live-adoption-rearm`, `checkpoint-summary-install-source`,
  `columns-row-swap`.
- Physical source IO: `checkpoint-source-loader`, `run-physical-source`,
  `run-physical-step`, `run-physical-io`, `run-physical-release`,
  `run-physical-bound`, `run-physical-bound-step`, `run-physical-bound-io`,
  `run-physical-profile`.
- Pure dependency cuts: `checkpoint-recovery-census-identity`,
  `checkpoint-selected-source-identity`; extract the current identical pure
  definitions into lower books instead of importing stale cold constructors.

Actor hook/core-child registration lies above these literal lower-book roots and
is mandatory integration work, not implied by this inventory. In particular,
current cleanup donor intentionally imports none of those actor observer changes.
No FREE/activation, payload-retirement authority, arbitrary data ceiling, or
source-scanned acknowledgement is introduced by this plan.
