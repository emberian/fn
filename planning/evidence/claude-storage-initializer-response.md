# Response to independent fresh-initializer review

Reviewed source: `8820acc9423495ecd82c4a19374b1a74937170ba`.
The exact received report is
[`claude-storage-initializer-review.md`](claude-storage-initializer-review.md),
SHA-256 `971581c7f4e7957d402291d114953a8014ba4ef61a48c218dd5dd81eebc9a8a6`.
This response is the coherent repair batch, not a second review cycle.

| Finding | Disposition and concrete result |
| --- | --- |
| F1 | Accepted. `fn-bsi-current-init-program-establishes-current-image` is now named in the book, specification and handoff as the whole-image/config-history durability keystone. `fn-bsi-current-init-program-establishes-relation` is explicitly a `:root`/`:transactions` projection. The test removes only `(:fsync-dir :config)`: the old relation still holds, `config/00000001.cfg` is durable-absent, and exact-image equality fails. No global relation strengthening was made. |
| F2 | Accepted. Each config/history/frontier publication has a distinct label family, and the closing fences gained `init-final-*` names so none collide with a publication cut. The test evaluates every cut name and proves it duplicate-free. `tools/transcribe_check.py` now registers `store:initialize -> fn-bsi-current-init-program`; it reports its helper-inlining/label-evaluation limitation and expected current-host fault-label mapping instead of checking the obsolete model. It therefore makes no claim that uninstrumented model cuts are host-killable. Adding host `faults.at` sites remains work for the host owner. |
| F3 | Accepted. Removed pairwise stage-name distinctness. The test executes all three publications with one equal stage name and reaches the exact image/relation. Existing-entry `O_EXCL` failure remains open. |
| F4 | Accepted. The physical `must-fail` uses a non-string config-stage while the test separately asserts `fn-bs-initial-inputp`; its failing relation is therefore attributable to `fn-bsi-fresh-inputp`'s path-name contract. The frontier-one `must-fail` remains the independent metadata-binding witness. |
| F5 | Accepted. The config-directory EIO witness comment now says the barrier runs, returns EIO, and terminates the runner at that failed barrier. |

`docs/prefixes.md` now registers `fn-bsi-`. The source and teeth certified
locally with ACL2 8.7:

```
python3 tools/certify_books.py books/byte-store-initializer \
  tests/acl2/byte-store-initializer-tests --jobs 1 --timeout-seconds 180
```

Result: `build/acl2/certify-20260921T074553Z-44991` passed both books.

The repaired owned closure also passed on hbox with two jobs:
`run-20260921T074632Z-ecbe`, archived as
`planning/evidence/manifests/certify-20260921T074637Z-1785855.json`.

```
python3 tools/transcribe_check.py
```

Result: exit 0; `transcriptions=10`, `fidelity-defects=0`,
`missing-host-cuts=0`, `syscall-drift=4`, `unmodelled=4`, plus the explicit
initializer helper-inlining `limits` row. The zero missing-host-cut count is
not evidence for initialization because that row is intentionally limited.
The four drift rows and four unmodelled paths are pre-existing and listed by
the tool's output; this batch introduces neither a closure claim nor a host
instrumentation claim.

Open work remains general K0 preservation, recovery establishment,
retained-history composition, existing/retry initialization, and a separate
configuration-history refinement decision with its preservation/K1-K4 impact
review.
