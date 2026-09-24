# Assurance review follow-up at `e160442f`

This is a source and archived-evidence audit of the older independent review's
six process findings. It does not certify an ACL2 book or qualify a native
image. The checks below use the source tree at `e160442f`; archived manifests
have their own source digests and toolchain identities.

The §5.0 and §11.1 edits correct invalid witness recipes and the standard for
calling a hypothesis redundant. They do not change fn behavior or discharge a
proof requirement. T1's invariant-removal tooth, T4's fragment-parent premise,
T3's second positive, and the T6 physical positive remain explicit open
assurance obligations until the specified ACL2 events and fixtures certify.

| Finding | Current disposition and next evidence |
| --- | --- |
| PRF-052 NEWNEWS certification | The old stale-certificate finding is repaired at this source. `python3 tools/green_check.py --json` reports `books/nntp-newnews`, its test book, `books/nntp-invariants`, and `books/nntp-effects` green at their current include closures, with no moved dependencies. The later archived run IDs are in PRF-052's refreshed note and evidence list. `python3 tools/ledger.py --check` finds the cited events. The registry's `certified` status is about those ACL2 events; native served-reader behavior needs separate image evidence. |
| Per-book proof cost | `tools/proof_cost.py` already runs as a warning in `make check`. A latest local manifest may cover only a small incremental selection, so “no measured book exceeds ten seconds” means only that manifest's measured books. Per-event detail is unavailable when the archived `.certify.log` was not retained. The warning should name the measured scope and compare source digests with the checkout when the manifest's remote tree is unavailable; it cannot establish a tree-wide cost bound from one incremental run. |
| Guard posture | The generated ledger distinguishes `verified`, `declared-off`, and the default statuses per function. The host's `fnn-bps-foundation-step` calls `fn-bpn-report-author-step` at `host/native/bp-service.lisp:168`; `books/bp-report-guards.lisp` explicitly verifies that function. `books/bp-node-machine-guards.lisp` also verifies `fn-bpn-step` and `fn-bpnf-step`. Several BP helper/invariant functions remain `declared-off` in the ledger, so certification of their theorems alone is not a guard-verification claim. Any new served path must identify its exact called function and guard book. |
| Checkpoint commit titles | WIP titles are compatible with the agreed frequent-checkpoint workflow. The substantive gate is source-matched certification, tests, and the frozen integrated image evidence, rather than a title convention. No history rewrite follows from this review. |
| BP counterexample suite | The contract's §11.1 explicitly leaves the N05 debt and N03/N04 selection positives open, and the planned A1 teeth/replay/loop test books do not yet exist. Existing related BP tests are not counted as exact §5.0 teeth merely because they cover adjacent behavior. An executable positive must assert its entire antecedent on a reachable trace; each negative must preserve all other premises and negate the conclusion. `tools/teeth_check.py` can count forms but cannot establish those semantics. The T1/T3/T4 rows now withdraw invalid claimed teeth, require T3's second positive, and name the separate T6 physical positive. Those fixtures remain open. |
| Contract delta | `specs/bp-node-machine.md` has no diff between `6bfab467` and `e160442f`; its broad regime still needs the planned per-slice proof and runtime review. This packet repairs the unsound §5.0 instruction that treated failed counterexample search as proof of redundancy, plus the specific counterexample-table defects above. Removal now requires ACL2 to prove the weakened theorem. This focused correction is not a review of the rest of the contract. |

Reproduce the source checks with `python3 tools/green_check.py --json`,
`python3 tools/ledger.py --check`, and `python3 tools/proof_cost.py` (or pass
`--manifest` to inspect a specific run). `make check` checks scaffold and
registries; `make certify` and a source-matched native image are separate gates.
