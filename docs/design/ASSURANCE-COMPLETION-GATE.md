# Served assurance completion gate

`python3 tools/assurance_completion.py --package CANONICAL-PACKET --report BRIDGE-REPORT`
refuses product completion independently of build and generated-candidate regression
results. It never launches ACL2 or Lean, publishes certificates, or modifies their
caches. The current semantic discharge join is unimplemented, so this gate remains
incomplete even if every book and generated candidate passes.

`tools/assurance_scope.json` declares the named `served-product` scope: supported
operator profiles, environment assumptions, and twelve required feature categories.
Its entries select claim IDs from the existing live `fn2-squares` store and name
required served subjects; they contain no claim status, proof, formula or witness.
Missing catalogue entries and empty served subjects are refused. The explicit
`FN2-SERVED-PROGRESS` requirement currently has no registry row. Persistent
reclamation has an unbound row. These represent missing coverage, not implemented
features or promises discharged by standalone model proofs. The catalogue needs
specification review whenever advertised behavior changes; automation cannot infer
that the catalogue is sufficient.

Run the same command with `--emit` to propose
`meta/emit/assurance-completion.lisp`. This generated book includes the actual OWED
assembly and independently checks the packet's manifest, arm inventory, canonical
function records and served call closure against the live ACL2 world. Its literal
scope and packet identities participate in its own certificate closure. The gate
requires a qualified record-toolchain cache entry at that current closure; an
existing `.cert`, old manifest, report flag or Markdown census does not qualify it.
Changing the scope, packet, checker, included statement or dependency invalidates
the corresponding evidence. The command checks the closure again after report reads.

`books/assurance-completion.lisp` uses the existing `fn2-square-rowp` to check the
actual statement body and admitted universal theorem. It rejects missing or unbound
rows, owed statements, unrelated theorem bodies, explicitly unreachable branches,
missing served subjects, malformed/cyclic/missing declared dependencies, and absent
formula-bound controls. Required subject names must occur in the live translated
formula's function calls; author `:formula` metadata cannot redirect this check.
It regenerates the positive and negative ground assertions through
`fn2-assert-square-evidence`. Witnesses and finite tests cannot upgrade `:owed`.
Every declared dependency must be another registry row with the same checks;
arbitrary unrelated theorem names cannot substitute for missing claim nodes.

The bridge check reconstructs the existing `served_semantic_inventory` directly
from the canonical packet. Every canonical served root remains in the denominator,
including roots lacking generated candidates. Submitted completion flags cannot
discharge the inventory. The required typed proof join for canonical evaluation,
domains, recursion, attachments and the actual caller-to-specification chain remains
an explicit blocker. Existing candidate/build commands retain their narrower meaning.

This gate checks evidence connections; it does not implement missing behavior or
prove that an advertised guarantee is useful. Structural subject occurrence alone
does not establish a refinement relation, specification independence or reachability.
Those require the actual admitted statement, its formal composition proofs, and
meaningful controls. The gate cannot discover omitted logical dependencies or
establish real-device fences, raw FFI correctness, fairness, hardware reliability,
kernel correctness or adequacy of the supported-object encoding. Those remain
explicit specification and trust boundaries, never new internal proof assumptions.

`python3 tests/test_assurance_completion.py -v` runs source functions under SBCL
with explicit world-access seams and temporary-file/cache-query controls. It invokes
the actual live row guard and checker, including a valid positive control and the
wrong-formula, witnesses-only, missing-root, unreachable, missing-served-binding,
missing-dependency and stale-closure refusals. This is local source regression
evidence, not ACL2 admission or current-closure certification of the new checker.
