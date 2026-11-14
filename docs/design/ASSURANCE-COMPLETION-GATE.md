# Served assurance completion gate

`python3 tools/assurance_completion.py --package CANONICAL-PACKET --report BRIDGE-REPORT`
refuses product completion independently of build and generated-candidate regression
results. It never launches ACL2 or Lean, publishes certificates, or modifies their
caches. One actual-served ACL2 descriptor-contract join is implemented as proof
events; its admission/qualification and the complete semantic discharge join remain
pending. This gate remains incomplete even if every book and generated candidate passes.

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
`meta/emit/assurance-resource-join.lisp` and `meta/emit/assurance-completion.lisp`.
The product checker includes the separate resource evidence book. That book includes the actual OWED
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

The first typed component is the descriptor facet of the unchanged required
resource-bounds category. `books/assurance-resource-join.lisp` independently specifies
the original residual contract: typed well-formed core and natural budget imply
result slot 2 of actual `fn2-machine-run` is at most that budget, with no valid-ID
premise or stopped-output exception. A second independent specification requires
slot 3 of actual public `fn2-turn` to be natural and at most `fn2-exec-aturn` on a
typed well-formed core. ACL2 translates these specifications in the actual composed
world. The checker compares the residual registry statement and public admitted
theorem exactly to those independently translated specifications, checks actual
function guards, input/output stobj ABI and guard verification, then generates
`fn2-assurance-residual-descriptors-joined` and
`fn2-assurance-public-turn-descriptors-joined` using the actual admitted proofs.
It does not execute a separate model of a turn.

Canonical records for `FN2-MACHINE-RUN`, `FN2-TURN` and `FN2-EXEC-ATURN` are mandatory;
complete raw records and each field digest participate in this evidence book's
identity. Coherently weakening the live residual statement, registry row and admitted
proof together fails the independent descriptor specification. Domain, result-slot,
called-function, guard and ABI mutants also fail. This evidence book needs its own
qualified current-closure entry, rechecked after reading inputs. Its proof events have
not yet been admitted or record-certified on the composed tree. This facet does not
establish observation/visit bounds, full-turn issuance history, CPU/allocation bounds
or the complete resource guarantee. It adds no formula-bound R22 witness package;
required top-level evidence remains separately checked and incomplete.

The bridge check reconstructs the existing `served_semantic_inventory` directly
from the canonical packet. Every canonical served root remains in the denominator,
including roots lacking generated candidates. Submitted completion flags cannot
discharge the inventory. The required complete typed proof join for canonical evaluation,
domains, recursion, attachments and the actual caller-to-specification chain remains
an explicit blocker. Existing candidate/build commands retain their narrower meaning.

This gate checks evidence connections; it does not implement missing behavior or
prove that an advertised guarantee is useful. Structural subject occurrence alone
does not establish a refinement relation, specification independence or reachability.
Those require the actual admitted statement, its formal composition proofs, and
meaningful controls. Outside the independently specified descriptor facet, a coherent
replacement of statement, theorem and controls by a weaker proposition is not detected
by the structural claim checker; each required specification needs its own typed join. Declared `:depends`
edges are authored claim connections, not an extracted theorem-rune dependency
closure. The gate cannot discover omitted logical dependencies or
establish real-device fences, raw FFI correctness, fairness, hardware reliability,
kernel correctness or adequacy of the supported-object encoding. Those remain
explicit specification and trust boundaries, never new internal proof assumptions.
The product command always reports actual theorem/constraint dependency closure as
unresolved: authored `:depends`, an empty list or a submitted completion flag cannot
stand in for extracted, qualified dependency evidence. No such extractor or discharge
is implemented yet.

`python3 tests/test_assurance_completion.py -v` runs source functions under SBCL
with explicit world-access seams and temporary-file/cache-query controls. It invokes
the actual live row guard and checker, including a valid positive control and the
wrong-formula, witnesses-only, missing-root, unreachable, missing-served-binding,
missing-dependency and stale-closure refusals. This is local source regression
evidence, not ACL2 admission or current-closure certification of the new checker.
