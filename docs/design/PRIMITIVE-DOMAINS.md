# Primitive domain pilot

The integer-power fragment requires an integer base and a natural exponent at
**each reached EXPT call**. `PrimitiveDomains.integer_power_correspondence`
relates canonical integer objects to the existing native integer result, and
`integer_power_result` proves that result is representable. It uses the shared
`PrimitiveContracts.expt_nonnegative` theorem, separated from the rational
library so the closed-evaluation foundation can import it directly.

The canonical object function is deliberately partial. It is not an interpreter
for arbitrary ACL2 numbers. Removing the exponent premise admits the represented
inputs 2 and -1: native completion returns integer zero, while the canonical
integer fragment refuses and the rational object 1/2 is not representable by
`Object.value?`. The existing rational mismatch theorem in `PrimitiveContracts`
remains unchanged. `tests/primitive-power-domain-unit.lisp` separately checks
ACL2's actual EXPT result and the nonnegative integer-result theorem.

Controls assert the whole positive premise and output for 3^4, the negative
exponent case, and rejection of a changed operator that adds instead of raising
to a power while preserving integer input/output shape. The generic theorem is
quantified over every represented input satisfying the domain, not just these
examples.

CNS uses unsigned-byte checks in its read-result path (`books/cns.lisp`) and
edge profile (`books/cns-kind.lisp`). Their logical power-of-two bounds motivate
this family. This source observation does not discharge a current served root's
call-domain obligations. The fresh canonical packet must bind the actual sites,
and the caller proofs must establish nonnegative exponents and represented
arguments before this certificate contributes to served coverage.

The three primitive modules passed a bounded Lean 4.30.0 author probe on forge
(`/tmp/assurance-primitive-probe5.log`), with six axiom censuses containing only
`propext`, `Classical.choice`, and `Quot.sound`. This is not an ACL2 record
certificate or current-world served-closure certification. The paired ACL2 book
subsequently passed record certification `certify-20261114T020826Z-3549697`: one
book, no local dependencies, 566 prover steps, 0.116 seconds. Its current closure
key is `fe690b3072a01c0113ae5d17a508c4cc2764a730a7b36671ff6aec4233d9ab2b`,
with an authenticated published record-toolchain cache entry on forge. Sol
independent source review found no domain or vacuity blocker. The full Mathlib
consumer of the moved theorem has not been recompiled because its cached
dependencies are unavailable; the existing rational theorem remains unchanged.

## List primitives for the timer consumer

`PrimitiveLists.list_primitive_correspondence` covers NTH and UPDATE-NTH with
natural indices and represented arguments. Independent canonical Object
operations preserve `Object.value?` through reads and writes, including dotted
tails and NIL padding. The domain does not require proper lists or array bounds;
those remain the caller's layout/guard obligations. No symbol equality or
package-alias injectivity is assumed by these structural operations.

The result-support theorems `nth_correspondence` and
`update_nth_correspondence` allow successive primitive calls to compose without
reassuming representation of the intermediate value. Controls assert the entire
padded output, preserve an unrelated element, reject a sibling-clobbering mutant
that keeps the target value, and expose both a negative-index completion and an
unrepresented rational insertion. `tests/primitive-list-domain-unit.lisp` is the
paired actual ACL2 completion/effect fixture.

This family serves the current clear-wait-timer pilot: its scheduler helper uses
field reads and writes, integer comparisons/decrement, and an exact status
symbol. These list certificates do not establish that helper's full contract or
its reached domains. The scoped canonical packet and caller composition remain
with the bridge owner.

The two new modules passed Lean 4.30.0 author probe
`/tmp/assurance-primitive-lists-probe2.log`, with all eight axiom censuses limited
to `propext`, `Quot.sound`, and `Classical.choice`. The first failed probe is
retained separately; it rejected a string-inequality proof tactic in a negative
control, repaired without changing the statement. The paired ACL2 fixture
passed exact-source record `certify-20261114T221932Z-490268` at `9da695c5d`: one
book with no local dependencies, 31 prover steps, 0.115 seconds. Its current
closure key `f35ecd36e708ee8707ac5f42bfc3b081586d737a397f892a8d0d57a1497dfbfc`
has an authenticated published record-toolchain entry. Negative-index and
dotted-tail controls concern ACL2 logical completion, not permission to execute
an out-of-guard native call. Reached-guard domain construction and actual timer
consumer binding remain pending.

## Reached guard branches

`natural_index_of_guard_branches` now derives a natural-index representation
from the observed native INTEGERP truth and a false negative comparison. The
NTH and UPDATE-NTH domain constructors use that witness directly. Neither
constructor grants a guard from a declaration: the consumer must prove that
these branch observations hold for its reached index.

The positive control supplies both branch facts and both call domains. Separate
hypothesis-removal controls show why NIL's numeric completion cannot replace
INTEGERP, and why an integer premise alone permits negative indices. The exact
modules passed author probe `/tmp/assurance-list-guard-probe3.log` with all
fourteen axiom censuses limited to `propext`, `Quot.sound`, and `Classical.choice`.
Earlier failed tactic probes are retained separately. This makes the domain
constructors available for the scoped timer proof; it does not itself bind an
actual exported timer call site or prove its full contract.
