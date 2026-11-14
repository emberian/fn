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
and the shared rational-library import change still need their respective gates.
