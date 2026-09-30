# Conditional immediate arithmetic objects

PRF-1173 names A-SELECTED-RUNTIME-IMMEDIATE-ARITHMETIC for the exact captured
GENERIC-+, GENERIC--, GENERIC-* and SB-KERNEL::FLOOR1 result-object paths.
The selected binary, saved core, toolchain and compiled primitive artifact
are qualification requirements. The logical operation name alone does not
establish that a caller uses one of these machine targets.

For add/subtract/multiply, both inputs and the mathematical result must fit
the selected signed fixnum interval [-2^62,2^62-1]. FLOOR1 is restricted to a
natural fitting numerator and a positive fitting divisor; the quotient fits.
The conditional primary-object unit is zero bytes and zero allocation
requests. It neither prices a broader bignum operation nor limits supported
stored data; unsupported unit domains remain unavailable until another
qualified family covers the actual operation.

The executable logical domain/result helpers describe the mathematical
conditions. They are not funded served validators: actual source operand and
result proofs must establish the conditions, and installation binds exact
executed targets. In particular, the helper's own arithmetic/checking costs
are not priced by the primitive unit. The guarded three-value candidate
returns :PRIMARY-OBJECT/0/0 or :UNAVAILABLE/NIL/NIL, never an admission.

Call and control frames, exceptions, asynchronous participants, automatic
collector, first-use and the whole operation allowance remain separate. No
arbitrary-width report division, general compiler lowering or complete
connection/control scheduler adequacy follows.
