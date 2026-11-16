# BOOT callback source work

This source binding audits CORE `273becee1` with canonical lower `17f802d44`.
It does not certify a runtime face, physical cost refinement, or BOOT admission.
`boot-callback-work.lisp` contains ACL2 arithmetic over the actual provider
components; the JSON inventory records every expanded source callee.

| Callback | Structural steps | Typed payload bytes |
| --- | ---: | ---: |
| bootstrap pack | 842 | 8468 |
| bootstrap verify | 1089 | 16724 |
| anchor zero | 690 | 4096 |
| anchor step | 7562 | 8256 |
| descriptor check, conditional | 3024 | 8480 |

Descriptor values exclude the forthcoming checked fresh-BEGIN callback and
its controller. They require the real PAGE continuation gate below. They
must not be bound as an unconditional generic FORMAT cost.

The primitive boundary matches the canonical directory audit: octet read,
write, copy, parse validation and hash loops are typed byte work; their
per-octet ownership internals are not charged again. Scalar field completion,
continuation control, fixed-schema BODY shape checks and core GET/store are
structural work. Declared guards and proof fixtures are excluded. Source SUM
includes short-circuit alternatives; branch MAX is explicit in payload work.
The same generated GET body executes READ-CODE again; these are actual
`fn2-machine-checked-reader-events`, `fn2-machine-field-events` and
`fn2-machine-snapshot-events` bodies, not fixture instrumentation.

Generated decode has eight resume reads, start/save nine operations each,
and at most six saved field reads plus seven store operations on each of
success and rollback. Encode scalar fields have two metadata reads across
sizer/checker/emitter; digest fields have ten plus three range admissions.
These are parameterized source-template contracts, not observed ACL2 emission.
Their extraction/refinement theorem and critical evidence remain owed.

PAGE needs this condition after full-window readability and before FORMAT:

```lisp
(or (not (equal phase *fn2-fc-phase-hash*))
    (equal (fn2-fc-pad-end row fn2-fc) len))
```

`phase` should reuse the existing actual FIRST-phase read. Failure returns the
existing `:context` result without mutation. `fn2-fc-decoded` computes PAGE
`pad-end=len`, writes it, then enters PREFIX. The source guard closes malformed
WFP state that otherwise returns `:byte` from PAGE-SPAN repeatedly. Raw WFP
alone does not justify the one-span bound. The donor does not add that guard.

The supported kind currently declares 32768 byte and 32 structural units.
Even the pack wrapper alone exceeds 32. The integrator must bind callback and
controller work together, resolve the kind budget and check independent
byte/step limits plus `fn2-run-quantitiesp` and the registry work ceiling.
FORMAT grant 4096 is not the complete callback: PAGE can scan then hash the
same span; terminal descriptor decoding has its own full parser quantum,
followed by five 32-byte root copies and Ref/build-field writes.
