# Conditional initializer array stores

PRF-1169 specifies the primary-object portion of the generated
UPDATE-FN-OCTETS$C-BUFI and UPDATE-FN-OCTETS$C-FILL store paths under
A-SELECTED-RUNTIME-INITIALIZER-ARRAY. The exact foundation, generated macro
expansion, standalone compiled PUT/CLEAR callers, compiler policy and toolchain
are part of the coordinate. Genuine UB8 backing and an installed NIL HONS
association are qualification obligations, not facts attested by a coordinate
list or scalar predicate.

The byte-store domain requires a natural index below 65536 and the existing
capacity, and a natural octet below 256. The fill-store domain requires a
natural fill at most 65536 and at most the existing capacity. Capacity is a
natural below the selected runtime's strict array dimension limit 2^44.
These are actual initializer site bounds, not stored-data truncation policy.
Larger old arrays remain borrowed and retained.

The named encapsulate has two executable local witnesses. Its conditional
unit theorems constrain primary object allocation to zero. Guard-verified
three-value selectors return :PRIMARY-OBJECT, zero bytes and zero requests
inside their domain, or :UNAVAILABLE, NIL and NIL otherwise. Neither result
is an admission or installed authority.

Caller inlining and control, value arithmetic, exception and memoization
paths, first-use, collector, constructors and old/new backing lifetimes are
separate obligations. The actual initializer source boundary and its byte/
fill argument domains live in the page owner's source proof, and must be
composed explicitly. The full INIT allowance and source/pool installation
remain open.
