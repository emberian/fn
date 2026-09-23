# Synthetic portable fn inbox in Mini

This public fixture contains three original Mini signed calls and their native
outcomes from one synthetic consumer history. The input articles and their
corresponding Mini inbox atoms are retained as exact octets. No private key,
live Store database, fn consumer cursor, or claimed Store verdict is included.

`first-*` is the first authenticated fn source, committed as one atomic Mini
content-resource invocation with the operation binding, immutable application
reply Q and exact portable inbox. `relay-*` adds `Path` and `Xref` to the
carrier but preserves the same signed source and source identity; its separate
evidence transaction returns the original Q without another application
effect. `changed-source-*` carries a different authenticated fn source with
the same Mini origin operation and local application; its separate conflict
transaction likewise leaves Q unchanged. Accepted counts after these calls
are 2, 3 and 4 (count 1 is the consumer resource birth).

The `*-inbox.bin` files are canonical
`DREGG/FN/PORTABLE-INBOX/v1` values exported after exact native Mini history
re-admission. Each paired `*-carrier.eml` is byte-identical to the carrier
inside that inbox. `first-reply.bin` is the original immutable Q exported
from the accepted first signed call. The `*-decision.json` files are
proposals, while `*-outcome.json` are normal native receiver confirmations.
`repeat-decision.json` is the historical exact repeat after all four accepted
events, with no new intent. The three decision objects share one operation;
the first and relay share one verified fn source identity, while changed
source differs. The first, relay, and repeat reply hex values are identical.

The full test scope, native image and Mini source hashes, timing, trust
boundary and command results are in
`planning/evidence/dregg-e1-portable-inbox-p1.md`. Portable fn authorship is
not local fn Store acceptance, and Mini confirmation is not an E2 ack.
`hash-benchmark.lean` is the exact standalone timing driver for the existing
Mini Lean cSHAKE implementation; it makes no semantic decision.
