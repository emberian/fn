# FNBS kind-18 frame checkpoint

`books/bp-fnbs-family-codec.lisp` defines the protected kind-18 frame for
`(epoch, operation-id, anchor-arrival, whole-arrival, exact-whole-wire)`.
The frame preserves those five values, rejects malformed or trailing bytes,
and bounds the whole wire to 131072 octets. The whole wire is evidence in a
future family replacement; the codec does not authorize retirement or Store
delivery. The byte test includes a positive round trip, empty-wire refusal,
and a same-prefix trailing-octet negative. No generic round-trip theorem or
verified codec guard is claimed in this checkpoint.

ACL2 8.7 toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
on hbox certified the book and test with incremental cached dependencies,
`run-20260923T213426Z-8e86`, manifest
`planning/evidence/manifests/certify-20260923T213429Z-212522.json`.
`make check` passed on the same source. This is a codec checkpoint, not a
machine-level N10 or publication/replay claim.
