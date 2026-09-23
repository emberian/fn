# Derived Store event index, scoped kernel evidence

The ACL2 `fn-cei-*` kernel builds a four-octet radix index from the exact
committed Store event list. It is a derived, rebuildable projection, not a
second journal or a persisted authority. Each lookup or extension follows
four octet keys; a builder-produced branch can contain at most the 256 octet
keys and one terminal key. The build is linear in the retained Store event
count and belongs at observed open/recovery, not at a served poll. One
completion path-copies four branches. Persistent roots held by live prior
views can retain those copied branches until the views are released; the
memory claim is for one current root plus explicitly retained prior roots,
not an unbounded-free historical snapshot claim.

The exact original manifests record the ACL2 8.7 executable, toolchain
identity, source digests, cache origins and results:

| Manifest | Scope | Result |
| --- | --- | --- |
| [index book](manifests/certify-20260923T230003Z-405888.json) | `books/consumer-event-index` | Passed |
| [index tests](manifests/certify-20260923T230101Z-408434.json) | `tests/acl2/consumer-event-index-tests` | Passed |

`fn-cei-get-of-build-is-committed-event` and
`fn-cei-correspondence-lookup` equate the derived lookup at an in-range
uint32 sequence to the exact event at that committed-list position, under
the bounded dense-history and correspondence premises. The test book has a
nonzero-sequence witness, path-copy preservation witness, a stale substituted
event whose lookup differs when correspondence is omitted, and a future
lookup counterexample. `fn-cei-extend-preserves-correspondence` establishes
the single-event extension shape.

This packet does not yet install the index in Store or change the called
`fn-col-poll`; it earns no poll work bound by itself. The Store transition,
reopen and poll caller join needs separate scoped certification and native
qualification.
