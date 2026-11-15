# Carrier hint presence

Candidate `527f4836f` distinguishes an absent carrier `:hints` option from an
explicit `:hints nil`. An omitted WFP hint now inherits the common hint, matching
the existing TYPE option behavior. Explicit NIL still suppresses inheritance;
a nonempty per-carrier hint still overrides the common hint. The theorem
producer, complete antecedents/conclusions, output projections and runtime
functions are unchanged.

The current `fn2-columns-carrier-specs` emits TYPE and WFP/custom-invariant
specifications only. This patch does not introduce carrier ROWS specifications
or change the separate frame-hint policy.

Three local source-control tests pass via
`python3 tests/test_columns_carrier_hints.py`. They execute the actual generator
functions in SBCL, without ACL2 admission:

- Current routing and complete formula identity against the prior source,
  including custom invariant/suffix, direct and MV projections, explicit TYPE
  and WFP hints, explicit NIL, and absent common-hint inheritance.
- The pre-TYPE-option source fails the opt-in control.
- The immediate pre-repair source fails the absent-WFP fallback control.

The existing ACL2 fixture adds exact expansion assertions for common WFP
inheritance and independent explicit-NIL suppression. It retains actual
constructor admission. These ACL2 assertions have not run. Parsing, secrets
and whitespace checks pass. No remote compute or active-candidate edits were
performed.

## Narrow qualification plan

Metadata-only dependency traversal gives this exact local closure for
`tests/columns-carrier-hints-unit`:

1. `books/operations`
2. `books/declare`
3. `books/columns`
4. `books/columns-guard-hints`
5. `books/columns-carrier-contracts`
6. `tests/columns-carrier-hints-unit`

Only columns and the fixture have edited source; the two intervening helper
closure keys also change. Query authenticated cache entries at the eventual
frozen source/toolchain before assuming reuse of operations or declare. Use a
bounded single-job author admission of this six-book scope first, retaining a
first refusal. After it passes, record-qualify the exact fixture closure using
the supported scoped farm route. No grant or launch is implied by this plan.

The foundation change rekeys columns descendants, so batch it with pending
shared proof APIs rather than overlaying the active application world. The
already successful source-hash and retention fixes use explicit carrier hints
and retain their exact routing under this change. Application consumers whose
previously absent WFP hint now inherits a common hint need their original
composed admission gate at that later freeze; the fixture alone does not
qualify those consumers.

Read-only Forge cache inventory at source `481facac5` found two integrity-checked
compiled entries with toolchain identity `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`:

- declare: `299f7489bcfaeeb7c1a8f777c4a3b4886c5be174761a2f63f69a39599466aba1`
- operations: `ffaf93d705d08918400704d108e7bffa6a3da8ae5ae2917128974f7d53c9e71b`

The four exact misses are columns, columns-guard-hints,
columns-carrier-contracts and the fixture. The fixture closure key is
`c54a3d3abb11079eb6a5c0817bc063d8b2cf6cf33cdada3d64b84a179e9dc34c`.
All six books permit only the plain certification world. No install, ACL2
process or record run occurred. Plan and cache-query details are retained in
`/tmp/carrier-hint-presence-plan.json` and
`/tmp/carrier-hint-presence-cache.json` locally and on Forge; installation must
revalidate entries and their compatibility when a gate is authorized.
