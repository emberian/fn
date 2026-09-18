# Validation plan

Only scaffold checks are executable today. The
[scenario catalog](scenarios/catalog.json) specifies future tests with stable IDs,
requirements, and expected outcomes. It is not a passing test suite.

## Evidence by layer

| Layer | Required validation |
| --- | --- |
| Abstract model | Executable examples; non-vacuous initial states; boundary cases; admitted definitions and certified invariants |
| Codec | Golden accepted/rejected vectors; independent decoder checks; round-trip/canonicality proofs; bounded-work cases |
| Storage | Small-state exploration of crashes at each write/barrier/publication point; uncertain failures; disk full; replay |
| Adapter | I/O ordering and stale-completion checks; fault injection; documented platform assumptions |
| NNTP | RFC clause checklist; independent transcripts and a real reader; all forms/ranges/errors; fragmented/coalesced input |
| Replication | Duplicate/reordered batches, missing dependencies, long contact gaps, carried media, replayed receipts |
| Retention/GC | Reservation exhaustion, multiple independent roots, release evidence, old-media reimport, interrupted compaction |
| Operations | Restart, checkpoint migration, corruption handling, backup restore/incarnation rules, concrete resource limits |

Use simulation seeds and bounded exploration parameters in reproducible evidence.
When a scenario is only partially executable, report the modeled boundary and
unmodeled effects. Process-kill tests alone do not establish power-loss behavior.
Tests of the logical core do not establish RFC compatibility of its future codec.

## Evidence record

Each meaningful validation summary records: requirement/scenario/proof IDs;
source revision or content digest; tool/runtime/platform versions; exact command;
result and artifact location; assumptions; omitted cases and remaining risks.
Update the registries after evidence exists, not when a test file is merely added.

## Current check

`make check` uses the standard library to check local Markdown links/anchors,
registry identities/references, milestone references, scenario coverage, and
evidence references for advanced statuses. It performs no network requests and
does not install dependencies, start a service, or run ACL2.
