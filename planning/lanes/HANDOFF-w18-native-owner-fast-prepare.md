# W18 shared native-owner fast-prepare handoff

## Source packet

Implementation revision `8cbeda97081b38b638b42aeee204f2e7e887bb1b` on
`w18/native-owner-fast-prepare`, based on `ef6a0177`. The packet adds
`books/owner-prepare-correspondence.lisp` and its test book, changes only the
owner prepare and pending-byte calls in `host/owner-host.lisp`, and updates the
Makefile, prefix/spec/scenario records, and generated ledger.

## Contract and caller

`fn-owner-prepare`, reached by the native shared-owner drain path, calls
`fn-opc-prepare`. The equality keystone proves the whole configured-owner
result equals the former `fn-ocfg-step (:store (:prepare record))` event under
the owner's maintained relation. The owner projection calls the certified
`fn-spc-prepare` store projection, copies every non-store owner field, applies
the same refresh, and retains the configured owner's live configuration, pins,
and staged record exactly. `fn-owner-pending-octets` now calls the logical
`fn-opc-pending-octets` projection.

Observed recovery establishes the premise through open/start/configure.
Configured events and the direct socket wrapper entries preserve it. The fast
path does not execute a relation, whole-state recognizer, history replay, or a
second semantic implementation. Recovery still performs full replay.

The equality tooth is a well-shaped composed owner with one real durable record
and a stale empty node; fast prepare stages a conflicting Message-ID while the
former replaying event refuses it. Wrong-sequence and conflict refusals also
remain executable tests.

## Validation and join

Clean two-root certification: `certify-20260921T101506Z-81697`. Targeted host
load: `1/1`. Production image hashes and the six passing native-owner tests are
recorded in
`planning/evidence/native-owner-prepare-correspondence-w18-2026-09-21.md`.

Only the two actual equality keystones are registered for PRF-014:
`fn-spc-prepare-equals-specification-under-relation` for the standalone store
wrapper and `fn-opc-prepare-equals-owner-event-under-relation` for the shared
owner. Do not register the multi-premise semantic bridge or describe either
theorem as whole-host equivalence.

No matched Linux timing was run. Complete physical adapter correspondence and
the broader native deployment gate remain open.
