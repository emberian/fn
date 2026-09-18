# Assurance closure checkpoint — 2026-09-18

54 ACL2 logical/assertion roots, the actual-core simulator, and 45 Python tests
passed. The [machine-readable record](2026-09-18-assurance.json) preserves the
exact commands, source and tool digests, versions, original run and correction.
ACL2 8.7 / SBCL 2.6.8 and Python 3.14.7 ran on macOS 26.6.1 arm64.

The original `make test` at revision `94e08a1` passed certification and the
simulator, then found three stale expectations in one host test. Its already
closed store correctly rejected mutation through the newly enforced exclusive
ownership guard before checking the recovery fence. The test now checks that
ownership is closed and mutation refuses, while retaining all actual reopen,
article and pin assertions. The complete original 45-test Python set then passed;
certified book sources were unchanged. This record does not call the original
`make test` invocation successful.

## Closed component claims

| Area | Established result |
| --- | --- |
| File traces | Actual kernel dispatch over arbitrary finite events preserves the state invariant and prior stable-record/success prefixes; acknowledged-record retention includes the explicit emitted-to-ghost-history premise |
| Small-state crashes | Exhausted bounded exploration: 211 states, 9,038 edges, frontier and record limits 2, with publication choices and recovery barrier counts covered |
| Live node/file completion | Fixed configuration, exact pending-record binding, actual durable node completion before acknowledgement, and full-node replay-extension equality |
| Wire | Event-yield state preservation, exact consumed-prefix/suffix accounting, and no invented event from empty input |
| Article syntax | Successful parsing establishes the syntax recognizer and source/header/body/field limits from the parser-success hypothesis alone |
| Wildmat | UTF-8 scalar/progress/output bounds, parser output recognition, and actual DP matcher equivalence to independent anchored semantics with rightmost precedence |
| Record codec | Successful exact schema-0 decoding re-encodes identical bytes; primitive and full record value round trips remain checked |
| Guard verification | All 21 CBOR and 45 record functions have proved guards; public encode/decode boundaries remain total, internal helper domains are explicit |
| Transfer | General reserve/add preservation and accounting; complete candidate length/octet/retained-byte agreement; exact missing positions; value-corresponding costed hot-path polynomial bounds |

The [transfer work contract](../../specs/transfer-work.md) counts list work in
completion, assembly and missing-position scans. It excludes public validation,
lookup and host arithmetic/runtime costs. Those exclusions are tracked work,
not an end-to-end runtime bound.

## Actual adapter evidence

The Python set includes 47 injected filesystem/completion rows in nine methods,
six actual process-death boundaries in one method, and three ownership/lifecycle
regressions. Prior crossposts and archive pins survive the applicable uncertainty
cases; lost-success retries remain duplicates and consumed allocation is not
reused. The [fault matrix](../../specs/store-fault-matrix.md) names operation and
before/after-effect coverage. Real process death retains OS caches and is not a
power-loss experiment.

An independent `cbor2` 6.1.4 run passed 38 cases against the now guard-verified
ACL2 codecs. Its complete manifest is embedded in the evidence JSON. This covers
the declared primitive/schema-0 composition, not a native signed-object format.
Previous independent NNTP-client and maximum-profile replay evidence remains in
the earlier records.

## Continuing closure work

At this frozen checkpoint the composed node's mixed-trace induction and actual
host adoption were separate work, as were observed-image loading, NNTP session
invariants, additional parser guards, public-operation work bounds and the next
malformed-store/partition matrices. Subsequent targeted results are recorded in
[current work](../../planning/now.md); they are not retroactively included here.

Physical barriers, filesystem isolation and retained stable storage remain
explicit assumptions. There is no freshness anchor, byte-accurate physical
reservation, checkpoint/compaction implementation, chosen native signing schema,
complete NNTP posting service, or deployment/flight qualification claim.
