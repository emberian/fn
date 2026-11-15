# Query read references: implementation plan

Status: active query lifetime and callback/reference composition remain
unqualified. The dormant pool primitive foundation and its leaf controls
are certified: the exact ten-book closure rooted at
`tests/pool-query-ref-unit` has key
`659b5c3975baac8a4db01f65b57271cc6fa10a42ed7ce4fa68ecfb70d832b57f`
under toolchain `8aeb1bea…`; record `certify-20261115T024211Z-748010`
certified pool, pool-ranges and the unit, reusing seven parents. Root
`a3b9723a1` integrated only that dormant foundation. It introduces no
served query-reference producer or cleanup/wake consumer.

The separate consumer lane contains actual query lifetime, checked owner
enqueue, CNS/upload/connection drainage and transaction preflights.
Independent global accounting preservation, reference effect lowering,
selected callback binding and full callback controls remain pending.
Authorization and network import remain inactive.

## Ownership subject

Add generated pool `query-ref-count` and two retained source descriptors in
`fn2-id-decides`, with active flags. Descriptors must outlive query scratch:
C successor resolution legitimately overwrites the query field stripe.
The independent query-reference accounting model counts each active descriptor
against its exact pool slot/generation, including two refs to the same slot.
No whole-state scan belongs on a served operation.

Do not reuse `out-count`. Its existing borrow-accounting subject is live I/O
OpRefs, and `fn2-pool-release-out` requires a matched terminal operation.
Query read references are real, separate claims; no synthetic OpRef is created.
Existing A2 accounting must remain unchanged across new pool writers.

## Exact lifecycle

1. Actual identity start validates source owner, generation and both windows.
   It acquires both new read references before admitting the new query.
   If the second acquisition fails, it undoes the first and leaves the old
   query, fields and incarnation unchanged. Same-slot windows count twice.
2. The summary and candidate reads keep both references. Source release,
   mutation, reset, transfer and input loan refuse while a reference exists.
   Reading and existing output loans remain compatible; their counts and
   terminal events are independent.
3. The actual candidate-to-done transition stores all scalar results and
   closes both references atomically. Repeated done and facts operations
   consume scalar results, not source octets. This is the read-lifetime end,
   not loss of the resulting identity facts.
4. Cancellation and recovery release stored descriptors exactly once through
   the low successor-release connection. Its replay sweep, core wrapper and
   importer cleanup callers must all participate. Replacement of a done
   query has no live old read references; malformed/incomplete claim states
   must refuse rather than lose a reference.
5. The importer's own snapshot remains owned separately after its query is
   done. Other active queries pinning that snapshot prevent private detach.
   Their completion closes their refs; later abort can then free the snapshot.

Holding whole-slot write-blocking references until successor release is
incorrect for the current producer. After identity lookup is done,
`fn2-txn-put-post-for` moves the digest to c0 at SCANNED and repurposes c0/c1
as scratch before resolve, stage, bind and reply. The actual query's octet
read lifetime must finish before that work. Normal reply and stale/changed
retry paths already release the successor before upload drain/new lookup.

## Resumable owner drainage

Current CNS draining releases ws and ns and stops on release refusal. A new
read hold must become a retained outcome, not a stop or a busy-spin.
Preflight both ranges before releasing either; otherwise ws could be freed
before a held ns is discovered and the next retry would use a stale ws.
While held, keep phase/resources and finish non-runnable.

When a query closes the last read ref, wake the actual source owner using
existing `fn2-machine-wake-row`, after checking machine ID, kind and generation.
Pool owner-slot is already the global machine ID, not a kind-local offset.
Both query windows share one owner triple, so the transition needs at most
one wake. Stale or mismatched owners receive no wake. No operation-completion
event is invented. A wake lets the owner recheck its held resources and drain.
Existing output-loan conditions still apply; a query completion does not
complete or decrement an I/O borrow.

## Required composition and controls

The pool operation model and query accounting must describe acquire,
rollback, completion and cancellation independently of implementation helpers.
The current CNS draining model/refinement, release accounting, direct effects,
public contract and whole-H/C controls must include the retained branch and
wake/retry result. Merely adding a zero-query-ref antecedent to an old
successful-release theorem would not connect this behavior.

Controls must exercise actual starts in two transactions sharing a source;
failed second acquisition; two refs to one slot; simultaneous output loans;
completion and cancellation; forbidden source writes/free/transfer while held;
CNS retained drainage followed by last-ref wake and successful retry;
stale owner generation; and unchanged scalar results after read refs close.
The earlier same-transaction duplicate/conflict and detach controls remain
required composition checks. Pool/query/CNS ownership is assigned. No execution grant has been allocated;
source parsing and checks do not establish these control results.

## Wake composition frontier

The prior source flush used the machine directory's single wake slot.
A composed callback that already posted a different wake can lose that
notification when query completion overwrites the slot. The candidate
transaction reply path has not been demonstrated reachable with an ACTIVE
query and a nonzero reply word; the generic composed callback seam remains
unsafe independently of that reachability question.

The current source shares the actual scheduler enqueue operation with the
executor, preserves the ordinary wake intent, and records the additional
scheduler effect in the diagnostic trace. Trace loss must invalidate replay
evidence without stopping legitimate scheduling. Runtime changes and a concrete two-owner composition control are present.
Independent trace replay and reference FIFO semantics are under construction;
current lifecycle fixtures remain source controls awaiting composition and
execution.

The reference correspondence subject is still open. An ACL2 `defattach`
does not establish logical equality between a constrained machine-run stub
and its selected callback. Generated obligations must name the selected
implementation and an explicit attachment-resolution/binding semantics or
paired relational hook contract. The first callback control must assert the
full initial relation, compare every result and post-state carrier, and
reject an omitted-enqueue mutation. The direct two-wake seam controls do not
establish served callback reachability.

## Reachable release composition (source audit, 2026-11-15)

At `peer-query-refs@6d89f3ced`, the production query producers are the sealed
upload's `fn2-txn-offer` and internal `fn2-peer-import-start-key`. TxnOffer
passes the actual upload owner: its name is in C0 or the injected-ID storage
page, and its digest in C0/C1. The internal importer queries its owned copy;
this is not an activated served import route. CNS/CONN lifecycle fixtures
exercise the generic query API, not an additional served producer.
Reclamation's scoped cold-source audit at `62363300e` found no query acquire
in checkpoint/recovery/commit/run-physical code; physical pins and credit
leases are separate ownership mechanisms.

Upload page and C1/C0 releases in `assembly-callbacks-d-upload.lisp` accept
only `:ok`/`:retired` before clearing handles or reclaiming the row. The page
preflight precedes manifest settlement/extent close, and both chunk checks
precede either chunk release. There is no yield or callback between these
checks and their bounded release set. Internal importer cleanup/detach also
checks the release result, retains its snapshot on `:held`, and can retry
through the existing abort entry. A future served importer still needs its
own connected wake/consumer contract.

The only incoming upload `:aborting` edges are pre-store work and identity.
Work rejects a held storage lease before its owner-loss edge; identity is
before store acquisition. Stored uploads remain `:sealed`, relay the child
transaction wake, then enter normal `:draining`. No page-held abort path is
claimed reachable, and its refusal is unchanged.

The `:page-loss` controls in `query-owner-drain-unit.lisp` pause after real
TxnOffer has acquired both references, checking the exact UPLOAD owner and
name page/gen/offset/length, plus the chunk digest source. An independent
query retains the page through actual QUIT and connection reclamation. They
require normal draining, a complete unchanged held callback result/core,
unchanged query/page/C0/C1 while quiet, last DONE/cancel wake, scheduler retry,
and final stale handles for all three ranges. These controls remain UNRUN.

Both generated admission rollback functions ignore release results:
`fn2-machine-range-releases` and `fn2-arms-registry-releases`. Their sole
callers are synchronous fresh-reservation chains, with installation only
after all reservations succeed. No write, query, callback or scheduler step
intervenes. Fresh reservations have fill/count zero, so the positive name
and 32-byte digest acquisition cannot succeed there. This excludes held
rollback in the current generated path, not arbitrary malformed states or
normal post-publication cleanup. `test_admission_rollback_source_shape.py`
checks the exact generator AST/control grammar and rejects inserted query
calls in each reservation chain; four source controls pass. This is a
source-change detector, not ACL2 admission or a lifetime theorem.

The raw core-release held/no-stop leaf gate does not qualify consumers.
Their execution requires coherent current-root query descriptor/start/DONE/
cancel, scheduler effects, owner callbacks and current pool-credit geometry,
preserving Send accounting. Complete descriptor-count lifecycle/frame
obligations and selected callback full-result correspondence remain separate.
