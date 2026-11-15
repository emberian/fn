# Query read references: implementation plan

Status: source design, not implemented or qualified. Foundation is current
020d6313c composed with peer-history-order through 277f927c3. The existing
same-transaction incarnation/detach controls do not establish cross-transaction
reference safety. Authorization and network import remain inactive.

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
required composition checks. Shared pool/CNS ownership and a narrow execution
grant must be coordinated before implementing this plan.
