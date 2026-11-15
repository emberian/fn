# Internal identity-preserving import

This producer is an internal C connection, not an authorized network import
entry. No carrier calls it. Authentication, ordered page admission, coverage,
and durable import-cursor advancement remain outside this implementation.

`fn2-peer-import-start` takes the transaction, evidence and optional receipt
field bases, and the actual pool owner. It validates the schema fields and
reserves an owned name/digest copy before starting the existing bounded
identity query. Generated per-transaction `fn2-peer-imports` state retains
the original scalar fields, receipt identity, owner and copy generation.
Each admitted identity-query start advances a non-wrapping runtime query
incarnation. The importer captures that incarnation and checks it before
declaration and cleanup; a replacement query is retained, including one
with the same owner and key. Exhaustion refuses before query or scratch
mutation. Query steps and transaction release preserve the incarnation.
The pool has no immutable mode: this is a private owned copy, not a claim
that arbitrary pool clients cannot modify memory.

After `fn2-identity-decide` completes, `fn2-peer-import-declare` compares all
original evidence and receipt fields, including byte contents, with that
snapshot and checks the completed query's identity. It constructs successor
arguments from retained values. Original origin, occurrence and foreign
history position remain values; they are not replaced by the local event.
Existing C union comparison decides duplicate versus conflicting payload.
Imported facts neither select a candidate nor create a local article.

An incomplete summary fold is declared before evidence and receipt slots.
Partial argument-copy failure therefore cannot stage a complete transaction.
Cleanup must retain a bound transaction across persistence uncertainty and
must not discard another writer's transaction on detected interference.
Initial interference leaves the private snapshot retained. A later import
abort releases only that snapshot when the successor is actually idle with
all slots empty and no live identity query references its pool generation.
The foreign query and successor are unchanged. Bound work or a live alias
refuses; cleanup can be retried after its owner finishes and releases it.
The alias check covers this transaction. The private-copy ownership contract
forbids handing its pool handle to other transactions; this is not a scan or
proof that arbitrary other clients cannot retain that private handle.
Only fixtures currently call this importer. Production slot/generation reads
are confined to its same-transaction materialization/query/successor path,
but generic query admission accepts caller-provided references and owner.
Before a composed producer can claim cross-transaction reclamation safety,
creation/transfer must enforce transaction-bound private references or the
producer must prove that these handles cannot escape. That claim is open.

The source fixture checks changed origin and occurrence, changed receipt,
changed name/digest contents and tags, duplicate counts, partial copies,
and attempted publication followed by authoritative reads of all four
schemas. Direct C bind/publication is not a persisted acceptance test.
Current evidence is source review and structural checks only: ACL2 admission,
guard closure and execution of these controls are still required.

The next ownership connection is a real query read reference, separate from
I/O descriptor `out-count`. Existing `fn2-pool-release-out` requires a matched
terminal OpRef; query reads cannot pretend to be operations. The proposed
state records the two query windows independently of reused query scratch
and counts their pool holds. Start must acquire both or roll back, including
two references to one window; replacement and cancellation must close the
stored references exactly once.

Read references cannot simply last until successor release: after the
query reaches `:done`, `fn2-txn-put-post-for` repurposes upload buffers before
that release. The completion boundary must therefore close read references
atomically with the stored scalar result; subsequent done/facts operations
read no source octets. Errors and cancellation need their own retained or
released states. This connection is not implemented or qualified yet.

The shared change must also extend the independent ownership and CNS drain
models. Current CNS drainage stops on a failed pool release. A live query
hold needs an explicit retained outcome and a bounded wake/retry connection
when its last read reference closes. Merely adding a zero-query-reference
premise to existing release laws would not establish that behavior. Current
root contains those drain/refinement books; the next implementation must
compose with that source rather than this lane's older base.
