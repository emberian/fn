# Internal identity-preserving import

This producer is an internal C connection, not an authorized network import
entry. No carrier calls it. Authentication, ordered page admission, coverage,
and durable import-cursor advancement remain outside this implementation.

`fn2-peer-import-start` takes the transaction, evidence and optional receipt
field bases, and the actual pool owner. It validates the schema fields and
reserves an owned name/digest copy before starting the existing bounded
identity query. Generated per-transaction `fn2-peer-imports` state retains
the original scalar fields, receipt identity, owner and copy generation.
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

The source fixture checks changed origin and occurrence, changed receipt,
changed name/digest contents and tags, duplicate counts, partial copies,
and attempted publication followed by authoritative reads of all four
schemas. Direct C bind/publication is not a persisted acceptance test.
Current evidence is source review and structural checks only: ACL2 admission,
guard closure and execution of these controls are still required.
