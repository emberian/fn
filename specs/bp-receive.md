# Experimental portable BP request receiver

`tools/run_bp_receive.py` provides the callable lab receiver:

```python
receive_bpa_request(
    *, store_root, inbox_root, receipt_root, bid, inventory, download, delete, source_eid,
    local_policy_authorized=True, pending_outcome=None,
) -> ReceiveResult(outcome: str, receipt_adu: bytes, staged_path: Path)
```

The function accepts a single bounded canonical `fn-bpa` **request** ADU.
`local_policy_authorized` is an explicit trusted local laboratory A_POLICY
input.  The request wire `authorization-context`, BPA BID, source EID,
destination EID, lifetime, NNTP `From`, and `Message-ID` do not authorize the
operation.

`source_eid` records the adapter's observed transport source; it is required
explicitly rather than fabricated by the receiver. It is provenance, not an
authentication result. The Store must already be initialized.

## Ordering

The complete portable request ADU is first staged with the coordinated FNBI
inbox: inventory, non-destructive download by BID, bounded framed temporary
write and fsync, immutable publication, and inbox-directory fsync.  The
staging call deliberately defers BPA deletion, then reopens the inbox before
reading the full framed ADU.  The adapter does not stage only the extracted
legacy article, so request work/context remains durable with the payload.

ACL2 function `fn-bpreq-article` decodes the wrapper and projects exact legacy
article octets.  The existing ACL2 article parser extracts the Message-ID;
`run_store.metadata` derives per-article archive/subject/evidence from that
ACL2 result and exact payload.  ACL2 verifies that the request subject equals
the derived subject.  The existing Store allocator, preparation, publication,
and recovery path accepts the article.  The host persists the exact encoded
Store record and request ADU with the receiver FNRJ before preparing and
committing the canonical receipt decision.  BPA deletion is attempted only
after both request context and receipt decision are durable.

A committed exact request arriving under a new BID returns `outcome ==
"duplicate"` and the byte-identical committed receipt without adding a Store
record, archive pin, receipt context, intent, or decision.  A persisted exact
context lacking a receipt decision may finish that decision without accepting
the article again.  If Store publication was durable before context
publication, ACL2 `fn-bpreq-existing-record` finds and encodes only the exact
ready/recovered Store record, which the receiver then binds into its first
durable request context; it does not reserve or charge another transaction.
A pending intent remains fenced by default.  The optional
`pending_outcome="committed"` or `"absent"` is an explicit operational
recovery decision for the matching persisted work/receipt identity: committed
regenerates and permits deletion, while absent retains the BPA request for a
later explicit action.  A distinct request with an already-used work ID is
rejected before Store mutation and its BPA BID remains present.

## Recovered acceptance gate

The receiver model does not treat transient Store success history as recovered
durability.  Its request-context replay accepts an encoded Store record only
when the Store is structurally valid, its file machine is `:ready`, the exact
record occurs in authoritative recovered `fn-sf-records`, and the node holds
the matching published article, subject, and archive binding.  A recovering or
fenced Store cannot create a receiver receipt.

## Limits and evidence

The portable ADU is bounded to 65538 bytes before ACL2 marshaling.  The exact
article must satisfy the current Store payload limit.  BID is a bounded ASCII
local transport key.  `tests/test_bp_receive.py` covers a first durable
acceptance, close/reopen with a new BID and byte-identical receipt regeneration
with one article/pin/record, malformed subject rejection with BPA retention,
conflicting request rejection without a second Store record, Store durable
publication before FNRJ context followed by close/reopen binding, and explicit
matching pending-intent recovery.

This is an experimental trusted-loopback lab path.  It performs no
cryptographic verification, does not infer an authenticated author from BP or
NNTP fields, does not transmit the returned receipt, and does not establish
BPA, filesystem, or physical media guarantees beyond its explicitly modeled
and host-boundary operations.
