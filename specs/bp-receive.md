# Experimental portable BP request receiver

`tools/run_bp_receive.py` provides the callable lab receiver:

```python
receive_bpa_request(
    *, store_root, inbox_root, receipt_root, bid, inventory, download, delete,
    bundle, source_eid, local_policy_authorized=True,
    wall_error_ms=2000, pending_outcome=None,
) -> ReceiveResult(outcome: str, receipt_adu: bytes, staged_path: Path | None)
```

`bundle` returns the raw BP bundle octets the agent holds for `bid`; `download`
returns the ADU that agent's own extractor produced.  Both are required,
because they answer different questions: the ADU is what fn accepts, and the
bundle is what fn identifies.

The function accepts a single bounded canonical `fn-bpa` **request** ADU.
`local_policy_authorized` is an explicit trusted local laboratory A_POLICY
input.  The request wire `authorization-context`, BPA BID, source EID,
destination EID, lifetime, NNTP `From`, and `Message-ID` do not authorize the
operation.

`source_eid` records the adapter's observed transport source; it is required
explicitly rather than fabricated by the receiver. It is provenance, not an
authentication result. The Store must already be initialized.

## Identity and expiry precede staging

Before anything is written, the host hands the raw bundle octets to
`fn-bpi-host-bundle-report` (`host/bp-ingress-host.lisp`).  ACL2 checks the
RFC 9171 §4.1 indefinite-array head, decodes exactly one CBOR item with the
certified profile decoder, runs `fn-bpp-decode` over those octets -- which
re-encodes them and refuses any non-canonical spelling -- and answers with
`fn-bpp-primary-identity` and `fn-clock-expiry-decision`.  Python performs no
part of this: not the frame check, not the field extraction, not the DTN epoch
or millisecond conversion, and not the expiry comparison.  The host supplies
`time.monotonic_ns()`, `time.time_ns()` and one configured error bound, and
ACL2 builds the `fn-clock-observationp` from them.

Four outcomes leave the BPA bundle exactly where it was -- staged nowhere,
deleted nowhere -- and stay distinct from each other and from a refusal to
accept something already staged:

| Outcome | Meaning | CLI exit |
| --- | --- | --- |
| `refused-identity:<reason>` | `:not-a-bundle`, a codec reason (`:malformed`, `:crc-mismatch`, `:noncanonical`, ...) or `:anonymous` (a `dtn:none` source, RFC 9171 §4.2.3) | refused |
| `refused-expired` | every admissible true time puts the bundle past its lifetime | refused |
| `uncertain-expiry` | the admissible interval straddles the lifetime, the host claims no wall reading, or the creation timestamp is zero (§4.2.6 "unknown") | uncertain |
| accepted path | `:live`; staging proceeds | ok |

`:uncertain` is an operator fence, never a deletion and never an acceptance.

## What the BID is now, and what it is not

The inbox file name and the duplicate check are the SHA-256 of the canonical
identity encoding.  The BID is retained as the transport handle and nothing
else: it is what `/download?` and `/delete?` are called with, and it is stored
in the FNBI frame beside the identity so that a pending delete can be finished
after a restart.  A redelivery of one bundle under a fresh BID therefore lands
on the same staged frame and reconciles; the stored frame keeps whichever BID
first carried it, and a differing BID is not a conflict.  Two bundles with
identical payloads and different identities are two staged requests.

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

`tests/test_bp_receive_process_crash.py` exercises five actual process deaths:
after durable FNBI staging, after Store acceptance before receiver context,
after context before intent, after intent before decision, and after decision
before BPA deletion. A parent readiness pipe selects the cut, then SIGKILL
terminates the dedicated receiver/ACL2 process group. Fresh recovery checks
exact staged and article bytes, record/article/pin counts, explicit pending
decision recovery and receipt equality before/after death or duplicate delivery.
These are additional process/cache-retention tests, distinct from exception
injection and from physical power-loss qualification.

This is an experimental trusted-loopback lab path.  It performs no
cryptographic verification, does not infer an authenticated author from BP or
NNTP fields, does not transmit the returned receipt, and does not establish
BPA, filesystem, or physical media guarantees beyond its explicitly modeled
and host-boundary operations.

The [composition assurance record](../tests/evidence/2026-09-18-bp-composition-assurance.md)
contains the five process-death cuts and combined 133-test result. The
[receiver proofs](bp-receiver-proofs.md) establish general logical replay and
receipt preservation against the Store as it evolves under ingress and
restart (`fn-bpr-live-receipt-regenerated-after-restart` is the byte-identical
receipt after restart as a theorem, with A-DURABILITY as `fn-sf-crash-imagep`);
they do not certify this adapter's physical I/O or BPA calls.
