# Experimental consumer position, version 1

Status: **selected experiment contract, unimplemented**, 2026-09-23. This
specifies E2 of [the sleeping-agent exchange](../planning/experiments/e1-e2-agent-exchange.md).
It is an fn design guarantee, not an NNTP or BP requirement and not a v0 release
gate. The selected E1 payload remains opaque to fn. The executable traces to
build against this contract are in
[`e1-e2-v1-traces.json`](../planning/experiments/e1-e2-v1-traces.json).

## Identity and version boundary

The logical v1 cursor scope is `(history-id, incarnation-id, consumer-id,
registration-epoch, principal-id, query-id, query-version, view-version,
position)`. `history-id`
is a durable identity minted when the Store is initialized; `incarnation-id`
changes whenever a copy, restore, or replacement could produce another writable
future from the same history. An ordinary process crash and replay of the one
authoritative history retain both IDs. A restore that cannot establish the
same committed prefix and its sequence mapping gets a new incarnation. An
ordinary checkpoint/compaction may retain the IDs only with an explicit
mapping from every live cursor position to the same committed prefix; otherwise
it also requires rebasing under a new incarnation. An endpoint address, TLS
certificate, BP EID, Message-ID, local article number,
wall clock or injection/acceptance stamp is none of these IDs. In particular,
an acceptance stamp can repeat or regress and cannot order a consumer scan.

`position` is the committed Store-record prefix scanned, not a per-group
number or the largest item returned. A valid position is at most the pinned
committed frontier. The v1 query selects a configured finite set of groups;
the ACL2 decision tests article membership and the caller's effective read
authorization at the pinned view. `query-version` changes with selection
semantics or group-set configuration. `view-version` changes whenever the
effective authorization or article visibility for the principal and query
could change, including a newly visible old article. If the implementation
cannot prove that a change preserves visibility, it changes the view version.
These versions are durable identifiers, not process-local counters.

The first trusted-peer, public-group profile uses a bounded versioned cursor
encoding. A future ACL2 decoder owns its field grammar, version check and
scope comparison; the authenticated caller is bound to the principal and
consumer entry before poll or ack. A cursor from another store, incarnation,
consumer, registration epoch, principal, query or view is refused before any
ack mutation. An unknown version is refused without guessing its meaning.
The cursor need not be secret in this profile: its position may reveal a
record-count bound, so this profile makes no cursor-metadata privacy claim.
The page and errors still disclose no denied article source or identity.
A later sealed-token profile could hide cursor fields and authenticate the
encoding, with a selected primitive and key lifecycle stated as separate
assumptions. No such cryptographic primitive is selected or required for v1.
The exact first wire encoding remains to be fixed before a served interface.

## Operations and their meanings

All requests have bounded lengths and an authenticated caller. `register`
binds a consumer ID, principal and query under the current view, and durably
sets its recorded position to zero with a fresh `registration-epoch`. The
epoch comes from a durable, never-reused Store allocation, not a wall clock;
exhaustion refuses registration. A duplicate registration with identical
scope returns the existing position; changing scope requires `rebase`.
`poll(cursor, limits)` pins one committed frontier, scans **at most** the
requested scan limit after the cursor position, and returns the visible
articles in commit order, a continuation cursor for the complete scanned
prefix, and `more` if that prefix does not reach the pinned frontier. Empty
pages still advance across holes, nonarticle events and filtered entries.
The page carries each selected article's exact stored source identity,
Message-ID, local membership and historical verdict reference separately.
It does not assert application verification or processing. A page is a read;
its return does not mutate the recorded ack.

This interface creates no article retention pin. A committed article that was
visible but has been reclaimed before polling is an explicit `unavailable`
gap at its record position: poll stops there and does not issue a continuation
past it. A consumer cannot claim at-least-once delivery of content that its
retention policy did not keep; recovery or an explicit application-level waiver
must resolve the gap. Nonarticle records and articles excluded by the pinned
query/view are ordinary scanned entries, not unavailable content.

`ack(cursor)` durably records only a consumer's declaration that its own
transaction finished through the cursor's scanned prefix. It requires the
current bound scope, including the registration epoch, and a position no lower
than the recorded one. Equal positions are idempotent. A lower position is
refused without rewind; a position beyond the committed frontier is refused.
`position(consumer-id)`
returns the durable recorded scope/position for recovery after an uncertain
ack. A valid poll token is not itself evidence of processing. `rebase` is an
explicit durable operation under a new query or view version: it resets the
recorded position to zero in the new scope so newly visible old articles can
be offered. It must not silently reinterpret an old token. `unregister`
durably removes the table entry; it does not erase the consumer's own inbox.
After unregister, reusing the same consumer ID allocates a new epoch; a delayed
ack from the prior registration is refused even if query and view match.
These operations do not pin articles for retention. Their outcomes are
`accepted`, `refused`, or `uncertain`; a write/commit ambiguity is `uncertain`
and fences further mutation until recovery, never a refusal guessed from a
lost reply.

The first policy budget is at most 16 configured groups, 128 Store records
scanned per poll, 32 articles returned, 262144 returned article octets, 512
token octets and 256 registered consumers. These are **proposed v1 policy
limits**, subject to a measured host budget before deployment. A requested
limit over policy is refused. A page stops before violating any independent
scan, item or byte bound; it still carries the cursor for the prefix actually
scanned. Oversize single articles are not silently skipped: the poll reports a
bounded refusal at that position, leaving progress unchanged, until an
explicit large-object retrieval contract exists. Register/rebase/ack metadata
is charged before the durable promise. A full table refuses registration;
there is no implicit expiry or unlimited unread backlog. Only explicit
unregister frees a slot in v1.

## Consumer transaction and recovery

The consumer's own database atomically stores a provenance inbox record keyed
by `(history-id, incarnation-id, source-identity, application-id,
operation-id)` **and** checks a unique application-operation index keyed by
`(application-id, operation-id)` in the same transaction. A new operation
applies one deterministic local transition and appends immutable reply Q to
the durable outbox. The same operation and source reuse the prior verdict and
Q. The same operation with different source is retained as conflict evidence
in the inbox, while the unique operation index prevents a second transition
or reply. A source-inclusive inbox key alone cannot enforce this rule. Only
after this transaction commits does the consumer call `ack`. An uncertain
consumer commit is settled by querying the inbox/outbox; an uncertain fn ack
is settled by `position`. If the ack
committed before Q was posted, the outbox still drives posting. Q keeps the
same authored source and Message-ID on retry; an uncertain post is settled by
identity lookup and exact-source comparison. An fn ack does not mean dregg
verified a receipt, an external effect happened, or an fn retention obligation
was released. Two consumers have separate positions and inboxes.

A restored store with a new incarnation causes `wrong-store` /
`rebase-required` for the old cursor even at the same endpoint and with
repeated local numbers. The consumer then explicitly registers/rebases under
the new scope and scans from its beginning, using its own application keys to
decide what to reuse. A view change similarly requires a scan from zero.
Whether the consumer regards an identical source reimported in a new store
incarnation as the same application operation is its own policy; the five-part
inbox key preserves provenance while the separate operation index makes the
deduplication/conflict choice atomic.

## Executable seam and obligations

This is not served by today's owner. The native read at
`host/native/owner.lisp:1041` calls `fn-owner-chunk` at
`host/owner-host.lisp:1051`, whose owner read enters `fn-served-step` at
`books/owner.lisp:971`, then `fn-auth-step`/`fn-nntp-step` over a pinned
archive. The publication helper is `fnn-owner-publish-prepared` at
`host/native/owner.lisp:667`; `fn-own-complete` reaches `fn-sn-finish` at
`books/owner.lisp:1114`. `books/owner.lisp` has a committed view/frontier and
`books/store-node.lisp` has Store prepare/finish/reopen, but neither holds a
store-history identity, consumer table, query decision or ack event.
`tools/fn_client.py` advances a host/port-and-group watermark after output;
that is not a consumer transaction. NEWNEWS and acceptance stamps cannot
substitute for this prefix scan.

Implementation must first add durable history/incarnation identity and the
bounded consumer-entry event to Store's record/replay/compaction/restore path,
including refusal, ambiguous publication, and every process-death cut. Then
add ACL2 query/poll/token-field/ack/rebase decisions over the actual committed
projection, with preservation and scope theorems and non-degenerate teeth.
The host-called served owner step must be the theorem subject, or have a named
equivalence to the inner decision. Only then may the native host carry bounded
bytes, invoke the selected seal/open primitive, and publish the Store event.
The consumer library owns its own crash-safe transaction and dregg verifier.
The trace file names the required two-database observations; passing article
arrival or a printed watermark cannot satisfy them.
