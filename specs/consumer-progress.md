# Experimental consumer position, version 1

Status: **selected experiment contract; ACL2 decision kernel and phase-aware
Store model certified in scope, local owner command source pending native image
qualification, no article fetch/poll**, 2026-09-23. This
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

The first trusted-peer, public-group profile uses `books/consumer-position.lisp`
cursor bytes: `fncu` (four octets), version 1 (one octet), five nonempty
length-prefixed octet IDs (history, incarnation, consumer, principal, query;
one through 64 octets each), then four big-endian unsigned 32-bit integers
(query version, view version, registration epoch, scanned position). The
maximum encoding is 346 octets under the 512-octet decoder preflight. The
ACL2 decoder owns field grammar, version check and scope comparison; the
authenticated caller is bound to the principal and
consumer entry before poll or ack. A cursor from another store, incarnation,
consumer, registration epoch, principal, query or view is refused before any
ack mutation. An unknown version is refused without guessing its meaning.
The cursor need not be secret in this profile: its position may reveal a
record-count bound, so this profile makes no cursor-metadata privacy claim.
The page and errors still disclose no denied article source or identity.
A later sealed-token profile could hide cursor fields and authenticate the
encoding, with a selected primitive and key lifecycle stated as separate
assumptions. No such cryptographic primitive is selected or required for v1.
The kernel fixes this candidate v1 encoding. Its eventual served command
framing and authenticated transport binding remain to be specified.

## Operations and their meanings

All requests have bounded lengths and an authenticated caller. `register`
binds a consumer ID, principal and query under the current view, and durably
sets its recorded position to zero with a fresh `registration-epoch`. The
epoch must come from a durable, never-reused Store allocation, not a wall clock;
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
is charged before the durable promise. Each event consumes one place in the
persisted Store transaction-count profile and its kind-specific ACL2 byte
ceiling is checked before reservation; the 256-entry table limit alone does
not bound repeated ack history. A full table or exhausted Store profile
refuses registration or publication, respectively;
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

The full E2 poll/fetch interface is not served by today's owner. The native read at
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

The executable `fn-cp-register`, `fn-cp-ack`, `fn-cp-rebase` and
`fn-cp-unregister` return `:write` proposals, `:no-op` for an idempotent
durable state already known, or `:refused`. `fn-cp-apply` models the projection
of a *committed* proposal; neither a proposal nor this in-memory application
means Store acceptance. The kernel checks current scope, monotone ack,
frontier, capacity and a scalar registration epoch without revalidating an
entire Store on each request. `qver` and `view` must be computed by an ACL2
owner policy projection, not accepted from client bytes. The poll/query
selection and this policy projection are still unimplemented.

The candidate v1 Store event envelope is the distinct `fnce` magic, version
one, operation-kind octet, three unsigned 32-bit fields for dense Store
journal sequence, allocator txid and generation, then an exact bounded
operation. The six kinds are bootstrap, register, ack, rebase, unregister and
incarnation rollover. The longest valid event is a 364-octet ack, under a
512-octet decoder preflight. A bootstrap commits ACL2-validated history and
incarnation IDs before any consumer registration. Host-supplied entropy is an
observation, not an endpoint, wall-clock or configuration-generation
derivation. A duplicate bootstrap in one Store history is refused. A normal
crash replay retains both IDs. Writable restore or clone must durably commit
an explicit new-incarnation transition before consumer service. The native
source now has a cold `checkpoint clone` and fenced `checkpoint clone-resume`
path: it copies exact Store bytes under an exclusive source lock, installs a
durable canonical rollover-event fence before exposing the destination, and
refuses ordinary opens until owner publication and an independent reopen
confirm the new incarnation. Production clone observes 32 new octets from
the OS CSPRNG and ACL2 rejects equality with the current incarnation or
history ID. Sibling uniqueness is probabilistic under the OS entropy trust
boundary, not a theorem of globally unique IDs. A same-ID or malformed proposal is refused
without publication; an occupied destination is untouched; uncertain
completion leaves the copied target fenced. This
source path awaits a combined saved-image witness and a served cursor test;
arbitrary filesystem copying is not a supported writable clone. The
selected exact-prefix pack retains every original event byte and reconstructs
the entire dense Store stream before open; its prefix reclaim may preserve
cursor positions only while this exact expansion remains the recovery path.
The separate node-checkpoint snapshot does not yet carry the consumer
projection and must not be used as consumer recovery authority. A future
checkpoint that retains only a logical summary must preserve the original
dense Store sequence base, consumer projection and replay offset; counting
only retained physical records would make a previously issued position mean
something else.

The `fnce` codec and Store event union/sequence/txid routing are in
`books/consumer-store-events.lisp` and `books/store-events.lisp`. The
acceptance-neutral `fn-replay-apply-record` arm advances the shared txid.
`books/consumer-store-projection.lisp` interprets that same committed Store
stream. The Store model stages through `fn-sn-prepare-consumer`, installs
the projection only at durable `fn-sn-finish`, reconstructs it at crash
recovery and observed reopen, and carries it beside physical configuration
history. `fn-csi-store-step-preserves-full-relation` covers the actual decoded
`fn-snrt-step` transition under a maintained phase-aware relation; its
`fn-snrt-run` induction covers arbitrary finite logical mixed traces, including
linked unfinished candidates, crash and recovery. The scoped ACL2 book/test
certification is recorded in
`planning/evidence/manifests/certify-20260923T210725Z-145187.json`.
That model proof does not establish native filesystem crash refinement or an
authenticated consumer caller. The global next epoch, entries and ack
positions must also survive checkpoint and compaction;
prechange checkpoint images need a versioned migration rule. The native
consumer record belongs to the existing dense Store journal sequence and
allocator txid stream, not to a second consumer log. Config records retain
their independent dense config sequence and stamp the next-unconsumed Store
txid. On a tie, config precedes the consumer event; multiple configs at that
txid retain config-generation order. Burned Store txids remain possible.
The logical consumer event order, recovery replay order and physical record
comparison must use this same relation. A scalar next epoch must be committed
with each register/rebase event: uncertain publication cannot reuse an epoch
until reopen has settled whether that event is in the durable prefix.
The native
publication path must exercise refusal and ambiguity around its
`record-linked`, `record-attempted`, `record-durable`, `record-completing`,
`record-staging-cleaned`, `finish-consumed` and `finish-durable` process-death
cuts, plus recovery cuts. The first local owner command source now runs through
`fn-owner-consumer-local-{bootstrap,register,ack,position,poll,unregister}` in
`host/owner-host.lisp`, which calls `fn-col-*` over the live owner. The
`FNCT` kind-4/5 codec and CLI plan in `books/consumer-local-control.lisp`
carry bounded request/reply bytes over the existing mode-0600 Unix control
socket. The host observes the connected peer's UID with Darwin `getpeereid`
or Linux `SO_PEERCRED` after `getpeername`, refuses a failed observation or
owner-UID mismatch, then pins the ACL2 local principal. Other ports refuse
this profile until they supply an equivalent peer-credential observation. The native
handler serializes each command with the owner, publishes
the exact ACL2 event through `fnn-owner-consumer-commit` and the shared
`fnn-owner-publish-prepared` gate, and returns a cursor only after durable
completion. `consumer bootstrap CONTROL` reads two 32-octet OS entropy
observations; ACL2 validates them, constructs the initial history/incarnation
event, and refuses a duplicate or equal identity. The source of entropy and
its uniqueness are host trust assumptions, not ACL2 theorems. A lost
post-submission reply is uncertain and `position` recovers
the recorded declaration. This source route still needs a combined saved
image and process-death test before it can be claimed served.

The local `consumer poll CONTROL ID CURSOR_OUT REPORT_OUT` source selector
examines at most 16 consecutive committed Store events and stops at the first
article in the registered historical group query. It returns an exact fncu
cursor at the scanned prefix and either empty report bytes or one exact
ACL2-encoded `fn-r` legacy article / `fn-e` accepted-article event. The
schema-1 composite event includes the received article, separate bound exact
authored source and identity, and historical verdict; legacy events retain
their explicit version and make no source-authorship claim. The FNCT kind-6
reply has a separate 196,963-octet payload ceiling, within the 4,194,304-octet
underlying frame payload ceiling; ordinary control requests retain their smaller cap.
Its cursor and report lengths are checked independently. Poll leaves the
durable consumer position unchanged; only a subsequent `ack` writes progress.
The current list-backed selector copies a 16-event window after a positional
walk of at most the configured Store transaction limit, so its pessimistic
work is that limit plus 16 event steps per poll, not constant-time lookup.
The native saved-image positive fetch/advancing-ack and Mini inbox/outbox join
remain separate evidence obligations.

That **local-owner profile** pins one OS owner principal inside ACL2; its
query is exact historical membership in one group that is configured at
registration, with fixed query version 1 and view version 0. The same local
owner can inspect its historical membership even if the active group table
later changes. This does not grant remote peers read authority and does not
implement the selected public-group poll. A remote profile must pin its
authenticated principal and effective visibility version from the current
ACL2 policy, and prove its fetched article window matches the committed Store
prefix. No seal/open primitive is required by this first trusted local profile.
The consumer library owns its own crash-safe transaction and dregg verifier.
The trace file names the required two-database observations; passing article
arrival or a printed watermark cannot satisfy them.

CNS-001: fn's selected v1 experiment requires a Store-scoped, versioned
consumer position whose registration epoch and acknowledgement are committed
in the ordinary Store history. A bounded poll may advance only over a pinned
committed prefix, and an acknowledgement declares consumer-owned processing
without asserting it. Crash/reopen must reconstruct the same position, while
an incarnation or view change fences the old cursor. The consumer must atomically
bind source-inclusive inbox evidence, a separate unique application operation
index, and a reply outbox before acknowledging. The logical Store model and
cursor decision kernel are implemented; local owner command source awaits a
qualified saved image, and poll/fetch, consumer database and the two-store
trace remain to be executed.
