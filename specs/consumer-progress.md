# Experimental consumer position, version 1

Status: **selected experiment contract; ACL2 decision, durable Store projection,
and bounded local-owner poll implemented; native signed poll, advancing ACK
with reply loss/reopen and fenced clone recovery passed in the scoped
`1d26e01f` campaign**, 2026-09-23. A source-ready `consumer status` diagnostic
is an experimental v1 addition and is not a v0 gate. This
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
committed frontier. The selected general v1 query selects a configured finite
set of groups; its ACL2 decision must test article membership and the caller's
effective read authorization at the pinned view. The implemented local-owner
profile selects exact historical membership in one registered group under a
fixed owner principal, query version 1 and view version 0. `query-version`
changes with selection semantics or group-set configuration. `view-version`
changes whenever the effective authorization or article visibility for the
principal and query
could change, including a newly visible old article. If the implementation
cannot prove that a change preserves visibility, it changes the view version.
These versions are durable identifiers, not process-local counters.

The v1 cursor in `books/consumer-position.lisp` uses `fncu` (four octets),
version 1 (one octet), five nonempty
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
The kernel fixes this v1 encoding. The local-owner `FNCT` kind-4/5 request and
reply and kind-6 poll-reply framing are implemented over a mode-0600 Unix
control socket with observed same-UID peer credentials. Remote authenticated
framing and policy binding remain to be specified.

## Operations and their meanings

The multi-item poll and unavailable-gap rules below are the selected general
v1 contract. The implemented local-owner command is narrower: it takes a
consumer ID and starts at that consumer's durable ack position, scans at most
16 events, selects at most one article from one registered group, and returns
that exact stored event rather than a multi-item page. Its native
qualification is stated in the executable seam below.

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

This interface creates no article retention pin (the selected
no-implicit-pin profile; [storage](storage.md)'s lifetimes table says the
same, and a retaining consumer mode would be a separately charged durable
hold, not a reading of this position). A committed article that was
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

The selected remote, multi-item E2 poll/fetch interface is not served. The
implemented local-owner route is distinct from NNTP: the native control
handler in `host/native/owner.lisp` calls
`fn-owner-consumer-local-{bootstrap,register,ack,position,poll,unregister}`
in `host/owner-host.lisp`, which calls the ACL2 `fn-col-*` decisions in
`books/consumer-owner-local.lisp`. `fn-sn-consumer` in
`books/store-node.lisp` carries the durable history/incarnation, registration
table, epoch allocator and ack positions. Consumer write proposals pass
through `fn-sn-prepare-consumer`, the ordinary publication barrier and
`fn-sn-finish`; recovery reconstructs the projection from the committed Store
stream. `fn-col-poll` is read-only over that committed event prefix. It reads a
derived sequence index in Store slot 13, rebuilt from the exact committed
event list on observed reopen; this index is not separate durable authority.
An NNTP watermark, NEWNEWS result or acceptance stamp cannot substitute for this
consumer position or its declaration of processing.

The executable `fn-cp-register`, `fn-cp-ack`, `fn-cp-rebase` and
`fn-cp-unregister` return `:write` proposals, `:no-op` for an idempotent
durable state already known, or `:refused`. `fn-cp-apply` models the projection
of a *committed* proposal; neither a proposal nor this in-memory application
means Store acceptance. The kernel checks current scope, monotone ack,
frontier, capacity and a scalar registration epoch without revalidating an
entire Store on each request. The local-owner ACL2 wrapper fixes the
authenticated owner principal, query version 1 and view version 0; register
checks one configured group and poll selects exact historical membership in
that group. Client bytes cannot choose principal, `qver` or `view`. The
general remote multi-group selection and effective visibility-version
projection remain unimplemented. `fn-cp-rebase` and its Store event are
modelled, but no local `rebase` command or remote view-change workflow is
served.

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
boundary, not a theorem of globally unique IDs. Clone paths and their
canonical aliases are bounded by the ACL2 512-octet native Store path policy.
A same-ID or malformed proposal is refused without publication; an occupied
destination is untouched. Uncertainty before durable rollover confirmation
leaves the copied target fenced. If fence removal fails after the independent
reopen confirmed the durable rollover, the command still reports uncertainty
but an already-unlinked fence can permit safe ordinary opens. The original
`bc9be7ec` saved image passed independent canonical-path refusal and
historical authored-verdict clone/reopen tests, as recorded in
[the frozen image evidence](../planning/evidence/native-reader-clone-bc9-2026-09-23.md).
The subsequent `1d26e01f` image passed advancing-ack selected-pack and
fenced-clone process-death/cursor checks; [its exact scope](../planning/evidence/native-poll-reader-clone-1d26-2026-09-23.md)
does not establish arbitrary physical power-loss safety. Arbitrary filesystem copying
is not a supported writable clone. The
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
`FNCT` kind-4 request, kind-5 cursor reply, kind-6 poll reply and kind-9 status
reply codec plus CLI plan in `books/consumer-local-control.lisp`
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
the recorded declaration. An earlier production image passed bootstrap,
register, position, equal-position ack, epoch refusal, independent Store
scope refusal, replay, and a killed-owner-after-durable-register case;
[its exact scope](../planning/evidence/native-e2-bp-4f66-2026-09-23.md)
does not include poll or advancing ack. The `1d26e01f` campaign subsequently passed signed poll, advancing ACK with
a killed reply, and recovered position; the broader two-store application
transaction crash trace remains open.

The experimental local-owner `consumer status CONTROL ID` diagnostic uses the
same local principal, query version, view version and registered consumer entry
as `position` and `poll`. It returns the committed ACK position, the committed
journal frontier and their difference in Store journal events. That difference
does not count unread or matching articles and says nothing about application
work. ACL2 validates the scope and computes the subtraction; the native
command only prints those fixed fields. Status performs a bounded registration
table lookup and reads fixed fields. It does not poll, write an ACK or journal
event, or scan retained history. This is an experimental v1 diagnostic and
does not change the v0 release gate.
Its fixed status reply payload is at most 13 octets. FNCT kinds 7 and 8 belong
to the local topic-control packet.

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
The `consumer-project` exact-file reader uses the ACL2 cursor and event
ceilings (346 and 196,608 octets). A file beyond either ceiling is a bounded
`:limit` refusal of that CLI request; malformed files within the ceilings
reach the ACL2 projector's codec refusal. Neither result advances an ack.
The called `fn-col-poll` reads at most 16 consecutive events by sequence from
the carried four-octet radix index, then runs the ACL2 article selector over
that window. It does not walk the acknowledged prefix for each poll. The
index is maintained when the committed Store directory grows and rebuilt
from the exact event list on recovery; that rebuild scans retained history,
and the index retains event references proportional to retained history.
The ACL2 correspondence proof equates the called indexed poll with a
proof-only list selector when the carried index and Store relations hold in
a serving phase. It derives the file-state and uint32 record-count conditions
from the maintained Store relation. Its stale-index and fault-phase negative
witnesses pass; independent structural-relation teeth and a source-matched
native poll cost measurement are still open. The original
`bc9be7ec` image's signed poll attempt failed before submission because the
CLI supplied the cursor output path as an extra ACL2 request argument,
as recorded in [the original failure](../planning/evidence/native-e2-poll-bc9-original.md).
The repaired `1d26e01f` image passed signed poll and advancing-ack recovery,
as recorded in [the native campaign](../planning/evidence/native-poll-reader-clone-1d26-2026-09-23.md).
The Mini durable inbox/outbox-to-ACK join remains an open evidence obligation.

The local profile's page contract is proved over the selector the host calls
(`fn-col-poll-scan-page-contract`, books/consumer-owner-local-progress,
PRF-116): the continuation lies between the recorded position and the
smaller of the pinned frontier and position plus the scan bound; an empty
page scanned only non-matching events and, when anything was scannable,
progressed past at least one; a nonempty page is the first matching event of
its window, just before the continuation. So a continuation never passes a
matching event that the page did not return. `fn-col-poll` answers a page or a
refusal, never a Store write proposal, and `fn-cp-ack`, which `fn-col-ack` calls, writes only the declared
cursor, forward, within the frontier and the recorded scope; an equal
position is a no-op and, after the committed ack, the same ack is a no-op.
The local profile has no reachable unavailable case: no native caller
reclaims article content (only the exact-prefix pack reclaims transaction
files, and it keeps every event byte), so the unavailable-gap rule above is
the general contract, unexercised here. The scan bound (16) and item bound
(one event) are in that theorem; the reply byte ceiling and the 346-octet
cursor are codec ceilings, not proved independent of the scan. A single
article larger than the poll reply ceiling has no retrieval contract yet.

CNS-002: two consumers with independent durable state exchange a signed
report and a reply through one fn node, each running the consumer
transaction above and acknowledging only after it commits. Each uncertain
fact at an ownership boundary is settled by its owner: an uncertain consumer
transaction by the consumer's database, an uncertain `ack` by `position`, an
uncertain reply POST by the identical source's resend or by fn serving that
exact source back through `poll`, never by an fn acknowledgement. The same
operation with a changed source is conflict evidence with no second
transition or reply. `tools/fn_consumer.py` is the external consumer and
`tests/test_native_consumer_exchange.py` the native scenario (SCN-061).
Today an identical signed resend over the local control route is answered
`refused`, not D25's duplicate, so the consumer settles such a POST by the
served exact source ([evidence](../planning/evidence/consumer-e2-2026-09-25.md)).

The read-only `consumer-project CURSOR.fncu ACCEPTED.fn-e` command calls
`fn-cpj-project` to check a supplied v1 cursor against a schema-1 accepted
event, its bound article and historical verified verdict. The current ACL2
projection has a [verified guard and scoped witness](../planning/evidence/mini-e2-consumer-project-2026-09-23.md),
but supplied files alone do not prove that a particular authenticated Store
poll returned them. It does not perform Mini's source verification or durable
inbox/outbox transaction. The `1d26e01f` native command projected the exact
event and cursor exported by the signed poll campaign.

The offline `fn consumer-inspect CURSOR.fncu` command reads a regular file
through the ACL2-owned 346-octet maximum encoding bound, then calls
`fn-cp-cursor-decode` and prints the exact five IDs as lowercase hex and the
query version, view version, registration epoch and position as decimal
fields in a `fn-consumer-inspect-v1` line. Malformed, truncated or trailing
input is refused by the decoder; overbound input is refused before decoding.
This is syntactic cursor inspection only. The token contents do not
authenticate an fn Store, prove that the cursor was accepted, establish that
the displayed epoch is current, or prove that any consumer processed an
article. IDs are printed as hex so arbitrary octets cannot inject terminal
control characters.

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
index, and a reply outbox before acknowledging. The logical Store model,
cursor decision kernel, durable local declarations and bounded one-group poll
source are implemented. Prior native declaration and independent clone checks
passed in their stated scopes, followed by native signed poll, advancing
ACK/reopen and fenced-clone cursor checks on `1d26e01f`. General authenticated
multi-group selection and the two-store trace remain open; the one-node
two-consumer transaction/ACK join is CNS-002.
