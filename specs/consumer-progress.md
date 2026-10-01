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
control socket with observed same-UID peer credentials. The separate FNCR request grammar is implemented as a logical component
(see authenticated remote consumers below); authenticated policy binding and
the remote served endpoint remain unimplemented.

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
scanned. Oversize single articles are not silently skipped: the poll answers
the named refusal `:oversize` at that position (`fn-col-poll-report`,
PRF-177), leaving progress unchanged, until an explicit skip or large-object
retrieval contract exists (PKT-466). Register/rebase/ack metadata
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

## Submission attempts and the saved artifact

A consumer's reply (or report) crosses fn's native boundary as a
submission, and a crash can separate fn's acceptance from the consumer's
record of it. The consumer therefore keeps three kinds of record, never one
mutable outbox row (gpt-6's review of wave 2, section 2):

- the **submission artifact**, immutable once committed: the authored
  source, both signatures, the author's principal, Ed25519 key, ML-DSA-65
  key and keyring generation, and the original context. A retry sends
  exactly these bytes under this key context; a later key-file or
  configuration change cannot alter it. Current permission is fn's to
  decide at each attempt and is recorded on that attempt; it never edits
  the artifact.
- **attempts**, each committed as in flight *before* the native boundary is
  crossed and answered afterwards in its own transaction. An attempt still
  in flight when a consumer process opens its database is unanswered:
  potentially successful, whether or not the dead process reached the
  socket.
- **observations** that the operation is stored: fn's answer to an attempt
  (accepted, or D25's duplicate) or fn's Store serving the exact artifact
  back through `poll` (the same authored source and the same two
  signatures, checked by the consumer itself).

The operation's state is derived: stored once any observation exists;
pending with no attempt; refused only when every attempt has a durable
refusal; otherwise uncertain. A later refusal settles the attempt it
answers and never an earlier attempt without a durable answer. An
uncertain submission is reconciled, not retried blindly: the saved
artifact is resent once per open attempt (D25 answers the same carrier
"already stored here", fn-sr-a-signed-retry-is-already-stored; NNT-019's
contract), and if that resend is refused the submission stays uncertain
until fn's Store serves the artifact back. Nothing is re-signed:
randomized ML-DSA-65 signing gives new signatures, and so a new carrier,
for an unchanged authored source, which D25 answers as a conflict
(fn-sr-a-re-signed-carrier-is-a-conflict, PRF-137). "Changed authored
source" is reserved for a changed message; a re-signed one has a changed
signature and carrier.

The consumer verifies every received report itself: the article fn's poll
served is checked by `tools/fn_verify.py check-article`, a separate process
importing nothing of fn's, against a keyring the consumer was given (never
fn's keyring), and the consumer's verdict is recorded beside fn's. A report
it cannot verify (unverified, an author it does not trust, or a principal
or authored source other than fn's projection) is kept as evidence and not
consumed: no operation, transition or reply; the cursor still progresses
over it. Who may claim an operation identity is the application's rule
(operation-id prefix to principal), not the signature's: a correctly signed
claim by another principal is conflict evidence in either arrival order and
does not occupy the identity.

| Cut | Consumer record after the cut | Settled by |
| --- | --- | --- |
| Death before the attempt is recorded | pending, no attempt | the next wake's first attempt |
| Death after the in-flight record, before sending | uncertain, one unanswered attempt | one resend of the saved artifact (a first acceptance) |
| fn committed, consumer killed before the answer arrived | uncertain, one unanswered attempt | one resend; if refused (e.g. revoked), fn's Store serving the artifact back |
| fn answered, consumer died before recording it | uncertain, one unanswered attempt | as above |
| Death inside the answer's transaction | rolled back: uncertain, one unanswered attempt | one resend (D25 duplicate) |
| fn's reply lost (exit 3) | uncertain, one answered-uncertain attempt | one resend (D25 duplicate) |
| A resend refused after an open attempt | uncertain; the refusal settles only that resend | fn's Store serving the artifact back |

CNS-003: a consumer never records an operation refused while one of its
submission attempts lacks a durable answer; it persists each attempt before
crossing the native boundary, resends only the immutable saved artifact
(source, both signatures and the author's key context), settles an
uncertain submission by D25's answer to that artifact or by fn's Store
serving it back, and consumes a received report only after verifying its
signatures itself with its own trusted keys and the application's rule for
who may claim that operation identity.
`tools/fn_consumer.py` is the client, `tests/test_native_consumer_exchange.py`
the native scenario (SCN-080) and `tests/test_fn_consumer_journal.py` the
stand-in journal test; the fn side it relies on is PRF-137
([evidence](../planning/evidence/consumer-e2-2-2026-09-26.md)).
One consumer process per database is enforced by the client, not stated:
`fn_consumer.py` holds an exclusive `flock` on `<db>.lock` from before it
opens the database until it exits, and a second process is refused (exit 1,
`database in use by pid N`) before it reads anything, so the in-flight
attempts a process finds on opening belong to a dead process (PKT-351).
The lock, the resend and the correlation are the client's own bookkeeping
under this contract; fn decides none of them.

## Two nodes

The exchange also runs across two fn nodes peered over NNTP. Agent A's
consumer talks only to node A's control socket and agent B's only to node
B's; neither consumer talks to the other node. A authors R into A's Store
(`hybrid-author`); A's outbound feed carries R to B, and B may also receive
it by its NEWNEWS pull (specs/peering.md, NNT-018); B's Store accepts R as a
kind-4 event with B's own verdict under B's enrolment of A's author; B's
consumer polls B, verifies R with its own keyring, commits its one
transition and immutable reply Q, and acknowledges its position on B; Q
crosses back by B's feed; A's consumer polls A, verifies Q with its own
keyring and correlates it with R.

Each hop keeps separate identities: the application operation
(application-id, operation-id), the authored source (its digest), the
signature carrier (the two signatures), and the hop-local stored projection
(the received article, which carries that node's `Path`). The authored
source and both signatures are the submission artifact's at every hop; the
stored projections may differ. A repeated transfer (the feed and a pull of
the same Message-ID, or a later offer) is one Store event at the receiving
node: the later arrival is answered duplicate (435 to an offer; the pull
does not fetch an article its Store holds), so the consumer sees one event
and performs one transition; its `repeat` disposition and the operations
key are the backstop for an operation served to it again (its own reply
served back). A node restart between a poll and its ack re-serves the same
page and cursor (poll is a read), and the ack is idempotent. A revoked
author's uncertain submission at its own node still settles only by that
node's Store serving the artifact back (PKT-322), while a node that received
the article before the revocation consumes it normally.

CNS-004: two consumers on two fn nodes peered over NNTP exchange a signed
report and a reply, each verifying what it receives with its own keyring and
acknowledging only its own node's position after its transaction commits;
the receiving node's stored event keeps the authored source and both
signatures of the carrier it received (PRF-177,
`fn-osp-authorized-event-keeps-the-carried-source-and-signatures`); a
repeated transfer, a lost reply, a consumer death at every ownership cut and
a node restart mid-poll produce no second application transition.
`tests/test_native_consumer_exchange_two_nodes.py` is the native scenario.
Its repeated-transfer witness records the actual complete NEWNEWS 230 answer
(including R's Message-ID), then asserts that B sends no ARTICLE command for
R after the feed has stored it. The pull is enabled only after B's STAT
confirms that first delivery; an issued NEWNEWS command alone is not evidence
that the response listed R (PKT-392).
(SCN-106) ([evidence](../planning/evidence/consumer-exchange-2026-09-26.md)).
The production variant (`tests/test_native_consumer_exchange_production.py`)
uses external process kills at the same six ownership boundaries. Application
cuts stop the consumer so the harness can SIGKILL it; the two owner cuts hold
an actual response in an external Unix relay, kill the owner and discard the
reply. Reopened ACK and article state must establish the durable outcome;
receipt of a response octet is only a cut trigger. The production owner runs
without a developer stop selector. Matching image observations remain separate
from this driver (PKT-466(b)).

Carriage over BP through the relay network is the separate CNS-010 contract
below (PKT-333 phase 2 / PKT-466(c)); CNS-004 remains the NNTP exchange.

## Bound consumers

`consumer show` is a read-only report of the current configuration's mark-6
consumer bindings, in row order. Each line is `consumer NAME account LOGIN`;
other account row kinds produce no line. The running owner and offline path
use the same renderer. Its plain FNLS request uses code 13, after the
evidence/query codes 8 through 12.

The local consumer runs over the owner's 0600 control socket as the one
local principal, so an unbound consumer reads every group: the operator's
power. The operator may bind a consumer to an account (decided by ember,
2026-09-27, PKT-642: the supported way to run an agent's consumer):

    fn operator CONFIG consumer bind NAME --account LOGIN
    fn operator CONFIG consumer unbind NAME
    fn operator CONFIG consumer show

A binding is a configuration record (`:consumer-bind`, delta code 24; a row
`(NAME LOGIN "" 6)` of the accounts slot), offline or live, and reaches the
consumer at its next request: every consumer request reads the latest
configuration. A bound consumer polls and acknowledges with
`fn consumer bound-poll CONTROL NAME SECRET-FILE CURSOR REPORT` and
`fn consumer bound-ack CONTROL CURSOR-FILE SECRET-FILE` (local-control
request codes 7 and 8), carrying the account's own password, read from a
file (one final line end is not part of it). There is no consumer-specific
secret: the password is checked against the credential AUTHINFO checks
(`auth.toml`'s credentials, then the redeemed accounts), so changing or
revoking the account's credential changes or revokes the consumer with it,
and nothing new needs issuing, storing or rotating.

CNS-006: a consumer bound to an account is served an event only while the
account's read rule (specs/nntp.md "Group access", NNT-046) admits the
consumer's query group, so every event it receives has an article with a
group the account reads; a request without the account's password, or a
plain `poll`/`ack` of a bound consumer, is refused; a refusal writes nothing
and keeps the position, so the events a bound consumer receives are the
unbound consumer's events in order, each delivered at least once and each
ack a forward declaration in scope whose repeat is a no-op; an unbound
consumer is served exactly as before.

ACL2 names each refusal (`:unbound`, `:credential`, `:access`, `:bound`,
`:unbootstrapped`, `:unknown-consumer`, `:scope`); the command line prints
it after the status (`consumer refused credential`) and exits 1. See
"Refusal reasons" below.
Why the rule refuses rather than skips: a consumer's query is one group
(`register NAME GROUP`), so under one configuration the rule admits all of
its events or none; skipping would move the position past events a later
rule may admit again, losing them silently. A refused consumer resumes where
it stopped when the rule admits the group again.

Not guarantees: the report is the event's exact Store encoding, so the
article's own header names every group it was posted to (as SEC-007 says of
NNTP). The socket stays the operator's: a process that can open it (the
owner's uid) can still register and poll unbound consumers, so a bound
consumer confines an agent that holds only its account's password, not a
process running as the operator; carrying bound requests to a non-owner
peer is PKT-673.
([evidence](../planning/evidence/consumer-identity-2026-09-27.md))

## Waiting

An agent's consumer should sleep until there is news for it, not poll on a
timer. A WAIT is a poll that may sleep first:

    fn consumer wait CONTROL NAME CURSOR REPORT --timeout S
    fn consumer bound-wait CONTROL NAME SECRET-FILE CURSOR REPORT --timeout S

(local-control request codes 9 and 10, a timeout of 0 to 3600 seconds; the
answer is the poll reply, kind 6, and the files are the poll's). The owner
polls the consumer exactly as `poll` / `bound-poll` would. If the answer is
an empty page and the deadline has not passed, the waiting thread sleeps on
the owner's commit signal, raised after every durable Store publication, for
at most the time left, and polls again; it never polls on a timer. The owner
answers the first poll that is not an empty page, or the empty page at the
deadline.

CNS-007: a wait's answer is the answer a poll of the same consumer gives at
the moment the wait returns: a refusal at once (a bound consumer outside its
account's rule is refused, not left asleep), an event the consumer can read
as soon as one is committed, and the empty page only when its timeout
passes; a wait writes nothing, so every guarantee of the poll (CNS-006, and
at-least-once delivery with one transition per repeated delivery, which is
the ack's) holds of it unchanged. At most 12 waits are admitted at once
(four fewer than the owner's 16 local-control workers, so other requests are
always served); one more is refused by name (`:waiters`, exit 1), never
queued.

Every waiter wakes at every commit and polls once (ACL2 decides what each
answers), so a commit costs at most 12 polls. An owner stop wakes every
waiter, whose next poll is refused. A wait holds its control connection for
up to its timeout; the client allows the timeout plus the ordinary ten
seconds for the reply. `tools/fn_agent.py` is a small agent client over
this: `next` (a bound wait, printed as one JSON line), `reply` (a follow-up
over NNTP as the consumer's account, with References) and `ack`
([fn FAQ, part 8](../docs/articles/fn-faq-8.txt)).
([evidence](../planning/evidence/agent-wait-2026-09-27.md))

## Refusal reasons and the JSON line

The consumer replies (FNCT kinds 5, 6 and 9) carry a status and no reason,
and a field appended to them would make an old client read a refusal as a
frame it cannot decode. The reason therefore travels as PKT-453's does
(specs/native-host.md, the reasoned reply): `fn consumer` sends every
command as the reasoned consumer request, FNCT kind 22, whose payload is the
kind-4 request's unchanged. The owner decides it exactly as the kind-4
request (`fn-ncr-request-decode-is-the-plain-decode`), answers an acceptance
with the consumer reply it always sent, and answers a refusal (or an
uncertain or failed end) with the reasoned reply, kind 18: the status and
ACL2's reason word. An owner that predates kind 22 answers the plain
refusal before acting on anything, and the client sends the kind-4 request
once more (`fn-native-control-reasoned-client-step`'s resend).

CNS-009: a consumer command's refusal names the reason the owner's decision
named, and the word the client prints is exactly that reason's
(`fn-ncr-printed-reason-is-the-decisions`); a bind of an unregistered
consumer name is refused by name; every consumer command can print one
ACL2-rendered JSON line.

The reasons: `unbootstrapped` (no consumer history yet; `register` then
bootstraps it and registers once more, and only for this reason or an old
owner's unnamed refusal, `fn-ncr-cli-after-retries-only-an-unbootstrapped-register`),
`unknown-consumer` (no consumer of that name), `no-such-group` and `query`
(register), `scope`, `unbound`, `credential`, `access`, `bound`, `waiters`,
`oversize`, `report` and `not-owner` (the socket's peer is not the node's
owner). `fn operator CONFIG consumer bind NAME --account LOGIN` of a name no
registration declared is refused `unknown-consumer`, live and offline
(`fn-col-bind-refusal-refuses-exactly-an-unregistered-bind`); the unbind is
never refused.

`fn consumer --json COMMAND ...` prints one line of JSON instead of the text
line, rendered by ACL2 (`fn-ncr-json-line`; every octet printable ASCII,
`fn-ncr-json-object-is-ascii`): `command`, `outcome`, `reason` (null for
none), for `status` the three counts, and for a poll or wait the report's
kind (`article`, `withdrawn`, `empty`, `unreadable`) and Message-ID.
`fn consumer-article [--json] REPORT` decodes a report file.
([evidence](../planning/evidence/friend-blockers-2-2026-09-27.md))

## Withdrawals

A consumer's query is one group, and a cancel is filed in `control.cancel`
(RFC 5537 section 5.3), so a consumer of the cancelled article's group never
selected the cancel, and a poll handed over an article its author had
already cancelled with no mark (the stranger rehearsal, PKT-710). DECIDED:
the consumer gets the withdrawal event, never the withdrawn content.

CNS-008: the page a poll, bound poll or wait serves is the poll's answer
with the view's withdrawals in it (books/consumer-withdrawal.lisp
`fn-cwd-page`). The withdrawal decision it reads is the one NNTP's
`430 withdrawn` reads: the owner's committed view's withdrawn articles and
withdrawal records.

- An article already withdrawn when its position is polled is delivered as
  a withdrawal report in place of its report, at the same cursor
  (`fn-cwd-page-never-serves-withdrawn-content`).
- An event whose withdrawal record withdrew an article of the consumer's
  group (a cancel, a supersession) is delivered at its own position as a
  withdrawal report naming that article (`fn-cwd-scan-delivers-a-withdrawing-cause`,
  `fn-cwd-page-of-a-withdrawal`); the cursor moves past it and never past
  the journal frontier (`fn-cwd-scan-withdrawal-advances`).
- A withdrawal report is the five octets `FNWD` 0x01 followed by the
  withdrawn article's Message-ID (`fn-ncr-withdrawal-report`); it carries
  nothing of the article and nothing of the cancel.
- While nothing is withdrawn the page is exactly the poll's answer
  (`fn-cwd-page-without-withdrawals-is-the-answer`), so every guarantee above
  (CNS-006, CNS-007, at-least-once delivery, the ack) holds unchanged; a
  wait answers the page and wakes for a withdrawal as for an article
  (`fn-cwd-wait-step-over-is-the-page-or-a-sleep-on-an-empty-page`).

Not guarantees: a consumer that polls after the cancel can meet the same
Message-ID twice (at the article's position and at the cancel's), as
at-least-once delivery allows; key your effects by Message-ID. The scan
still stops at 16 events per poll and walks the view's withdrawal records R
and withdrawn list N for each event not of the group: 16 x (R + N)
comparisons per poll in the worst case. Lane flip-L8-2's live refresh of
the view's withdrawals landed in batch AV (35c406204, 2026-09-27), so the
withdrawal arms read a populated view; no native case yet observes a
withdrawal event at a consumer (tests/test_native_consumer_*.py have none):
that observation is open.

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
reply's payload ceiling is its 9 header octets, the widest cursor (346) and
the Store composite ceiling `*fn-stxa-max-octets*` (the u32 frame payload in
all); ordinary control requests retain their smaller cap. ACL2 encodes the
selected event (`fn-col-poll-report`) and answers the named refusal
`:oversize` for a report above `*fn-stxa-max-octets*`; that is reachable only
for a profile whose record bound R lies in the 355 octets above it (PKT-467).
Its cursor and report lengths are checked independently. Poll leaves the
durable consumer position unchanged; only a subsequent `ack` writes progress.
The `consumer-project` exact-file reader uses the ACL2 cursor and event
ceilings (346 octets and `*fn-stxa-max-octets*`; `consumer-project --bounds` prints the
two as ACL2 computes them). A file beyond either ceiling is a bounded
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
article larger than the poll reply ceiling is refused by name (`:oversize`)
and has no skip or retrieval contract yet (PKT-466).

CNS-002: two consumers with independent durable state exchange a signed
report and a reply through one fn node (and, under CNS-004, through two
nodes peered over NNTP, each consumer on its own node), each running the consumer
transaction above and acknowledging only after it commits. Each uncertain
fact at an ownership boundary is settled by its owner: an uncertain consumer
transaction by the consumer's database, an uncertain `ack` by `position`, an
uncertain reply POST by the identical source's resend or by fn serving that
exact source back through `poll`, never by an fn acknowledgement. The same
operation with a changed source is conflict evidence with no second
transition or reply. `tools/fn_consumer.py` is the external consumer and
`tests/test_native_consumer_exchange.py` the native scenario (SCN-061).
An identical resend over the local control route (`hybrid-author` or
`operator post`) is answered D25's duplicate (PKT-166); if that answer is
lost too, the consumer settles such a POST by the
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

## BP application exchange

CNS-010 applies the same external application transaction to the carried
path: A's real consumer durably authors immutable signed R, the BP mission
carries it through the relay outage, and B's real consumer verifies it with
its own keyring before committing one local transition plus immutable Q.
B's node forwards Q by a separate undertaking; A independently verifies and
correlates it. Application operations, exact authored sources, signature
carriers, hop-local stored projections, bundles and forwarding attempts
remain distinct identities. Transport or retention receipts alone prove no
application transition.

SCN-1027 runs `tests/bp-dtn7/run_mission_four_node.py --report signed` using
`tools/fn_consumer.py`, rather than synthesizing the application outcome in
the transport driver. It cuts B in-transaction and after commit, cuts A
after ACK, and repeats R through a distinct BP undertaking after the first
one releases. The final witness requires one transition each, independently
verified received sources and both signatures equal to the immutable
artifacts, and settled forwarding pins. The driver fails on a signed author
or application failure with its logged cause; it never substitutes unsigned
content. Explicit `--report unsigned` remains a separate transport control.

The older signed mission's manually issued poll/ACK and manually authored Q
are transport evidence only. The new application driver is source-ready;
matching native/relay observations and the complete original PKT-466(c)
acceptance remain pending. No proof about the application's SQLite commit
or an external effect follows from fn's existing carried-source or relay
policy theorems.

## Authenticated remote consumers

CNS-011 (PKT-255, ratified PKT-673) requires the complete account-scoped
remote profile, including immutable multi-group registration, authoritative
query/view versions, explicit rebase, and restore/compaction cursor mapping.
Operator commands remain private. SCN-1031 preserves the full scope while its
components land; PRF-1125 remains planned until the actual host boundary exists.

The first implemented component is `books/consumer-remote-codec.lisp`.
A remote request has distinct magic `FNCR`, envelope version 1 and kind 1;
it cannot enter the `FNCT` owner-control dispatcher. Its fields are operation
(one-based enumeration register, rebase, poll, wait, position, status, ack,
unregister), UTF-8 login, credential bytes, consumer ID, encoded group list,
cursor bytes and wait seconds. Fields use the existing frame grammar:
login is `:text`, credential/consumer/groups/cursor are length-prefixed blobs,
and seconds is `:nat`. Unused group and cursor fields encode the single byte
zero; unused seconds is zero. An ACK's explicit consumer must match its
cursor. Group definitions occupy a separate blob and never the cursor's
64-octet query-ID field. The group count and frame preflight are funded by G,
the supported operator profile's group allowance. Encoding refuses a frame
specification or payload beyond the selected codec widths; profile admission
must establish representability before this component is exposed.

The decoder requires the host's protected-channel observation before reading
or hashing the request. It validates the frame and operation-specific fields;
it does not authenticate an account, establish TLS security, authorize a
consumer, or execute a Store operation. `fn-cr-decoded-request-is-protected-and-consumer-only`
proves that an admitted request had that observation and satisfies this
consumer-only grammar. All eight operation witnesses, cross-consumer ACK,
private operation/local-frame refusals, group names beyond cursor-ID width,
and damaged/versioned/over-budget frames are in the component tests. No host
caller, network listener or concrete buffer refinement is claimed yet.

The complete authority and durability implementation remains the work in
[the remote implementation plan](../planning/consumer-remote-implementation.md).
Existing FNCT response and reason codecs are the response contract to reuse.
No downgrade to a local request frame is permitted on the remote endpoint.

The logical CP kernel additionally represents remote entries as the existing
eight cursor/progress fields followed by a canonical ordered group-octet list
and a durable account-incarnation ID. Its `:remote-register` and
`:remote-rebase` proposals carry those fields atomically with scope;
identical retries preserve the current position, while any exact definition
or account-incarnation change requires explicit rebase and a fresh
registration epoch, even when the opaque query ID happens to compare equal.
ACK preserves both metadata fields. `books/consumer-remote-position.lisp`
proves exact installation and ACK preservation, and the kernel state/capacity
invariants cover the extended shape. These proposals are not yet accepted by
the durable CPE event codec, so the remote path remains unreachable in the
served composition; authentication and persistence are still unimplemented.

The consumer projection now has seven fields, with durable authority in
trailing slot6 while the Store remains14 fields. The authority tuple is
`(:authority revision creation-watermark authority-namespace accounts pending)`.
The initial constructor explicitly supplies an empty authority; recovery
does not accept a six-field projection or infer missing authority. Ordinary
consumer progress, append-frontier advance and incarnation rollover preserve
the entire authority value. This representation component does not yet make
authority adoption or remote requests reachable in the served machine.

The implementation uses one conservative global visibility revision. A
durably adopted change that cannot be proved to preserve visibility must
advance it, including changes outside a particular consumer's groups. Such
cross-scope invalidation requires explicit rebase. Ordinary article append
and consumer progress do not themselves advance it. The revision is a nonwrapping supported-codec integer. Creation identity
is an exact48octet token: current authority namespace40 plus the persisted
new-account row-stage transaction coordinate8. The namespace is the served
consumer incarnation32 plus its persisted authority-begin coordinate8.
Unchanged account tokens remain literal, including across credential rotation
and restore. New or recreated accounts name the actual committed stage, never
a reservation expectation or an independent next-creation counter. The actual
allocator/profile currently refuses after uint32 transaction exhaustion,
although the authority envelope represents uint64 coordinates. Codec width
does not establish allocator lifetime or namespace nonreuse; exhausting an
actual supported resource must refuse before publication without wrap.

Its comparison namespace starts at the first durable consumer-authority
bootstrap, only when that namespace has no previously usable cursors. The
bootstrap atomically binds the current authoritative configuration and
visibility roots; it does not count pre-bootstrap publications or scan the
history. Revision is a comparison fence, not a historical policy-event count.
The namespace/incarnation must be durably unique and nonreused across
recovery and restore. Existing CP6 cursors require proved migration or an
explicit refusal/invalidation; they are never silently interpreted in the
new namespace. No remote operation becomes available before the actual
account adoption producer and this bootstrap commit together.

Adopted account rows are
`(:account login-octets creation activep exact-adopted-descriptor-octets)`.
Committed deletion leaves a tombstone; a later committed recreation receives
a fresh creation identity. Unchanged adopted accounts keep theirs across
restart and credential-table adoption. Both static and redeemed credentials
belong to this authority contract. Editing and reverting a file without a
committed adoption does not represent two authority changes.

A candidate table larger than one supported record is built with bounded
staged rows, preserving unchanged identities and deletion tombstones by a
stream merge. Its pending tuple names the candidate, expected base revision,
maintained row count, prospective creation-coordinate watermark, explicit
preparation descriptor, last login, digest commitment and ready status.
Preparation is `(:account-preparation phase old-cursor reverse-rows
forward-rows root namespace watermark)`. Merge consumes one selected
ordered row and advances the borrowed old cursor only for an exact matching
account or deletion tombstone. Seal requires the old cursor to be empty,
so omitting an old account cannot silently erase its creation/tombstone.
Individually durable preparation ticks move one reversed row to the forward
root; the final fence does not reverse, validate or reconstruct a table. Pending rows and provisional identities
never authorize requests. A small final durable fence switches the complete
configuration and authority together; it uses established carries and digest
finalization, never a full-table scan. Failure or crash before the fence
retains the prior admitted authority. Each stage funds actual event bytes,
retained old/new-map coexistence and release debt before frontier allocation.
Concurrent static and redeemed changes serialize or reject/rebase against
the exact authority base. These producer, replay and funding obligations
remain open; the representation recognizers are proof/recovery predicates.

The current fixed CPE grammar has a scalar exact encoded charge in
`fn-cec-event-charge`, corresponding to `fn-cpe-encode` without allocating
the encoding for admission. This does not authorize remote/staged event tags
or establish their canonical retained-context demand.

The existing CPE native publication path now consumes
`fn-cpb-event-verdict-carried` through
`fn-owner-consumer-publication-verdict` before frontier allocation.
Its payload charge equals the maintained Store history row charge, while
retaining all existing release debt and the maintenance reserve. The atomic
prepared-event/completion pipeline still owns durable acceptance. This
preflight does not establish physical-frame or canonical allocation funding,
and remote/staged events remain unavailable until those producers agree.


The source account staging codec uses a distinct `fnce` version2 envelope
and the logical tag `:consumer-authority`. Its bounded operations are
`authority-begin`, `authority-row`, `authority-tombstone`,
`authority-seal`, `authority-prepare`, `authority-fence` and
`authority-discard`. The envelope carries three u64
coordinates; each row carries the exact candidate/base comparison and
creation identity. A credential row uses the existing native AUTHINFO
login domain (at most64octets), principal32, salt16, three32octet
verifier keys/digests and a posting bit. That supported credential grammar
derives a maximum321octet row. It does not cap the number of adopted
accounts; a table uses separately charged stages. Other credential
schemas require a corresponding versioned codec rather than truncation.

The current source codec proves complete decode-after-encode and exact
scalar charge, including coordinates above u32. It is not yet installed
as an accepted Store event. CP7 account/revision representability, durable
namespace/creation freshness, bounded complete-table preparation, exact
profile/canonical/retirement funding, shared live/recovery interpretation
and the final atomic auth configuration fence remain required before
activation. No version1 fixed512 consumer admission covers these records.

The staged source interpreter `fn-caa-step` accepts seven version2 account
operations: begin, row, tombstone, seal, prepare, fence and discard. It returns
`(:ok next-consumer completed-account-root-or-nil)` or a refusal. Only the
exact ready fence returns a root for installation. That root is
`(:account-root policy exact-login-trie forward-auth-credentials)`; trie values
are `(:account-binding account-row credential-or-nil)`. The actual owner
installs this separately funded sidecar and CP7 together, and the joint
configuration-first recovery fold retains the third result. The source
substream replay is not the complete Store/config recovery fold.

The exact login trie reuses `fn-midx` character branches with the established
AUTHINFO native domain (`fn-auth-credp`, names at most64octets). Octet keys
map bijectively to characters; the terminal is a separate keyword. A maintained
alphabet/uniqueness invariant bounds branch fanout by257. Structural counters
follow the actual get/put paths: lookup visits at most257*(name-length+1)
entries, put visits at most514*(name-length+1), and put constructs at most
259*(name-length+1) conses. These exclude caller row/control metadata and
are not funded quantum constants. The actual stage must compare its complete
work and allocation demands with the admitted quantum/profile and otherwise
yield through a cursor. Per-node canonical carry production, old/new/retired
root funding and the atomic owner/recovery joins remain unimplemented. No
remote endpoint or new Store-event admission is activated by this source unit.

The source carried trie mutator `fn-cait-put-octets` returns the existing
exact trie together with parallel four-field annotations for each branch-list
node: root carry, value carry, child annotation and tail annotation. It
rebuilds the selected path and borrows untouched annotations. Its boundary
proof equates the actual changed trie to `fn-cai-put-octets` and the returned
annotation to the proof-only canonical abstraction, including root size.
Neither that abstraction nor `fn-scs-summary` runs on the update path. The
bounded new account/binding constructor must supply the exact value carry.

This component does not yet thread those annotations through durable account
stages or actual owner publication. The older259cons structural allowance
excludes annotations; the new conservative primitive-constructor allowance
is `5439 * (login-length + 1)`, and entry visits are bounded by
`771 * (login-length + 1)`. These quantities exclude caller metadata, scalar
width work, old/new/retired graph coexistence and measured heap. Admission
must fund them and fit the actual quantum, or use a resumable path update,
before an account stage can activate. No owner sidecar is marked ready merely
from these component proofs.


The shared source interpreter `fn-carf-event-step` retains four result fields:
`(:ok next-CP7 new-account-root-or-nil fence-event-count-or-nil)`. It invokes
one account adoption decision, preserving its returned root and the actual
fence event coordinate. The generic older CPE projection refuses private
authority records. The Store/concrete codec recognizes the version2 authority
subtype; shape dispatch distinguishes it from topic records. Wire recognition
alone never authorizes BP metadata or an account change.

Visibility classification is produced by the actual control refresh. The
withdrawal companion returns the exact existing withdrawal result and a
conservative effect, reusing its one new-plan decision and existing target
lookup. A typed cancel plan or an arriving target of an older withdrawal
fences current cursors, including withdrawal reports whose previous visible
article list is empty. The visible companion reuses the existing verdict-growth
predicate: an ordinary noncontrol, nontargeted plain or verified append
preserves the revision; a verdict change to an older article fences it.
Generic discontinuity conservatively fences. Keyring, topic, retention and
configuration changes are also conservatively fenced. This is not a
changed-if-and-only-if claim or a bound on the existing withdrawal scans.

The pre-frontier candidate overlay selects the oldest existing history row
first, even after its article expired. It selects the candidate only when no
older row matches. Its boundary equates row/plan/withdrawal selection with
appending that candidate to the captured history without cloning the history.
The pure proposal refuses exhausted revision before an allocator call. The
actual owner still must bind the candidate to projected transaction/frontier,
owner/config/authority epochs and immutable binding, fund the entire change,
and revalidate after any yield before allocation. Completion must consume the
same decision once and publish CP7, seven canonical carries and account root
atomically. Those actual owner/native ordering joins remain open.

The shared source joint fold uses the exact physical journal comparator:
configurations at the same transaction coordinate precede the Store event.
Its model effect annotations are explicit model inputs, never host Boolean
assertions or a replacement for recovery's retained withdrawal/visible
accumulator. Actual recovery must call the same core producer at each event.
The source component does not activate the remote endpoint or close Q13.

The source carried account interpreter `fn-caac-step(s,event,metadata)` returns
the complete logical decision, next fixed4 metadata and a published root carry
only at an accepted ready fence. It uses the logical interpreter's bounded row
selection plan and fixed reconstruction, invoking the carried trie mutator
exactly once. Account-list cells carry head and tail metadata; reversal moves
one row and one credential cell. Old/new/pending metadata is part of retained
lifetime debt. Seven CP child carries accompany CP7 without changing Store14,
authority6, pending9 or root4. No served call summarizes shared account trees.

The input metadata must be established by the actual initial/cold producer and
preserved jointly with row/index/credential authority. Decision equivalence
alone does not establish this: corrupted metadata yields the same decision but
wrong size readiness. The full maintained metadata boundary, profile quantum,
byte/allocation/retirement funding and atomic owner publication remain open.
Fixture exact-size observations after creation, rotation, deletion/recreation
and multi-row merge are source observations, not a proof of every transition.

Configuration authority preflight is saved as one process-local proposal. The
core computes the next CP7 before any configuration write; the actual staging
producer captures the approved result, exact staged record, scalar coordinates
and current poststage process epoch. A durable completion consumes that result
once before installing its CP7/carries; a mismatch requires recovery and never
a normal postdurable refusal. Consume clears the proposal even on mismatch;
unstage/reset must clear it too. Epoch/namespace/revision/coordinate checks
bind an already established immutable staged-object relation: different
payloads can share coordinates, so those checks alone prove no payload identity.
The proposed host hunk currently supplies no carry metadata and establishes no
canonical readiness; complete metadata/funding and actual owner/recovery hooks
remain mandatory before activation.

The newly allocated account row and credential carries have exact constructor
boundaries and literal witnesses, including each retained row hypothesis. These
are constructor prerequisites; they do not establish the complete maintained
account/preparation metadata relation, cold establishment or admission funding.

The assembled configuration completion routes its once-consumed approved
result through one full-result owner collector. The core retains approved CP7
and metadata literally; a configuration completion emits no newly adopted
account root. Missing metadata cannot establish readiness. The new source
publication unit and current owner collector still require matching admission,
funding and recovery evidence; opaque routing observations establish only
ordering and result retention.

The bounded initial account metadata producer calls the actual `fn-cp-initial`
constructor and uses parsed history/incarnation byte counts to establish exact
seven-field carries. It creates empty adopted/pending account metadata and no
usable authority namespace or account authentication root. Nonempty restore
must retain metadata established by the same actual durable stage replay; seven
field child sizes alone cannot reconstruct maintained row/trie annotations.

The complete account publication relation is proof-only. Ordered authority rows
correspond to exact maintained trie bindings, valid credentials and their encoded
descriptors; complete reconstruction excludes phantom entries. Credentials are
exactly the live-row projection. One-cell preparation preserves the complete row
sequence while extending its prepared credential prefix. Seal preserves the
relation, and fence publishes the complete root under the explicit agreement of
pending and preparation watermarks. The actual current-binding lookup belongs to
the adopted rows and returns the exact requested live account. These constituent
proofs do not establish universal begin/stage construction, carried size metadata,
cold provenance, funding or actual owner publication. Served callers consume the
maintained relation; they never execute its whole-graph predicates.

The current-account request boundary consumes the owner's single committed
publication tuple, checking its process epoch, authority namespace/revision and
completed-fence count against current CP7 and Store count. A missing or stale
publication is unavailable; it never authorizes an empty default configuration.
Every request and WAIT wake resolves its explicit login in the committed exact
trie and performs the existing credential comparison anew, returning that
account's principal and durable creation token. Equal passwords do not substitute
accounts. Publication freshness checks are bounded scalar checks; the owner
producer must establish the complete root relation to current adopted CP7 rows.
A valid-looking phantom credential demonstrates why shape alone is insufficient.
Parsed request-byte funding precedes credential hashing. The selected actual
owner read wrapper is source assembly only: installed publication, metadata
funding, resumable current readscope and the TLS FNCR endpoint remain open.

The actual account begin establishes empty complete candidate coverage. Each
selected stage preserves complete reconstruction under explicit fresh ordering,
watermark and exact new-binding conditions. These conditions remain obligations
of the actual row/tombstone planner and old-cursor lifecycle. This construction
proof complements prepare/fence and current lookup; it supplies neither canonical
metadata nor funding or atomic owner/recovery establishment by itself.

The actual row planner supplies the complete valid new binding for new, retained
and recreated accounts under its explicit codec, old-row and namespace premises.
The actual tombstone planner preserves the old typed token and exact name. These
planner boundaries discharge the selected-stage binding obligation; complete
composition must also establish ordered keys, cursor coverage and watermarks.
Canonical metadata/funding and atomic live/recovery publication remain separate
mandatory obligations before any remote account becomes usable.

The proposed actual `fn-owner-account-publication-verdict` calls the additive
`fn-cpb-authority-event-verdict-carried` wire/history gate using the existing
FNCE codec's scalar exact row charge. Existing CPE entry points stay separate.
This source assembly is **NOTREADY** until its budget/Store book and literal
49-octet begin /321-octet maximal row witnesses pass in a matching ACL2 world.
The charge counts the persisted event payload, not its physical envelope or
canonical heap. A successful wire resource verdict alone never authorizes an
account path update, frontier allocation or adopted root: actual transient
allocation, quantum, old/new/reversed/forward coexistence and retired graph
funding, exact maintained metadata and atomic publication remain required.


The whole same-pass authority size boundary is now source-admitted at
`fn-caac-step`, rather than inferred from isolated constructors. Its maintained
inputs are exact old metadata, the authority size domain, the actual complete
stage/cursor relation with alphabet-unique trie, and the complete preparation
relation on a preparation tick. A successful decision produces exact seven CP
child carries and matching adopted/pending account annotations; an accepted
final fence returns the exact completed root carry from that same decision.
Actual bounded row/tombstone planners discharge row and credential carry inputs,
and actual prepared lookup discharges the credential carry for reversal. The
namespace width/octet premise follows from the maintained preparation domain;
that structural implication establishes no namespace nonreuse lifecycle claim.
Every retained whole-step/root hypothesis has an executable removal witness.
The actual carried create/delete/tombstone/recreate sequence preserves metadata
and the old tombstone token while assigning recreation its new persisted stage.
These are protected source proofs/executions, with no matching normal certificate
or runtime activation claim in this packet. Actual initial/cold establishment of
the combined semantic/trie/size relation, the shared live/cfg-first carried caller,
funded operation census and scheduling quantum, retirement lifetime, and atomic
owner publication remain mandatory before the TLS FNCR account endpoint serves.

Actual saved configuration preflight consumes the same metadata4 installed by
the owner publication collector. Its source boundary preserves exact full
metadata while advancing the comparison revision and discarding pending
preparation; adopted rows stay literal. Exhausted revision refuses before
staging/durable write. The readonly getter neither rebuilds metadata nor
establishes correspondence: every actual CP writer, reset and cold replay must
maintain or explicitly invalidate the joint relation. The selected host join
is source assembly only, with canonical/funding/activation still unavailable.

The sole carried metadata successor is fixed5:
`(:account-carries sevenCPfields adoptedRowsMeta pendingPrepMeta entriesListMeta)`.
The first four meanings stay literal; the fifth holds per-entry list/tail
annotations. Old4 is explicitly unavailable at successor producers. Actual
initial, authority and config producers call their decision once and maintain
this full tuple; no serving operation reconstructs an annotation from a graph.
Ordinary consumer progress must use the maintained entry producer, not retain
a stale slot5 carry after register, ACK, rebase or unregister.

Consumer entry preparation now inspects one table cell or rebuilds one prefix
cell per tick, retaining the unchanged suffix and its annotation. Its exact
selection/removal matches the existing first-match semantics; duplicate states
are corruption tests, not valid admitted tables. A ready cursor does not grant
a publication or freshness right. The selected local final proposal/application
now matches the original decision/applier under that exact prepared selection.
The local8 carry rebuilds only its fixed fields, preserving canonical numeric
tail collapse; the remote10 ACK delta requires its proved noncollapsing tail.
All retained boundary hypotheses have literal removals, and register/rebase/ACK/
unregister complete fixed5 outcomes execute. Whole fixed5 completion preservation,
parsed remote-definition validation, captured source revalidation and
allocation/retirement/quantum funding still precede atomic final mutation.
Process epoch alone cannot authorize a resumed mutation: all CP-changing
writers must establish the agreed actual source rule and final validation must
share a nonyielding owner span with frontier allocation. No schema shape,
source proof or ready cursor silently supplies that missing lifecycle.

The paired account/config source producer now retains six fields:
`(:ok CP7 newlyPublishedRootOrNil fenceEventCountOrNil metadata5 rootCarryOrNil)`.
The actual account decision runs once, and its complete metadata and final-root
carry survive this result literally; a config decision likewise runs once and
publishes no replacement account root. The guarded low producer and an actual
create/delete/tombstone/recreate execution are source-admitted. These result
packing facts are corollaries of the existing whole metadata boundary, not new
keystones establishing atomic owner publication or recovery association.

The canonical authority6 layout is
`(:authority revision creationWatermark namespace40 adoptedRows pending)`.
The sole owner account publication layout is
`(:ready processEpoch namespace40 revision fenceEventCount root4)`.
An actual account-fence/config fixture checks that the forty-octet namespace
stays literal, the scalar revision advances, the previous publication becomes
unavailable, and swapped namespace/revision slots fail. This exercises the
actual bounded availability accessor, not the host STATE collector or disk I/O.
The high Store callback, attributed same-load cfg-first CP metadata production,
all-writer source revalidation, funds and atomic installation remain open;
no nonempty restart metadata may be invented from a current STATE getter.


The bounded checkpoint annotation mapper visits one list/trie cell or returns
one completed child per scheduling tick. It preserves the complete pending
output across yields; missing pair annotations refuse instead of triggering a
size summary. Real-parser provenance supplies complete list/trie annotations
only with explicit child coverage. Literal ghost infos test this relation and
are not wire-parse observations. Whole CP7 sameparse metadata association and
actual cold caller/source-holder/funding joins remain open.

The committed account root includes policy, exact lookup index and credentials;
CP7 adopted rows alone do not retain this publication after fence clears pending
preparation. The coordinated checkpoint producer must retain
`(:ok CP7 committedRootOrNil fenceEventCountOrNil)` in the existing consumer R
root, with separate metadata from the same parse. Fence count is the dense
committed event count (`event.sequence + 1`), independent of allocator txid.
No parsed shape or size carry establishes authority; nonempty old results do
not acquire a missing committed root from a current STATE getter. The actual
cfg-first producer/decoder association remains an open join.

The additive FNCR source caller captures the real current CP, dense event count,
canonical process coordinate, ready account publication and installed owner
post-config in the same serialized span. Every scope tick reauthenticates the
explicit login and rechecks its account creation, namespace/revision and current
configured generation. The resettable canonical coordinate is not source
freshness or custody. A genuine retained-source issuer and its revalidation are
still required before article lookup or a mutation.

The source scope producer borrows the installed READ table, served groups and
closed moderation entries. It follows first-match READ precedence and hides a
shared queue unless the named login moderates every queued group. One access
row, served group, closed entry, moderator cell or output spine cell is processed
per tick. The carried key must agree before any such step. Its logical
continuation refinement and positive/hypothesis-removal source witnesses are
implemented; no whole configured table is reconstructed or revalidated.

The concrete FNCR source decoder locates the definition blob in a retained
client octet buffer. Fixed-width fields are parsed separately; group count is
checked against the supported profile before allocating a name, and each group
step preflights its codec width before copying or grammar work. Stored query
order is canonical and strictly increasing, which also rejects duplicates in
linear total work. There is no historical article-grammar 65535 group ceiling
on this producer. A truncated stream is refused rather than silently shortened.
These are source components of CNS-011. The actual digest/parser refinement,
installed transport admission/custody, durable variable CPE publication and full
native endpoint/scenarios remain open.

The selected source registration cursor compares one stored/request group cell
per tick; new-registration capacity counts the borrowed CP table one cell per
tick. A retry with the exact current durable account creation and ordered query
keeps its old query version, registration epoch and position. A changed register
refuses with rebase-required. Explicit new/rebased definitions use consumerID as
the opaque queryID and the maintained fresh CP registration epoch as qver. The
current authority revision and account creation remain separate scope fields.

The source definition cursor carries its exact uint16-name wire octet sum and
query count during the existing accept/reverse pass. FNCE version4, codes6/7,
represents remote-register/remote-rebase independently of local FNCE1, account
adoption FNCE2 and signing binding FNCE3. Its bounded producer emits one fixed
header or one <=256-octet name chunk per step, and refuses changed source keys or
mismatched remaining count/charge. Chunk residual and measure correspondence
are source theorems; the full logical decoder is a recovery reference. It is
not called on the served path. Concrete buffer/replay refinement, exact carried
Store budget/atomic finish and installed source custody remain open. A consumer
query profile cardinality must be independently configured/validated; it cannot
be inferred from per-article groups or a historical 65535 codec ceiling.

The required operator dimension is the typed current-C limit
`max-consumer-query-groups`, separate from article group cardinality and the
fixed storage-profile format. The bounded producer borrows the current limit
tail, examines one row per tick, and preserves first-match semantics. It
refuses changed current-source coordinates or Store R, and returns unavailable
when the row is absent. Accepted source policy requires a valid FNCR field
grammar and payload width plus the FNCE4 worst-case record charge below the
actual admitted Store R. No arbitrary default or 65535 query ceiling applies.
This policy is not allocation authority: selected host representation and
retained current-source custody require their genuine installed issuer, which
is currently unavailable. The existing typed C delta codec carries the row;
atomic current-C publication remains the actual collector's responsibility.

The remote definition producer now preserves the complete same-pass list
annotation through every accepted bounded tick, including reversal, and its
finish returns that exact annotation and canonical-size carry. The proof-only
observer never runs on a request. The FNCE4 scalar charge is the exact reference
encoding length from the carried group wire count; the group-count field has
fixed width, so charge correspondence does not require count equality, while
the stream producer still requires exact count/name correspondence. These are
source-only boundaries; genuine runtime funding/source custody, publication
and the remote scan/reply still remain open.

The additive remote scanner source carries exact uninspected query and article
group suffixes, compares one bounded name pair per tick, and emits each selected
event once. Its original no-skipped-match source theorems and concrete
single-FnHISTAt refinement retain their own evidence coordinate. The actual
retained backing adapter uses the dense all-event source, validates token and
ordinal custody, and offers EVERY non-NIL event to current visibility before
query selection. A NIL dense row remains unavailable at its exact position.
Catalog ordinals cannot stand in for Store event positions.

The bounded current-view producer examines one maintained article or withdrawal
cell per tick. It distinguishes visible articles, withdrawn articles, withdrawal
causes and retired/invisible articles. A cause filed outside a query can offer
its withdrawn TARGET inside that query; the cause's payload and groups are not
the withdrawal report. Each target then passes bounded query selection and the
same current READ/shared-queue moderation producer. Report inputs retain only
readable, visible groups and their local-number memberships. These internal
producers require actual owner-view/config/source custody across every yield;
their guarded definitions and literal fixtures do not install that custody or
prove the complete joined pipeline.

The saved semantic continuation now composes those bounded visibility, query
and READ producers for one dense event. Each tick invokes at most one existing
producer tick. A withdrawal cause can select several targets: a filtered report
input retains the original event position and its remaining visibility
continuation, and only exhaustion of that event advances one dense position.
READ exclusion resumes the remaining targets or the cause's eligible content.
Source and READ-generation changes refuse before touching saved children.
The actual owner STATE join retains each semantic/report continuation and
callback alias; cancellation does not consume them. It refuses unregistered
history custody, and a pending report stays unavailable until its genuine
bounded writer can consume it. The guarded internal entries and fixtures are
source evidence, while the high same-current CEP/CP validator, actual report
writer, funding, physical completion and complete host refinement remain open.

The target-only concrete withdrawal writer reuses the existing FNWD1 report.
It appends one octet per tick into the concrete buffer and has a complete
result-and-buffer-effect source boundary against its logical observation.
The maximum Message-ID width comes from that existing codec. The writer emits
only the selected target Message-ID; source/extent refusals preserve the buffer.
It requires an actual reserved extent and retained source from the installed
caller, which remains unavailable. It does not encode visible article content
or finish aggregation of several targets into a complete poll response.

The internal high reader captures the actual installed history/view/config
readout and sole current CP/carries aliases in the same owner span, then freshly
authenticates and rechecks fixed source/account/configuration coordinates before
each bounded policy, consumer selection, READ-definition or event step. The
current-C query limit is selected one row per tick and checked against the
prepared count and actual record ceiling before consumer selection. A changed
consumer, account incarnation, operation, source or supported dimension refuses
without consuming saved aliases. This source caller does not establish the
missing atomic current CP/carries/root publication association or native BODY;
its activation readout remains unavailable. Actual high getter admission,
complete host refinement and complete original remote scenarios remain open.

Remote replies share the existing FNCT typed consumer response contract:
kind 5 progress/position, kind 6 poll/WAIT, kind 9 status and kind 18 reasons.
The logical remote client refuses the legacy local-request resend path. An
unavailable source uses the existing busy status and fixed
remote-source-unavailable reason; only that exact pair is interpreted as
unavailable. Refusal and ambiguous durable outcomes remain distinct. The draft
FNCR kind-2 response grammar is historical source only and is not the selected
remote response contract. Store R bounds durable records independently of the
actual report producer's ceiling; a large query event cannot invent report
allocation or codec authority. Current-C query validation therefore covers
FNCR request and FNCE4 Store-record widths, while the separate report-profile
compatibility function validates the existing FNCT codec. Its genuine installed
report-profile source remains unavailable.

The serialized remote holder retains scanner/reader/reply/callback aliases on
cancellation. The aggregate return invokes genuine callback completion before
clearing aliases, quiescing the history reader and returning the registered
backing epoch pin BEFORE refunding the SAME shared pool. The native completion
getter remains explicitly unavailable; empty pure continuations cannot release
physical custody. Source admission/guards and literal fixtures are separate
from normal certificates, installed runtime authority, qualified images,
deployment and the complete original remote scenarios. Those remain open.

The internal visible report writer emits an ordinary RECORD with exactly the
original payload and Message-ID and a current authorized group projection.
The projected routing metadata is node supplied; it is not the author's signed
statement, and no signature over a changed composite is claimed. It prepares
one bounded codec name or emits one octet per tick. The complete concrete
buffer-effect source boundary and actual RECORD/FNCT parser fixtures pass;
physical payload reader funding, native report extent custody, complete CWAIT
statement attachment composition and multi-target reply aggregation remain open.
