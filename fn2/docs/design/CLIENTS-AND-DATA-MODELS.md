# fn2: its clients and the data models they need

Written 2026-10-28 for the fn2 design. Read-only research: GitHub issues on
`emberian/fn` (all 19), the drafted replies in `build/coordinator/replies/`,
fn's specs and docs at `origin/dev` `6521f18c4` (2026-10-28), minidregg at
`main` `44176f433`, helm (`akapug/helm` `main` `23124dc4a`, 2026-10-02, read
through the GitHub API; the local `~/dev/helm` checkout is from 2026-08-07),
and ember's prompts recovered with `cv`. A file:line cites the source at those
revisions. "Said" quotes are verbatim.

## 0. What ember says fn is for

Ember's own words, oldest first:

- **2026-09-18** (recorded in `specs/bp-path.md` status): "the capabilities
  supplied by BP are central to fn, not an optional late interface."
- **2026-09-30** (recorded in `docs/architecture.md`, Purpose): "The longer-term
  direction is a high-assurance persistent event-log substrate between
  Robigalia systems, with minidregg and breadstuffs layered on or integrated
  with it." The same paragraph: "durable identity, authorization, history,
  consumer progress, retention obligations and recovery must have explicit core
  contracts that applications and adapters can share." And: "Observability is
  part of making that substrate usable." Architecture's central questions:
  "what does this node have, why does it keep it, what has it undertaken to do,
  and what evidence permits it to release that obligation?"
- **2026-10-03**, ember on issue #14: "one way to think is about the 'redis of
  it all' that fn is; its basically persistent networked datastructures. so
  we'll be layering on conventions and have been in mini ... we're not quite
  yet ready to take on the agentic usecase proper. the core idea of fn is to
  have bounded, metered, execution, 'software with a warranty.' it isn't there
  yet, but we'd like it to have really strong statements about resource
  utilization, fairness/QoS, scale, etc while also being concretely efficient."
- **By 2026-10-09** (quoted in issue #17, filed that day), on checkpoints: "at the end of the day
  a checkpoint is a trusted operation and ultimately the system state needs to
  be represented as some recursion scheme over some causal structure, so there
  are some constraints, but ultimately feel like the 'Log Should Override.'"
- **2026-10-14** (session d0d33f7b #2828): "there's an agent community that
  wants to deploy fn for use but i know we're not ready yet still".
- **2026-10-16** (d0d33f7b #3945, on akapug's arc-chat re-assessment): "what
  IS our core architecture? what are all the layers and modules of our
  software, what are the interfaces between them, what protocol functionality
  shows up where, what's the core heart of the server's data & persistence
  model".
- **2026-10-27** (minidregg `docs/DEMO-PREFIX-2026-10-26.md:344`): "fn is not
  yet ready"; fn is out of the minidregg demo. Same day (d0d33f7b #5003): "i'd
  like fn to be usable for other dregg projects soon/eventually."
- **2026-10-28** (d0d33f7b #5907), the fn2 framing: "our fn2 we should be
  *semantics-first* and not worry as much about the proofs until we've
  actually gotten the implementation into a state where we WANT assurance from
  it ... i'm hoping that we can use this as sorta a 'high performance database
  node' for the robigalia operating system someday, this node is sorta like the
  generalized redis/postgres for the datamodels we're reaching for". Same
  prompt: "we're not convinced that our crash model is actually an appropriate
  model of the OS or hardware, and we should make sure that our crash model is
  'more tough.'"

Robigalia: there is no `~/dev/robigalia*` checkout. In the transcripts it is
ember's seL4-based capability OS in Rust (2015 origin, `#robigalia` on
Freenode); breadstuffs/dregg lanes in June 2026 built a "Robigalia v0 demo"
(a bootable seL4 image) and a "robigalia / firmament desktop substrate". So
fn's Robigalia client is prospective: the persistence and correspondence
service between capability-OS nodes. No requirement document for it exists.

Taken together, ember's framing has five parts: (1) persistent networked
datastructures, of which NNTP groups are one convention; (2) an event log as
the authority, with folds and checkpoints beneath it; (3) bounded, metered,
fair execution with stated resource promises; (4) BP/DTN as a first-class
path between nodes; (5) applications (Mini, breadstuffs, helm) layered on top
through shared core contracts, not through fn growing application semantics.

## 1. The clients

### 1.1 Mini and sleeping agents, through the consumer surface

**What they do today.** The consumer surface is fn's one application-facing
primitive beyond NNTP (`specs/consumer-progress.md`, "Experimental consumer
position, version 1"; `specs/applications.md`). Its verbs: `register`, `poll`,
`wait`, `ack`, `position`, `rebase`, `unregister`, `status`, and the `bound-`
forms that carry an account's password. Meanings:

- A cursor (`fncu` v1, at most 346 octets) names `(history-id,
  incarnation-id, consumer-id, registration-epoch, principal-id, query-id,
  query-version, view-version, position)`. `position` is the committed
  Store-record prefix scanned, never a group number. A cursor from another
  store, incarnation, consumer, epoch, principal, query or view is refused
  before any mutation.
- `poll` is a read and pins nothing. `ack` is the consumer's durable
  declaration that its own transaction finished through the prefix: forward
  only, equal is idempotent. Delivery is at-least-once until ack. Every
  outcome is accepted, refused or uncertain; an uncertain one fences mutation.
- `wait` is a poll that sleeps on the owner's commit signal (timeout 0 to
  3600 s). At most 12 waits at once (16 local-control workers less 4); each
  commit wakes every waiter, so a commit costs up to 12 polls (CNS-007).
- A withdrawn (cancelled or superseded) article arrives as a withdrawal
  report: `FNWD` 0x01 plus the Message-ID, never the content (CNS-008).
- The implemented profile is narrow: one consumer reads one group, scans at
  most 16 events per poll and returns at most one article. The general v1
  contract (up to 16 groups, 128 records scanned, 32 articles, 262,144 octets
  per page, 256 consumers) is proposed, not served.
- Exactly-once is the consumer's job: its own database keys an inbox by
  `(history, incarnation, source, application-id, operation-id)` with a unique
  `(application-id, operation-id)` index, commits its transition and reply Q,
  and only then acks ("Consumer transaction and recovery").
- All of it runs over the owner's mode-0600 Unix control socket. "Same
  machine only, for now" (`docs/agents.md`). Remote authenticated consumers
  (PKT-673, decided 2026-09-29; CNS-011) exist as source pieces only; the
  decoder "is not called on the served path."

Mini is the first real consumer. `docs/FN-CONSUMER-E1.md` and
`Kernel/FnConsumerOperation.lean` make a Mini processing transaction for a
public `DREGG/FN/NATIVE-PREFIX/v1` report, keyed `(consumer Mini domain,
consumer semantics, application, operation)`, with conflict evidence on a
separately domain-separated nonce. `Kernel/FnConsumerFrontierCore.lean`
replays fn consumer progress inside Mini: a `Key` (application, `fncu` scope,
control binding, gateway subject/target/capability), a `Cursor` (position,
receipt, mode), and a `checkAfter` that admits a transition only if it starts
at the prior position, advances by at most `maxPollScan`, and names the prior
receipt; a selected transition must name the sequence just before its end.
`Kernel/FnConsumerFrontierScenario.lean` proves a legacy, selected, empty,
selected chain reaches position 7 and that a duplicate transition is refused
(by `decide`). Mini signs at the client with fn's hybrid profile (Ed25519 +
ML-DSA-65) and submits with `fn hybrid-author`.

**What they asked for** (`docs/FN-UPSTREAM-REQUESTS.md`, 2026-09-26; fn's
answer `docs/FN-UPSTREAM-REPLY-2026-09-27.md`):

- Large signed sources: Mini's AgentGrain R is 191,283 octets, stored as a
  198,919-octet article (the carrier adds about 7.5 KB of `FN-Authorship`).
  fn widened `hybrid-author`'s source field to the u32 frame (PKT-codex-003).
- Separate A/B identities in the two-store harness (PKT-codex-001).
- The remote consumer (PKT-255): the same `fncu` cursor and report bytes over
  an authenticated connection, with wait/poll/ack giving the same three
  outcomes and `position` to settle an uncertain ack. Not built.
- PKT-322: a revoked author's uncertain post can settle only by reading the
  article back. Open, waiting on ember.

fn's reply also states what fn will not do, and fn2 should keep it: fn does
not decide publication consent or select history ("fn is semi-untrusted
transport here"); it keeps no secrets (encrypt before signing); it never
redacts a signed article; size is the operator's profile, not a per-consumer
cap.

**The numbers.** One grain: 191,283 octets of source. Mini's E1 adapter caps a
consumer history at 16 accepted events and an origin package at 17,408 bytes
(`FN-CONSUMER-E1.md`). E1/E2's twelve v1 traces are "specified-not-executed";
four native source-execution cases passed on 2026-10-03 at 21.6, 11.9, 47.7
and 31.1 s (from akapug's 10-16 re-assessment, citing
`planning/experiments/e1-e2-agent-exchange.md:244-255`). minidregg's backlog
keeps "Selected exchange across two machines; configurable fn node address"
(O31) after the demo.

### 1.2 helm (and its successor name, arc), the first real outside client

helm is akapug's "steering station" for a multi-model coding-agent fleet:
Claude Code hooks deliver chat between tool calls, orca/herdr hold panes, a
durable dispatch ledger and a whole-suite gate decide what lands. Python
stdlib only, Linux only, "because its chat lives in RAM at `/dev/shm`"
(README). By mid-October akapug's tree calls the chat "arc chat" (`~/.arc`,
`arc/chat.py`, `/dev/shm/helm-chat/main.jsonl`).

**What it stores today, and how:**

| Record | Storage | Identity, order, durability |
| --- | --- | --- |
| Room post (row) | RAM append under a flock, one serialized writer `chat._append_once`; rotated at 2 MiB | row id; per-room order from one writer. Durable copy is *rendered text* (`ts [room] body`), so a restore loses `reply_to` and signatures; DMs are never journaled (#14) |
| DM lane | RAM | lost at reboot (#14) |
| Delivery cursor | a file per (room, seat, session) holding `{dev, ino, off}`, a byte offset plus file identity; rotation needs its own journal | at-most-once: a row committed then lost in a pipe buffer (task/2920) |
| Ack | another row appended to the store | |
| Dispatch row (an obligation: build/review owed by a seat) | append-only event ledger, written inside the writer lock before any notification (`docs/DISPATCH-ADD-CONTRACT.md`) | idempotent by operation key: a repeat returns `existed=True` ("never-send-again"); `notify-failed` and `delivered` are further events; bound to exact commits |
| Premise (a prior at confidence 1.0, an operator-stated truth) | `_global/.state/attest-chain.jsonl`, `rec_hash = blake2b(canonical(core) + predecessor_hash)` (`docs/CONCEPTS.md`, `ATTESTATION.md`) | a thin claim (digest) with the text kept elsewhere; supersession is a new chain record; a dregg node may optionally anchor the digest, "never the proof" |
| Signed turn | each post was a self-write turn on a dregg chat node, digest `chat:b2b:<blake2b-256>` | turned off 2026-10-11 during a hub-load incident; "0 of 49,960 rows carry turn"; owner's ruling "unsigned until fab+arc on minidregg" |
| Post outcome | `notify_port.DeliveryResult`, evidence OBSERVED / NOT_OBSERVED / UNKNOWN | "Direct match" to fn's accepted/refused/uncertain |

helm's architecture law is fn-shaped already: "Every fact is an **event**
(immutable, append-only) or an **artifact** (authored content with
identity)"; "Every derived view ... is *read-only as truth*"; "Every store must
say what it derives from" (`docs/ARCHITECTURE.md`).

**What it asked for.**

- #14 (2026-09-30), four layers fn could carry: (1) the durable journal
  (Message-IDs, References, exact bytes, withdrawals); (2) delivery that
  survives a lost wake (redeliver until ack); (3) across machines and owners
  (peering); (4) humans reading with any newsreader. Thirteen critiques; the
  data-model ones: senders unauthenticated by default ("an unauthenticated
  From is a prompt-injection channel"); 12 waiters too few, and "A sleeping
  waiter should not hold a control-client slot"; one group and one article
  per poll; total history cannot run open-ended (no D13); the agent inbox
  needs the operator socket; "Waiting costs nothing" is false for an LLM seat.
  helm keeps three jobs for itself whatever sits underneath: waking an idle
  seat, tracking who owes a reply, per-seat signed turns. "wake is helm's
  layer in either design."
- 2026-10-08, five needs "across several of [our products]": retention
  settable on a running node; exactly-once operations with a receipt ("a
  cancel is itself an operation"); identity is a key and roles are narrowable
  delegated rights; NAT traversal and delay-tolerant sync for weak devices
  (phones behind home routers); a conformance test for agreement and ordering
  a downstream port can run.
- 2026-10-08, the record question: helm needs to sign its own fabric records
  (a land, a verdict, a forge write), each carrying an op id, the signing key
  and the previous head, so a retry is answered `replayed`. Mini's
  `DREGG/OBJECTIVE/ACTIVITY/SIGNED/v2` has the shape but seals only closed
  kinds. Asked: (a) an `invoke` on an application object, (b) a generic
  signed-record kind, or (c) something else? Interim: `HELM/FORGE/RECORD/v1`.
  No answer is recorded.
- #17 (2026-10-09): checkpoint substitution as an explicit release of
  retention pins (proposed RET-008, six clauses C1-C6: a checkpoint is an
  immutable `(history, prefix-head, prefix-sequence, fold-id, summary-digest,
  identity-commitment)`; creating one is a `:checkpoint` obligation;
  substitution is `fn-retain-release` of `:archive` pins; "the log overrides";
  precedence by authority not kind; the identity commitment makes duplicate
  refusal checkable after bodies are gone).
- #18 and #19 (2026-10-16): a published release so outside agents can run E1;
  served remote `wait`/`ack` over TLS; the 12-waiter cap as an operator setting
  or a per-group wake; one consumer spanning several groups.
- The 10-16 re-assessment's "real answer" is on helm's side: a transport
  port, `append(row) -> Evidence`, `read(room, after=row_id)`,
  `wait(seat, timeout)`, `ack(seat, row_id)`, with cursors moved to row ids,
  so that "fn, Mini or tmpfs" become a provider choice.

**The numbers.** About 2,300 chat rows a day across all rooms and about 41 a
day in finished task rooms (7 days to 2026-09-30); by 10-16, 2.5k (10-08),
5.7k (10-15) and 4.7k (10-16, partial) rows a day, "about 3-7k rows/day at
about 1 KB/row"; the live store 427 rooms + 27 DM lanes, 281 MB, 49,960 rows.
Unsigned post 0.163-0.209 s (CLI wall time); room-tap wake 0.34-2.16 s (the
2.0 s `POLL_S` tick); a fresh mention did not wake the seat beacon within 36 s
(n=1); doorbell 60 s debounce, 12 rings an hour; the old waiter cost "7-10% of
a core per waiter". Ed25519 over a 1 KiB row: 30.7 µs to sign, 77.5 µs to
verify (`cryptography`). The dregg chat node it used to sign through held an
11.81 GB store and booted in up to 25 m 41 s. The falsifiers akapug set for
fn: wake p95 > 2 s; heap > 2 GB at one day of chat; the waiter cap blocks a
30-seat fleet; an acked row redelivered after a crash.

### 1.3 akapug's fleet and its other products

**Today.** About 30 seats on 4 boxes (#19), Claude, Codex, Kimi, DeepSeek,
Grok, Gemini and local models. It does not run fn: its probe stopped at the
toolchain (ACL2 8.7 + SBCL 2.6.8; Ubuntu ships SBCL 2.6.0; a 25-70 minute
image build) and at access (the public node answers `LIST ACTIVE` with 480;
TLS 1.3 connect + greet 746 ms, then about 165 ms per command).

**Asked for, beyond helm's chat:** a one-way archive of finished task rooms
into a private fn group (row id as Message-ID, `reply_to` as References, the
dregg turn digest in a header, never DMs), about 40 rows a day, about 1,200 a
month; an account on `fn.fg-goose.online` or a tarball to start it; one of the
"two independently provisioned participants" for a minidregg preview, on mixed
old homelab hardware. And through #17, Simbi's ClockDAG: "community-credit
ledgers on donated devices with small disks, so those devices must checkpoint
and drop old bodies. If fn carries correspondence for those devices, we need
checkpointing that never silently erases a promise or reopens a duplicate."

**Where fn stands (drafted, not posted).** `replies/issue-18.md`: "There is
no 6.6.0 to publish"; the version line restarted (next tag 5.1.1); the
storage format is mid-replacement, so a node installed now would need an
export/import or a wipe; the account line is left for ember. `replies/
issue-19.md`: the consumer *meaning* is fixed and proved, the *transport* is
what limits; remote wait/ack "Realistically weeks, not days", sequenced after
the storage landings; the waiter bound to become "an operator setting priced
by the node's memory profile" and the wake per-group or per-inbox; multi-group
by write-time fan-out into a per-agent inbox group or by a multi-group cursor;
"Transactions are never reclaimed ... a node you run would set the budget near
2^32". Neither reply is posted (#18 and #19 have no comments).

### 1.4 Human readers, through NNTP and the web

**Today.** Any newsreader (tin, slrn, Thunderbird; #6 asks for a Gnus report,
#7 for any untried reader) over TLS with SCRAM logins; the node's own web
page (`docs/web.md`, `docs/reader.md`): invitations, sign-up, group lists,
"older posts", post, "Remove my post" (cancel), three post outcomes rendered
for people ("Posted!", "The server said no", "We couldn't tell whether the
server took it"). The node decides every group, post and removal on the
friend's own connection; private groups look absent. `max_sessions = 64` by
default; each signed-in person is one node connection.

**Asked for** (the issues ember filed 2026-09-27): full-text search over the
groups an account can read (#1; today XPAT over Subject/From in one group,
recent 2,000 articles); a thread API as JSON built from References (#2);
MIME attachments shown well (#3); a peering-map view (#4); reply by email
(#5); translations (#8); packages (#9). #1 says: "Agents use fn as shared
memory: 'what did we decide about X last week?' is their most common
question."

**Numbers** (`docs/operator.md` §11, September 2026, shared ZFS server): a
post confirmed in about 0.6 s (0.8 s signed); about two posts a second
sustained; reading one article about 0.5 ms; a 40,000-article store (2 KiB
each) opens in about 14 s and uses about 1.3 GB. Elsewhere: unsigned POST
6.5 ms on tmpfs, signed POST p95 282 ms on tmpfs and 786 ms on ZFS, owner CPU
91-93 ms per signed POST (`docs/operator-internals.md`, `CHANGELOG.md`, as
quoted 10-16).

### 1.5 Peers, through NNTP feeds and BP/DTN

**Today.** NNTP streaming peering with distributions, `path-identity` loop
detection, `436` "try later" when full (the feeding node keeps the article);
two nodes, hbox and fsn1 (`docs/nodes/`), the public one
`fn.fg-goose.online`. Two-node consumer exchange CNS-004 runs over NNTP
peering: each consumer talks only to its own node, a repeated transfer is one
Store event, each hop keeps its own stored projection while the authored
source and signatures are identical. BPv7: a pinned dtn7-rs exchange passed
with durable sender work, lost receipt, restart, duplicate recognition and
receipt regeneration (2026-09-18); one ION-DTN LTP/UDP feasibility run (no
non-destructive receive, no bundle id returned to the sender). Forwarding over
BP is a retention obligation in the sender's workflow journal, released only
by the peer's receipt or an explicit, recorded waiver (`docs/operator.md`
§8).

**Asked for:** INN peering guide (#12); IPv6 peering (#10); from akapug, NAT
traversal and delay-tolerant sync for weak devices.

**The shape that matters for fn2** is `specs/lifecycle.md`'s "one letter":
stable Message-ID across retries; one transaction for content, both
memberships and obligations; a lost reply produces no second membership; a
portable batch carried relay to relay, paused, resumed, duplicated, imported
out of order; release only on durable evidence; compaction keeping roots,
numbering history and evidence. Its warranted-lifecycle table names the open
prefixes: (b) reconciliation across restart rests on the Message-ID, not an
operation identity; (e) the identity history has no lifetime policy; (f) a
retry after reclaim must still answer duplicate.

### 1.6 Operators

**Today** (`docs/operator.md`, eleven chapters): the store's disk, start/stop,
`status` / `health` / log, groups and moderation, accounts, invitations,
private groups, signed-post bindings, agents' consumers (`consumer bind NAME
--account LOGIN`), certificates (post-quantum key exchange first), opening to
the internet, peers and BP carry (`carry ... list|inspect|pause|resume|drop
[--abandon]`), backups and moves, recovery ("uncertain", a damaged record log,
"no store", the store full), limits (`policy set max-transactions |
max-history-octets | max-article-octets N`, live, STO-038), `store compact`,
`store reclaim` (offline, or live with `reclaim_live = true` and a heap
reserve of about a second copy of the history).

**Asked for:** `health --explain` (#11); an offline timeline viewer for native
trace spans (#15); an observation-journal inspector for resilience failures
(#16). Architecture: an operator must relate an issued operation to its
phase, reason for waiting or refusal, durable publication and retained
resources; "internal getters alone do not establish it."

**Numbers:** a store `init` on a small machine holds "about seven thousand
short posts"; the public node's budget is 32,768 transactions, the default
2^32-1. Compaction "relieves files, not transactions" (`specs/storage.md`).

### 1.7 fn's own swarm (a client that is not one)

#14 point 8: "The agents building fn do not use fn." Lanes coordinate through
LANEDUMP files, `build/coordinator/claims.jsonl` and briefs. minidregg's
north star makes helm-shaped coordination a first-class target ("rooms as
cells, posts as signed turns, premises as attested claims, review verdicts and
land-receipts as receipts on chain"; "Our own development fleet is the first
user"). fn2's first dogfood client is available in-house.

## 2. The data models

### 2.1 Per client: objects, identity, ordering, visibility, retention, durability

**Mini / sleeping agents.**

- Objects: a signed authored source (report R, reply Q), exact bytes up to
  the profile's article bound; its carrier (source + `FN-Authorship`, two
  signatures); a consumer registration; a cursor; an ack; a withdrawal
  report. The application operation and its inbox/outbox live in the
  consumer's own database, not in fn.
- Identity: Message-ID (exact octet equality, OBJ-002); content digest;
  `(history-id, incarnation-id)` for the store's lineage; `(consumer-id,
  registration-epoch)`; on the consumer side `(application-id,
  operation-id)`. A Store position, local number, acceptance stamp or wall
  clock is none of these.
- Ordering: the node-local committed Store-record prefix. Per consumer,
  forward-only. No global order across nodes; Mini supplies its own causal
  history and receipts.
- Visibility: the principal's read rule at a pinned view; a view change
  (including a newly visible old article) bumps `view-version` and forces a
  rebase from zero.
- Retention: the consumer pins nothing; reclaimed content is an explicit
  `unavailable` gap. Mini's publication consent and history selection are its
  own (FN-UPSTREAM-REPLY §4).
- Durability: acceptance only from persisted state; an uncertain write fences
  mutation; resending the exact signed tuple is the lookup (`ACCEPTED`,
  `DUPLICATE`, `CONFLICT`).

**helm / arc.**

- Objects: room rows (post, reply, react, with addressees stamped at post);
  DM rows; dispatch rows (build/review obligations) and their events
  (`notify-failed`, `delivered`, verdict); lands, verdicts and forge writes
  as signed fabric records; premises as a hash chain of digests; per-seat
  cursors and acks; presence (a TTL channel, disposable); opaque CRDT updates
  through a blind relay (`docs/ARCHITECTURE.md`, local multiplayer).
- Identity: row id; dispatch id as the operation key; seat name is a label,
  the key is the identity (need #3); `rec_hash` for a premise; for fabric
  records, `(op id, signing key, previous head)`.
- Ordering: per room, one writer's order (akapug: "Chat does not need a
  global consensus order; per-room order from one writer is enough"); per
  signer, a previous-head chain; dispatch rows bound to exact commit SHAs.
- Visibility: rooms readable by the fleet; DMs by their two parties; rooms
  shared across owners need a transport and a principal boundary helm does
  not have ("every seat is the same UID").
- Retention: today forever and unbounded (rotated RAM plus a rendered
  journal); asked: settable on a running node, finished task rooms archived,
  DMs durable, threading and signatures kept through restore.
- Durability: obligation first, notification best-effort, the gap recorded;
  exactly-once by operation key with a receipt; a cancel is itself an
  operation; a wake within seconds, cheap per waiter, for about 30 seats
  watching home room, DMs and mentions from any room.

**akapug's other products (ClockDAG on donated devices).**

- Small disks: checkpoint, then drop bodies, keep identities; a checkpoint is
  valid only if recomputable from the log; invalid transactions kept as replay
  defence; quorum-verified checkpoints may replace a provisional local suffix
  but never an adopted one (#17's ClockDAG evidence).
- Weak, intermittent links: NAT traversal, delay-tolerant sync.
- A conformance suite for agreement and ordering a port can rerun.

**Human readers.**

- Objects: articles (exact bytes, MIME inside), groups, memberships with
  local non-reused numbers, threads (References: may be missing, malformed
  or cyclic, OBJ "Article bytes"), accounts, invitations, withdrawals.
- Ordering: per group, article numbers; threads as a reference graph.
- Visibility: per-account read and post rules; private groups look absent.
- Wants: full-text search over what the login can read, a JSON thread tree,
  attachments. fn's chosen split: "Presentation clients own MIME display";
  search and threads are clients beside the server (#1, #2).

**Peers.**

- Objects: portable articles and statements, batches with content
  dependencies, receipts, forwarding obligations; never raw pages
  (`docs/architecture.md`, "Three representations").
- Identity: Message-ID and content identity, separate from each node's
  stored projection (`Path`, `Xref`, injection records are outside the
  authored source, OBJ-003).
- Ordering: none required between nodes; each node assigns its own numbers;
  duplicates idempotent; out-of-order import must converge on validated fact
  sets, not identical local variants (OBJ-004).
- Retention: a forwarding pin held until the peer's grounded receipt or a
  recorded waiver.

**Operators.**

- Objects: configuration history (generations), the store profile, live
  limit rows, the capacity vector, health observations, decision journals,
  trace spans, operation phases.
- Need: every refusal named; headroom stated; "what does this node have, why
  does it keep it, what has it undertaken to do".

**Robigalia (prospective; no requirements written).** INFERRED from ember's
framing only: a persistence and correspondence service between capability-OS
nodes, so the same primitives under capability-scoped (attenuable) access
rather than login accounts, and an interface below NNTP.

### 2.2 What a "generalized redis/postgres" would have to offer them

The analogies to Redis and Postgres below are mine, offered to make ember's
phrase concrete; each row says what fn has now.

1. **Immutable content objects.** Exact bytes, algorithm-tagged identity,
   chunk manifests for large bodies, collision as quarantine not overwrite.
   Needed by every client. fn has it (OBJ-001..003; the catalog's columns,
   STO-027). Postgres analogue: none native (large objects); Redis: none.
2. **Append-only streams with cursors and acknowledgement.** A group is a
   stream; the node-wide Store log is the stream of streams. Redis Streams'
   `XADD` / `XREADGROUP` / `XACK` / `XPENDING` correspond to post / poll /
   ack / position. fn has the single-reader form, proved, local only. Missing:
   a cursor over several streams (helm's inbox, CNS-011's multi-group query);
   per-stream wake; remote served transport; competing consumers that claim
   work from one stream (helm's `work claim`, a review queue) — fn has none,
   only one position per consumer.
3. **Keyed insert-if-absent with conflict.** The Message-ID binding is a
   unique key with three answers (stored, duplicate, conflict, D25). Missing:
   an *operation identity* separate from the Message-ID (lifecycle gap (b));
   an op-id index the node keeps so a retry is answered `replayed` (helm need
   #2; today the consumer keeps it); mutable keyed state (set, compare-and-set,
   delete) of any kind — fn has no Redis-hash or Postgres-row analogue at all.
   Whether fn2 grows one is a design question (§4, question 1).
4. **Signed records with a per-signer chain.** fn signs exact authored bytes
   at the client (hybrid Ed25519 + ML-DSA-65); the node checks and stores.
   Missing: a generic signed-record kind for an application's payload
   (helm's (b)); a previous-head field and the node's check of it; a
   principal header bound to the authenticated login by default (#14 point 5;
   NNT-013's bound-logins is opt-in). fn already has equivocation detection
   for statements (`fn-sn-equivocatorp`, STO-010 table).
5. **Attested claims (statements).** `specs/objects.md` already lists a
   Statement record: kind, issuer, scope, subject references,
   terms/dependencies, authenticated encoding; key and policy evidence is kept
   forever. helm's premises are claims with a digest, an issuer and
   supersession; Mini's receipts are claims about accepted prefixes. Missing:
   statements open to applications, supersession as a first-class relation,
   and lookup by (issuer, subject, kind).
6. **Obligations with evidence-gated release.** fn's retention ledger
   (`:archive`, `:forward` pins; release only by an explicit predicate over
   committed evidence; independent pins survive one another's release) is
   the primitive neither Redis nor Postgres has. helm's dispatch ledger is
   the same shape for a different obligation ("who owes a reply"); #14 notes
   fn's obligations are custody obligations only. #17 proposes a third kind,
   `:checkpoint`. Generalising "obligation" to an application-declared kind
   with a release predicate would carry helm's owed-reply ledger, Mini's
   delivery undertakings and BP custody under one rule.
7. **Snapshots and authorization.** A connection reads a pinned committed
   version (snapshot isolation in Postgres terms); per-principal read rules
   hide groups (row-level security). Missing: narrowable delegated rights
   (akapug need #3) and a capability form for Robigalia; the agent inbox
   still needs the operator socket (#14 point 3).
8. **Folds, checkpoints and history compaction.** Packing exists; content
   reclamation exists offline (`store reclaim`); history compaction H ("every
   decision computed from summary plus suffix equals the one computed from
   the full history") is not implemented and needs D13 (STO-010). #17's
   `fold-id` and "the log overrides" are the client's statement of what H
   must be. Postgres analogue: a materialized view with a provable refresh;
   here the view may replace bodies only by releasing pins.
9. **Wait and notify.** fn has a commit signal and a sleeping wait. Needed:
   remote, multiplexed (a sleeping waiter holds no worker slot), woken per
   stream or per inbox, with a stated cost per waiter and per commit.
10. **Metering and typed refusal.** The capacity vector, the transaction
    budget, live limits, `:unaffordable` / `:history-exhausted` /
    `:memberships` refusals, and three outcomes everywhere. Missing:
    per-principal accounting (C1-08), fairness between principals, and a
    budget that expiry can return (today reclaim frees bytes, never
    transactions; only H under D13 raises admission headroom).
11. **Replication of portable objects.** NNTP peering and BP carriage move
    portable objects and statements; duplicates are idempotent; releases are
    grounded in a durable record at a node of the system. Missing: a defined
    convergence statement for application streams, and NAT/DTN reach for
    weak devices.
12. **Query.** OVER, HDR, XPAT over bounded windows. fn's chosen line is that
    search and threads are clients beside the server, reading what the login
    may read (#1, #2). A "postgres" reading of ember's phrase would put at
    least secondary indexes (by References, by issuer, by subject) in the
    node; STO-001 already demands that any index answering a range query be
    validated for completeness, and an external index is in the trust
    boundary.

## 3. F_node's claim surface: the semantics fn2 must keep

`specs/node-functionality.md` (status "design, wave 4") defines one object
that every functional-correctness theorem refines: an ideal functionality
F_node in Canetti's sense, written as an ACL2 state machine `(mv s2 effects)
= (fn-ideal-step s e)`. Current state of its books at `origin/dev`:
`books/served.lisp` is present with `fn-served-step-preserves-connp`,
`fn-served-step-effects-are-typed` and `fn-served-step-partition-independence`;
`books/ideal.lisp` (the P0 skeleton the status line names) was deleted on
2026-10-17 (`cdb0f7114`, "M1-b consumer: delete the 70 tier-B books");
`books/ideal-node.lisp`, `dtn-channel.lisp` and `system.lisp` never existed.
Several lemma books the spec cites "left with the breaking cut". So the spec is
the claim surface, mostly unproved; it is what fn2's semantics should be
measured against.

### 3.1 The state and its projections

Five fields: configuration, the relay (which already composes the store node,
the BP sender and receiver, a terms table and undertakings), connections,
the clock observation, and an outbox of unacknowledged effects. Everything
else is a projection, never a separate field:

| Projection | Definition |
| --- | --- |
| `fn-ideal-store` | the relay's store node |
| `fn-ideal-history` | the store's committed records |
| `fn-ideal-generation` | the store's durable frontier ("the generation is the durable frontier") |
| `fn-ideal-node`, `fn-ideal-archive` | the node and its acceptance state |
| `fn-ideal-pins` | the retention ledger's pins |
| `fn-ideal-pinned-archive s conn` | the replay of the first `version` records: what a connection reads |

The configuration carries groups (no duplicates), capacity, max connections,
line limit (510) and body limit (8192), the BP sender and receiver configs
and the terms table. A connection is `(id, wire, session, version)` with
`version <= generation`. The recognizer `fn-ideal-statep` carries every
invariant the served path needs ("No whole-state revalidation on a served
path").

### 3.2 The interface

Inputs by port: client `(:open id)`, `(:octets id octets)` (any list, any
partition), `(:close id)`; host `(:store ev)` (prepare, io, finish, crash
with a frontier and record choice, recover), `(:reopen frontier records)`,
`(:clock obs)`, `(:contact plan)`, `(:advance id)`; peer `(:bundle src
octets)`; BP transport observations; operator `(:post record)`,
`(:declare-group name)`, `(:enqueue ...)`, `(:undertake ...)`,
`(:release receipt-id)`. Outputs are a closed effect type: `:reply`, `:close`,
`:write`, `:submit`, `:delete`, `:receipt`, `:refused` (one of the finite
`*fn-ideal-refusals*`), `:uncertain`. Note what is absent: no consumer port
(register/poll/wait/ack) and no account or configuration port beyond
`:declare-group`. fn2's consumer surface would have to enter here.

### 3.3 The refinement

R (the owner process, the reader, the store host over the certified books)
refines F_node as a deterministic trace refinement in three layers:

- **Layer A**, inside ACL2: the function the host calls per event equals the
  ideal step. Landed for the reader port (`fn-reader-chunk` calls
  `fn-served-step` on the whole read; chunking is irrelevant by
  `fn-served-step-partition-independence`). Every other port is open.
- **Layer B**, the host contract A-HOST: bytes in order and unaltered, each
  I/O outcome reported honestly and once, each effect performed exactly
  (`fn-assume-host-events`, `fn-assume-host-report`). No theorem yet takes it
  as a hypothesis.
- **Layer C**, the crash schedule: a death is `(:store (:crash fc rc))` over
  `fn-sf-crash-imagep`, a restart is `:reopen`; "A cut the model cannot
  express is a fidelity defect, not a passing test." A-DURABILITY enters only
  as that hypothesis, discharged per platform. (Ember's 10-28 doubt about the
  crash model's toughness lands exactly here.)

Equality, not indistinguishability, because the current profile has no
secrecy and authority is an oracle (`fn-assume-policy-authorizedp`): the
simulator is the identity. It stops being trivial at three named seams:
signatures on receipts and native articles (the forgery event; P6 replaces
the host boolean with `fn-sig-verify`), content identity by digest (avoided by
quarantining on collision, OBJ-001, "That decision must be preserved"), and
confidentiality (D04, later).

### 3.4 The server-robustness theorems

"Clients cannot crash us regardless of what they send", every one quantified
over every state satisfying the invariant and every event without hypothesis:

1. **Totality** (3.1): `fn-ideal-step` guard-verified with guard `t`, its
   whole call closure `:common-lisp-compliant`, and
   `fn-ideal-step-is-total-and-typed` (the state stays a state, effects are
   typed).
2. **Work per step bounded** (3.2): an instrumented twin equal to the step
   and `cost <= k * (1 + n + line-limit + body-limit + groups + capacity)`,
   exponent 1 in input length and each configuration term; the report must
   quote `*fn-ideal-cost-k*` beside a measured chunk cost.
3. **Retained memory bounded** (3.3): `size <= max-conns * (line + body +
   session) + per-charge * capacity + fixed`, true only if every retention
   charge is positive (`posp`; today `natp`).
4. **The only failures are typed refusals** (3.4):
   `fn-ideal-every-effect-is-typed`; `fn-ideal-outcomes-are-three`
   (accepted, refused, uncertain); `fn-ideal-refusal-changes-no-committed-history`;
   `fn-ideal-uncertain-iff-fenced`. The CLI exit-code table (0/1/3/4) is the
   image of the third.
5. **The reply stream is F_node's** (3.5):
   `fn-ideal-reply-stream-is-partition-independent`, whose content is the
   NNTP audit plus the certified cursor and selection theorems.

And **connection isolation** (3.6, the sixth subsection):
`fn-ideal-connection-isolation`, a connection's replies are a function of its
own octets and the version it pinned, under any interleaving of other
connections' events. With 3.5 it is "the whole 'we implement the semantics'
claim for readers". Open (M7).

### 3.5 The refusal theorems and the strawman audit

Section 4 sorts the existing "a bad thing fails" theorems: branch-of-definition
refusals prove nothing about the system (rename `-by-definition`, keep as
rewrite lemmas, never cite as evidence); teeth whose witness fails only a
shape clause prove nothing (each needs a well-shaped witness that fails a
semantic clause); reachability witnesses are witnesses, not teeth; the
legitimate teeth drop a semantic hypothesis against a well-shaped witness;
unreachable branches are marked `unreachable-in-composition`. The system
property behind each refusal is the positive keystone beside it (for example
`fn-prepare-allocates-fresh-monotone-txid`). fn2 should inherit the rule, not
the list.

### 3.6 Composition with the network: F_dtn

F_dtn is an unauthenticated, adversarially scheduled channel: it never
fabricates; the adversary delays, reorders, duplicates, drops and injects;
it has no clock (expiry is decided by the receiving node's own clock). The
composed system is a map of endpoint to F_node plus one F_dtn. Two theorems:
`fn-sys-release-is-grounded-end-to-end` (an obligation is released only
against an authorized receipt grounded in a durable record at a node of the
system, and the archive pin survives, under every schedule) and
`fn-sys-duplicate-delivery-is-idempotent`. Progress is not claimed here
(PRF-018 needs a fairness assumption and a contact plan).

### 3.7 M1-M10

| | Milestone | State per the spec, checked against `origin/dev` |
| --- | --- | --- |
| M1 | F_node book: state, step, statep, initial state, projections, witness trace | the skeleton existed and was deleted 10-17 |
| M2 | served path in logic mode | landed as `fn-served-step` |
| M3 | guard closure walker and ledger rule | open |
| M4 | partition independence lifted to the ideal run | per-connection law landed; lift open |
| M5 | typed refusals, the three theorems of 3.4 | open; "M5 retires D13" |
| M6 | cost and size bounds, `posp` charges | open |
| M7 | connection isolation | open; the owner keystones it lifts landed |
| M8 | A-HOST and A-DURABILITY as hypotheses of the run | open |
| M9 | F_dtn and the composed system | open; no `fn-sys-` definition exists |
| M10 | the crypto seam: `fn-sig-verify` replaces the host boolean | open; `books/crypto-seam.lisp` exists |

**What fn2 should keep from this**, as semantics rather than as a proof
backlog: one state machine with ports and a closed effect type; history and
generation as projections of the log; per-connection pinned versions;
three outcomes with refusal changing no history and uncertain iff fenced;
work and memory bounded by configuration and input length; isolation between
connections; release grounded in durable evidence under an adversarial
channel. What it must add: the consumer, account and configuration ports
that F_node omits, since they are what the clients in §1 actually use.

## 4. Capabilities: who needs them, what exists, the gap

| Capability | Who needs it | Exists today (fn `origin/dev`) | Gap |
| --- | --- | --- | --- |
| Exact-byte immutable objects, collision quarantine | all | yes (OBJ-001..003, catalog STO-027) | large-body chunk manifests not fixed; none for fn2 yet |
| Client-signed records, node verifies | Mini, helm, peers | hybrid Ed25519 + ML-DSA-65 via `hybrid-sign` / `hybrid-author`, local control socket only | signing needs the native image on the same machine; no generic application record kind; no previous-head chain; principal not bound to login by default |
| Keyed insert-if-absent (duplicate/conflict) | all writers | Message-ID binding, D25 three answers | no operation identity separate from Message-ID; node keeps no op-id index for `replayed` |
| Mutable keyed state (set, CAS, delete) | helm (dispatch state, cursors), Robigalia (inferred) | none | absent by design so far; question 1 |
| Append-only streams (groups) with local numbers | all | yes | none for the stream itself |
| Cursor + ack, at-least-once, fenced uncertainty | Mini, helm, akapug, fn's own swarm | local, one group per consumer, 16 events and one article per poll | multi-stream cursor, pages, remote transport (CNS-011 / PKT-673 / PKT-255) |
| Wait / wake | helm (30 seats on 4 boxes), Mini | local `wait`, sleeps on commit signal, 12 waiters, wake-all | remote; waiter holds no worker slot; per-stream/per-inbox wake; operator-set bound; measured p50/p95 |
| Competing consumers / claim | helm (`work claim`, review queues) | none | absent |
| Withdrawal as an event | Mini, helm, readers | yes (CNS-008; `FNWD` report) | withdrawal-aware confinement theorem for the served page (#14 point 11) |
| Per-principal visibility at a pinned version | readers, Mini, helm | read rules, pinned connection versions, view-version | narrowable delegated rights; capability form; agent inbox without the operator socket |
| Obligations with evidence-gated release | peers (BP custody), Mini (undertakings), helm (owed replies), ClockDAG | `:archive` / `:forward` pins, independent-pin preservation | application-declared obligation kinds; `:checkpoint` kind (#17) |
| Settable retention on a running node | akapug, helm, ClockDAG | per-group expiry, live limits (STO-038), `store reclaim` (offline, or live with a heap reserve) | reclaim never returns transactions; identity history has no lifetime policy |
| History compaction (fold over a prefix, log overrides) | ClockDAG, helm at 3-7k rows/day, any long-running node | packing only; H "Not implemented" (STO-010) | D13 anti-resurrection summary, `fold-id`, invalidate-and-recompute (#17 C1-C6) |
| Statements / attested claims | helm premises, Mini receipts, identity evidence | Statement record in `objects.md`; key and verdict evidence kept forever | open to applications; supersession; lookup by issuer/subject/kind |
| Replication: NNTP feeds | peers, cross-owner rooms | streaming peering, distributions, 436 backoff | INN guide (#12), IPv6 (#10) |
| Replication: BP/DTN | peers, weak devices, Robigalia | dtn7-rs exchange with receipt regeneration; one LTP feasibility run | NAT traversal; a production BP profile; F_dtn theorems unproved |
| Query: search, thread tree | readers, agents ("what did we decide about X") | XPAT over Subject/From, 2,000-article window; OVER, HDR | body search, cross-group (#1); thread JSON (#2); whether indexes live in the node |
| Metering and typed refusal | operators, every client ("software with a warranty") | capacity vector, transaction budget, named refusals, three outcomes | per-principal accounting and fairness; cost and memory bounds unproved (M6) |
| Operator observability | operators | status, health, bounded logs, decision journals, opt-in trace spans | an operation's phase, reason and held resources on the running interface; #11, #15, #16 |
| Installable release | akapug, any outside client | none published; version line restarted (next 5.1.1) | a tarball after the storage format settles; format stability or migrations |
| Conformance suite for ordering/agreement | akapug's ports | test books and native scenarios, internal | a runnable external suite |

## 5. The five questions the fn2 data model must answer

1. **What is the unit of state: an immutable record in a log, or also a
   mutable keyed object?** fn today has only the first (articles, events,
   statements) plus the Message-ID binding. "Generalized redis/postgres"
   suggests keyed, updatable state. If fn2 has it, is a key's current value a
   fold over that key's log entries (so "the log overrides" still holds and
   compaction is a summary of a fold), and what is the CAS / op-id rule that
   answers a retry `replayed`? If not, which client keeps that state, and
   where (helm's dispatch rows and cursors, Mini's inbox, Robigalia)?
2. **What are streams, and what does a cursor range over?** Today a group is
   a stream and a consumer reads exactly one, at the node-wide Store
   position. helm's inbox is a selection (home room, DMs, mentions from any
   room). Is the primitive a multi-stream query with a durable, versioned
   definition (CNS-011), write-time fan-out into per-agent streams, or both;
   are there competing consumers that claim entries; and what does a wait
   cost per waiter and per commit, stated as a bound?
3. **What is identity: of an object, an operation, a principal, a history?**
   Message-ID, content digest, `(history, incarnation)`, `(application,
   operation)`, login, key. Which of these does the node itself enforce
   (uniqueness, conflict, `replayed`), which are carried opaquely for the
   application, and how do principals delegate narrowed rights (akapug need
   #3, Robigalia's capabilities) instead of the operator socket being the
   only strong authority?
4. **What does the node promise to keep, for how long, and what may replace
   it?** Every durable class needs a lifetime, a removing capability and an
   obligation (STO-010). For fn2 at chat volume: which obligations are
   built in (archive, forward, checkpoint) and which are application kinds
   (owed reply, undertaking); does reclamation return the transaction budget;
   what is the anti-resurrection summary (D13) that lets identities outlive
   bodies; and is a checkpoint exactly #17's claim, `(prefix-head, fold-id,
   summary-digest, identity-commitment)`, released by pins and overridden by
   committed log?
5. **What is the wire and the semantic boundary?** NNTP is one convention
   over the store; the consumer surface rides a local control socket; BP
   carries portable objects; Robigalia will want something below both. Which
   operations are F_node ports (fn2 must add consumer, account and
   configuration ports), which wire carries them remotely with TLS and the
   login it posts with, what is the per-node order a client may rely on
   (helm needs per-room single-writer order, not global consensus), and what
   is the convergence claim across nodes (validated fact sets, OBJ-004)?
