# The mutable service owner

Status: executable model in [`books/owner.lisp`](../books/owner.lisp), keystones
in [`books/owner-invariants.lisp`](../books/owner-invariants.lisp), witnesses
and teeth in [`tests/acl2/owner-tests.lisp`](../tests/acl2/owner-tests.lisp).
The host is [`tools/run_owner.py`](../tools/run_owner.py) over
[`host/owner-host.lisp`](../host/owner-host.lisp). This is packet C1-05 of
[the swarm cycles](../planning/swarm-cycles.md); it fills the "Owner events
and effects" contract row for connection/generation, committed view version,
one pending transaction and read pin lifetime. Submission identity and
partial-output tracking stay with their own packets.

## Native owner integration checkpoint

The native adapter is `host/native/owner.lisp`, loaded by the common saved
image. It calls the same `host/owner-host.lisp` entries over one exclusively
owned Store and persists the shared submission's FNFD intent/resolution before
releasing the corresponding effects. The frozen `03eb3ba3` default/DTN
image batch has scoped native runtime evidence in
[the integration report](../planning/evidence/native-owner-integrated-2026-09-21.md).
Later native control changes have separate
[source-pinned evidence](../planning/evidence/native-control-accept-shutdown-2026-09-21.md);
neither result is a complete native deployment gate. The Python-host evidence
below does not certify this adapter.

`fnn-owner-serialized` holds the service mutex across a semantic operation and
installs a global stop before releasing it on uncertain persistence or a core
fault. Later open/read/close mutations check the same stop under that mutex.
Owner and control listeners share a bounded nonblocking accept observer;
SIGTERM sets a monotonic request that an ordinary owner thread consumes.
Shutdown wakes connected clients without closing descriptors underneath their
workers, then joins those workers before closing shared
journals or the Store. `tests/test_native_owner.py` contains the two-client
postpublication injection: the ambiguous article may recover, but the second
client must not obtain a fresh posting grant. Its passing frozen-image scope
is recorded in the integration report above.

This global boundary applies to uncertain shared state and core failure. It
does not replace HST-005's connection-local fault isolation contract: an
attributable failure that leaves the shared state valid must still use
`fn-own-fault` and preserve other connections. The native adapter currently
stops the process for an unexpected serious condition; the scoped survival
scenario still needs native adoption. ACL2's connection-local theorem alone
does not justify continuing after shared-state corruption, and stopping every
connection does not discharge that survival requirement.

Safe FNFD filename adoption and the public operator/auth callback are
integrated. Outbound feed/timers and TLS remain integration work. The native
public operator reaches the local control socket
through `books/native-control.lisp` and `host/native/control.lisp`; its exact
article enters `fn-owner-control-submit` under `fnn-owner-serialized` and then
uses the same durable FNFD intent, Store attempt and resolution sequence as a
served submission. Configured posting disablement is installed in the owner's
one injection configuration and therefore refuses both ordinary NNTP and
control admission.

The local transport is one bounded sealed FNCT request and one bounded sealed
reply per AF_UNIX connection. ACL2 owns the frame grammar, maximum sizes,
Message-ID/group validation, status classes and exit codes. Raw Lisp reads one
regular payload file, moves bounded octets, and performs socket lifecycle only.
Failure before request handoff is refused; loss after handoff is uncertain,
because the missing reply cannot distinguish durable acceptance from a request
the owner never observed. Before removing a stale socket node, the service
holds an exclusive lock on the ACL2-derived adjacent `.lock` path; another
Store configured with the same control path is refused and cannot steal the
live endpoint. The persistent lease inode is not unlinked; this argument, like
the socket node itself, assumes the configured parent directory excludes an
independent attacker that can replace entries. Stop hooks use shutdown only to
wake connection owners, which perform the final close before the close hook
releases the lease. The control adapter never opens the Store.

HST-002 also requires bounded active control clients, one absolute receive
deadline per frame and linear input accumulation, including one-byte reads.
These resource obligations are not yet met by the integrated transport, which
resets its timeout per read and copies its retained prefix repeatedly. The
assigned followup must enforce ACL2-projected limits before thread creation
and byte consumption; a socket backlog is not an active-client bound. SCN-015
tracks these cases separately from the completed endpoint/lifecycle witnesses.

## What the owner is

One process owns one store. It holds the exclusive writer lock
(`run_store.Store`, `writable=True`), reopens the store through
`fn-sn-open-observed` exactly as the CLI does, and then drives the owner
machine `fn-own-step` over the state `fn-own-start` built from that reopen
(`fn-owner-recover`). The owner state carries the live `fn-sn` composition,
the committed view, the open connections, the pending transaction owner, a
proof-only completion ledger, the latest clock observation and the group
configuration facts.

The committed version is the generation: the length of the durable record
history. The committed view is refreshed only when the store is at an idle
phase, where [`fn-snt-relation`](../books/store-node-traces.lisp) says the
live node is the exact replay of the durable records. A connection pins the
committed view when it opens and keeps it until the host advances it. Each
connection carries one served connection (wire framing state, NNTP session,
pinned archive; [`books/served.lisp`](../books/served.lisp)): the served
port `fn-own-read` is one `fn-served-step` per socket read over that
connection, never over the live node, and `fn-own-read-step` is its
per-event law (one `fn-nntp-step` against the pinned archive).

Events: `(:open)`, `(:octets id octets)` (the served port),
`(:read id wire-event)` (its per-event law), `(:advance id)`, `(:close id)`,
`(:begin id)`, `(:store fn-snrt-event)`, `(:complete)`,
`(:reopen frontier records)`, `(:observe clock-observation)`,
`(:declare-group name)`, and `(:outcome id outcome)`, reserved for the POST
fold (w4/post) and a no-op until it lands. Every store transition, including
the resolution transitions, goes through the proved `fn-snrt-step`;
completion is the actual `fn-sn-finish`.

Records are opaque (`docs/proof-style.md` section 1): the owner, the view,
the connection and the group fact each have a shape predicate, a
constructor, total accessors and exported record lemmas. The served port and
the connection events are guard `t` verified; the store events carry
`(fn-sn-statep (fn-own-store o))`, the invariant their callees carry, and
`fn-own-complete` is verified. `fn-own-store-step`, `fn-own-step` and
`fn-own-run` are declared but not verified because `fn-snrt-step` (store) is
not guard verified; that is an open item below.

## Keystones

Each row names the property, its hypothesis stack and the covered scope, in
that order. Counts live in the generated ledger.

| Keystone | Property | Hypotheses | Covered scope |
| --- | --- | --- | --- |
| `fn-own-read-is-served-step-on-pinned-prefix` | The effects one socket read produces are those of `fn-served-step` over the connection's wire and session and `fn-node-acceptance` of `fn-sf-replay-node` over the first `version` durable records at the pinned frontier | `fn-own-relation`, the connection exists | One `fn-own-read`, the call `fn-owner-chunk` makes for every socket read |
| `fn-own-read-is-served-step-on-pinned-prefix-after-any-trace` | The same equality on the state after any finite owner-event list | `fn-own-relation` at the start, the connection exists at the end | Every reachable owner state |
| `fn-own-reader-sees-pinned-prefix-replay` | The effects of one framed wire event are those of `fn-nntp-step` on the connection's session against the same pinned-prefix archive | `fn-own-relation`, the connection exists | One `fn-own-read-step`: the per-event law of the served port (`fn-served-step` is `fn-wire-drive` then the fold `fn-served-nntp-run` of `fn-nntp-step`, `books/served.lisp`); the host calls `fn-own-read` |
| `fn-own-reader-sees-pinned-prefix-replay-after-any-trace` | The same equality on the state after any finite owner-event list | `fn-own-relation` at the start, the connection exists at the end | Every reachable owner state |
| `fn-own-completion-consumed-once` | `fn-own-complete` is idempotent on the whole owner: a second completion consumes nothing and appends nothing | none | Every owner state; the ledger grows by the kernel's own `fn-sf-completion` pair exactly once per `:completing` phase (`fn-own-complete-ledger-is-exact-pair`) |
| `fn-own-pinned-prefix-survives-any-trace` | The prefix of the durable history a connection pinned is unchanged after any finite trace, reopen included | `fn-own-relation`, the connection exists at the start | Records only grow along owner traces (`fn-own-run-records-prefix`); nothing below a pin may be reclaimed |
| `fn-own-reclaim-floor-below-every-pin` | The compaction floor (lowest pinned version) is at or below every pin | `fn-own-relation`, the connection exists | The invariant compaction must respect; compaction itself does not exist yet |
| `fn-own-connections-bounded-after-any-trace` | At most `max-conns` connections; each session is `fn-nntp-sessionp` with a configured group name or nil and a cursor inside RFC 3977 section 6's range or nil | `fn-own-relation` | Every reachable owner state; a step whose session leaves the bound closes that connection |
| `fn-own-completed-post-survives-close-and-any-trace` | A pair the owner consumed as a completion has a record in the durable history after any finite trace: close, crash, reopen through `fn-sn-open-observed` under `fn-sf-crash-imagep`, more posts | `fn-own-relation`, the pair is in the ledger | Post-then-disconnect durability; A-DURABILITY enters as the `fn-sf-crash-imagep` hypothesis of `(:reopen ...)` |
| `fn-own-run-preserves-relation`, `fn-own-run-preserves-store-relation` | Every step and every finite trace keeps `fn-own-relation`, hence `fn-snt-relation` on the embedded store | `fn-own-relation` | All ten events |
| `fn-own-open-observed-start-relation` | The owner started over a successful `fn-sn-open-observed` satisfies the relation | `fn-sn-open-okp`, `natp max-conns` | The host root, `fn-owner-recover` |
| `fn-own-every-fact-is-clock-stamped`, `fn-own-declare-group-without-clock-is-refused`, `fn-own-declared-group-is-replayed` | A group-configuration fact carries the clock observation current when it was created; none is created without one; the live group view is the replay of the fact log | `fn-own-relation`; a clock observation present | The fact record kind and its replay |

Witnesses (`tests/acl2/owner-tests.lisp`): two readers at versions 0 and 1
with a post between them answering `GROUP fn.letters` differently through
the served port and through its per-event law, a read cut inside the command
line, a stalled reader that stays pinned through a second post, a close, an
exact-image reopen after which a fresh reader sees version 2, and the whole
sequence as one `fn-own-run` trace. One concrete violating value per
hypothesis per keystone, each an `assert-event` on the negated conclusion.
Recorded open there: the connection-exists hypothesis of
`fn-own-pinned-prefix-survives-any-trace` has no violating value (an absent
connection makes both sides `nil`), so it is unnecessary and stays only
because the statement is frozen this wave.

## Host

`tools/run_owner.py` is a single-threaded event loop. Loopback NNTP
connections are served one socket read per `fn-owner-chunk`, which is one
`fn-own-read`; the reply stream and the close verdict are the book's two
projections of the effect list (`fn-served-reply-octets`,
`fn-served-closingp`). A peer that does not consume its output stops being
read once its backlog reaches 64 KiB and costs nothing else, so a stalled
reader cannot block a post. The process root `fn-owner-recover` dispatches
on `fn-sn-open-kind` under `fn-own-open-kind-ok-is-okp`, never on
`fn-sn-open-okp`, so no whole-state recognizer runs per recovery. The control
channel is a Unix socket with one request line per connection: `POST`,
`VERSION`, `CONNECTIONS`, `ADVANCE <id>|ALL`, `OBSERVE`, `DECLARE-GROUP`,
`QUIT`. `run_store.py post --owner <socket>` is the thin client; the reply
line maps to the CLI exit codes of [the host spec](host.md) (committed 0,
refused 1, uncertain 3, fault 4). A post through the owner is the same
`post_article` sequence the plain CLI runs, with the owner bridge reporting
each observation as a `(:store ...)` event.

Clock observations come from `time.monotonic_ns` and `time.time_ns` (DTN
milliseconds) with the configured `--clock-error-ms` half-width, supplied
before every socket chunk and every control command. `fn-own-observe`
accepts only a later observation of the same clock
(`fn-clock-later-observationp`), and it answers with one of three distinct
words that the host reports and does not compute ([D10-a](../planning/decisions.md)):

| Outcome | When | What the owner keeps |
| --- | --- | --- |
| `observed` | a later observation of the same clock, which includes a reading **equal** to the one held | the new reading |
| `refused` | the monotonic counter went backwards, `has-wall` changed, or a widened error bound moved the earliest admissible true time back | **no clock at all** |
| `invalid` | the message carried no observation | the reading it had |

A refusal costs the owner its clock because the host has contradicted the
clock it was reporting, and [the clock spec](time.md) allows a node that
discovers its clock was wrong to stop being sure. With no clock the owner
refuses to inject (`441 posting failed; this server has no usable clock
reading`), refuses to create a group fact, and answers DATE with `503 no
clock observation supplied`; facts already created keep the stamps they were
created under. Recovery is one event: with no clock held, the next reading
is admitted whatever it says. The cost is stated in D10-a, including the
generated Message-ID a node may re-mint after a backwards correction, which
the durable path refuses as the duplicate it is.

Host-only, outside the proof: socket I/O, the output backlog bound, the
control line grammar, the clock readings themselves, and the decision to
advance a connection. The wire framing state is inside the owner's
connection record, not in the host. The group-fact log is kept in the owner
process and is not yet persisted to disk: persistence of facts as a durable
record kind is the open item below.

## Open items

- Persist the group-configuration fact log through the record kernel so a
  reopen replays it; today `(:reopen ...)` keeps the in-model facts and the
  host process loses them.
- `fn-nntp-step` is not proved to preserve `fn-nntp-sessionp`; the owner
  fails closed by closing a connection whose stepped session leaves the
  bounded set. Proving preservation in `nntp-invariants` would make that
  branch unreachable.
- `tools/run_reader.py --store` keeps its shared-lock snapshot path and
  cannot run alongside an owner on the same store; making it a thin client
  of the owner is the next step once partial-output tracking (HST-002) lands.
- `fn-own-store-step`, `fn-own-step` and `fn-own-run` are not guard verified:
  `fn-snrt-step` and `fn-snt-step` (store) have no guard and call
  transitions that carry `(fn-sn-statep s)`. Store gives the dispatchers
  that guard and verifies them; the owner then verifies its three.
- The relation does not carry `fn-served-connp` per connection, so the owner
  does not yet inherit `fn-served-step-effects-are-typed`; carrying it needs
  the served port to refuse a non-octet read (`fn-wire-octet-listp`), which
  the host never sends.
- The POST fold (w4/post): the served step will produce a submission effect;
  `Owner.submit` in `tools/run_owner.py` runs the durable path for it and
  feeds the outcome back through `fn-owner-outcome` / `(:outcome id outcome)`,
  which the book ignores until the fold gives it a meaning.
