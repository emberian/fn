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
committed view when it opens and keeps it until the host advances it; its
NNTP session runs `fn-nntp-step` against the pinned archive and never against
the live node.

Events: `(:open)`, `(:read id wire-event)`, `(:advance id)`, `(:close id)`,
`(:begin id)`, `(:store fn-snrt-event)`, `(:complete)`,
`(:reopen frontier records)`, `(:observe clock-observation)`,
`(:declare-group name)`. Every store transition, including the resolution
transitions, goes through the proved `fn-snrt-step`; completion is the actual
`fn-sn-finish`.

## Keystones

Each row names the property, its hypothesis stack and the covered scope, in
that order. Counts live in the generated ledger.

| Keystone | Property | Hypotheses | Covered scope |
| --- | --- | --- | --- |
| `fn-own-reader-sees-pinned-prefix-replay` | The effects a reader step produces are those of `fn-nntp-step` on the connection's session against `fn-node-acceptance` of `fn-sf-replay-node` over the first `version` durable records at the pinned frontier | `fn-own-relation`, the connection exists | One `fn-own-read-step`, the call `fn-owner-chunk` makes for every wire event |
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
with a post between them answering `GROUP fn.letters` differently, a stalled
reader that stays pinned through a second post, a close, an exact-image
reopen after which a fresh reader sees version 2, and the whole sequence as
one `fn-own-run` trace. One `must-fail` per hypothesis per keystone, as
concrete instances with that hypothesis dropped.

## Host

`tools/run_owner.py` is a single-threaded event loop. Loopback NNTP
connections are served one wire event per `fn-owner-chunk`; a peer that does
not consume its output stops being read once its backlog reaches 64 KiB and
costs nothing else, so a stalled reader cannot block a post. The control
channel is a Unix socket with one request line per connection: `POST`,
`VERSION`, `CONNECTIONS`, `ADVANCE <id>|ALL`, `OBSERVE`, `DECLARE-GROUP`,
`QUIT`. `run_store.py post --owner <socket>` is the thin client; the reply
line maps to the CLI exit codes of [the host spec](host.md) (committed 0,
refused 1, uncertain 3, fault 4). A post through the owner is the same
`post_article` sequence the plain CLI runs, with the owner bridge reporting
each observation as a `(:store ...)` event.

Clock observations come from `time.monotonic_ns` and `time.time_ns` (DTN
milliseconds) with the configured `--clock-error-ms` half-width, supplied
before every post and control command. `fn-own-observe` accepts only a later
observation of the same clock (`fn-clock-later-observationp`); a wall reading
that moves the earliest admissible time backwards is rejected and reported.

Host-only, outside the proof: socket I/O, the per-connection wire staging
(`fn-wire-initial-state 510 8192`, as in the reader), the output backlog
bound, the control line grammar, the clock readings themselves, and the
decision to advance a connection. The group-fact log is kept in the owner
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
