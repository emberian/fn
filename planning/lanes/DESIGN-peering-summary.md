# Design summary: peering as a port of F_node (wave 4)

Lane `w4/peering-design`, branched at `ca66782`. Deliverable:
[`specs/peering.md`](../../specs/peering.md). No certification ran; every
ACL2 form there is a statement to be proved, using existing names exactly.

## The design in one paragraph

Peering is a transit interface on the same listener as the reader: IHAVE
(RFC 3977 §6.3.2) and CHECK/TAKETHIS streaming (RFC 4644), inbound and
outbound, as F_node events and effects. Inbound ends in the one acceptance
path every article takes: `fn-peer-transfer` computes the injection arguments
from the received octets and calls `fn-node-prepare`; the `239`/`235` is
answered only on the store's `:durable` completion. The article bytes are
stored exactly (D01); the RFC 5537 §3.2.1 Path prepend is *rendered* on the
way out from a `(:peer-transit peer diag generation)` evidence value, so no
signed source is rewritten and no relaying-agent rule (§3.6: only Path and
Xref may change) is broken. The peer table is a typed configuration record
(`fn-cfg-peerp`, deltas `:set-peer`/`:remove-peer`) under reconfiguration;
the DTN relay is the same profile with the same decision function, record,
history predicate and loop check, over a different convergence layer.

## Decisions worth arguing about

- **History is the store plus its bindings.** `fn-node-bindings` is consed on
  every durable completion and never removed by release, so it is the
  tombstone D13 asks for; no separate history file, no date cutoff, exact
  duplicate suppression across restart (`:date-cutoff` reserved, unreachable).
- **Three outcomes survive RFC 4644's two-code TAKETHIS.** Accepted `239`,
  refused `439` with the typed reason, uncertain `400` and close: the only
  RFC-honest retry-later signal after the bytes have arrived. IHAVE gets
  `436` because that code exists.
- **Capacity: defer at offer, refuse at transfer.** `431`/`436` before the
  bytes (the peer retries after a capacity raise), `437`/`439` after them
  (RFC 3977 lists disc space among rejections), reason journaled.
- **Exactly-once is a journaled decision, not a wire guarantee.** The FNFD
  feed journal records offer/sent/outcome per attempt; after a crash an
  in-flight entry is resolved by CHECK, whose `438` is the peer's history.
  At most one accepted outcome per (peer, msgid); never a blind TAKETHIS.
- **Peer deltas change decisions, not state.** Reconfiguration §3.7 stays
  true (acceptance, retention, bindings equal); this design adds the sentence
  that future transit decisions differ (K7).

## Seven keystones

K1 peering refines acceptance (transit node = post-path node on ACL2-computed
arguments; an accepted transit article satisfies every acceptance premise);
K2 loop freedom (Path names us → refused; never offered to a peer Path
names; rendering only prepends); K3 merge (two nodes peering both ways
converge to `fn-exchange-merge` of their initial fact sets, hence to each
other by `fn-exchange-merge-commutative-member`; lace twin via
`fn-lace-merge-commutative-ids`); K4 duplicate suppression complete and
restart-proof; K5 feed exactly-once under crash-then-replay; K6 the
served-path robustness theorems restated over the new events with one extra
cost term; K7 peer reconfiguration. Teeth per hypothesis, with the witnesses
that must not be degenerate: two-group article with one membership,
identity in the middle of a three-entry Path (and the tail-entry/`.POSTED`
acceptances), a `438` in the merge run, a released-but-tombstoned article, a
crash after the third `feed-sent` of five.

## INN interop

INN 2.7.x under `/tank/fn/inn` on hbox (tag, sha and tarball digest pinned
in `tests/inn/pin.json`), `incoming.conf` and `newsfeeds`/`innfeed.conf`
configured both ways, eleven scenarios: IHAVE, pipelined CHECK/TAKETHIS,
INN→fn, duplicate, `435`/`438`/`437`/`439` policy paths, loop both
directions, throttle/backoff both directions, fn killed mid-feed and
mid-transfer. The evidence record quotes INN's `history` and `news.notice`
lines, fn journal digests, and what was not shown.

## Inter-agent

Agents are principals; posts are signed statements over exact source bytes;
peering carries them unchanged through INN. Reserved now: header fields
`FN-Statement` and `FN-Policy`, the `(:peer-transit ...)` evidence value,
the `:statement` exchange kind, and a `(:principal id)` peer auth slot.
Equivocation is detected at merge by `fn-lace-reissue-detected-after-merge`;
a relayed policy change needs the authority's signature.

## Packets and dependencies

K0 registry → K1 inbound (service integrator) and K2 outbound feed (scheduler
owner) in parallel → K3 peer config (after reconfiguration R2) → K4 INN lab
on hbox → K5 history index and cost → K6 BP unification → K7 merge theorem →
K8 inter-agent reservation. Depends on w4/post (authored-source projection,
`(:post)` transfer value), w4/served-path (F_node books, refusal
enumeration), w3/scheduler (contacts and ticks), w2/mutable-owner (single
pending slot, connection pins), reconfiguration R2+ (`fn-node-config`,
`cfg-gen`).
