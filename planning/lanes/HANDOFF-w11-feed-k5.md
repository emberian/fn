# Handoff: w11/feed-k5 (finishing K5, and the three things in front of it)

Branch `w11/feed-k5` from `dev` at `1e29d82`, worktree
`build/lanes/w11-feed-k5`. Spec: [`specs/peering.md`](../../specs/peering.md)
§3 and §4 (K5). Evidence:
[`planning/evidence/feed-k5-w11-2026-09-21.md`](../evidence/feed-k5-w11-2026-09-21.md),
with the gate records `twonode-15ac399-2026-09-21.md` and
`twonode-2c27ef6-2026-09-21.md` beside it.

The predecessor lane ([`HANDOFF-w11-twonode-feed.md`](HANDOFF-w11-twonode-feed.md))
got an article across between two fn nodes and named two blockers in front
of K5's `kill -9` restart-by-offer. Both are closed. A THIRD was under
them, invisible until they were, and it is the one that actually stopped
the article.

## 1. The 90-second accept refusal: a connection leak, and a silent refusal

**Cause.** The owner never released a connection the BOOK told it to close.
`fn-served-closingp` is true of the effects after QUIT's `205`;
`tools/run_owner.py` set `conn.closing`, armed the socket for write, stopped
reading it and never called `drop()`. The socket stayed open, the selector
spun on it, and the entry stayed in `fn-own-conns` for the lifetime of the
process. At the bound `fn-own-open` answers NIL and the host closed the new
socket with no greeting, no `ACCEPT-FAULT` and no log line.

**Measured, with its control.** One owner at `--max-connections 4`, reading
`(fn-owner-connections state)` after each client: four QUIT-terminated
connections leave the table holding `3:0 2:0 1:0 0:0` and everything after
reads `server closed the connection`, including a client that does not
QUIT. Same code and store, eleven clients that close WITHOUT QUIT: all
greet, table empty every time. After the fix, eleven QUIT-terminated
clients against a bound of 4: all greet, table empty every time.

**Why it was 90 seconds.** `tools/deploy_gate.py`'s `Conn.close` sends
`QUIT`; `feed.py wait` opens a connection every 0.5 s. A node at
`--max-connections 32` walls at poll 33 -- 16.5 s into a 90 s deadline,
which is what gate `0e5a7f8` recorded to the half second. Raising the
default from 8 to 32 in wave 11 moved the wall from the fourth probe to the
thirty-third.

**Fixed** (`tools/run_owner.py`): a closing connection is dropped once its
reply has left the socket; the refusal at the bound prints `ACCEPT-REFUSED`
with the count and the bound; a failure between the owner's open and the
selector registration releases the ACL2 connection; a selector registration
with no connection behind it is unregistered instead of spun on.

## 2. A lost connection requeues, per peer

`feed_drop` told ACL2 only `(:feed-conn peer nil)`, which stops selection
and resolves nothing. `fn-own-feed-lost` (`books/owner.lisp`) applies
`fn-feed-lost` to ONE peer through `fn-own-feed-lost-one`
(`books/owner-feed.lisp`): the in-flight entry returns to `:queued` with its
attempt counted and a backoff, and the connection is forgotten.
`fn-own-feed-lost-one-touches-no-other-peer` is the theorem that says it is
not `fn-own-feed-restart-all`.

The record it authorizes is `(:feed-outcome peer msgid attempt 400)` and NOT
the `(:feed-restart peer)` the predecessor's packet proposed. That is the
record a `400` on the wire already writes and the one `fn-feed-apply-record`
replays as `fn-feed-queue-requeue-inflight`, so replay reaches the state the
live machine reached; `fn-feed-restart` RETIRES the attempt where
`fn-feed-lost` counts it, and a `:feed-restart` record would therefore
diverge.

**Live on the wire, gate `15ac399`, the cut scenario:**
`MODE STREAM; CHECK <fed-cut@…>; TAKETHIS <fed-cut@…>` -- cut -- then
`MODE STREAM; CHECK <fed-cut@…>` and node B answers **`438`**. That second
CHECK is the requeue; the `438` is the peer's own history absorbing the one
retransmission a lost reply can cause, which is the whole of K5's
two-generals-honest argument, observed for the first time. Gate `a5c6792`,
on the same scenario, recorded no second offer at all.

## 3. The feed enqueue was never journaled

**This is what stopped K5.** `specs/peering.md` §3.3 writes
`(:feed-enqueue peer msgid tick)` before the entry is `:queued`. Nothing
wrote it. `fn-own-feed-durable-records` existed and **had no caller**: the
host installed the served effects of `fn-own-outcome` and not the feed
records, so a queued entry lived in memory and nowhere else until its first
offer. An article accepted while a peer was unreachable did not survive the
process that accepted it -- which is exactly K5's scenario.

`fn-own-outcome-records` and `fn-own-transit-outcome-records`
(`books/owner.lisp`) state, once and in ACL2, the condition under which the
records are owed -- the same connection, in-flight submission and `:durable`
completion the transition itself uses. `host/owner-host.lisp` reads them off
the owner before the outcome moves it and installs them; `drain` flushes
them before the loop writes the 240.

Measured: one node, a peer record naming `127.0.0.1:1`. POST answers 240 and
`<store>/feed/b.fnfd` is 135 octets naming the Message-ID; after `kill -9`
and a restart it is 184 octets and its frames are, in order, kind 6
`:feed-restart`, **kind 1 `:feed-enqueue`**, kind 6 `:feed-restart`. Kind 1
had never been on disk.

## What a successor should not undo

1. **The loss record is an outcome-400, not a restart record.** It is chosen
   so that replay and the live transition agree on the attempt count. If the
   journal ever grows a loss kind of its own, `fn-feed-apply-record` has to
   grow the matching arm in the same commit.
2. **`fn-own-feed-lost` is per peer.** `fn-own-feed-restart-all` on a lost
   socket settles another peer's genuinely in-flight entry, which is the
   second transfer K5 forbids.
3. **The host drops a closing connection.** Without it the model's
   `closing` effect is advisory and `fn-own-conns` is a leak.
