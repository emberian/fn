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

## K5 ran

Gate `2c27ef6` on persvati, 130 steps. Node B stopped; node A accepts
`<fed-restart@example.invalid>` by POST; **`kill -9` node A**; both nodes
restart on their pinned ports.

| row | value |
| --- | --- |
| A's FNFD journal names the queued article, before the kill | 1 |
| B receives it after A's restart | `220 0 <fed-restart@example.invalid> article follows`, attempts=1 |
| octets B serves against octets A serves | identical=True |
| **B's own store, before the kill and after** | `fn.letters` **6 articles -> 7** |
| the wire in front of B | `MODE STREAM; CHECK <fed-restart@example.invalid>; TAKETHIS <fed-restart@example.invalid>` |
| offers / article blocks / accepted / refused-as-duplicate | **1 / 1 / 1 / 0** |
| A's restart log | `FEED b replayed 11` |

The offer is a `CHECK`, never a blind `TAKETHIS`. "Exactly one copy" is a
count in the receiver: a reread cannot tell one copy from two, because the
store refuses the second and the reread looks identical either way. The
negative the keystone claims -- no duplicate transfer -- is asserted and
holds.

Two defects in this lane's own teeth were found by that run and are fixed
rather than accommodated: `S< 238` was being counted as an article block
(it is permission to send, not a send), and the scenario never recorded
that node A holds what node A posted, so a later step asserted A did not
hold it -- an assertion only a working feed could expose as false.

## Open, each with what closes it

| Item | What closes it |
| --- | --- |
| `CAPABILITIES` names neither `IHAVE` nor `STREAMING` on a transit connection | `fn-peer-capability-lines` exists, is proved and is **unreachable**: `fn-auth-step` answers `CAPABILITIES` at `books/nntp-auth.lisp:786`, above `fn-peer-step`. `fn-auth-capability-lines` must build on the peer list with the record from `(fn-peer-session-peer (fn-auth-session-base as))`, and `fn-peer-command`'s arm is then removed. The arity change restates the four hint sites at `books/nntp-auth.lisp:932,1272,1281,1290`, and `tests/test_owner.py::test_the_capability_block_does_not_yet_name_the_transit_commands` is the test that says the day it changes. |
| A second offer in one session draws `335`/`238` rather than `435`/`438` | unchanged from `w11/twonode-feed`: the session pins the node at open. Whoever owns `specs/peering.md` §2.2 decides whether the offer-time history reads the live node. |
| `--tree` does not change the deploy directory | `tools/deploy_gate.py:485` has no tree in the path while the lock at `:590` does, so two gates at one revision on one host `rm -rf` each other. Putting the tree in the path moves `tests/test_deploy_gate.py:153`, `tests/test_scale_gate.py:232`, `tests/test_twonode_gate.py:119,173` and `docs/interop-inn.md:27`; a guard step before the ship moves the step counts the self-tests pin. |
| `fn-feed-replay-is-the-live-feed-modulo-inflight` (§4 K5) | the live machine that emits its own journal now exists; the general equation does not. No theorem relates a crash image of the feed file to the live feed. |
| **A post through the control channel feeds nobody** | `drain` flushes the feed records for the served POST and the transit path, which are the two that reach `fn-own-outcome`. The control channel's `POST` calls `post_article` (`tools/run_store.py:1826`) straight down the durable path and never calls `fn-owner-outcome`, and `fn-own-feed-durable` has exactly two callers, `fn-own-outcome` and `fn-own-transit-outcome` (`books/owner.lisp`). So an article an operator posts through `fn post` on a running node becomes durable and is **never offered to any peer**. Not this lane's, and not observed on a wire here -- it is read off the call graph. What closes it: the control POST goes through the owner's queue and outcome, as a served POST does, rather than round the side of it. |

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
