# Handoff: w11/twonode-feed (the first crossing between two fn nodes)

Branch `w11/twonode-feed` from `dev` at `19f3302`, worktree
`build/lanes/w11-twonode-feed`. Spec:
[`specs/peering.md`](../../specs/peering.md) §§1.1, 2.2, 3.2 and the wave-11
status section at its end. Evidence:
[`planning/evidence/twonode-feed-w11-2026-09-20.md`](../evidence/twonode-feed-w11-2026-09-20.md).

## What this lane found

The two-node gate had been green at 63 steps with 6 not exercised, and the
reason recorded in its evidence -- "peering: not available on this tree" --
was wrong. The transit surface was there. Four separate defects stood
between it and a crossing, and every one of them was in code that had run
green.

1. **`fn-af-proto-article-check` on both transit paths.** RFC 5537 §3.4.1 is
   the INJECTING agent's check on a PROTO-ARTICLE; its first refusal is a
   present `Injection-Info`, which every injected article carries. Applied
   in `fn-peer-decide-transfer` it refused every offer `:proto-article`;
   applied in `fn-own-feed-groups-of` it made the article's Newsgroups read
   as `NIL`, so no peer was ever a feed target. **This is why nothing had
   ever crossed.** Fixed with `fn-af-relayed-article-check` (§3.6 step 1),
   with `fn-af-proto-article-check` restated as that check behind its two
   own refusals so its value is unchanged on every input.
2. **`peer add` could never make a record.** The CLI default
   `--inbound-max-octets 1048576` is 32x `*fn-record-max-payload*`, which
   `fn-cfg-peer-inboundp` caps, so every default invocation was refused
   `:peer-record`. The default is 0 now and ACL2 supplies the ceiling.
3. **Three never-run harness defects**: `FEED_DRIVER` called an `article()`
   it never defined; neither article builder wrote a `Date`, which
   `fn-peer-decide-transfer` requires; and the gate wrote its peer records
   AFTER starting both servers, into stores under an owner's lock, for an
   owner that reads the peer table only at startup.
4. **Three type errors that ended the owner process**, all on the transit
   and feed paths: octets re-encoded in `transit_decide` (w10/v0-matrix's
   one-liner, taken here); group names as strings where the submit global
   holds octets; and `acl2_boolean` anchored at the first octet where a
   `:mode :program` error triple prints a leading space.

5. **No fn node could have a name of its own.** `fn-peer-local-identity`
   reads the configuration policy slot `path-identity`; nothing on this tree
   could write it; an unset slot reads as the empty string, which
   `fn-path-names-p` never matches. **RFC 5537 section 3.5 loop suppression
   was inert in every deployment.** And the identity had a SECOND owner:
   `*fn-owner-agent*`, a hard-coded `fn.example.invalid`, wrote Path and
   Injection-Info, so two nodes on one gate wrote the same Path and neither
   could recognise itself in the other's articles. `fn policy set|get` and
   `fn-owner-agent-of` fix both.
6. **A fifth never-run defect, found by the gate itself**: `FEED_DRIVER`'s
   `post` read its reply with `conn.read_line()` where `Conn` has `line()`.
   The AttributeError fires AFTER the article is on the wire, so the article
   became durable, the feed offered it and the peer took it -- and the gate
   recorded "POST answered 'nothing'" and skipped the wait. The wire tap is
   what caught it.

7. **The feed was altering the article body.** `Session.send_block`
   (`tools/run_feed.py`) used `rstrip(b"\r\n")` where the terminator needs
   exactly one CRLF removed, so an article whose body ends in a blank line
   arrived one line shorter. Measured, not guessed: gate `0e5a7f8` reported
   `source_lines: 11, target_lines: 10, only_on_target: [], only_on_source:
   []` in BOTH directions -- one line fewer and not one line different in
   content. RFC 5537 section 3.6 lets a relaying agent alter Path and Xref
   and nothing else.
8. **A connection could end the owner at accept.** Everything in
   `accept_nntp` can raise, and an unexpected error unwound through `run`.
   It is wrapped now: the fault is printed with its traceback so the
   diagnosis survives in the server log, and only that connection is lost
   (`ACCEPT-FAULT`). Same rule as the feed containment.

## What is in the branch

| File | What |
| --- | --- |
| `books/article-fields.lisp` | `fn-af-relayed-article-check`, and `fn-af-proto-article-check` restated over it. One new `defun`, no statement changed. |
| `books/peer-inbound.lisp` | `fn-peer-decide-transfer` and `fn-peer-injection-arguments` call the relaying check. |
| `books/peer-inbound-invariants.lisp` | the two `e/d` disable lists name the new function beside the old. |
| `books/owner-feed.lisp` | `fn-own-feed-groups-of` calls the relaying check. |
| `tests/acl2/article-fields-tests.lisp` | five assertions separating the two checks. |
| `host/owner-host.lisp` | `fn-owner-group-octet-list`: the transit memberships reach the submit global as octets, converted by ACL2 where the global is written. And the inbound bound of 0 selects `*fn-record-max-payload*`. |
| `tools/run_store.py`, `bin/fn` | `--inbound-max-octets` defaults to 0. |
| `tools/run_reader.py` | `acl2_boolean` strips like its two siblings. |
| `tools/run_owner.py` | `transit_decide` passes octets; `feed_dial` requires a 2xx greeting; `feed_poll` and `feed_read` contain a feed fault as `FEED-FAULT <peer>` instead of ending the node. |
| `tools/twonode_gate.py` | `configure_peering` (records written while the stores are free, nodes restarted on pinned ports), the `TAP_DRIVER` wire recorder with its one-shot armed cut, `deliver_by_feed`, `scenario_owner_feed_streaming`, `scenario_feed_peer_cut`, K5 teeth on the restart run, `Date` in both article builders, and `article()` defined in the driver. |
| `tools/deploy_gate.py` | facts not in `FACT_KEYS` are rendered instead of silently dropped. |
| `host/store-node-host.lisp`, `tools/run_store.py`, `bin/fn` | `fn policy set|get <slot> [value]`: `fn-store-cfg-set-policy` / `fn-store-cfg-policy`, through the same `fn-cnode-record-acceptablep` that `peer add` and `group create` use. |
| `host/owner-host.lisp` | `fn-owner-agent-of`: the injecting agent is the `path-identity` policy slot, not a constant. `fn-owner-feed-backoff-ms`: the host waits the peer record's own outbound backoff between dials. |
| `tests/test_owner.py` | `TransitPortTests` and the `OwnerFixture` split. |

## Three things a successor should not undo

1. **`fn-af-proto-article-check` keeps its name, its value and its callers on
   the POST path.** The split is additive on purpose: `books/nntp-post` and
   `books/bp-ingress` are injecting agents and must keep refusing a
   proto-article that carries `Injection-Info`.
2. **The gate restarts both nodes on their own ports.** A peer record names
   a port; an ephemeral restart silently ends the feed and the run then
   measures the wrong thing.
3. **The tap is a recorder.** It parses nothing and decides nothing. Its one
   active behaviour, the armed cut, is armed by the gate creating a file and
   disarms itself; without it there is no way to place a crash between "the
   receiver has the article" and "the sender heard the outcome".

## Open, each with what closes it

| Item | What closes it |
| --- | --- |
| `CAPABILITIES` renders the reader block on a transit connection | `books/served`'s capability list has to read the session. RFC 3977 §5.2.2. `tests/test_owner.py::test_the_capability_block_does_not_yet_name_the_transit_commands` asserts the current behaviour, so the day it changes the test says so. |
| Should a host fault on a transit connection reach the wire as the `403` fourth outcome? | A design question, not a defect: today a feed fault is contained and logged, and a served-path fault has the 403. Nothing decides the transit case. |
| **A lost connection never requeues the in-flight entry, so the feed makes no further progress for that peer until the process restarts.** | The packet, and it is small. The host drops the socket (`feed_drop`) and tells ACL2 only `fn-owner-feed-connect peer nil`; nothing applies `fn-feed-lost`, which is the transition for exactly this (`fn-feed-queue-requeue-inflight` plus a backoff deadline). What is needed is a PER-PEER restart or loss on the owner's table -- `fn-own-feed-restart-all` is wrong here, because settling another peer's genuinely in-flight entry would cause the second transfer K5 forbids -- plus the `(:feed-restart peer)` record that authorizes it, written before the state moves. Until it lands, the entry waits for `fn-own-reopen`. Measured on gate `a5c6792`: after the tap cut, node A reconnected every 5 s, sent `MODE STREAM` and offered nothing, seven times over. |
| The owner's `--max-connections` default of 8 is reachable in a two-node run | A two-node run holds a persistent feed connection each way, a tap backend session per dial, and the harness's probes. On gate `ea76826` node B refused four steps at accept. The gate runs its nodes at 32 now; whether a feed connection is released promptly, and whether 8 is the right default for a peered node, is not answered. |
| Duplicate suppression at OFFER time does not see an article accepted earlier in the SAME session | By design: the session pins the node at open and RFC 4644 2.4.2 makes an offer advisory, so a second `IHAVE` in one session draws 335 and the transfer then draws 437, and `CHECK` draws 238 and `TAKETHIS` 439. It is still a cost -- a streaming peer pays the bytes for every article it has already sent on that connection. Whoever owns specs/peering.md 2.2 should decide whether the offer-time history reads the live node, and say so either way. `scenario_feed` asserts 435/438 and so reports this as a gap. |
| `host/reader-host.lisp`'s `*fn-reader-agent*` | The same hard-coded identity this lane removed from the owner. The reader's `--post` path should read the policy slot too; not this lane's. |
| `tools/run_feed.py` | It is a second driver for `tests/test_feed.py` and its Python copy of an owner decision has drifted three times. This lane did not touch it and does not propose retiring it without measuring what `tests/test_feed.py` would lose. |
| fn does not prepend its path-identity to a relayed article's Path | unchanged from wave 10; loop suppression on the return leg rests on the peer's history answer. |
