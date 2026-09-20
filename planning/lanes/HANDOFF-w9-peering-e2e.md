# Handoff: w9/peering-e2e (the peer CLI, the per-peer scheduler, the owner's transit port)

Branch `w9/peering-e2e` from `dev` at `52eb0db`, worktree
`build/lanes/w9-peering-e2e`. Spec: [`specs/peering.md`](../../specs/peering.md);
its wave-9 status section is the per-item record and the list of what is
open. Siblings whose books this lane did NOT edit: `books/peer-config.lisp`,
`books/peer-inbound*.lisp` (w6/peering-inbound-2), `books/peer-feed*.lisp`
(w6/peering-feed), `books/scheduler.lisp` and `books/scheduler-invariants.lisp`
(unedited on purpose, see the finding below).

## What exists

| File | What |
| --- | --- |
| `bin/fn` (edit) | `fn peer add|remove|list` with the record's fields as options; `add`/`remove` refuse while an owner holds the store (a configuration record needs the writer lock), `list` is read-only. |
| `tools/run_store.py` (edit) | `Acl2Store.set_peer` / `remove_peer` / `peer_names` / `peer_slot_text` / `peer_slot_nat`; `command_peer`, `peer_listing`, `peer_arguments`; the `peer` subcommand. |
| `host/store-node-host.lisp` (edit) | `fn-store-cfg-peer-record` (builds the record with `fn-cfg-peer-make`, `nil` when `fn-cfg-peerp` is false), `fn-store-cfg-peer-delta-record` (the admissibility test and the encode `group create` uses), `fn-store-cfg-set-peer`, `fn-store-cfg-remove-peer`, `fn-store-cfg-peer-names`, `fn-store-cfg-peer-slot-text`, `fn-store-cfg-peer-slot-nat`. Now includes `../books/peer-config`. |
| `books/scheduler-peers.lisp` (new) | the per-peer scheduler as a table of `fn-sched-statep` keyed by peer name: `fn-sched-tablep`, `-find`, `-boundp`, `-put`, `-peers`, `-install`, `-forget`, `-step`, `-tick`; keystones `fn-sched-table-tick-is-the-peer-tick` (subject rule), `fn-sched-table-tick-touches-only-its-peer`, `fn-sched-tablep-of-table-tick`, and the per-peer retry bound transported from `fn-sched-retries-stay-within-the-contact-bound`. |
| `tests/acl2/scheduler-peers-tests.lisp` (new) | two peers with different queues, the subject rule on the witness, isolation (the other peer's retries and tick are untouched), and one violating value per hypothesis (unbound peer, keyword key, non-state value, duplicate-key table, `other = peer`). |
| `books/owner.lisp` (edit) | `fn-own-open-peer o peer cfg`, `fn-own-transit-subp`, `fn-own-transit-inflightp`, `fn-own-transit-outcome o id kind reason word`, step arms `(:open-peer peer cfg)` and `(:transit-outcome id kind reason word)`. No existing function, arity or statement changed. |
| `books/owner-invariants.lisp` (edit) | `fn-own-take-installs-the-queued-submission-whatever-it-carries`, `fn-own-transit-outcome-touches-only-its-connection`, `fn-own-transit-outcome-needs-a-transit-submission`. |
| `host/owner-host.lisp` (edit) | `fn-owner-peer-for-address`, `fn-owner-open-peer`, `fn-owner-transit-decide`, `fn-owner-transit-outcome`, `fn-owner-transit-kind/reason/evidence`; `fn-owner-take` answers `:taken-transit` beside `:taken` and exposes `fn-owner-submit-transitp` / `-peer`. |
| `tools/run_owner.py` (edit) | the role is decided at accept (`peer_for_address` then `open_peer`); `drain` branches on `taken-transit` into `transit()`, which asks ACL2 for the transfer decision, runs the same durable path on `:want`, and feeds the outcome back. |
| `tools/twonode_gate.py` (edit) | a real peer record on each node through the CLI, `peer list` checked, and the RFC 4644 streaming half asserted on the transferred article (CHECK 438, TAKETHIS 439). |
| `tools/inn_lab.py` (edit) | `fn_peer_record()`: the fn node writes a peer record for INN (source address `127.0.0.1`, `--streaming`) before it starts. |
| `Makefile`, `specs/peering.md`, `planning/deputies/BOARD.md` | the two new roots; the wave-9 status section; three CHANGE entries and one NOTE. |

## The finding a successor must not undo

**The per-peer scheduler cannot be a peer field on `fn-sched-item`.**
`fn-sched-promotion-position-decreases` (KEYSTONE) has
`(fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)` in its
*statement* and `fn-sched-aging-bound` (KEYSTONE) reaches the same test
through `fn-sched-eligible-runp`. Both are peer-blind. Filter selection by
the open contact's peer and a promoted work for another peer is neither
selected nor moved closer to the head of the promotion queue: the
conclusions fail on a reachable state, and the only repair is an extra
argument to a function named inside a keystone. `books/scheduler-peers.lisp`
keys one scheduler per peer instead; the aging bound is then per contact,
which is what it always meant.

## Certification

| Root | State | Evidence |
| --- | --- | --- |
| `books/scheduler-peers` | certified | persvati `run-20260920T180716Z-da35`, `build/acl2/certify-20260920T180719Z-1531308` |
| `tests/acl2/scheduler-peers-tests` | certified | same run |
| `books/owner`, `books/owner-invariants` | **uncertified, blocked on two other lanes' open forms** | persvati `run-20260920T180927Z-a8a4`, evidence `build/acl2/certify-20260920T180931Z-1553858`: 29 books published, and exactly six failed. Two are root causes and neither is this lane's: `books/peer-config` fails at `DEFTHM FN-CFG-SET-PEER-DELTA-IS-ADMISSIBLE` (the form w6/peering-inbound-2 has already closed on its own branch, commit `3901d55`, not yet on dev) and `books/nntp-effects` has no certificate on dev: in THIS run it was cut by the runner's 1800 s per-invocation cap (its log stops inside the XOVER block), and in w5/owner-followups' 5400 s run it reached a real verdict and FAILED at `fn-nntp-hdr-labelled-line-is-block-text`. So the owner is not one long run away: `books/nntp-effects` is genuinely open and `books/peer-inbound` includes `nntp-post` which includes it. The other four are cascades: `peer-inbound` and `nntp-post` include them, `served` includes `peer-inbound`, `owner` includes `served`. **Nothing in this lane's owner edits has been refuted or confirmed**; the books were never reached. |
| everything else touched | host and Python only | `make check` green; `tests/test_twonode_gate.py` 19 tests pass |

`tests/test_inn_lab.py` has one error on this branch and the SAME error on
dev (`inn_start`, the nnrpd pid parse, `IndexError`): pre-existing, verified
by running it in the dev checkout, not caused by this lane.

## What is open, with the obligation each needs

1. **Certify the owner, after merging the two open forms.** Merge
   `w6/peering-inbound-2` (its `fn-cfg-set-peer-delta-is-admissible` fix) and
   whatever closes `books/nntp-effects`, then
   `python3 tools/farm.py submit persvati --jobs 6 --remote-root
   /home/ember/fn-lanes/w9-peering-e2e --closure books/owner
   books/owner-invariants tests/acl2/owner-tests`. Until those two land, no
   run of this lane's owner books can reach a verdict: they are six levels
   above the failing forms. Use `--timeout-seconds 5400` when you do:
   `books/nntp-effects` needs about 2600 s and is cut silently at the default
   1800 s, which reads as "no certificate" rather than as a failure.
2. **Teeth for the owner's three transit theorems.** `tests/acl2/owner-tests.lisp`
   needs a transit submission witness (a `(:transit peer kind msgid octets)`
   at the head of the queue) and one violating value per hypothesis. Not
   written in this lane.
3. **Milestone 3, the feed driven by the owner.** `books/peer-feed.lisp` had
   not landed on dev at this HEAD. When it does: `fn-own-tick` runs
   `fn-sched-table-tick` for each configured peer and `fn-feed-tick-step`
   under that peer's contact, with the FNFD journal durable before the offer,
   and `tools/run_feed.py` folded into the owner's loop (one process, one
   store lock).
4. **Milestones 4 and 5's outbound halves.** K5's crash-replay evidence and
   the gate's A-feeds-B scenario both need the feed; today the gate's
   offering side is its own socket client, which is stated in the evidence
   and in the spec's status table.
5. **K6 and K7.** K6 restates `books/ideal.lisp`'s robustness theorems over
   the peer event kinds (`(:open id peer)`, `:feed-octets`, `:tick`); K7 is
   `fn-cfg-peer-delta-preserves-the-node-and-changes-only-decisions` at the
   node level (`fn-cfg-peer-deltas-change-only-peers` is the certified
   value-level half).
6. **`(:principal id)`** is reserved in the record and matches nothing at
   accept: identity is the configured source address and A-PEER stands.
