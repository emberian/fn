# consumer-exchange (2026-09-26): two agents on two nodes

Lane consumer-exchange, wave 4 lane 12 (brief
`build/coordinator/queue/done/w4-consumer-exchange.txt`; the mandate's
sections 9 and 10; gpt-6's wave-2 review section 7). Branch
`lane/consumer-exchange` from dev 5391f1d9. Ids: PRF-177, CNS-004, SCN-106,
PKT-466, PKT-467.

## What now works

Two agents on TWO fn nodes, A and B, peered over NNTP (the streaming feed
both ways, and B also pulling A by NEWNEWS), exchange a signed report R and
reply Q across interruption. Agent A's consumer talks only to A's control
socket and B's only to B's. B verifies R with its own keyring, commits its
one transition and immutable reply Q, and acknowledges its position on B; Q
crosses back by B's feed; A verifies Q with its own keyring and correlates
it with R. The feed-and-pull repeated transfer, the lost reply, a consumer
death at every ownership cut and a node restart mid-poll produce no second
application transition. Two consumer processes on one database are refused
by a lock.

## Step 1: one consumer process per database (PKT-351), 51aa91dd

`tools/fn_consumer.py` takes an exclusive `flock` on `<db>.lock` before it
opens the database and holds it for the process lifetime; a second process
is refused (exit 1, `fn_consumer: database in use by pid N`) before it reads
anything. flock, not sqlite's `locking_mode=EXCLUSIVE`: the kernel releases
it when the holder dies (the `os._exit(97)` cuts, SIGKILL); it covers the
process from before the first read, where sqlite's exclusive mode takes its
lock at the first write and would let the second process read first; and the
holder writes its pid so the refusal names it. The lock is the client's own
bookkeeping under CNS-003, not an fn decision.

`tests/test_fn_consumer_journal.py` (9 OK on the laptop and on hbox):
`test_a_second_process_on_the_database_is_refused_by_the_lock` holds the
first process inside the stand-in's `hybrid-author` with its attempt
in flight, and the second process is refused with the holder's pid and the
attempt stays `in-flight` (without the lock the second process would have
turned it `unanswered`); after release the next process sees the answer.
`test_the_lock_dies_with_its_holder`: a process cut at `attempt-recorded`
holds nothing.

`tests/test_anchor.py` on hbox: 27 OK through `tools/hbox_native.sh`, which
now exports `FN_ACL2` (the store-command tests find ACL2 through it; no
PATH change was needed). The laptop-only note is retired.

## Step 2: the two-node exchange (PKT-333 phase 1), e6bab332

`tests/test_native_consumer_exchange_two_nodes.py`, class
`NativeTwoNodeConsumerExchangeTests`, on the developer image (the owner stop
cut is developer-only). Its own two-node helpers, modelled on
`tests/test_native_peering.py`'s (plaintext loopback peering with
source-address authentication, `peer add NAME PATH 127.0.0.1 PORT fn.* fn.*
127.0.0.1 true`, path identities `a/b.exchange.example.invalid`) and
`tests/test_native_peer_pull.py`'s `RecordingProxy` in front of A for B's
pull (`peer pull A 2`). Owner stdout goes to a file (no unread pipe). Each
author is enrolled on both nodes in the same generation order; each consumer
is registered on its own node only, with a keyring made from the authors'
public key files by `fn_verify.py keyring-entry`.

### The cases and their outcomes (hbox, both runs green)

`test_exchange_across_two_nodes_and_every_cut`:

| Case | Outcome |
| --- | --- |
| Repeated transfer: R by A's feed and listed again by B's NEWNEWS pull; then an IHAVE of R from A's address | B stores R once (`operator status` articles=1); two pull rounds complete after R's arrival with no `ARTICLE` for R through the proxy; IHAVE answered `435 duplicate` |
| Node restart mid-poll (a probe consumer on B) | the same report (sha256 `50aabca3…`) and cursor (`e185eb8d…`) re-served after B restarts; the ack twice leaves position 6 |
| Cut 1 `in-transaction` at B | B's database holds nothing; B's position 0 |
| Cut 2 `after-commit` at B (death between the claim's commit and the ack) | transition r1 and Q pending committed; ack unsent; position 0 |
| Cut 3 B's owner commits the ack, dies before replying | consumer exit 3, ack `uncertain`; B's position 6 |
| Cut 4 `before-post` | the uncertain ack settled by `position` (no second ack); Q still pending |
| Cut 5, the lost reply: B's owner stores Q, dies before answering | consumer exit 3; the resend of the saved artifact answered D25's duplicate: Q `stored`, 2 attempts, settled by `post-answer`; still one transition |
| Cut 6 `after-ack` at A | A correlates Q with R on the next wake: one transition `reply-r1`, r1 `replied`, inbox `repeat` (its own R) then `applied` (Q) |
| Frontiers | B's inbox `r1 applied`, `reply-r1 repeat` (its own Q served back); each node holds two articles |

`test_revoked_author_settles_by_observation_across_nodes` (PKT-322 with a
second node): A's owner accepts R and A's consumer dies (`after-post`); R
reaches B; A revokes its author (`hybrid-revoke-next`); B consumes R (one
transition); A's resend is refused and settles only itself (journal `submit
unanswered`, `reconcile answered 1`); R is `stored` by `store-observation`.

### Per-hop identities (run r1)

The consumer databases' inbox rows, each received article re-checked with
`fn_verify.py check-article` and the receiving consumer's keyring:

| Identity | R | Q |
| --- | --- | --- |
| Application operation | (fn-e1, r1) | (fn-e1, reply-r1) |
| Authored source SHA-256 (submission = at A = at B) | `32ba90dc298f…` | `90c2928825a8…` |
| Signature carrier (SHA-256 of both signatures; submission = at A = at B) | `8f5c7110c4e1…` | `7eba78ec3be9…` |
| Hop-local projection at A | `1d48434bf5a6…`, `Path: a.exchange.example.invalid!not-for-mail` | `e5477b6810b6…`, `Path: a.exchange.example.invalid!!b.exchange.example.invalid!not-for-mail` |
| Hop-local projection at B | `aa06b98b7d92…`, `Path: b.exchange.example.invalid!!a.exchange.example.invalid!not-for-mail` | `bd3109833fb8…`, `Path: b.exchange.example.invalid!not-for-mail` |

The projections differ (each node's Path); the authored source and both
signatures are the submission artifact's at both hops, and both consumers'
own verdicts are `verified`. The test asserts the source, the signatures,
the Message-ID and both verdicts; it records whether the projections differ
(they may).

## Step 3: the theorems (PRF-177), 2727a53a

(a) The carried-source keystone, `books/owner-signed-post.lisp`
`fn-osp-authorized-event-keeps-the-carried-source-and-signatures`. Subject:
`fn-pa-authorized-event`, which host/native/owner.lisp
`fnn-owner-attempt-transit`'s `:ok` arm calls through host/owner-host.lisp
`fn-owner-peer-carried-event`. Whenever it forms an event, the received
octets' carrier form is `:ok`; the event's authored source is the carrier's
source; the article record is `fn-record-encode` of the record over exactly
the received octets; and `fn-hsig-authorize-at` holds of the carrier's
source, principal, keys and signatures: the two signatures the verdict
authorized are the carrier's. No existing keystone stated this
(`fn-osp-authorized-event-binds-the-post` gives the verdict's Message-ID and
generation; `fn-hsig-injected-carrier-retains-exact-signed-source` is the
authoring side). Teeth (tests/acl2/owner-signed-post-tests.lisp): the served
witness `*ospt-event*` satisfies the full conclusion, with the source
`*tha-root-source*` and the signatures `*tha-signatures*`; removing the
hypothesis: the same carrier at a node with no enrolment forms no event and
the conclusion fails (`must-fail`).

(b) PKT-256, CORRUPTED state (tests/acl2/consumer-owner-local-progress-tests.lisp):
the no-op conjunct of `fn-cp-ack-writes-only-a-forward-declaration-in-scope`
without its frontier premise. The state after the committed ack of
`*colp-cursor*` (recorded position 2), with the frontier lowered to 1. The
retained hypotheses are asserted (scope match; declared = recorded
position), the omitted one is false, the kernel answers `(:refused
:future)`, and the conclusion `must-fail`s. Unreachable on the served path:
`fn-col-scope-entry` refuses an entry above the frontier.

(c) PKT-254. `books/consumer-owner-local.lisp` `fn-col-poll-report`: ACL2
encodes the selected event (`fn-col-poll-report-octets`: `fn-stxa-encode`,
or `fn-rcon-record-encode-impl` for a legacy record) and answers the named
refusal `:oversize` for octets above the kind-6 reply's report ceiling
(`fn-ncl-poll-event-bytesp`, `*fn-stxa-max-octets*`); a non-octet report is
`:report`. host/owner-host.lisp `fn-owner-consumer-local-poll` now serves
exactly that answer; before, the host encoded the event itself and an
oversize report reached `fn-ncl-poll-reply-encode`'s `:bad`, which faulted
the owner's control reply ("ACL2 refused a local-control reply status").
Keystone `fn-col-poll-report-fits-or-refuses-by-name` and
`fn-col-poll-report-is-a-page-or-a-refusal` (books/consumer-owner-local-progress.lisp):
a non-page or empty page passes through; a fitting report is the page with
the event's exact encoding; an oversize report is `(:refused :oversize)`;
never a write, so the position is unchanged. Teeth: the reachable page's
report is its exact encoding and `fn-ncl-poll-reply-encode :accepted`
accepts it; the oversize conclusion fails on it (`must-fail`); a scope
refusal passes through. The oversize antecedent is not witnessed
concretely: it needs a report above 4,294,966,940 octets. It is reachable
only for a profile whose record bound R lies in the 355 octets between
`*fn-stxa-max-octets*` and the u32 Store payload (PKT-467). The explicit
skip is not built (PKT-466 (a)).

(d) PKT-262, INTENDED under CNS-002: `register` sets the recorded position
to zero and the local-owner query is exact historical membership, so a
consumer registered after an article polls it first. Witness in the
progress test book: an article at sequence 1, the registration at 2, the
first page is that article, continuing at 2. Stated in
specs/consumer-progress.md.

The assurance chain for the slice: native entry `fnn-owner-attempt-transit`
(B's NNTP transit) -> executed ACL2 subject `fn-pa-authorized-event` over
the received octets -> the stored kind-4 event -> (a) its authored source,
record and authorized signatures are the carrier's -> B's poll serves it
through `fn-col-poll-report` (c), the event's exact encoding -> the observed
result: the consumer's own `check-article` of the served bytes gives the
submission's source and signatures (the per-hop table). The ack side is
PRF-116's (`fn-col-ack`), unchanged. The Python consumer is an external
client: its lock, resend and correlation are its own bookkeeping under
CNS-003, and it decides nothing fn decides.

## Registry

CNS-004 in planning/requirements.json and specs/consumer-progress.md's new
`## Two nodes` section (placed after CNS-003's paragraph, before "Executable
seam and obligations"); CNS-002's "through one fn node" names the two-node
shape. PRF-177 (proofs.json, proof-events.json), SCN-106 (catalog). The
spec's stale 196,963 and 196,608 poll ceilings now name
`*fn-stxa-max-octets*`. Packets: PKT-351, PKT-256 and PKT-262 closed;
PKT-254 and PKT-333 narrowed; PKT-466 (the remainder) and PKT-467 (a
decision) opened. docs/agents.md's consumer paragraph describes the
implemented consumer.

## Certification and native runs

- Farm persvati `run-20260926T114837Z-6029`, manifest
  `planning/evidence/manifests/certify-20260926T114912Z-1309060.json`,
  passed, 9 certified (consumer-owner-local 2.0 s, consumer-owner-local-progress
  4.3 s, owner-signed-post 4.7 s, consumer-owner-index-invariants 3.8 s and
  five test books, each under 2.2 s), 181 from the cache; no book over 10 s.
- hbox r1 (e6bab332, tests only):
  `/tank/fn/scratch/consumer-exchange/native-r1`, status 0; developer image
  `b12749be…` core `97c6d9d0…`; logs two_nodes `27b9126e…` (2 OK, 28.5 s;
  witnesses `0ce1c0df…`, `2449b170…`), test_native_consumer_exchange
  `021b296d…` (8 OK), test_fn_consumer_journal `5f053742…` (9 OK),
  test_anchor `97a2744c…` (27 OK).
- hbox r2 (2727a53a, the host now serving `fn-col-poll-report`): `/tank/fn/scratch/consumer-exchange/native-r2`; developer image
  `06796689…` core `5b05c3f7…`; two_nodes `11a1ef0d…` (2 OK, 23.5 s;
  witnesses `b3d9c6ef…`, `f1935117…`; same outcomes as r1: IHAVE `435
  duplicate`, no pull ARTICLE for R, Q settled by `post-answer`, the probe's
  position 6, projections differ at both hops), test_fn_consumer_journal
  `b43f777f…` (9 OK), test_anchor `85e14e4e…` (27 OK). The first
  test_native_consumer_exchange run in r2 (`0fd38c02…`) errored AFTER every
  assertion passed: a HARNESS failure of this lane's invocation, which set
  `FN_CONSUMER_EXCHANGE_EVIDENCE` to a directory for the two-node witnesses
  while that module writes the same variable as a file. Rerun on the same
  image without it (`--no-build`): `323e4c97…`, 8 OK. The two-node module's
  r1 and r2 logs are committed under planning/evidence/consumer-exchange/.

`make check-lane` in this worktree: every check passes except the proof-cost
ratchet on three books this lane did not touch (books/native-admin 15.9 s,
books/native-operator 11.8 s, books/peer-pull-session 11.7 s, all from dev's
peer-feeds merge certification certify-20260926T112155Z-967430); dev
5391f1d9 fails it the same way. Not widened here.

## Not done

- The explicit skip past an `:oversize` article (PKT-466 (a)) and whether
  the branch should exist (PKT-467, waits on ember).
- The six cuts on the production image (PKT-466 (b)).
- Phase 2: BP carriage through the relay network. multi-peer-relay had not
  merged at launch (dev 5391f1d9), so the four-node mission was not run
  (PKT-333 phase 2, PKT-466 (c)).
- The repeated transfer's pull did not fetch R because the feed delivered
  it first; the proxy records B's commands, not A's NEWNEWS answer, so that
  R was listed is inferred from the NEWNEWS instant preceding R's arrival.
