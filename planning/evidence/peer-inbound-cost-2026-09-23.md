# Why `peer-inbound` took 805 s, and the repair (lane COST-peer, 2026-09-23)

Branch `cost/peer` from `dev` 549c750a. The diagnosis was read from existing
certify logs; the slow form was not rerun except for one step-limited
sample (3 million steps, 38 s) with accumulated persistence on, because the
log's `Rules:` list names what opened but not what it cost. The repair was
tried in one `tools/proof_repl.py` session on the Mac (65 of 71 closure
books installed from `~/.cache/fn-certs`; `nntp-post`,
`injection-invariants`, `node-config`, `config-records`, `replay` and
`hybrid-store` had no cached pair and were included uncertified from source,
which is sound for timing and says nothing about certification).

## The logs

| log (persvati) | what it is |
|---|---|
| `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/books--peer-inbound.certify.log` | the 310-book run: book 804.8 s |
| `/home/ember/fn-gates/t13-conform/build/acl2/certify-20260922T225718Z-866045/books--peer-inbound.certify.log` | `dev` plus the relayed-octets edit, jobs 4: book 875.2 s |
| `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/` | did not reach `peer-inbound` |

## Event times

| event | seam run | t13 run |
|---|---|---|
| `(verify-guards fn-peer-command)` | 802.1 s, 96 820 949 steps | 871.3 s, 95 009 258 steps |
| `fn-peer-step-submission-is-typed` (next largest) | 0.37 s | 0.62 s |
| the other 139 events | 2.3 s together | |

One event is 99.7% of the book. It is a guard verification with no hint.
Its guard conjecture is small (three arms: IHAVE, CHECK, TAKETHIS). What it
needs is `(fn-node-statep node)` for the call of `fn-peer-decide-offer`,
which `fn-peer-sessionp-forward-fields` supplies, and that
`fn-peer-single` returns a true list. The log prints `Goal`, `Goal'` and
`Q.E.D.`: gag mode hid the rest. There was no induction, no splitter note
and no forcing round. All 96.8 million steps went into simplifying one goal.

## What the prover did

The `Rules:` list of the event opens `fn-peer-decide-offer`,
`fn-cfg-peer-find`, `fn-cfg-peer-of-rows`,
`fn-cfg-peer-inbound-max-inflight`, `fn-af-message-idp`,
`fn-peer-probe-obligation-id`, `string-append` and `binary-append`. The
guard mentions `fn-peer-decide-offer` three times, and each copy is under a
test of the decision's kind. The persistence sample, over the first 3
million steps (`:frames-a`, which counts the attempts in flight), says
where the work goes:

| rune | frames | tries |
|---|---|---|
| `(:definition fn-cfg-peer-find)` | 1 985 129 | 1 |
| `(:definition fn-cfg-peer-of-rows)` | 1 984 806 | 1 |
| `(:rewrite fn-nntp-article-idp-is-consp)` | 1 950 986 | 129 166 |
| `(:definition fn-nntp-article-idp)` | 1 925 954 | 6 258 |
| `(:definition binary-append)` | 1 884 222 | 810 |
| `(:definition fn-nntp-message-id-tokenp)` | 1 381 766 | 6 154 |
| `(:linear fn-peer-message-id-len)` | 1 021 979 | 18 565 |
| `(:definition fn-af-message-idp)` | 989 549 | 18 424 |
| `(:definition fn-cfg-peer-slot)` | 978 044 | 3 028 |
| `(:definition fn-cfg-rows-with-key)` | 971 000 | 3 016 |

All of the work sits under the one opening of `fn-cfg-peer-find`.
`fn-cfg-peer-of-rows` is the peer table's record builder. It does fourteen
`fn-cfg-peer-slot` lookups, each a `fn-cfg-rows-with-key` scan, and then
builds a record through nested `cond`s and an `append` and tests it with
`fn-cfg-peerp`. Every length and bound term the expansion produces tries
the linear rule `fn-peer-message-id-len`, and each try relieves its
hypothesis by opening the message-id grammar (`fn-af-message-idp`,
`fn-nntp-article-idp`, `fn-nntp-message-id-tokenp`): 18 424 tries in the
first 3% of the proof.

## Cause

Line 65 of `books/peer-inbound.lisp` enabled `fn-cfg-peer-vocabulary`
book-wide. That is the export theory of `books/peer-config`, and it holds
`fn-cfg-peer-find`, `fn-cfg-peer-of-rows`, `fn-cfg-peer-slot`, the peer
recognizers and the inbound/outbound accessors. `fn-peer-decide-offer` is
still enabled when the guard events run, because `fn-peer-vocabulary` is
disabled only after them. The guard of `fn-peer-command` therefore opened
the decision, and the decision opened the peer-table lookup. The goal only
needed to know that the node is a `fn-node-statep`. This is the class the
brief names first: a recognizer and codec left enabled that a dispatching
goal opened. Here the goal dispatched on the decision kind and the
recognizer was the peer table. It is also the pattern of review F3, a
vocabulary opened at the top of a book. It is not an induction, a
`:use` with heavy hints, forcing, or a genuinely large proof.

Two experiments in the session measure it. Each ran once and was undone:

| `verify-guards fn-peer-command` with | time | steps |
|---|---|---|
| hint disabling `(:d fn-peer-decide-offer)` | 0.06 s | 22 032 |
| hint disabling `(:d fn-cfg-peer-find)` only | 0.10 s | 36 511 |

Closing the lookup alone removes the whole cost, even with the decision
open.

## Repair

`fn-cfg-peer-vocabulary` is removed from the book-wide `local` enable, with
a comment giving the reason. Nothing else changed. The whole book loaded
with the change: every form up to the export `deftheory`, 143 forms,
including every theorem and every guard event. So no proof in the book
needed the peer table open. The proofs that read a peer record already
name `fn-cfg-peer-find` in their hints. No theorem statement, hypothesis or
hint changed. Nothing is skipped, and no `:verify-guards nil` was added.

## Session times (proof_repl, Mac)

| event | before (seam log, persvati) | after (session, Mac) |
|---|---|---|
| `(verify-guards fn-peer-command)` | 802.1 s, 96 820 949 steps | 0.08 s, 33 717 steps |
| every event of the book, summed | 804.8 s over 142 events | 3.7 s over 142 events; the largest is `include-book "node-config"` at 1.6 s |

After the change the event's `Rules:` list still opens
`fn-peer-decide-offer`, but not `fn-cfg-peer-find` or
`fn-cfg-peer-of-rows`. The Mac ran the sample at about 12.8 s per million
steps and persvati ran the original at 8.3 s, so the gain is not a
difference between the machines.

## The neighbours (log numbers; not changed here)

**`peer-inbound-invariants`** took 1.0 s in the seam run and 1.6 s in the
t13 run. It is not slow.

**`peer-config`** took 92.9 s in the seam run and 92.0 s in the dev-head
run. The cause is a different one. Four theorems about
`fn-cfg-peer-rows` cost 85 s of it, and each re-splits the same case
product of the row builder:

| theorem | time | steps | subgoals |
|---|---|---|---|
| `fn-cfg-peer-names-of-peer-rows` | 26.2 s | 14 679 190 | 15 448, split 612 ways at `Goal`, deepest `Subgoal 612.16.8.4.10.5` |
| `fn-cfg-peer-rows-keyed` | 23.3 s | 14 736 731 | the same 15 448 |
| `fn-cfg-peer-rows-are-few` | 22.1 s | 16 412 962 | the same 15 448 |
| `fn-cfg-peer-rows-are-rows` | 13.3 s | 2 912 624 | 2 986 |
| `fn-cfg-peer-find-is-a-peer` | 7.3 s | 3 337 339 | 1 620, one split on `fn-cfg-peer-of-rows` |

In each of these proofs the splitter's if-intro list is `binary-append`,
`fn-cfg-ag-car`, `fn-cfg-ag-cdr`, `fn-cfg-peer-outbound-auth`,
`fn-cfg-peer-rows` and `true-listp`. `fn-cfg-peer-rows` is one flat
`append` over transport, inbound, outbound and auth. The accessor codec
`fn-cfg-ag-car`/`-cdr` is open (line 29 enables `fn-cfg-vocabulary`
book-wide), so the splitter multiplies the four halves' cases, 612 at the
top, and rewrites `append` through each. The same product is paid four
times. The repair is per-half row functions (or per-half lemmas about the
four `append` operands) with each property proved per half. The theorems
would then close by `fn-cfg-rows-with-key-of-append` and its siblings.
That is a new proof structure in a book low in the graph, and it is not the
lemma repaired here, so it is left to a lane that owns `peer-config`.

**`peer-feed-invariants`** took 48.9 s in the seam run and 54.8 s in the
t13 run. No single cause: the largest events are
`fn-feed-done-survives-a-driven-record` (7.4 s, 3 399 subgoals),
`fn-feed-droppedp-of-state-of-set-state` (7.4 s, induction, deepest
`Subgoal *1/3.758.6`), `fn-feed-count-accepted-after-an-accepted-head`
(6.5 s) and `fn-feed-droppedp-of-state-of-append-one` (6.0 s, induction).
Each opens its own feed-step definitions. It is not the cause repaired
here.

## Not verified

- The book was loaded form by form in a live session, not certified. The
  farm run below is the certification.
- Six closure books were included uncertified from source in the session.
- `fn-cfg-vocabulary` (the config codec) is still enabled book-wide in
  `peer-inbound`. It cost nothing measurable here, and closing it is the
  F3 rule's work, not this lane's.
