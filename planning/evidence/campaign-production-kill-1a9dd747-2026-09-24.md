# External-kill campaign on the 1a9dd747 production image — 2026-09-24

This is a runtime record. It certifies nothing and proves no theorem. It
gives P10's "passes on the production image" a run without a cut selector:
the production image `fn-host` served NNTP POSTs and was killed by SIGKILL
to its pid at scheduled instants, 184 times over two runs, and every POST
was judged after a restart from the same store.

**Result in one line.** 0 torn, 0 lost-240 and 0 reused numbers in both
runs. Every POST that got `240` rereads byte-identical by `ARTICLE` and by
`inspect`. Every POST that died without a reply is either absent (the
resubmission is accepted with exactly one new transaction) or present and
identical (the resubmission is refused and adds nothing). Client exit codes
0, 1 and 3 map one-to-one onto `240`, `441` and "no reply". The judge exits
0 on both records.

## Image, tree, invocation

| what | value |
| --- | --- |
| image | `/tank/fn/gates/qual-1a9dd747-20260924/build/fn-host` (production launcher, `exec`s SBCL, so the owner pid is the SBCL process) `60e14e2afe8703574a9d74d89dc632a6c030a668fa261a74d92dd7589bb686d9`, `fn-host.core` `12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd`, hashed at the run ([`image.sha256`](campaign-production-kill-1a9dd747/image.sha256)); [qualification record](native-cut-1a9dd747-2026-09-24.md) |
| runtime | SBCL 2.6.8 `/tank/fn/sbcl`, `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, `LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib`, `ACL2_CUSTOMIZATION=NONE`, no `FN_NATIVE_*` variable in any owner's environment (`Node.env` strips them), Python 3.12.7, Linux, stores on `/tank` (ZFS) |
| driver | [`tests/campaign/native_production_kill.py`](../../tests/campaign/native_production_kill.py), `f761aaf23e14…` at the run ([`driver.sha256`](campaign-production-kill-1a9dd747/driver.sha256)). It reuses `native_operator_campaign`'s `Node` (config, `operator init`, `operator run` start and stop, `store inspect`, NNTP `ARTICLE`) and `injected_from`, unchanged (`3e9e2283…`, the same hash as the 1a9dd747 campaign). After the runs only its `judge` verb gained the killed-POSTs table; `run` and `client` are as run. |
| invocation | [`run.sh`](campaign-production-kill-1a9dd747/run.sh): `python3 -m tests.campaign.native_production_kill run --image $G/fn-host --work $S/work$n --out $S/run$n.json --seed $n --kills 80 --concurrent 12` for n = 1, 2, then `… judge $S/run$n.json`. 2026-09-24 15:20:45Z to 15:50:13Z; 12:28 and 16:59 wall; peak driver RSS 1.98 GB (the `inspect` children). |
| ports | kernel-assigned (`127.0.0.1:0`): 44671, 45549 (run 1), 56605, 49335 (run 2), 57735 (the capacity run below). None is listening after the runs (`ss -ltn`). Nothing touched `/tank/fn/node`, 1119 or 119. |
| raw data | hbox `/tank/fn/scratch/campaign-production-kill/`: `run1.json` `df6f29ab456ec744436eacf19bc9fe91b0eb3c7f32c4dc87319dae361c9954cc`, `run2.json` `496b8656bd0a0f0b14d38555aadda6abea3426ac07a2466bd2636571ea3aa56f`, `work1/`, `work2/` (stores, payloads, every `owner-N.err`). Copies in [`campaign-production-kill-1a9dd747/`](campaign-production-kill-1a9dd747/) with [`SHA256SUMS`](campaign-production-kill-1a9dd747/SHA256SUMS). |

## What one kill is

1. **Stream.** Zero to two unkilled POSTs of random size through the client.
2. **Numbers before.** `GROUP fn.letters`, then `HDR Message-ID low-high`.
3. **The killed POST.** A fresh Message-ID and size, sent by a client process.
   The client prints `SENT <CLOCK_MONOTONIC>` the moment its last octet is
   written. The driver sleeps and then spins to `SENT + delay` and sends
   `SIGKILL` to the owner's recorded pid. Measured kill instants are within
   0.011 ms of the schedule.
4. **At death.** The owner's exit (−9 in all 184), the tail of its log, the
   store's `transactions/`, `staging/` and `allocation-frontier.json`
   against the state before the POST, and a read-only `store ROOT inspect`
   of the killed Message-ID with no owner running. The store listing after
   `inspect` equals the listing at death in all 184 kills.
5. **Restart.** `operator CFG run` on the same config and store. The owner
   recovers at start, as the node does under its unit, with no separate
   `operator recover`. It was ready in 184 of 184 restarts.
6. **Judge inputs.** `ARTICLE` of every POST of this iteration. For each
   POST that died without a reply, a resubmission through the client plus
   the new-transaction count, then `ARTICLE` again. Then the number map
   again.

**Concurrent kills.** Two clients each send `POST` and the article body,
then hold. The driver releases both terminators, and the delay runs from the
later `SENT`. The two terminators were 0.00 to 0.11 ms apart.

**Close.** When the store holds 116 transactions, it is closed: the map, then
`ARTICLE` for every POST it ever saw, then SIGTERM, then `inspect` for every
POST. A fresh store takes over. See "The 128-transaction capacity" below for
why. Each run used two stores. The judge checks numbers per store.

**Sizes.** POST payload octets per class: tiny 180, small 2100, medium 12500,
large 31000, and over 33600, which is above `fn-own-body-limit`, 32768.

## Schedule

A calibration phase POSTs every class three times with no kill and polls the
store to time each phase from `SENT`. The run 1 medians, in ms:

| class | `.allocation-` seen / gone (frontier replaced) | `.stage-` seen / gone | transaction visible | `240` |
| --- | --- | --- | --- | --- |
| tiny | 1.9 / 24.2 | 60.3 / 125.4 | 91.6 | 157.1 |
| small | 6.8 / 28.0 | 70.6 / 128.2 | 94.7 | 158.3 |
| medium | 27.9 / 53.0 | 86.4 / 145.8 | 118.3 | 180.5 |
| large | 70.7 / 90.4 | 145.5 / 209.3 | 180.4 | 253.1 |
| over | – | – | – | 37.5 (`441 … not received`) |

Run 2 is within about 40 ms of these (in [`judged2.md`](campaign-production-kill-1a9dd747/judged2.md)).

Delays are drawn by a seeded RNG (seeds 1 and 2), per size, in these bands:

- **early**: uniform over [0, 0.9·txn).
- **window**: uniform over [0.9·txn, reply + 3 ms]. This is the
  durable-completion window, from just before the transaction appears to
  just after the reply.
- **late**: uniform over (reply + 3, 1.4·reply + 5].
- **mid-article**: 10 to 95 % of the article sent, then 0 to 20 ms.
- **over-limit**: an over POST killed mid-article or 0 to 40 ms after `SENT`.

The schedule per run: 80 single kills (33 window, 19 early, 14 late, 8
mid-article, 6 over-limit) and 12 concurrent kills (6 window, 3 early, 3
late), shuffled.

## Per-outcome counts

The first table counts every POST the judge saw: the killed ones, the stream,
calibration and resubmissions. The second counts the killed POSTs alone. A
concurrent kill has two.

| verdict | run 1 | run 2 |
| --- | --- | --- |
| 240-and-identical (ARTICLE after the restart, and at close by ARTICLE and `inspect`, equal) | 87 | 97 |
| died-absent (430, then the resubmission `240` with one new transaction and an identical reread; for an over POST the resubmission `441 … not received` with none) | 69 | 78 |
| died-present-identical (220 and identical, then the resubmission `441 posting failed; the article was refused` with no new transaction) | 24 | 22 |
| refused (`441`, absent after the restart; all over-limit `441 posting failed; the article was not received`) | 34 | 27 |
| torn | **0** | **0** |
| lost-240 (a `240` later absent from any map, ARTICLE or `inspect`) | **0** | **0** |
| reused-number (a number seen before a kill later naming another Message-ID, or a Message-ID renumbered, or a seen number vanishing) | **0** | **0** |

| killed POSTs | 240-identical | died-absent | died-present-identical | total |
| --- | --- | --- | --- | --- |
| run 1 single | 8 | 51 | 21 | 80 |
| run 1 concurrent | 3 | 18 | 3 | 24 |
| run 2 single | 4 | 61 | 15 | 80 |
| run 2 concurrent | 0 | 17 | 7 | 24 |

The 14 died-absent over-limit POSTs are included. Their resubmission is
refused for size, as it must be.

**Client exit codes.** Over both runs:

- rc 0 always came with `240 article received OK`.
- rc 1 came with `441 posting failed; the article was not received` or
  `441 posting failed; the article was refused`.
- rc 3 always came with no reply.

No `441 … uncertain` line was observed: a SIGKILLed owner writes nothing. The
judge checks that each client's rc equals the classification of its reply
octets, and that no reply appears under two codes.

**Readers.** At both closes of both runs, every present article has the same
SHA-256 by `ARTICLE` and by `inspect`. Each killed POST's pre-restart
`inspect` agrees with the post-restart `ARTICLE` on presence and bytes.

**Numbers.** In each store the numbers are 1..n with no gap: 116 and 58 in run
1, 117 and 74 in run 2. A death before publication consumed no number that
any reader later saw.

## Kill instants against the phase reached

The production owner logs one line per connection and one per completed post
(`accepted post path=served connection=N message-id=…`). It logs nothing
between those two lines. So the owner log gives two phases, and the store
state at death gives the finer one. The table covers both runs, 184 kills.
The "linked" rows count a new transaction of either victim.

| store state at death | kills | bands | killed at, ms after `SENT` | victims with `accepted post` logged | victims answered `240` |
| --- | --- | --- | --- | --- | --- |
| `untouched` (no store change) | 63 | early 21, window 12, late 2, mid-article 16, over-limit 12 | 1.8 to 277.7 | 0 | 0 |
| `.allocation-` stage present | 18 | early 10, window 6, late 2 | 10.4 to 229.9 | 0 | 0 |
| frontier replaced, no stage, no new transaction | 26 | early 8, window 13, late 5 | 48.5 to 306.2 | 0 | 0 |
| `.stage-` present, no new transaction | 17 | early 4, window 12, late 1 | 48.9 to 202.5 | 0 | 0 |
| new transaction and an `.allocation-` stage (concurrent) | 1 | window 1 | 158.4 | 1 | 1 |
| new transaction, `.stage-` still present | 21 | window 15, late 6 | 112.3 to 258.0 | 0 | 0 |
| new transaction, staging empty | 38 | early 1, window 19, late 18 | 57.4 to 243.6 | 14 | 14 |

Two points in this table:

- **No reply before durability.** No kill before the transaction was linked
  and its stage cleaned found a `240` or an `accepted post` log line.
- **The log line matched the reply.** In every kill the victims that the
  owner logged as accepted are the victims that got `240`, 15 of 15.

The 38 − 14 = 24 kills in the last row with no reply are deaths after the
record was durable and before the reply. With the 21 kills of the row
above (linked, stage not yet removed), their POSTs are the 46
died-present-identical victims. Those deaths lie in the stretch the developer
campaign cuts at `record-staging-cleaned`, `finish-consumed` and
`finish-durable`. The per-kill rows, with the owner log tail at each death,
are in [`judged1.md`](campaign-production-kill-1a9dd747/judged1.md) and
[`judged2.md`](campaign-production-kill-1a9dd747/judged2.md), and in the
JSON (`owner_log_tail`, `pre`, `death`).

The bands overlap the phases, as the table shows. The same delay reaches
different phases from kill to kill: owner latency varied by about 40 ms
between runs, and a concurrent POST waits behind the other. The kill
instant is exact. The phase is what the store shows at death.

## Failures

**None in the two counted runs.** The judge lists 0 failures and exits 0 on
both.

**The 128-transaction capacity (harness finding, and one for the
coordinator).** The first attempt at run 1 (started 14:55Z, one store, no
rotation) is kept as
[`capacity-run.json.gz`](campaign-production-kill-1a9dd747/capacity-run.json.gz)
and [`capacity-run-judged.md`](campaign-production-kill-1a9dd747/capacity-run-judged.md)
(raw `superseded/run1.json`, `5b7f5c80…`). After the 128th transaction
(`00000000000000000127.txn`, iteration 67), every POST was answered
`441 posting failed; the article was refused\r\n`. The owner logged
`refused post path=served connection=6 message-id=<pk-1-0159@production-kill.invalid>`.

- **Cause.** `operator init` writes the default store profile, which holds
  128 transactions (`tools/run_store.py:34` `MAX_TRANSACTION_COUNT = 128`).
  The owner refuses at `host/native/owner.lisp:714`:
  `(>= (fnn-owner-service-records service) (fnn-config-max-transactions store))`.
- **Effect on the judge.** The 20 died-absent POSTs from iteration 67 on
  could not be resubmitted, and the judge of that attempt flagged them. The
  capacity refusal itself is correct. The counted runs rotate the store at
  116 transactions.
- **Within capacity.** In the 67 kills before capacity, that attempt also
  had 0 torn, 0 lost-240 and 0 reused numbers.

Three things for the coordinator:

1. The refusal names no reason. It is W3 of the
   [developer campaign](campaign-1a9dd747-2026-09-24.md).
2. The capacity comparison is decided in host Lisp, not by ACL2. That bears
   on the one-owner rule and on P9.
3. The live node's `fn.toml` names no store profile. Whether its store has
   the 128 bound was not checked here, because this lane does not read
   `/tank/fn/node`.

**W3 again.** Every resubmission of an article that was present and identical
was answered `441 posting failed; the article was refused` (46 times). The
wire cannot tell this duplicate from a conflict or a capacity refusal.

## What this establishes

- On the production image and core `12ece6cc…` itself, with no developer
  selector, 184 SIGKILLs of the serving owner kept every durability
  property the campaign checks:
  - The kills are spread over the whole POST timeline, from mid-article to
    after the reply, with 39 of 92 per run drawn inside the durable-completion
    window.
  - The kills include 24 during two concurrent POSTs.
  - The checked properties: no `240` before the record was durable and its
    stage cleaned; no `240` later absent; no torn article; no reused number;
    recovery at the next start in every case; three distinct client
    outcomes.
- P10's "passes on the production image", read as "the production image
  survives process death at any instant of a POST with the table's
  outcomes", now has production-image evidence. Until now it had the
  developer twin, plus two boundary kills.

## What this does not establish

- **Not coordinate-precise.** No kill names a `fn-bs-*-program`
  coordinate. The store state at death is a coarse partition: several
  table cuts fall in one state, and some state changes happen between
  cuts. So this run complements the developer-image cut campaign, where
  each of 20 cuts names its coordinate. It does not replace it. Nor is it
  the equivalence argument that the developer and production images share
  every write path.
- **No ACL2 differential.** No state was checked for membership in the byte
  model's image at death.
- **Process death only.** These are process deaths on ZFS, not power loss.
  D14's durability qualification is untouched.
- **Recovery and checkpoints.** Recovery deaths (killing the owner during
  its own start-up recovery) were not scheduled. The kills during the 184
  restarts were not taken, and the checkpoint cuts were not reached.
- **Other paths.** Transit (IHAVE/TAKETHIS), the operator control path and
  the BP paths were not exercised. Only the served POST path was.
- **The live node.** Nothing here was run on it.
