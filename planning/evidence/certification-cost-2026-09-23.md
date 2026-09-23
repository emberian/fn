# Where a certification run's time goes, and what would make it ten times faster (lane PROFILE, 2026-09-23)

Branch `tooling/profile` from `dev` 549c750a. No certification was run for
this study. Everything below comes from runs already on disk: the archived
manifests and the per-book ACL2 logs, copied off the boxes with rsync.

## The data

| run | box, jobs | books | run wall | where the logs are |
|---|---|---|---|---|
| seam tree, `certify-20260923T000250Z-1473169` | persvati, 4 | 310 | 1639 s | `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/` (sources: commit 3102c6f2, all 310 digests match) |
| image closure (freeze), `certify-20260922T200011Z-3216833` | hbox, 8 | 165 | 1877 s | `/tank/fn/gates/freeze-dev-28fb4bd0/build/acl2/certify-20260922T200011Z-3216833/` (all 165 digests match the gate tree) |
| dev head treewide, `certify-20260923T003741Z-1790068`, stopped | persvati, 8 | 345 of 425 finished | about 1028 s when stopped | `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/` (no manifest; 425 drivers name the requested set) |
| `certify-20260922T225718Z-866045` (t13) and `certify-20260922T232404Z-1113276` (t6b, 169 books, 2988 s) | persvati, 4 | | | used only to cross-check |

Method. Each `*.certify.log` was parsed for every `Summary` block: `Form:`,
`Rules:` (the `:DEFINITION` runes counted), `Time:` (total and prove),
`Prover steps counted:`, plus the splitter notes and subgoal names between
one summary and the next. Wrapper events (`encapsulate`, `progn`,
`make-event`) were left out of the sums so nothing is counted twice. The
`certify-book` summary gives ACL2's own time for the whole book. The
dependency graph is `tools/certify_books.py`'s own `dependency_graph`, run
over each run's exact sources. The schedule was replayed with the runner's
policy on a virtual clock: whenever a slot is free, start the first ready
book in the queue. The replay reproduces the measured runs: 1638 s against
1639 s for the seam run, and 1877 s against 1877 s for the freeze. For the
freeze, its histogram of concurrency is the same as the one built from the
logs' file times.

## 1. The shape of a run: the wall is one chain of books

| run | CPU (sum of book walls) | CPU / jobs | critical path over include-book edges | run wall | chain share |
|---|---|---|---|---|---|
| seam, jobs 4 | 4778 s | 1195 s | **1595 s** (21 books) | 1639 s | 97 % |
| freeze, jobs 8 | 4937 s | 617 s | **1877 s** (20 books) | 1877 s | 100 % |
| dev head, projected, jobs 8 | 5250 s | 656 s | **1072 s** (21 books) | about 1075 s | 100 % |

The seam run's chain is `cbor > wildmat > frame-fields > frame-journal (43)
> frame (87) > identity > hybrid-store > replay > store-files >
store-files-invariants > store-node (307) > store-node-invariants (311) >
store-node-traces (109) > store-node-resolution (661) > store-observed >
owner > owner-invariants (46) > owner-fault > owner-config >
owner-prepare-correspondence > its test`. Five books on it are 1497 s of
the 1595 s.

The dev head projection uses the 345 finished logs, the seam log's wall for
the 72 books the stopped run never reached, and 1.5 s for 8 books with no
log anywhere. It already includes the `store-node-resolution` repair (7.6 s,
from the T4-snr session). Its chain then runs through `nntp-invariants (70) >
nntp-effects (106) > nntp-post > peer-inbound (805) > ... > owner-agent`, and
**one guard proof in `peer-inbound` is 802 s of the 1072 s**.

**The scheduler.** `run_schedule` starts ready books in *requested order*,
first ready first, which is dependency order. It does not prioritise the
critical path. Replayed on the seam run with the walls archived *before* that
run, critical-path-first would have finished at 1607 s instead of 1638 s, a
saving of 31 s (2 %). At 8 or more jobs it saves nothing on any of these
runs: once the chain is 97 to 100 % of the wall, no ordering can help.

**Busy slots.** In the seam run all 4 slots were busy for 807 s of the
1638 s, and only one process ran for 398 s. In the freeze, a single process
ran for **916 of the 1877 s**, the store chain's tail. The run is not short of
workers. Persvati has 24 cores and a slot cap of 16. The same book at the
same digest proved at a median of 1.03 times its jobs-4 prove time when run
at jobs 8 (36 books, 2521 s against 2636 s summed), so more jobs costs almost
nothing. Running several *runs* on the box at once is a different matter. The
t6b run overlapped the seam and t13 runs and shows `store-node` at 485 s
against 307 s and `store-node-resolution` at 1695 s. Those sources were not
checked for identity, so treat that as an observation, not a measurement.

## 2. Load against proof: load is not the cost

| run | certify-book time, summed | include-book phase before the first event | median per book | largest | steps 3 to 5 (retract, write .cert, compile) | process start and driver |
|---|---|---|---|---|---|---|
| seam | 4759 s | **151 s (3.2 %)** | 0.51 s | 1.06 s (`bp-native-app-tests`) | 84 s | 19 s |
| dev head (345) | 3885 s | 118 s (3.0 %) | 0.28 s | 0.92 s | 101 s | |
| freeze | 4917 s | 49 s (1.0 %) | 0.26 s | 0.72 s | 30 s | 20 s |

`books/owner` includes four books directly and about 150 transitively. It
loads them in 0.6 s and certifies in 1.6 s. Across the seam run, 262 of the
310 books take under 5 s each, and together they take 303 s. The fixed
per-book cost is about 0.8 s: load, compile and process start. A chain of 20
books therefore has a floor of about 16 s. Changing the include structure or
the toolchain would save a few percent of CPU and nothing on the wall. It is
not on the list.

Proof time is the cost. In the seam run, 8 events take 55 % of all event
time, 29 events take 77 %, and 48 events take 84 % (14 443 events in total).
In the freeze, 9 events take 64 %.

## 3. The top thirty books, their top events, and the causes

Classes: **(a)** a recognizer, codec or step function left open that a
dispatching goal expands, so the goal splits case by case; **(b)** guard
verification opening its callees; **(c)** induction or a `:use` fan whose
instances make each case heavy; **(d)** forcing rounds; **(e)** a large proof,
or time spent outside the rewriter. **(e\*)** marks events whose step rate is
under 70 000 steps/s against a typical 150 000 to 1 000 000. Their time is not
in rewriting (type-set, linear arithmetic or ground evaluation are the usual
suspects), and the log cannot say which. They need one profiled session before
anyone repairs them. Forcing rounds (d) appear once in the whole top tier (2
rounds, `bp-fragment-invariants`, 13 s). They are not a cost here.

"sg" is subgoals printed and "split" is the largest splitter note. The run
column says which log the numbers come from: the seam run's where the book is
in it, otherwise dev head's.

| # | book (run) | wall | top events | class | repair shape | saving |
|---|---|---|---|---|---|---|
| 1 | `peer-inbound` (seam) | 805 s | `(verify-guards fn-peer-command)` 802 s, 96.8 M steps, 2 sg, 19 defs opened | b | The guard conjecture repeats `fn-peer-decide-offer` inside three `let` conjuncts, and the prover opens it, together with `fn-cfg-peer-find`, `fn-nntp-keywordp`, `-string-octets` and `fn-peer-single`, in every one. Give `:guard-hints` that keep those closed and cite their type facts (`true-listp` of `fn-peer-single`, the decision kind). | about 800 s |
| 2 | `store-node-resolution` (seam) | 661 s | `fn-snrt-step-success-history-monotone` 342 s (21 394-way split, 44 defs); `fn-snrt-step-records-prefix` 315 s (21 393-way) | a | **Repaired on dev** (T4-snr: the prepare arms were closed; the whole book now takes 7.6 s in the session) | 654 s |
| 3 | `bp-primary-invariants` (seam) | 657 s | `fn-bpp-block-crc-width` 458 s (134 M steps, split 108 over `fn-bpp-crc-octets`, `-eidp`, `-timep`, `-dtn-sspp`, `floor`, `nth`); `-accepted-block-has-valid-crc` 39 s (4916 sg); `-bundle-age-round-trip` 42 s (e\*, 63 k steps/s) | a + arithmetic | Prove the width of `fn-bpp-crc-octets` once per CRC type with `floor` closed. Then prove the block theorem by cases on the CRC type, with `fn-bpp-blockp` and the field recognizers closed. The other three events over 25 s in the book (`-crc-octets-are-octets` 36 s, `-accepted-input-is-canonical-by-construction` 30 s, `-decode-yields-block` 26 s) have the same codec open. | 555 s, then 90 s more |
| 4 | `bp-release-invariants` (dev) | 387 s | `fn-bprl-release-record-replays-decision-by-definition` 318 s (29 280-way split at `Goal`, 86 defs: `fn-bp-statep`, `-workp`, `-pendingp`, `-receiptp`, `fn-node-statep` ...); `-release-removes-the-forward-pin` 65 s (580-way split, 64 defs, a 4.8 kB `:use`) | a (+c) | This is the store-node-resolution shape again. Write one lemma per journal-record kind with the state recognizers closed. The forward-pin theorem should reach `fn-node-statep` through its preservation lemma instead of opening it. | 380 s |
| 5 | `store-node-invariants` (seam) | 311 s | `fn-sn-finish-preserves-indexedp` 119 s (5249-way split, 48 defs); `fn-snt-prepare-that-stages-advances-by-one` 95 s (hint enables `fn-node-statep`, `fn-statep`); `fn-snt-prepared-durable-is-idle-at-successor` 60 s (54 defs) | a | As `store-node-resolution-cost-2026-09-23.md` sets out: one finish lemma per arm, and the field facts of `fn-node-prepare` and `fn-node-complete` stated as lemmas so the node recognizer stays closed. | 260 s |
| 6 | `store-node` (seam) | 307 s | `(verify-guards fn-sn-finish)` 305 s (5744-way split over `fn-record-p`, `-groupsp`, `-payloadp`, `-msgidp` ...) | b | The guard hint enables `fn-sn-statep`, and the record codec then comes open under it. Keep `fn-record-p` and its field recognizers closed in the guard hint and cite the record typing lemmas. The export disable should also close `fn-sn-prepare-retention`, `-identity` and `fn-sn-identity-context` (the T4-snr recommendation). | 300 s |
| 7 | `bp-node-machine` (seam) | 251 s | `fn-bpn-answerp-forward-shape` 129 s and `fn-bpn-machine-recordp-forward-shape` 120 s (about 1460-way splits, 29 defs) | a, **in `books/defrecord.lisp`** | The macro proves `<recognizer>-forward-shape` with the new recognizer and every field predicate enabled. It only needs the recognizer's first conjunct. Prove it in a theory holding just the recognizer and the shape predicate. This is one macro edit. Across the tree the 130 forward-shape events take 256 s, and 249 s of that is these two. | 249 s |
| 8 | `anchor-invariants` (dev) | 174 s | `fn-anchor-accept-list-latest-never-goes-back` 85 s (induction, 40 defs); guard of `fn-anchor-node-accept-list` 9 s; `-preserves-nodep` 9 s | c | Give a step lemma for one `fn-anchor-node-accept`, then run the induction with the anchor recognizers closed. | 80 s |
| 9 | `tcpcl-octets` (dev) | 154 s | `fn-tcl-decode-segment-append-error` 53 s, `-append-ok` 36 s, `-need-short` 12 s (a 66 to 91-way split at `Goal` on `fn-tcl-decode-segment`, 27 M steps) | a | Write a decode-of-append lemma for each header case, with `fn-tcl-decode-segment` closed in the three theorems. | 95 s |
| 10 | `bp-sequence-fidelity` (seam) | 132 s | `fn-bpn-sf-step-preserves-nonreuse` 73 s (10 `:cases` with the step enabled, 11 538 sg); `-recover-step-` 38 s; `-stage-step-` 9 s | a | One lemma per event kind, then the step theorem by `:cases` with `fn-bpn-sf-step` closed. | 105 s |
| 11 | `store-node-traces` (seam) | 109 s | `fn-snt-prepare-retention-preserves-relation` 51 s (14 sg, 38 M steps); `fn-snt-record-directory-preserves-relation` 34 s (9112 sg); `-prepare-identity-` 11 s | c | These are `:use` fans of 6 to 8 instances with `fn-snt-relation` open. Make the used facts rewrite rules about the arm, or give per-arm relation lemmas. | 90 s |
| 12 | `nntp-effects` (seam) | 107 s | `fn-nntp-date-octets-length` 46 s (6 sg, 26 M steps, `floor`/`mod`); `-listgroup-initial-is-a-status-line` 13 s; `-group-initial-` 9 s | e (arithmetic) | Prove length lemmas for `fn-nntp-pad2`, `-pad4` and `-digit-octet`, then state the date length with those closed. | 60 s |
| 13 | `tcpcl-session` (dev) | 103 s | `fn-tcl-touch-rx-preserves-cheapp` 22 s (190-way split, hint enables `fn-tcl-session-cheapp`); two `-preserves-sessionp` at 9 s each | a | Give field lemmas for `touch-rx` and keep the session recognizer closed. | 30 s |
| 14 | `peer-config` (seam) | 93 s | `fn-cfg-peer-names-of-peer-rows` 26 s, `-rows-keyed` 23 s, `-rows-are-few` 22 s, each re-splitting `fn-cfg-peer-rows` 612 ways (15 448 sg) | a | Prove one shape lemma for `fn-cfg-peer-rows`, then the three theorems with it closed. | 70 s |
| 15 | `policy` (seam) | 88 s | `fn-pol-current-is-stmt-or-nil` 49 s (1 sg, 337 k steps, 7 k steps/s); the admission of `fn-pol-current` 18 s (same rate) | e\* | Profile first. The time is not in rewriting. | up to 65 s |
| 16 | `frame` (seam) | 87 s | `(verify-guards fn-frame-workflow-protected)` 84 s (298 sg, 17.7 M steps, 18 defs) | b | Give guard hints with the frame field codec closed. | 80 s |
| 17 | `feed-connection-invariants` (seam) | 84 s | `fn-fc-step-preserves-state` 42 s (`:cases` plus `fn-fc-step`, `-next-state` and `-result` enabled, 7702 sg, 43 defs); `-from-line-` 14 s; `-table-remove-` 13 s (induction) | a | One lemma per step arm. | 40 s |
| 18 | `bp-primary-cbor` (seam) | 79 s | `fn-bpc-u64-bytes-fields` 37 s and `-have-eight-octets` 32 s (0 subgoals: the whole cost is simplifying `Goal` with `floor`/`mod` over constants, 10 M steps) | e (arithmetic) | Treat a u64 as two u32 halves and reuse `fn-bpc-u32-octets-fields`, which takes 1.9 s. | 65 s |
| 19 | `nntp-invariants` (seam) | 75 s | `fn-nntp-next-or-last-preserves-consistent-session` 62 s (a 3 kB `:use` instance, 624-way split) | c | Replace the instance with a lemma about the next/last result. | 60 s |
| 20 | `records-canonicality` (seam) | 68 s | `fn-record-parse-groups-reencode-prefix` 40 s and `-value-length` 21 s (induction, 43 and 38 defs, 25 to 36 k steps/s) | c (e\*) | Give an inductive step lemma for one parsed group. Profile the low rate first. | 55 s |
| 21 | `peer-feed-invariants` (seam) | 49 s | no event over 8 s; many between 2 and 7 s | e | Not worth a lane on its own. | |
| 22 | `owner-invariants` (seam) | 46 s | `fn-own-snrt-step-keeps-configuration` 35 s (hint enables ten step functions, 19 122 sg) | a | One configuration-footprint lemma per arm, the snr repair's shape. | 34 s |
| 23 | `wire-outbound-invariants` (dev) | 45 s | `fn-wire-drive-of-host-rendered-article-preserves-source` 43 s (a 4-instance `:use`, 1481 sg) | c | Turn the instances into a rewrite rule. | 40 s |
| 24 | `frame-journal` (seam) | 43 s | `(verify-guards fn-frame-workflow-encode)` 37 s (101-way split) | b | As for `frame`. | 35 s |
| 25 | `records-invariants` (seam) | 41 s | `fn-record-impl-round-trip` 39 s (4 sg, 27 k steps: **1 k steps/s**) | e\* | Profile first. | up to 37 s |
| 26 | `bp-workflow-binding-core` (seam) | 31 s | enabling `fn-bp-binding-statep` opens 63 defs, in three events of 14, 8 and 8 s | a | Close the recognizer and give field lemmas. | 25 s |
| 27 | `bp-workflow-invariants` (seam) | 30 s | `-work-with-status-preserves-workp` 12 s and `-work-with-attempt-` 9 s (47 defs) | a | Same shape as 26. | 20 s |
| 28 | `statement-invariants` (seam) | 29 s | `fn-stmt-header-encoding-bound` 12 s | e | | 10 s |
| 29 | `bp-bundle-invariants` (seam) | 27 s | `fn-bpb-encode-block-head` 17 s (260 sg) | e | | 15 s |
| 30 | `bp-adu` (seam) | 20 s | `fn-bpa-encoding-bound` 17 s (3 k steps/s) | e\* | Profile first. | 15 s |

By class, over the top 30: (a) 13 books, carrying most of the seconds
(store cluster, bp-release, bp-node-machine through defrecord, bp-primary's
codec, tcpcl, sequence-fidelity, peer-config, feed-connection, owner,
bp-workflow). (b) 4 books, with 1228 s of guard proofs between them
(peer-inbound, store-node, frame, frame-journal). (c) 5 books, with 347 s in
their top events. (e) and (e\*) 8 books.

## 4. The tenth: a prioritized list

Each row is replayed on the seam run's graph (310 books) and on the dev head
projection (425 books), with the changes above it applied. The **after-times
are estimates**. A repaired event is set to 2 to 5 s (guard proofs 5 s), and
the only measured anchor is T4-snr's (466 s and 416 s became 0.01 s). A lane
that repairs a book measures its own number.

| # | change | owner | seam run wall at jobs 8/16/24 | dev head wall at jobs 8/16/24 | CPU (seam / dev) |
|---|---|---|---|---|---|
| 0 | today: requested order, seam at jobs 4, dev at jobs 8 | | **1638** | **1649** (1072 once the snr repair below lands, which it has) | 4778 / 5907 |
| 1 | runner: critical-path-first, jobs 16 | **done here** | 1595 | 1648 | same |
| 2 | `store-node-resolution` prepare arms closed (T4-snr) | **on dev** | 1076 | 1072 | 4121 / 5250 |
| 3 | `peer-inbound`: guard hints for `fn-peer-command` | lane | 1037 | 1061 | 3324 / 4453 |
| 4 | `store-node`: guard hints for `fn-sn-finish`, export disable of the prepare arms | lane (low in the graph: root's treewide run) | 1037 | 1061 | 2958 / 4087 |
| 5 | `store-node-invariants`: per-arm finish lemma, prepare/complete field lemmas | lane | 1037 | 1061 | 2699 / 3828 |
| 6 | `bp-primary-invariants`: CRC width per type, codec closed | lane | **482** | **516** | 2144 / 3273 |
| 7 | `bp-release-invariants`: replay by record kind, forward pin through preservation | lane | 482 | 506 | 2144 / 2894 |
| 8 | `defrecord`: `<recognizer>-forward-shape` in a minimal theory | lane (bottom of the graph: recertifies everything once) | 322 | 366 | 1896 / 2645 |
| 9 | `store-node-traces`, `owner-invariants`: arm lemmas instead of `:use` fans | lane | 292 | 312 | 1772 / 2521 |
| 10 | guard hints in `frame` and `frame-journal`; `nntp-effects` date length; `nntp-invariants` next-or-last | lane | 234 | 269 | 1555 / 2304 |
| 11 | the 30 to 100 s tier: anchor, tcpcl-octets, tcpcl-session, sequence-fidelity, peer-config, policy, bp-primary-cbor, records-canonicality, records-invariants, feed-connection, wire-outbound | two or three lanes | 173 | 197 at 16 (205 at 8) | 1120 / 1636 |
| 12 | the rest of `bp-primary-invariants` (three events of 26 to 36 s) and `bp-bundle-invariants` encode-block-head | lane | **148** | **187** | 1019 / 1535 |

**Where it lands.** The seam run goes from 1639 s to about 148 s, which is
11 times faster and meets the target. The dev head treewide run goes from
1649 s to about 187 s, 8.8 times faster. Measured from where dev stands today
(1072 s, with snr already repaired), that is 5.7 times, and ten times would be
107 s. It stops short for a reason. After row 12, dev's chain is `records >
records-invariants > statement-codec > statement > statement-invariants (32)
> store-files-invariants > store-node > store-node-invariants (48) >
store-node-traces (19) > store-node-resolution > owner-invariants (12) >
owner-config`, and no single book on it is over 50 s. The books that remain
heavy are `anchor-invariants` (93 s after its top event is repaired),
`tcpcl-session` (82 s), `tcpcl-octets` (62 s) and `feed-connection-invariants`
(53 s). Each of them spreads its time over many medium events. Reaching 107 s
means taking those four books and `store-node-invariants`' remaining 48 s
apart as well. Below about 20 s per chain the fixed per-book cost of section
2 is the floor, so a chain of 12 books cannot go below about 10 s.

**Scheduling after the repairs.** Once rows 2 to 12 land, CPU / jobs comes
close to the chain, and the order starts to matter. On the dev projection at
jobs 8, requested order gives 310 s and critical-path-first gives 192 s. At
jobs 4 the figures are 491 s and 384 s. Row 1 is cheap today and pays for
itself after the proof work.

**What does not help.** More jobs than 16 changes nothing. Neither does
changing the include structure or the toolchain options for loading (section
2). ACL2's provisional certification (`--pcert`) would take the chain out of
the wall: the Convert wave has no edges, so its floor is the largest single
book. On today's seam run that means about 805 s plus the Create and Complete
chains. But `triage-2026-09-22.md` records the project's decision that pcert
is the discovery mode and not the certification mode, for ACL2's own reasons.
It is listed here only as the one lever that is not a proof repair, and it
needs a decision from ember before anyone uses it.

The largest waits in practice are not in this list, because they are not
proof time. They are the lane runs that recertified 60 to 150 books from
`sha256` up with an empty cache ("Certification cost" in `how-we-work.md`),
and runs sharing a box (section 1). An `--affected-by` run against a cache
that holds `dev`'s head avoids both.

## What was implemented

`tools/certify_books.py` now schedules a parallel run critical-path-first:

- `archived_walls(books)` reads each book's most recent `book_wall_seconds`
  from `planning/evidence/manifests/`. That directory is pushed to the farm
  with the tree. A book with no archived wall counts as 1 s.
- `critical_path_priority(books, graph, walls)` gives each book its own wall
  plus the longest chain of requested dependents above it.
- `run_schedule(..., priority)` takes the ready book with the largest value
  and breaks ties by requested order. `--jobs 1` keeps requested order
  exactly, as before.
- Under `--pcert`, Create and Complete use the same priority. Convert has no
  edges, so its priority is longest-book-first.
- The manifest records a new `schedule` field: the policy, the number of books
  with an archived wall, and the predicted critical path.

Tests, in `tests/test_certify_runner.py`, class `CriticalPathScheduleTests`
(the file passes 36 of 36):

- the priority values on a small DAG (three small free books, and a chain of
  three large books listed last);
- the start order that `run_schedule` produces on that DAG, with and without a
  priority;
- the real runner with a fake ACL2 and an archived wall file: the chain head
  takes a first slot, and the manifest's `schedule` field is checked;
- one job keeps requested order;
- the runner's policy replayed on a virtual clock for that DAG: 31 s in
  requested order, 30 s with the chain first.

What it would have saved: 31 s on the seam run (1638 s to 1607 s, replayed
with the walls archived before that run), and nothing on the freeze or on dev
head at jobs 8, where the chain is the whole wall. After the proof repairs it
saves 118 s of 310 s on the dev head tree at jobs 8.

`make check` exits 0.
