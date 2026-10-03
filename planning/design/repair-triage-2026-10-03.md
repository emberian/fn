# Repair triage: tags independent of severity, and the fast rebuild-in-place order

Decision note, 2026-10-03, by the TCB-SHRINK architect (Claude Fable 5.1), analysis only (no code).
Inputs: planning/repair/ (241 items at 02:30 UTC; the brief said 214, the ledger grew),
build/coordinator/inspection-sweep-2026-10-03.md, Astra's r71/r72 FINDINGS, check-lane-355a5c843,
decisions/tcb-shrink-2026-10-03.md with its review outcome, lanedumps/failure-scope.md and
failure-scope-review-1.md, build/coordinator/lock-check-burndown.md (129 rows), and the lanes'
branches (lane/host-lifecycle, lane/owner-offlock, lane/codex-fence-boundary). Every item carries the
tags below in its JSON (`repair.py show ID` prints them; `python3 repair.py list` is unchanged).

## 0. The answer

- 48 of 241 items are LIVE today (reachable on a running node by a remote client, an operator verb on a
  deployed node, or a data-loss path on a deployed platform); 108 are CONDITIONAL (a race, a fault, a
  non-default platform or configuration, a stalled disk); 85 are LATENT (gates, tests, packaging, parked
  code, proof tooling, stale comments).
- 151 are LOCAL (the fix is the fix whatever gets rebuilt); 55 DISSOLVE in a named rebuild slice (their
  code is replaced and the finding becomes that slice's acceptance test or theorem); 35 are BRIDGES
  (live today, dissolve later, need a hand fix now). Of the 35 bridges, 25 are already fixed on a lane
  branch, in progress, or duplicates of one that is; 10 need new hand work, and two of those are
  deployment controls rather than code (section 3).
- The generated WRAPPER layer alone (FAILURE-SCOPE's def-section/def-actor: closed classification,
  fence before unlock, monotone exit escalation, registration with the join as the receipt,
  admit-or-close, the connection-scoped envelope) dissolves 36 ledger items and the whole R7 class of
  the lock-check burndown (88 rows), in about five lane-days, before any actor moves into ACL2. It is
  the best defects-per-day step by a factor of ten and goes first. The primitive close/errno words
  dissolve R10 (41 rows) and four items in three days. Then OWNER-OFFLOCK's queued-work pattern (six
  live items), then the actors in parallel: committer, mux, cold line, services.
- Severity and urgency are different axes: of the 51 high-severity items, 22 are live (19 distinct), 19
  are conditional and 10 are latent; 15 of the 51 dissolve in the wrapper or an actor and need no
  hand fix at all. Nothing in the tagging says "fix immediately" because it is high; section 3 says
  which ten need a hand now.

## 1. The tagging scheme

Three axes, written into every item by `repair.py set ID exposure=... locus=... disposition=...
[slice=... acceptance=...]`.

EXPOSURE (independent of severity; what it takes to reach the defect on the node as deployed):
- `live`: reachable today on a running node: a remote client triggers it (S010, S044, r71-F13), an
  operator verb on a deployed node does (S029, S033), or it is a data-loss path on a deployed platform
  (S045; r72-F1 on the OpenBSD friend node), or it is paid on every request (X05, r71-F11).
- `conditional`: reachable only in a rare or non-default condition: a race between two threads (S021,
  S084), a fault or EIO already in flight (S015-S020), a non-default platform or filesystem (S070,
  S086, S087), a configuration not in use (S088 proxy, S006 bp-node serve), a stalled disk.
- `latent`: not reachable today: gates/tests/packaging (CL*, S055-S064, S126-S142), parked or dead code
  (S078, S111, S115, S117), proof-tooling and generator work (DC*, GEN*, HM*, L0x, X06: raw dispatch is
  unsound but there are 0 raw entries), stale comments, the extracted product (S039, S041, S116).

LOCUS (the actor or subsystem the code belongs to after the rebuild; one of twelve):
committer, connections (the I/O loops, TLS, web face, the served step on a connection's behalf),
lifecycle (accept/stop/run, the log writer, the fence), cold-line (extent realizer, cold workers, leases),
reclaim-publication (reclaim pass, checkpoint publication, export, extent release), log-kernel (seal/
sync/rotate/recover/open), peer-services (feed, pull, BP, TCPCL), operator-verbs (control socket,
offline verbs, live admin), store-books, served-books, gates-tests-packaging, generators (def-*, HM,
proof tooling: work items, not defects).

DISPOSITION (what the rebuild does to it):
- `LOCAL`: survives any rebuild; fix it where it is (books, gates, verbs' semantics, served policy).
- `DISSOLVES-IN <slice>`: the code that holds the defect is replaced by that slice; the finding becomes
  an ACCEPTANCE TEST or THEOREM the slice must satisfy, named by `acceptance=` (section 1.1), so "goes
  away" is verified when the slice lands, never assumed. A DISSOLVES-IN item is never live (by
  construction: a live one is a BRIDGE).
- `BRIDGE <slice>`: dissolves in the slice, but the exposure is live today, so a small hand fix lands
  now and the slice supersedes it; the acceptance test still ships with the slice.

SLICES (the rebuild steps of section 2): `wrapper`, `primitives`, `carrier`, `pure`, `committer`,
`mux`, `cold-line`, `lifecycle`, `services`, `bp`, `log-kernel`, `verbs`, `reclaim`.

### 1.1 Acceptance classes (what `acceptance=` names; the slice ships each as a test or a theorem)

| class | the slice must show | items |
|---|---|---|
| wrapper:fence-before-unlock | a fault or indeterminate inside any section or gated body installs the fence BEFORE the mutex is released; a native injects at each site (`FN_NATIVE_*_FAULT` selectors) and the owner exits 3/4, never keeps serving | S016 S017 S019 S020 S080 r71-F1 r71-F2 r72-F2 |
| wrapper:closed-classification | `fn-fs-classify` answers :refusal only for a declared closed set; an unknown `fnn-store-error` subclass and every raw `error` classify :fault; theorem plus a teeth test with a fresh subclass | S023 S031 S074 S077 S090 S097 S109 X08 |
| wrapper:class-plus-step | an OS error AFTER the section's first durable effect classifies :indeterminate (exit 3), before it :refusal/:fault as declared; the step counter is the def-entry/def-holder cut list | S110 X10B r72-F6 |
| wrapper:exit-escalation | `fn-ort-stop-exit-escalate`: 3 dominates 4 dominates first-wins; S015's native (stalled barrier + SIGTERM + failed barrier) exits 3 | S015 S028 |
| wrapper:receipt-join | a thread's registration ends at the OWNER's join, never at self-deregistration; a hold after the publisher's/exporter's last shared effect keeps `fnn-owner-wait-workers` waiting; a NIL worker is impossible by type | S018 S084 r71-F10 r71-F12 |
| wrapper:admit-or-close | a socket handed to a stopping loop is admitted under the receiver's lock or closed and settled by the adopter; forced both orderings (`FN_NATIVE_ADOPT_HOLD`), no write to a closed wake fd | S021 r71-F9 |
| wrapper:connection-scoped | a per-connection or per-attempt failure (RST, refusal, socket error) ends that connection with a named outcome fed to ACL2; the process never stops; natives per listener (S001/S004/S006/S007 cases on lane/host-lifecycle) | S006 S007 S027 S036 |
| wrapper:accept-outcome-table | accept's errno classification (:again / :exhausted / listener-level) is an ACL2 table; the lane's `fnn-accept-attempt` lists are its hand version | S001 S004 |
| wrapper:actor-top-boundary | every thread's top handler is the generated envelope: no condition escapes a thread; the web face, the TLS accept threads and the log writer included | S030 S066 |
| wrapper:fence-step-pure | the fence is a pure state update (STOPPING, exit code, first fault) under the lock, logging after; two simultaneous faults record the first | S081 |
| primitives:close-row / lock-word / rename-word / errno-word | close returns :ok or (:uncertain errno) and every close site is a declared row (R10); flock answers :locked or (:error errno); rename-no-replace answers (:error EINVAL) as definite; pread returns the errno word, never "short file" | S075, S070, S087, S089 (R10's 41 rows) |
| committer:no-inline-reader | theorem `fn-cmt-no-section-while-waiting`: no commit from a :reader quantum while a batch is in flight; forced web-POST-during-batch schedule | S003 r71-F5 |
| committer:feed-off-owner / seal-off-owner | the FNFD frames and the seal's extension+append+fence are job phases off the owner (OWNER-OFFLOCK READY 1); a feed-journal device stall during START does not block a reader quantum (native) | S014 r71-F6 r72-F4 |
| actor:no-protect-exports | no `:protect t` export reachable from an actor step; `*inside-absstobj-update*` is 0 after every native | L03 |
| mux:no-cold-await | a cold miss on a loop thread is an issued row and an observation, never a wait; pipelined TLS lines with a cold second article keep the loop stepping other connections | S010 r71-F3 r71-F7 |
| mux:timer-eligibility | the next poll deadline is the minimum over the SAME predicate the timer fires on (theorem over `fn-mux-step`); a yielded cursor across an expired idle deadline sleeps, measured poll count | r71-F11 |
| mux:inbox-bound | accepted-but-unbegun sockets are bounded by ACL2's admission before the inbox | r71-F13 |
| mux:phase-machine / no-recursion | the connection phase machine is one ACL2 step (no :hs-wait double count; proxy deadline checked only when due; the handshake queue drains iteratively) | S085 S088 S091 CL14 CL15 |
| cold-line:lease-per-read | every pread off a lock holds an issued row or a page-file lease (HM T1(b)); `fn-pgs-fill-realize` is an instance; pause-after-capture-while-retirement-runs native | S022 S082 X14 r71-F4 |
| cold-line:visit-bound | a settlement quantum's work is bounded by its own groups, not all pending groups | r71-F14 |
| services:round-deadline / per-window-deadline / idle-wait / windowed-reply / web-on-loops / fd-registry | each worker's round has a deadline; a send's deadline is per window; an idle worker waits on a condition, not a 50 ms poll; replies are written as rendered windows; the web face is connections on the loops; journals of removed peers are closed | S054 S067 S106 S035 S145 S032 S144 S037 S065 S112 |
| lifecycle:reap-off-section / bounded-mailbox | the empty-head check runs before the section; the writer's mailbox bounds swaps as it bounds lines | r71-F8 r72-F7 |
| bp:step-bound | reassembly and dispatch are per-step quanta with a VISIT bound; a keepalive-only peer does not starve the accept loop | S008 S025 S026 |
| log-kernel:program-cut / windowed-zeroing | every writable-open effect (the rotation completion included) is a cut of `fn-lg-open-program` executed by the interpreter; tail zeroing is windowed | r72-F1 S047 r72-F8 |
| verbs:windowed-read | journal, import listing and import pass read windows through `fn-hx-list-window`/`-read-at`, never a whole file | S011 S013 r72-F10 |
| carrier:raw-dispatch / globals-to-stobj / program-to-logic | the owner's globals live in the carrier stobj; `fn-owner-io` and the writers are raw-dispatched; the per-POST guard is O(1) on the served fixture | X05 cg-owner-io-guard CL03 X16 CL13 |
| pure:encoder-roundtrip / acl2-parses / word-table | the DEFLATE encoder is ACL2 with `inflate(encode(x)) = x`; ACL2 parses the BP budget file; the refusal-word mapping is a table in books | S005 S146 r71-F15 |

## 2. The counts

Exposure x disposition (241 items):

| | LOCAL | DISSOLVES-IN | BRIDGE | total |
|---|---|---|---|---|
| live | 23 | 0 | 25 | 48 |
| conditional | 51 | 47 | 10 | 108 |
| latent | 77 | 8 | 0 | 85 |
| total | 151 | 55 | 35 | 241 |

Locus x disposition:

| locus | items | LOCAL | DISSOLVES-IN | BRIDGE | what the LOCAL ones are |
|---|---|---|---|---|---|
| gates-tests-packaging | 56 | 53 | 3 | 0 | check-lane reds, test weaknesses, release scripts (CL03/CL13/X16 dissolve in the carrier) |
| operator-verbs | 34 | 25 | 9 | 0 | effect order, stage cleanup, UID checks, self-signed files, anchor; 9 dissolve in wrapper/primitives/verbs |
| peer-services | 31 | 13 | 11 | 7 | books-level protocol fixes (S051-S053, S024, S098-S100); 7 live bridges (feed/pull deadlines, idle wait) |
| connections | 24 | 1 | 11 | 12 | S002 is the one local fix (the D27 buffer twins); the rest is the mux actor and the wrapper |
| reclaim-publication | 20 | 9 | 8 | 3 | ARENA-FORGET and retention (X01-X04, S038, S045, S050) are local; the fence class dissolves |
| served-books | 17 | 17 | 0 | 0 | served-catalog-live's and sweep-ops' work (SCL1-4, S042-S044, S120-S122, X07) |
| store-books | 15 | 15 | 0 | 0 | extracted-product and books fixes, dead entries |
| log-kernel | 12 | 6 | 5 | 1 | r72-F1 is the one live bridge |
| generators | 12 | 11 | 1 | 0 | work items (DC/GEN/HM/L); L03 is the committer actor's rule |
| committer | 9 | 0 | 2 | 7 | every committer item dissolves or bridges: it is the first actor |
| lifecycle | 6 | 0 | 3 | 3 | |
| cold-line | 5 | 1 | 2 | 2 | DH01 is the slice itself |

Slice x disposition (90 non-LOCAL items):

| slice | DISSOLVES-IN | BRIDGE | lock-check rows dissolved | effort (lane-days) | items per lane-day |
|---|---|---|---|---|---|
| wrapper | 27 | 9 | R7: 88 (about 72 swallow, 4 over-fence, 12 unfenced-gated) | 5 (Fable) + 3 (Opus site conversion) | 36 + 88 rows / 8 |
| primitives (close/lock/rename/errno words) | 4 | 0 | R10: 41 (21 ignored-close, 20 foreign-close) | 3 | 45 / 3 |
| committer | 1 | 5 (+ L03) | | 15 | 7 / 15 |
| mux | 5 | 5 | | 15 | 10 / 15 |
| cold-line | 3 | 2 | | 10 (with DH01) | 5 / 10 |
| services (feed, pull, web, control) | 1 | 9 | | 20 (4 lanes x 5) | 10 / 20 |
| lifecycle | 1 | 1 | | folds into wrapper + committer | |
| carrier (STAGE-5B) | 3 | 2 | | 10-15 (in progress) | 5 / 12 |
| bp | 3 | 0 | | 15 | 3 / 15 |
| log-kernel | 2 | 1 | | 20 | 3 / 20 |
| verbs | 3 | 0 | | 10 | 3 / 10 |
| pure | 2 | 1 | | 5-10 | 3 / 7 |

Severity against exposure, to make the point that they are different axes: high 51 = live 22
(19 distinct; 3 duplicates) + conditional 19 + latent 10; of the high ones 15 are DISSOLVES-IN and need
no hand fix (r71-F1 F2 F4 F9 F10 F12, r72-F2 F3's neighbours, S008, S016, S017, S019, S020, X08, L03);
of the 48 live ones 26 are medium or low (S014, S022, S029, S032, S033, S035, S037, S042-S045, S050,
S051, S053, S054, S065, S067, S106, S120, S122, S144, S145, X03, X07, S002's sibling). The lock-check
burndown's 129 rows are not ledger items; 88 (R7) dissolve in the wrapper and 41 (R10) in the primitive
close rows, so after steps 0 and 1 the baseline holds only what LOCK-CHECK cannot classify.

## 3. The fast rebuild-in-place order

Each step lands behind today's interfaces (the ~110 section sites keep their thunks; the actors keep
their threads; the natives are the control and stay unchanged), deletes what it replaces in the same
commit, and ships the acceptance classes of its items. Effort is honest lane-days at the swarm's
observed cadence (host-lifecycle: 13 items in two days; stage-5b tier A: 8 writers in one lane;
def-holder: 3,800 lines in three days).

STEP 0 (days 1-5): THE WRAPPER. FAILURE-SCOPE emits `def-section`/`def-actor` as ONE host envelope
and three ACL2 pieces (`fn-fs-classify` with a CLOSED refusal set, `fn-ort-stop-exit-escalate`, the
lifecycle machine with the join as the receipt), with failure-scope-review-1's four must-fixes (closed
refusal set; class-plus-step for OS errors after a durable effect; non-local exits declared or faulted;
the post-fence cleanup set without pending-extent release). t45 (lane/codex-fence-boundary) is its hand
version and lands first as the bridge for the fence class. Then an Opus lane converts the ~110 section
sites file by file (owner 43, mux 14, admin 7, feed 7, control 5, hybrid-control 5, pull 5, web 5, ...)
to the generated wrapper: mechanical, the thunks unchanged, LOCK-CHECK strict inside the converted
files. DISSOLVES: 27 items + 9 bridges verified (section 1.1's wrapper classes) + R7's 88 rows. This
step removes the two largest classes of the month (node-stopping: a client/peer event stops the node;
swallow: a fault keeps serving) without moving any decision into ACL2 beyond the classifier, and it is
what makes every later actor's failure table a declaration. Effort: 5 Fable + 3 Opus lane-days.
Parallel: yes (FAILURE-SCOPE, HOST-LIFECYCLE already there).

STEP 1 (days 2-5, parallel): PRIMITIVE WORDS FOR CLOSE, LOCK, RENAME, PREAD. The 43 `fn-hx-*` stubs
become the logic-mode signatures of books/host-primitives.lisp (F family only); io.lisp's `fnn-posix`
wrappers answer the words; every close site is a declared row in tools/lock_discipline_contracts.json
`close_sites` with its owner (R10's 41 rows: 21 ignored-close become `(:uncertain errno)` observations
the caller classifies, 20 foreign-close become rows). DISSOLVES: S070, S075, S087, S089 + 41 rows.
Effort: 3 lane-days (LOCK-CHECK's lane, it owns the contracts file).

STEP 2 (days 3-8, parallel): OFF-LOCK WORK AS A RECEIPT LEDGER. OWNER-OFFLOCK's READY 1 (lane/
owner-offlock cc97926c1, d7fe7f5c8: the seal's extension+append+fence and the FNFD frames are job
phases off the owner; `fn-oqw-*`) lands; the same pattern takes the cold await off the loop thread
(r71-F7: the await becomes an issued row the loop observes, the bridge for mux:no-cold-await), the
accept tick's reap check out of the section (r71-F8), and the offline-mode cache miss (S022). BRIDGES
verified: S014, r71-F6, r72-F4, r71-F7, r71-F8, S022. Effort: 4 lane-days beyond READY 1.

STEP 3 (week 2-3): THE COMMITTER ACTOR (tcb-shrink section 3.3, with the review's additions: the
forced web-POST-during-batch schedule, the feed-stall native, M1/M1b/M1c for the envelope, the seal off
the owner per OWNER-OFFLOCK). DISSOLVES/VERIFIES: S003, r71-F5, S016, S080, L03, and the committer's
wrapper rows become theorems. Effort: 15 lane-days (one Fable for the book, one Opus for the natives
and the deletion). Depends on step 0 (the envelope) and STAGE-5B tier A (landed on its lane).

STEP 4 (week 2-4, parallel with 3): THE I/O LOOP ACTOR. `fn-mux-step` over a loop stobj with child
connection stobjs; poll is the one blocking primitive; the timers, the interest mask, the idle deadline
and the phase machine are the step. DISSOLVES/VERIFIES: S010, r71-F3, F7, F11, F13, S085, S088, S091,
CL14, CL15, and the idle-deadline observation feeds `fn-exp-*`. Effort: 15 lane-days. Depends on step 0
and step 2's cold-await row.

STEP 5 (week 3-5): THE COLD LINE. DEF-HOLDER's DH01 (page-read-direct re-expressed; `fn-pgs-fill-realize`
as an instance) + the executor loop as `fn-cold-step` + HM T1(b)'s teeth as natives. DISSOLVES/VERIFIES:
S022, S082, X14, r71-F4, r71-F14. Effort: 10 lane-days.

STEP 6 (week 3-6, one lane per service): FEED, PULL, WEB, CONTROL as actors on the envelope; the web
face becomes connections on the loops (S037/S065 dissolve there, not before). DISSOLVES/VERIFIES: the 10
services items. Effort: 4 x 5 lane-days.

STEP 7 (weeks 5-8): BP/TCPCL actors (S008, S025, S026; 15 lane-days), the LOG KERNEL as an executed
program (r72-F1, S047, r72-F8; 20), the VERBS as programs over `fn-hx-*` (S011, S013, r72-F10; 10).

PARALLEL FROM DAY 1, no dependencies: PURE (S005 is fixed on lane/sweep-peer; the encoder's move to
ACL2 with the round-trip theorem, S146, r71-F15, and the 1,800 lines of section 1.2 of the plan: 5-10
lane-days), CARRIER (STAGE-5B in progress: X05, cg-owner-io-guard, CL03, CL13, X16), and the 151 LOCAL
items on their sweep lanes (served-catalog-live, sweep-gates, sweep-store, reclaim-retention,
arena-forget).

PARALLELISM. Once step 0 has landed, every actor is independent in the model but not in the files: the
committer and the loop both edit owner.lisp and mux.lisp, the cold line edits extent.lisp and
owner.lisp. Three actor lanes at once is the practical ceiling (committer, mux, cold-line), each owning
a line range the coordinator names, plus the four service lanes on their own files, plus carrier and
pure: eight to ten lanes, which is the swarm's size. Calendar: steps 0-2 in week 1; steps 3-5 in weeks
2-5; step 6 in weeks 3-6; step 7 in weeks 5-8. The 90 non-LOCAL items are dissolved or verified by
week 8; the wrapper's 36 (and the fence/node-stopping classes) by day 5.

WHY THE WRAPPER FIRST AND NOT AN ACTOR: 36 items + 88 rows in eight lane-days is ten times the rate of
any actor slice (the committer: 7 items in 15); the wrapper is a precondition of every actor (an actor's
failure table is a def-actor row); it changes no decision's owner except the classifier, so it is the
smallest in-place change; and it is the one step that turns this month's two defect CLASSES into
declarations, which is what ember asked for: findings that dissolve as the system improves, verified by
the acceptance classes, not by assertion.

## 4. The bridge list: the only items that warrant a hand fix now

35 items are tagged BRIDGE. Twenty-five are already handled: fixed on a lane branch awaiting READY
(S001/S004: `fnn-accept-attempt`; S006/S007: `fnn-connection-scoped`; S003/r71-F5: the logical
connection awaits; S010/r71-F3: item 3; S018/r71-F10, S021/r71-F9, r71-F11, r71-F12, r71-F13: items
9-13, all on lane/host-lifecycle; S014/r71-F6 and r72-F4: OWNER-OFFLOCK READY 1; S005: lane/sweep-peer
07d21aaaf; X14: lane/def-holder; X05/cg-owner-io-guard: STAGE-5B in progress; r72-F1: sweep-store in
progress). Their READYs land in the batch runner's next tranches; the acceptance tests in section 1.1
ship with the slices that supersede them.

The ten that need NEW hand work now, with the smallest fix that holds until the slice:

| item | locus | hand fix now (small) | superseded by |
|---|---|---|---|
| r71-F7 (owner.lisp:4366 `fnn-owner-cold-await`): a cold read parks the I/O loop thread | connections | OWNER-OFFLOCK's receipt pattern: the loop registers the row and returns to its poll; the settle is an `arrived` completion (the shape `fnn-mux-await` already has for commits) | mux (step 4) |
| r71-F8 (owner.lisp:5977): every accept tick enters a :control section to reap nothing | lifecycle | read the cold head's emptiness under the extent lock before `fnn-owner-serialized`; enter the section only when non-empty | step 2 / lifecycle actor |
| S022 (extent.lisp:1043): offline-mode cache miss preads under extent + owner | cold-line | route the duplicate test's miss through `fnn-owner-cold-issue-locked` (the issued row) as OVER's miss is, or bind `*fnn-extent-no-io*` and answer :cold | cold-line (step 5) |
| S054 / S067 / S106 (pull-service.lisp:433, :521, :438): one serial worker, no round deadline | peer-services | a per-round deadline from the profile (ACL2 names it; the host passes it to each `fnn-recv`) and a per-peer skip when exceeded | services (step 6) |
| S035 (feed-service.lisp:242): whole article under one 10 s deadline | peer-services | the deadline per `fnn-send-all` window, proportional to the window (the mux's `+fnn-mux-send-seconds+` per window is the model) | services |
| S145 (feed-service.lisp:23): the feed worker takes the gate 20x/s idle | peer-services | wait on the commit condition variable (or a per-feed waitqueue the COMPLETE notifies) instead of a 50 ms sleep-and-poll | services |
| S032 / S144 (web-host.lisp:120, pull-service.lisp:288): replies built whole by repeated concatenate | connections | write each rendered window to the socket as `fnn-owner-feed-logical` produces it (one `fnn-send-all` per window; drop the accumulator) | services (web on loops) |
| S037 / S065 (web-host.lisp:317, :322): one web thread serves inline | connections | NOT code: a deployment control. The public node's web port sits behind the edge's Caddy (fn-public-node-edge); rate-limit and connection-cap it there, and keep health on the control socket. No small in-process fix exists short of the web actor | services (web on loops) |

Everything else live is LOCAL and already owned (section 2's locus table): the served-books items
(SCL1-4, S042-S044, S120, S122, X07) on served-catalog-live/sweep-ops; the retention items (X02, X03,
X04, X11, S050) on arena-forget/reclaim-retention; S002 (the buffer twins) and S029 (the control
frame's list conversions) on sweep-ops; S033 (live reconfiguration reads the history under the owner)
on sweep-ops-cfg; S045 (no read-back before dropping covered segments: a verify step in the publication
program) and S051/S053 (books/peer-pull, peer-feed) on sweep-store/sweep-peer. None of them is
superseded by a rebuild slice, so none is a bridge: the fix is the fix.

## 5. What is deliberately NOT urgent

- The 10 latent high-severity items (S009, DC01, DC05, GEN-CARRIED-VIEW, GEN-TEETH, HM02, HM03, X06, X13,
  cg-report): work items and gates, on their lanes, no node behaviour depends on them today. X06 (raw
  dispatch drops conjuncts) becomes urgent the day the first raw-dispatched entry lands (the carrier
  slice), not before; it is tagged so.
- The 47 conditional DISSOLVES-IN items: no hand fix; their acceptance tests ship with the wrapper (27),
  the actors (16) or the primitives (4). A hand fix now would be deleted within weeks.
- The 85 latent LOCAL items: the sweep lanes' backlog in their own order (gates first where they are
  red today: B8 / host_loaded_check exits 1 in `make check`, X13's recertify).
- Duplicates (S004, X15, r71-F3, F5, F10, r72-F2, F8, F10, CL05) carry the tags of their primary so a
  listing by cell counts each defect once per primary; the counts above include them (241 rows); the
  distinct-defect figures are 48 - 3 live, 55 - 2 dissolve, 35 - 4 bridge.

## Appendix: regenerating the counts

`python3 planning/repair/repair.py list` prints the items; the tags are the JSON keys
`exposure`, `locus`, `disposition`, `slice`, `acceptance`. The tagging table that wrote them is the
session script (every item's tuple in one place); it should become `repair.py tag` or a committed
`tags.json` read by `repair.py report`, so that a new item without the three tags is refused and the
cell counts regenerate per report.
