# Design: the disk, the network and the clock as an adversarial environment (2026-09-27)

Lane time-model (Opus 5.5). Status: READY FOR REVIEW (the design); slice 1 is
built on lane/time-model (section 9). Ids: PRF-308, HST-026, SCN-182, PKT-845
(from tools/next_id.py on dev 4fe07cc21; the coordinator renumbers at merge if
another lane took one).

Ember, 17:40Z on F4: "maybe we need a much more robust scheduler/time/event
model, because a laggy disk that needs maintenance is a real fact of life that
we shouldn't sandpaper away with our model."

## 1. The problem in one paragraph

The owner is a cooperative quantum scheduler (books/owner-scheduler.lisp,
owner-commit-class, owner-commit-steps, owner-commit-pipeline). Its proved
bounds are counted in QUANTA: status waits at most one quantum
(fn-ocs-inspect-waits-at-most-one), control at most three of the other
classes (PRF-248). Converting that into seconds needs "each quantum is
short", and nothing makes it so when a quantum or the thing a request waits
for touches the disk. A 5 s fdatasync, a device that stalls for a minute
while a RAID rebuilds, a full disk, a read-only remount: today each of those
becomes "everything behind it waits", with no deadline, no honest answer to
the client, and nothing in `health' that says why. The F4 bar ("within one
scheduling step") inherits the longest step, which is the disk's. The
measurement shows the shape even on a healthy ZFS pool: control 284/284
under 10 s but p99 6.1 s; a served read peaked at 10.35 s (F4.md).

## 2. What already exists (and is kept)

The migration is incremental because a lot of the model is already right.

| piece | today | where |
|---|---|---|
| The barrier off the owner | the batch's append+fdatasync runs in the syncer thread with the owner RELEASED; START and COMPLETE are :commit quanta | owner-commit-steps, owner-commit-pipeline; host/native/owner.lisp fnn-owner-commit-pipeline, fnn-owner-start-syncer |
| Admission during a barrier | :inspect (status/health), :reader and :commit only (PKT-828) | fn-ocs-in-flight-admits-only-inspect-commit-and-reader |
| Reads during a barrier | at the reader view (the completed prefix), never the batch in flight | books/owner-reader-view.lisp, owner-reader-read.lisp (PRF-288, PRF-296) |
| Replies after the barrier | a member is told 240/441 only in a COMPLETE after its barrier returned fenced; a failed barrier is the stop (exit 3), every member uncertain | fn-ocs-members-told-only-after-the-barrier, fn-ocs-failed-barrier-stops-telling-no-member |
| The barrier's completion is already an event | the syncer leaves its word (:fenced / :failed) and notifies the committer, which reports it to ACL2 (fn-ocp-commit-event) | fnn-owner-commit-pipeline |
| The clock is already partly an input | every read hands the owner one reading (monotonic ms + wall ms, fn-owner-observe) | fnn-owner-advance-clock |
| The service log does not block on the disk | lines are offered to the log writer thread (PKT-508) | host/native/io.lisp fnn-log-line |

What is missing is the other half of "the completion is an event": a
completion that does not come. Nothing has a deadline, time never reaches a
decision about I/O, and there is no mode in which the node says "the disk is
slow" and acts on it.

## 3. The model

### 3.1 Environment, events and time

The node is a state machine; its environment is adversarial and unbounded in
latency: the disk, every peer and client socket, and the clock. The rule:

1. **The owner never blocks on I/O.** Every I/O the owner needs is a
   REQUEST it issues (a barrier, a publication, a checkpoint write, a feed
   journal flush, a peer send), carried out by a thread or loop that is not
   the owner, and every request ends in exactly one COMPLETION EVENT:
   `(:ok ...)`, `(:failed condition)`, or `(:timeout)`. The owner consumes
   events; it never waits inside a quantum for one.
2. **Time is an input event.** A decision that depends on time takes a
   monotonic clock reading (`now`, milliseconds, from
   `get-internal-real-time`, CLOCK_MONOTONIC on Linux and Darwin) as an
   argument. Nothing in ACL2 reads a clock; the host never compares times.
   A deadline expiring is a clock event `(:clock T)` appended by whoever waits
   (the committer's timed wait in slice 1); section 3.7.
3. **A timeout is not a failure.** An fdatasync that has not returned after
   its deadline is PENDING, not failed: the bytes may yet become durable.
   Only the device's own error (EIO, ENOSPC, EROFS) is a failure, and a
   failed barrier stays what it is today: the recovery event (store fenced,
   exit 3, every member uncertain). The deadline changes what the node does
   *while* it waits, never what it concludes about durability.

### 3.2 Requests and their classes

| request | issued by | completion consumed by | today's wait |
|---|---|---|---|
| batch barrier (append + fdatasync of the record log) | START / COMPLETE (seal) | the committer, then COMPLETE | syncer thread, owner released; **no deadline** |
| inline barrier (bound submission, BP transit, operator post) | a :control / :poster / :transit quantum | the same quantum | **inside the quantum, owner held** (PKT-825 (c)) |
| feed intent flush (a configured peer) | START, per member | START | **inside the START quantum** (PKT-825 (a)) |
| configuration publication (config/ records, live reconfigure, XREDEEM) | a :control quantum | the same quantum | **inside the quantum, owner held** |
| checkpoint publication | the publisher thread | the owner, at the next quantum | off the owner already |
| service log line | any quantum | the log writer thread | off the owner already |
| socket reads/writes | the mux I/O loops | the loops (render off the mutex) | off the owner already |

The migration moves each "inside the quantum" row to the first form: issue in
one quantum, complete in a later one, with the owner released in between.

### 3.3 The disk's state: a mode, decided by ACL2

`books/owner-time-model.lisp` (slice 1) carries the disk's observed state in
the scheduler's value: the barrier pending (issued at T, with deadline D),
the last completed barrier's latency and the maximum seen, and a count of
slow episodes. The disk's MODE is a function of that state and `now`:

| mode | when | the node does |
|---|---|---|
| `ok` | no barrier pending, or pending for less than D | everything as today |
| `slow` | a barrier pending for D or longer | reads and status/health answered from the durable view as always; the in-flight batch's posters keep waiting (their reply follows the completion event); **new POSTs refused try-later** (nothing stored); health and status say `disk slow: barrier N ms pending (deadline D ms)`; the service log says when the mode was entered and left |
| `stalled` (slice 2) | pending for H (a second, larger profile field) or longer | as `slow`, and the in-flight members are answered **uncertain** and closed: their bytes may still land, and their clients must check (RFC 3977 section 6.3.1: "SHOULD either check whether the article was successfully posted before resending"); mutating control is answered try-later |
| `failed` | the device returned an error | today's recovery event: fence, every member uncertain, exit 3 |
| `read-only` / `full` (slice 3) | the device refuses writes (EROFS / ENOSPC on an append) | a failed barrier today (exit 3). Proposed: the refusal is known *before* anything was appended (a pre-append ENOSPC is a refusal, not an ambiguity), so the node stays up serving reads and answers every write try-later with the reason, until the operator frees space or remounts; `health` exit 1 |

Transitions are ACL2's: `ok -> slow` at the first clock event `(:clock T)` or
admission with `now - T >= D`; `slow -> ok` at the barrier's completion
event (`recovered after N ms` in the log and in health until the next
barrier); `* -> failed` at a failed completion. Recovery needs no operator
action: the next completion event is the recovery.

### 3.4 What each client is told (accepted / refused / uncertain / pending)

The four answers stay distinct at every boundary:

- **Accepted** (240 / 235 / exit 0): only after the member's barrier
  returned fenced (unchanged keystone).
- **Refused** (441 for POST, 436 for IHAVE, 431 for CHECK, a distinct exit
  code for the control socket): nothing was stored and nothing was
  prepared. A try-later refusal is a refusal: the client may retry.
- **Uncertain** (441 "the outcome is uncertain, do not repost" and a close;
  436 and a close for transit; exit 3 for control): the bytes may or may not
  become durable. Reached only by a failed barrier (today) or by the
  `stalled` mode's deadline H (slice 2), never by the slow deadline D.
- **Pending**: no answer yet. A member of a batch whose barrier is
  pending is pending until the completion event (or H). Pending is honest:
  RFC 3977 promises the poster a response, not a time.

The RFC choice for "try later" on POST. RFC 3977 section 6.3.2 gives 436
("Transfer not possible; try again later") to IHAVE only; POST has 440 at
the command ("Posting not permitted") and 441 after the article ("Posting
failed"). So a new POST during `slow` is answered **441 with the reason**
(`441 posting failed; the disk is slow (a write has waited N ms, deadline D
ms): nothing was stored, try again later`), and slice 2 moves the refusal
forward to the POST command itself as **440 with the same reason**, so the
client does not send the article for nothing (that needs the disk mode as an
input to the served session machine: the high-fan-in part, deliberately not
slice 1). IHAVE gets **436** with the reason; CHECK / TAKETHIS **431** / **439**
(RFC 4644 sections 2.4, 2.5); a peer is thus deferred with the protocol's own
retry code, and fn's own outbound feed already treats 431/436 as back-off
(books/peer-feed.lisp). The brief's "436 for new POSTs" is therefore 441 now
and 440 in slice 2: 436 is not a POST response.

### 3.5 Deadlines and budgets are profile fields, decided by ACL2

- **D, the barrier deadline** (`barrier-deadline-ms`, a `:set-limit` row of
  the live configuration, read like `log-batch-records`; default 5,000 ms).
  After D the node is `slow`. A profile that legitimately takes longer for a
  batch (a 64 x 4 MiB batch on a spinning disk) raises it; D27: admission
  policy belongs to the operator's profile, and an unset row is ACL2's
  default, never a host constant.
- **H, the stall deadline** (`barrier-stall-ms`, slice 2; default 60,000 ms).
- **Q, the work bound per quantum**, the owner's own CPU work: already the
  batch bound (`log-batch-records`, `log-batch-octets`), the exposure charge
  (PRF-161) and the render windows. Q is separate from I/O waits because no
  I/O happens inside a quantum once the migration is done; until then the
  rows of section 3.2 marked "inside the quantum" are the exceptions the
  F4 statement names as hypotheses.
- **Per-class answer deadlines** (the F4 D below) are derived, not
  configured: D_read = (quanta bound) x Q_time, stated with its hypotheses.

### 3.6 Maintenance: what the operator sees and does

| the disk | health | status | the log | the operator does |
|---|---|---|---|---|
| healthy | `disk ok: last barrier N ms, max M ms, slow episodes K` | the same line | nothing | nothing |
| slow | `disk slow: barrier N ms pending (deadline D ms)`; new POSTs refused | the same line | `disk slow: barrier pending past D ms` once, `disk recovered after N ms` once | look at the device (iostat, zpool status); raise D if the profile is simply slow; nothing to restart |
| stalled (slice 2) | `disk stalled: ...`, health exit 1 | the same | per member answered uncertain | as above; clients check with STAT |
| full / read-only (slice 3) | `disk full` / `disk read-only`, exit 1 | the same | the refusal | free space or remount; the node resumes at the next successful barrier, no restart |
| failed | the node stopped, exit 3 | n/a | the recovery event | `fn recover`, as today |

Planned maintenance (slice 3): `operator maintenance begin|end` puts the node
in a drain mode (new writes refused try-later with "maintenance", reads
served, the in-flight batch allowed to complete), so an operator can quiesce
writes before a device operation without stopping the service.

### 3.7 Determinism: time is a recorded event, the fold reads the last one

Requirements (ember, relayed by the coordinator 2026-09-27, after Fare
ch. 3): "all sources of non-determinism are either eliminated or recorded";
the log records the non-determinism the host produces, clock readings
included, so the fold is a pure function of the log; a clock reading is an
EVENT the host appends, never a call made inside an owner step; the fold's
deadline logic reads the last recorded time.

**The rule.** The host reads the monotonic clock and APPENDS a clock event
`(:clock T)`; ACL2 records T in the owner's value (the last recorded time,
kept monotone); every time-dependent decision (a deadline, an admission, a
rendered figure; later retention and expiry) reads the last recorded time,
never an argument taken from the environment at decision time. A decision
that needs a fresh time asks for one ON DEMAND: the host appends a clock
event immediately before it, in the same critical section.

**Who appends clock events, and when.** Every disk-clock reading is taken
inside the gate mutex that orders all clock events, so a reading below the
recorded time is a true regression of the clock, never two producers'
readings arriving out of order.

| producer | when | cadence field |
|---|---|---|
| the committer | at each expiry of its timed wait while a barrier is pending (the wait is ACL2's `fn-otm-wait-ms`: the time to the deadline, then the cadence) | `clock-event-ms` (profile; default 1,000 ms) |
| the committer | stamped on the barrier's issue and on its completion (the event carries its reading; recorded before the event is applied) | on demand |
| a served read quantum | today's `fnn-owner-advance-clock` reading, once before the read's transition, feeds `fn-owner-observe` (the injection date); a POST's shed admission appends its own clock event just before it decides | on demand |
| the health/status render | once, before the render | on demand |
| an idle owner (slice 2) | at the cadence, so recorded time never lags wall progress by more than the cadence while nothing else happens (retention and expiry decisions) | `clock-event-ms` |

**Where the events are recorded.** Two logs, by what the decision
produces:

- A decision that reaches DURABLE state (an injection date; slice 3:
  retention expiry, a stall's uncertain answer) is preceded in the RECORD
  LOG by the clock event it read: the event rides the same batch as the
  records it stamps (one more entry, no extra fsync), so recovery's fold
  (`fn-cpr-replay`, `fn-ock-recover-extended`) reads recorded time and
  replays byte for byte. Today the injection's observation is inside the
  article's stored octets, which is the same property for that one use.
- A decision that produces NO durable state (the disk's mode, a shed POST,
  health's figures) records its clock events in the owner's DECISION
  JOURNAL (slice 2: the (event, reading) pairs the gate and committer fed
  ACL2, written by the log writer thread, never on the owner), because the
  record log is exactly what a slow disk cannot take: a clock event that
  had to be durable before the node could say "the disk is slow" would wait
  behind the stalled barrier it is measuring. The durable fold is
  independent of these by theorem (fn-otm-disk-event-keeps-the-pipeline:
  no disk event changes the pipeline's value; no shed produces a record).

**A late or backward clock event** is recorded and decided by name, never
smoothed:

- *Backwards* (`T` below the last recorded time; a monotonic clock should
  never do this, so it is a host or kernel defect): the event is recorded
  as `:clock-regressed` (the count shows in health), the recorded time
  stays at its maximum, and no deadline moves backwards: a mode already
  `slow` stays slow. (The wall clock's own discontinuities stay
  `fn-owner-observe`'s: `:refused`, `clock-unusable` replies.)
- *Late* (the gap since the last clock event exceeds the cadence, e.g. the
  committer thread was descheduled): the next event records the gap (slice
  2: `:clock-late GAP` in the journal and in health). Deadline logic
  applies at the recorded time, so a late event can only make a deadline
  fire LATER than wall time would, never earlier: the answers stay honest
  (a POST admitted near the deadline is pending, not lied to), and the
  F4-W bound carries the cadence as a named term (H + Q_max + cadence).

Slice 1 implements the rule for the disk's decisions: every disk event
carries its reading and is recorded first (the disk state's `now` and
`regressions`); `fn-otm-admit-post`, `fn-otm-wait-ms`, `fn-otm-disk-lines`,
`fn-otm-shed-reply` read the recorded time only. The decision journal and
the record log's clock entries are slices 2 and 3; lane proto-determinism
hands over the other ambient reads it finds (`fnn-owner-wall-milliseconds`,
salts, ordering), each of which becomes one of the producers above or goes.

## 4. The F4 bar this proposes

F4 as written ("every control request within 10 s; no read past the
work-quantum bound") mixes a proved quanta bound with an unbounded quantum
length. Proposed, in two statements, each with its hypotheses and its
scope:

**F4-R (reads and status).** Every served read and every status/health
request on the log route is answered within **D_R = 3 x Q_max** of its
admission to the gate *regardless of the disk's state*, where Q_max is the
longest quantum that contains no I/O wait. Hypotheses: (h1) the store commits
through the record log (format 9); (h2) no quantum admitted while a barrier
is pending contains an I/O wait: true of :inspect, :reader and the
committer's START-NEXT today; (h3) the served read's octets are in memory
(the arena), not a device read; (h4) the host's CPU is not starved. Proved
part: while a barrier is pending, before a waiting reader is admitted only
:inspect and :commit quanta run, at most one START-NEXT that took members,
and at most one :inspect more than the :commit quanta
(fn-otm-barrier-reader-bound, slice 1). Measured part: Q_max and the
latency under an injected 30 s stall (slice 1's native case).

**F4-W (writes).** Every POST is answered accepted, refused, uncertain or
try-later **within H + Q_max** of its article's arrival, and every POST
arriving while the disk is `slow` is refused try-later within Q_max.
Hypotheses as F4-R plus (h5) the barrier's completion event or the tick
reaches the committer (a thread that is not blocked on the device). Slice 1
proves and measures the second half (a new POST during `slow` refused at
once, with the reason); slice 2 adds H and with it the first half.

**Mutating control** (group create, grant, operator post) is today a
:control quantum that waits for the in-flight COMPLETE and then publishes
config/ records with its own fsyncs inside the quantum. Its F4 statement
becomes F4-W's form after slice 2 (answered try-later during `slow`, its
publication an I/O request) and the carried-state work of PKT-825 (f) /
control-quanta (the quantum's CPU work, not its I/O). Until then it is
named as the exception, with its measured tail.

The 10 s client deadline stays as the qualification's observable; the bar is
F4-R and F4-W with their hypotheses stated next to the numbers.

## 5. What carries over (proofs)

- Every scheduler keystone carries over unchanged: the new top value's pick
  IS the pipeline's (fn-otm-next-is-ocp-next), and the committer's events
  map one-to-one (fn-otm-commit-event-is-ocp-commit-event). PRF-248,
  PRF-267, PRF-272 (pipeline) and PKT-828's admission theorems are cited,
  not restated.
- The durability keystones (fn-ocs-members-told-only-after-the-barrier,
  fn-ocp-complete-only-after-the-barrier) are untouched: the deadline never
  produces a :complete, and `slow` never tells a member anything.
- The reader view (PRF-288, PRF-296) is untouched: a shed POST never joins a
  batch, so the capture discipline sees nothing new.
- The shed POST's outcome is fn-own-outcome's :refused outcome (no pin
  moved, nothing durable, feeds unchanged) with the reply text ACL2 renders
  for the reason; the served-invariants' refusal case covers the state.
- New obligations: the disk-state machine's transitions and their teeth
  (slice 1); the stall deadline's uncertain answer (slice 2: a new release,
  `:stalled`, beside fn-ocs-member-release's, with the keystone that no
  member is told acceptance or refusal before a fenced completion even when
  H fires); the pre-append refusal of full/read-only (slice 3: a crash-model
  point: the refusal is decided before `log-written`, so no cut changes).

## 6. What moves in the host (an incremental migration)

- **Slice 1 (built)**: the committer's wait for the syncer becomes a timed
  wait whose timeout ACL2 names (fn-otm-wait-ms); the barrier's issue, each
  timeout and the completion are events into the gate's value; a reader
  quantum whose step queued a POST asks ACL2 whether to admit it and, when
  the disk is slow, sheds the queued POSTs as refusals with ACL2's reason
  line; health and status render ACL2's disk line from the gate's value and a
  clock reading taken at the request.
- **Slice 2**: H and the `stalled` release; the POST command's 440
  (disk mode into fn-scr-post-step's config input as an admission flag,
  high fan-in: one lane certifying itself); IHAVE's 436 and CHECK's 431
  during `slow` (transit admitted in flight only to be answered try-later);
  mutating control answered try-later during `slow`; the admin verb
  `policy set barrier-deadline-ms N` (books/native-admin.lisp's slot list).
- **Slice 3**: the inline barrier (PKT-825 (c)) and the feed intent flush
  (PKT-825 (a)) ride the committer's batch as requests; configuration
  publication becomes a request with its own completion event (the :control
  quantum stages, a publisher completes); ENOSPC/EROFS before the append
  become the `full` / `read-only` refusals; `operator maintenance`.
- **Slice 4**: the peers and the network in the same form (a peer send is a
  request with a deadline: the feed worker's backoff becomes ACL2's event
  consumer), the mux loops' idle deadline as an event, and an audit that the
  served read touches no device (h3).

## 7. Rejected alternatives

- **A watchdog thread that kills the owner after a long fsync.** A slow disk
  is not a failure; killing converts "slow" into "uncertain for everyone"
  and restarts into the same slow disk.
- **Answering in-flight posters uncertain at D.** D is a latency figure an
  operator tunes for throughput; H is the honesty deadline. Conflating them
  would turn every slow batch into "check with STAT".
- **O_DIRECT / async fsync (io_uring) now.** The request/completion model
  is the prerequisite; the mechanism under it is a later choice, and the
  syncer thread already gives the owner the asynchrony.
- **436 for POST.** Not a POST response (RFC 3977 section 6.3.1).

## 8. Open decisions for ember (packets)

- **PKT-845 (a) the default D.** 5,000 ms proposed (a healthy batch is
  milliseconds on hbox's pool; 5 s is well past any healthy fdatasync and
  under the 10 s client deadline). Rejected: 1 s (a spinning disk under a
  64 x 4 MiB batch sheds spuriously). Continues without it: the default is
  one constant in books/owner-time-model.lisp.
- **PKT-845 (b) whether `slow` changes health's exit** (today: the line
  only, exit unchanged). Proposed: exit 1 (degraded) in `stalled`, not in
  `slow`.
- **PKT-845 (c) F4's bar** as F4-R / F4-W above, replacing "within one
  scheduling step".

## 9. Slice 1: what was built (see planning/evidence/time-model-2026-09-27.md)

Filled in by the slice's record: the book, its keystones and teeth, the
host lines, the native case with an injected 30 s stall.
