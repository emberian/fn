# time-model (2026-09-27): the disk as an adversarial environment, slice 1

Lane time-model (Opus 5.5). Design: planning/design-time-model-2026-09-27.md
(READY FOR REVIEW). Ids: PRF-311, HST-026, SCN-182, PKT-853. Base dev
4fe07cc21.

## 1. What slice 1 is

A batch barrier is a request with a deadline, the disk's mode is ACL2's over
RECORDED time, reads and status never wait on a pending barrier, and a POST
arriving while the disk is slow is refused try-later with the reason.

- books/owner-time-model.lisp (`fn-otm-*`): the gate's value (OCP DISK CLOCK)
  over the pipeline's (books/owner-commit-pipeline.lisp); pick, fold and
  commit steps unchanged. DISK: the pending barrier (issue time, deadline,
  slow flag), the last and max completed latency, the slow episodes. CLOCK:
  the recorded time (max of the readings) and the regressions count.
- Time is a recorded event (design section 3.7): every disk event carries
  one monotonic reading the host takes INSIDE the gate mutex
  (host/native/owner.lisp fnn-owner-disk-event), recorded before the event
  applies; every decision reads the recorded time.
- The deadline D: the live configuration's `barrier-deadline-ms` limit row
  (host/owner-host.lisp fn-owner-barrier-deadline), default 5,000 ms.

## 2. The assurance chain

native entry (fnn-owner-commit-pipeline: :issue after fnn-owner-start-syncer,
:clock at each expiry of the timed wait, :return on :collect;
fnn-owner-handle-chunk-read -> fnn-owner-disk-admit -> fnn-owner-shed-queued-locked;
fnn-owner-sched-snapshot for health/status) -> executed ACL2 subjects
(fn-otm-disk-event, fn-otm-wait-ms, fn-otm-admit-post, fn-owner-shed-outcome
= fn-owner-outcome :refused + fn-otm-shed-reply, fn-otm-health-lines /
fn-otm-disk-lines, fn-otm-next, fn-otm-commit-event, fn-otm-committer-wake)
-> keystones (section 3) -> observed result (section 5).

## 3. Theorems (PRF-311; REPL-admitted on hbox, book + test book)

- KEYSTONE `fn-otm-barrier-reader-bound`: with the barrier pending (phase
  :staged) and a reader waiting at every pick, the commit class waiting only
  when the committer's wake is :start-next, the quanta before the reader
  hold no control/poster/transit quantum, at most one START-NEXT that took
  members, and inspects <= commits + 1. The commit's event is unconstrained
  (the first draft's "every event is a START-NEXT's" hypothesis was found
  redundant and removed after the weakened theorem was PROVED).
- KEYSTONE `fn-otm-disk-event-keeps-the-pipeline`: no disk event changes
  the pipeline's value, so the durability keystones (PRF-267/272) hold of
  every run with deadlines.
- `fn-otm-next-is-ocp-next`, `fn-otm-commit-event-is-ocp-commit-event`,
  `fn-otm-observe-keeps-the-disk`: the scheduler keystones carry over.
- `fn-otm-recorded-time-is-monotone`, `fn-otm-shed-only-past-the-deadline`,
  `fn-otm-past-the-deadline-sheds`, `fn-otm-shed-iff-slow`,
  `fn-otm-return-recovers`, `fn-otm-clock-event-never-issues`,
  `fn-otm-return-records-the-latency`, `fn-otm-wait-reaches-the-deadline`,
  `fn-otm-issue-only-when-none-pending`, `fn-otm-issue-is-pending-and-admits`.

Teeth (tests/acl2/owner-time-model-tests.lisp): a reached run from
fn-otm-init (START, issue at 1,000 ms, clock events at 3,000/5,999/6,000,
a 30 s stall, a regressed reading, the completion at 31,000); exact
health/status lines, log lines and the shed reply; each keystone's complete
antecedent and conclusion; removal witnesses for the reader bound (barrier
not pending: a control quantum runs; no reader waiting: three :inspect
quanta, no :commit; the commit waiting past its wake: two START-NEXTs) and
for the wait theorem (a reading one short; no barrier pending); must-fail
for the unhypothesised statements.

Cost: the book loads in 3.0 s ACL2 time with its includes (REPL, hbox);
certification figures in section 5.

## 4. What is NOT done (the design's later slices)

The stall deadline H and the in-flight members' uncertain answer; 440 at
the POST command (the served session machine's input); IHAVE 436 / CHECK
431 during `slow` (transit is not admitted in flight: peers wait, TCP
backpressure); mutating control try-later; the inline barrier (PKT-825 (c))
and configuration publication as requests; the `policy set
barrier-deadline-ms` admin verb (the limit slot is read; books/native-admin
does not yet accept it); the decision journal; clock events in the record
log for durable time decisions; `clock-event-ms` as a profile field (the
cadence is a constant, 1,000 ms).

## 5. Native (SCN-182) and certification

Certification: books/owner-time-model certified on hbox inside native-r1
(certify-20260927T180859Z-1964698: 3.1 s wall, 1,246,809 prover steps; the
only uncached book of the image closure). The test book is REPL-admitted on
hbox (all 90 forms); the batch certifies it (Makefile root added).

Images: tools/hbox_native.sh --images developer,production --mem 40G on hbox.
- r1 (7841d17f5): the developer image build failed: host/owner-host.lisp
  defined fn-owner-shed-outcome before fn-owner-outcome (program-mode
  definition order; classified implementation, mine). Fixed in 5666b6762.
- r2 (5666b6762; developer image sha256 b34ab815...53bdc9):
  - tests.test_native_owner_scheduler OK (7 ran), log 3da86b53...ccba
    (its source assertions now name fn-otm-next / -observe / -commit-event /
    -committer-wake).
  - tests.test_native_commit_log OK (8 ran), log d192a748...ded0c1.
  - tests.test_native_owner 17/18, log d2889f8d...c1: the one red is
    test_the_chunk_loop_keeps_its_suffix_and_reads_a_clock_per_step ("the
    suffix was not the next step's input: NIL", a raw compile of
    tests/native_owner_chunk_loop_raw.lisp): the red scheduler-3's record
    names as input-loop-2's, red on dev; not this lane's.
  - tests.test_native_slow_disk: 1 of 2 failed at its LAST check (STAT on a
    reader that had not re-pinned: a reader keeps its version until GROUP;
    classified harness). Fixed in 1184f28c3 and rerun on the same r2 images
    (--no-build): OK (2 ran), log 2f699431...ccba:

```
disk stalled 30s: reads n=98 max=0.003s (baseline max 0.000s); status n=49 max=0.168s
(first third max 0.168s, last third max 0.138s); health max 0.156s;
disk slow: barrier 7227 ms pending deadline-ms=5000 slow-episodes=1 posts=try-later;
shed POST answered in 0.001s: b'441 posting failed; the disk is slow (a write has waited
7252 ms, deadline 5000 ms): nothing was stored, try again later\r\n'; held POST 240 0.008s
after the device came back; health after: last-barrier-ms=30433 slow-episodes=1;
next POST b'240 article received OK\r\n'
```

Reading: with a barrier stalled 30.4 s, 98 reads (GROUP, ARTICLE) peaked at
3 ms and 49 `status` calls (each a whole CLI process) at 168 ms, with no
growth from the first third of the stall to the last; `health` and `status`
said `disk slow` from the deadline on; a new POST was refused with the reason
in 1 ms and was not stored (STAT 430 after recovery); the held POST was not
answered during the stall and got its 240 8 ms after the device came back;
`health` then said `disk ok` with the 30,433 ms barrier and one episode; the
next POST was accepted. The service log named the episode entered and left.

Waiting vs working: about 25 min of this lane was waiting on two image
builds and module runs on hbox (r1 wasted on the definition-order error);
the proofs took minutes each in the REPL (one 60 s timeout on a first walk
formulation that case-split badly, fixed by stating one step's facts as
lemmas over okp).
