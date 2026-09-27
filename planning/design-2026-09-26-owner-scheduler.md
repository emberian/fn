# The owner's scheduler: one mutation owner, three tiers, bounded quanta (2026-09-26)

Lane owner-scheduler (Fable 5.1), ember's priority 2 of 2026-09-26 ("we need a
better mutation scheme"), from gpt-6's consolidation review section 7
(planning/review-2026-09-26-gpt6-consolidation.md): "one semantic owner does
not require one enormous critical section". The finding it answers is PKT-321
(qual-b6759850, qual-dfa810fc, qual-69046a76: under three tight-loop readers
and one POST every 0.5 s, control-socket requests queued past their 10 s
deadline from t = 384 s, served reads had minute-long outliers, POST p99 was
84 s). The measured numbers are in
planning/evidence/owner-scheduler-2026-09-26.md; the requirement is HST-023,
the proof target PRF-248, the scenario SCN-171.

## 0. What was wrong, in one sentence each

- **The mutex decided the order.** `sb-thread:with-mutex` admits whichever
  thread wins the wake-up race; the thread that just released it, whose
  socket already has the next command, wins again (barging). Three readers
  in a tight loop can hold the owner indefinitely against a control request
  that arrived seconds earlier. Nothing in ACL2 decided this; nothing in the
  tree could bound it.
- **The critical section rendered the reply.** A served step's reply was
  written into the live octet buffer and copied out under the mutex
  (PRF-192): O(reply) array work per step while every other connection
  waited; a 3 MiB ARTICLE held the owner for its whole walk.
- **Two critical sections per read.** The exposure charge (PRF-161) took the
  mutex, released it, and the step took it again: two gate passes, two
  chances to lose the race.
- **Host bookkeeping queued with semantics.** The service's worker and client
  lists were edited under the owner mutex, so an accept or a worker's exit
  waited behind a POST's fsync.

## 1. The three tiers

1. **The bounded semantic step** (under the mutex; ACL2's transition). One
   served read with its drain (`fn-owner-chunk-span`, then `fn-owner-take`
   and the durable attempt when the read produced a submission), one
   control-socket request, one transit step, one maintenance step (the
   checkpoint capture, the publication's done step, the log reopen decision,
   a connection's open, close and release). It updates authoritative state
   and returns a typed result. Its work is bounded by the books that define
   it; this design does not change a step's semantics or its size. The
   authoritative journal writes (the Store's record and frontier, the FNFD
   feed journal) happen inside it: durable acceptance is decided here and
   nowhere else.
2. **The render plan** (an immutable value produced by the step against the
   connection's pinned view; rendered outside the mutex). The step's effects
   are pointers into the pinned archive and are never mutated, so the step's
   result IS the plan: `fn-splan-step-make` carries the effects, and
   `fn-splan-step-plan` appends the drain's completion reply, the redeem
   reply and the exposure close as `(:reply octets)` effects. Rendering is
   `fn-splan-window` into a fresh buffer of the window's size, the
   continuation an immutable value again; ACL2 sizes the window
   (`fn-splan-window-size`, section 3.3): the remaining octets of the effect
   the window starts in, zero exactly when the plan is done
   (`fn-splan-window-size-is-positive-until-done`).
3. **I/O execution** (outside the mutex; connection-multiplexing's I/O
   loop, host/native/mux.lisp, two threads for every connection). It
   receives the octets, asks for a step, renders the plan's first window
   (`fnn-mux-queue-plan`) and, each time the socket has taken a window,
   renders the next (`fnn-mux-flush`) before it reads the connection again;
   the connection record holds one window and the plan's continuation,
   never the whole reply, and hands the step's outcomes (close, STARTTLS,
   consumed prefix, submission) back into its bookkeeping. A deferred step
   (`:defer MS`, the exposure charge) arms the connection's resume timer
   and the same octets are stepped again. The loop holds no owner state; it
   calls the owner only through `fnn-owner-serialized` with the
   connection's class. A pull's logical connection renders its plan the
   same way in the pull thread (host/native/pull-service.lisp
   `fnn-pull-local-send`).

What leaves the critical section: the rendering of ARTICLE, BODY, HEAD, OVER
and every other reply's bytes (the array writes and the copy), the socket
writes (already outside since PRF-192; now also the windows), and the
diagnostic sink (already a queue with an ACL2-bounded backlog, PKT-508: a
sink that stops draining costs the serving threads nothing). What cannot:
the semantic step itself and the journal writes it performs; the exposure
charge (it is part of the step's admission and is now decided in the same
critical section as the step); the reading of the step's typed result off
the ACL2 globals (a pointer copy, O(1)).

## 2. Service classes and the fairness rule (ACL2 decides)

Four classes, in `*fn-osch-order*`: **control** (the control socket's
requests: status, health, group create, control grant, admin, key
management, the hybrid author path; and the maintenance steps: the
checkpoint capture, the publication's done step, the log reopen),
**reader** (a reader connection's quanta: its open, served steps, idle
decision, TLS establishment, close and release), **poster** (the operator's
submission through the control socket, `operator post`:
`fnn-owner-control-submit-serialized`), **transit** (a peer connection's
quanta, the push feed's steps, the pull feed's, the BP node's and its
applications': `fnn-owner-transit-serialized`). The class of a quantum is
the socket it arrived on: a host observation, never a decision about the
request's content; a connection's later quanta carry the class its open
established (ACL2 named a peer: transit), so the control class holds no
per-connection bookkeeping and a control request queues only behind other
control requests and maintenance. A served POST is a reader quantum whose
step includes the drain, as before: "POST's semantic step is unchanged".
Every caller names its class explicitly or through the transit wrapper; the
default of `fnn-owner-serialized` is control, the class of the callers
that are the control socket's (admin, auth, keys, login bindings, peer
invite, hybrid control).

The rule (books/owner-scheduler.lisp): the host keeps a count of waiting
threads per class and a per-class FIFO of arrival tickets; when the owner is
free it asks `fn-osch-next (s waiting)` which class runs. The answer is the
first class with a waiter in cyclic order from a cursor, and the cursor
moves to the slot after it. Within the picked class the head ticket enters.
A quantum is what runs between the gate's admission and the release.

**The theorem** (`fn-osch-control-waits-at-most-the-bound`, PRF-248): for
every cursor and every sequence of waiting observations in which control has
a waiter, at most `*fn-osch-bound*` = 3 quanta of the other classes run
before a control quantum. So a control request's wall-clock wait is at most
three quanta of the others plus its own, and a quantum is one bounded step:
under the mixed hour's load that is three served steps (a median 1 ms, a
long OVER hundreds of ms, a POST's durable attempt hundreds of ms on ZFS),
not the unbounded run of reader steps the bare mutex allowed. The same
cyclic scan gives every class the same bound (the argument is symmetric in
the slot). Teeth: from cursor 1 with every class waiting the delay is exactly
3; with control absent for four picks and present at the fifth the delay is
4 and the theorem's conclusion fails (the hypothesis-removal witness).

**The quanta per class**, today: reader, one served step (bounded by the
served machine's work per read: the wire's line and body limits, PRF-161's
per-address step rate); poster, one durable attempt (bounded by the record
codec's ceilings and the profile); transit, one served step on a peer
connection or one feed tick; control, one request (a status page render is
bounded by the report's size; a group create is one publication). None of
these bounds is new; what is new is that a class's quantum count between two
control quanta is bounded by the theorem. "Large responses yield" is the
render tier's property (windows), not the step's: a step that answers a
20,000-row OVER still builds the rows inside its quantum (PKT-476 (3), the
arms' cost) and yields only after; splitting such a step into resumable
quanta is the arms' redesign (catalog-slice 7b, served-line-iterative), in
section 3.3.

## 3. The plan, its invariants, and the join with the arms

### 3.1 The invariants

- **A plan built at version v renders exactly the pinned view's bytes.** The
  connection's pinned view (its archive, trie and buckets, or after
  catalog-slice 7b its version over the catalog) is what the arm read when
  it produced the effects; the effects hold pointers into it; ACL2 values are
  never mutated, and a reclamation appends (it does not rewrite a row's
  handle in place: catalog-slice's answer to payload identity). So whatever
  the owner does after the step, the plan denotes the same octets.
  `fn-splan-windows-are-the-reply`: a plan drained to done wrote
  `fn-served-reply-octets` of the effects, for any window size and any
  pacing. `fn-splan-window-is-a-prefix-of-the-reply`: every window is a
  prefix of what remained, at most W long, and non-empty while anything
  remains (the loop progresses).
- **The mutex is held only across a bounded step.** Every entry is
  `fnn-owner-gated`; nothing renders, writes a socket, sleeps or waits on a
  log inside; a thread that enters the gate while it holds the owner is a
  host fault (the nested quantum would wait on itself; SBCL's recursive-lock
  error said the same before the gate). The gate records each hold's duration and each wait's
  duration and folds them into ACL2's histogram (`fn-osch-observe`; the row
  invariant `fn-osch-row-observe-keeps-okp`: the five buckets sum to the
  holds), which `health` prints. A hold over a second is visible as such.
- **The live octet buffer is input-only under the mutex.** `fn-octets` is
  filled from the socket's byte vector for the span read and the POST
  payload; the reply is rendered into the thread's own `fn-octets$c` object.
  The publication thread keeps its congruent `fn-octets-pub`.

### 3.2 The typed step (adapter-retirement-2's ServedStep fence)

`fn-owner-chunk-span` returns `(:served-step EFFECTS CLOSEP STARTTLSP
SUBMITTEDP CONSUMED REFUSAL-LINES EXPOSURE-CLOSE)` (`fn-splan-step-make`,
recognizer `fn-splan-step-p` checked once at the boundary) instead of
installing six globals; the host reads it through the accessors. This is the
shape adapter-retirement-2's `books/owner-results.lisp` names as ServedStep
with the plan's effects in the reply slot. Batch AQ reverted
adapter-retirement's merge (two modules red on the batch image), so
`fn-splan-step-make` is the ServedStep heading to dev; when that lane's
book returns, one of the two definitions goes (deletion map row 6).

### 3.3 The plan effects the arms will emit (specified, not implemented here)

Today the retrieval arms build the reply list inside the step: ARTICLE
appends the status line, `fn-nntp-stuff-lines` of the stored lines and the
terminator (books/nntp-responses.lisp `fn-nntp-article-response`); OVER
builds its rows. The plan vocabulary admits typed effects the renderer
expands off the mutex, so an arm can emit the plan and not the bytes:

- `(:reply-lines STATUS LINES)`: the status line, then the dot-stuffed block
  of LINES and the terminator. Renderer case: `fn-nntp-stuff-lines` (now a
  loop, served-line-iterative) over the pinned lines, a window at a time.
  Keystone owed with the arm change:
  `fn-splan-render-of-reply-lines-is-the-arm-octets`, equating the rendered
  octets with the `(:reply ...)` the arm builds today.
- `(:reply-rows STATUS ROWS)`: an OVER or HDR row set rendered per row.
- After catalog-slice 7b: `(:reply-arena STATUS HANDLE PART)` naming an
  arena range and the part (head, body, whole), rendered from the byte
  owner; the version pinned by the connection resolves the handle.

Each kind adds one case to `fn-splan-fill` and one keystone; the loop, the
windows and the host are unchanged.

**The window size is ACL2's** (`fn-splan-window-size`, asked by
`fnn-owner-render-next` before every window). Today every effect is
materialized: an octet list the arm built inside the step. Holding that
list while a slow client drains the reply costs sixteen octets per octet
(a cons and a fixnum) where the rendered vector costs one, so a windowed
render of a materialized effect would retain up to sixteen times the reply
per draining connection and falsify connection-multiplexing's
per-connection figure (books/connection-budget.lisp, PRF-223: two
articles and a status line). The rule is therefore: the window is the
whole of the effect it starts in, one loop pass of O(reply) rendering
(tens of milliseconds for a 3 MiB list, the same order as the socket
write) and one vector retained while the socket drains; the
per-connection reply term stays the mux lane's, and PKT-644 (a) stays open
until the arms emit the pinned kinds above, whose windows are the fixed W
that bounds the loop's work per pass (a pointer into the pinned view
retains nothing). A plan of several effects (a POST's 340 and its
completion, an XREDEEM's reply, the exposure close) is several windows,
so the loop's next-window path is exercised now. These are the arms' books
(catalog-slice, served-line-iterative), not this lane's; the interface is
recorded in build/lanes/owner-scheduler/LANEDUMP.md.

## 4. The host (host/native/owner.lisp, control.lisp; owner-host.lisp)

- The gate: `fnn-owner-gate` (a short mutex and a condition variable; the
  per-class waiting counts, tickets and serving counters; the holding
  thread; ACL2's scheduler value). `fnn-owner-gate-enter` waits until the
  owner is free, ACL2 named this thread's class and the thread holds the
  class's head ticket; `fnn-owner-gate-leave` folds the hold and wait and
  asks ACL2 for the next class (nil when nobody waits). The class's slot is
  ACL2's too (`fn-osch-classp`, `fn-osch-class-index`); the host keeps no
  order of its own. `fnn-owner-gated` wraps the (now uncontended) owner
  mutex in the two. The gate mutex is held for a list update and one ACL2
  call, never across a step or I/O.
- `fnn-owner-serialized (service cid thunk &optional (class :control))`: every
  semantic entry names its class; the loop's open is :reader and its later
  quanta (step, idle, TLS-established, close, release) carry the
  connection's class (:transit for a connection ACL2 named a peer at open);
  the control-socket submission is :poster; the feeds, the pull and BP call
  `fnn-owner-transit-serialized`; the control socket's other verbs default to
  :control.
- `fnn-owner-handle-chunk`: one gate pass per read: the clock, the charge
  (`(values :defer MS)` when ACL2 defers), the span read, the typed step, the
  refusal lines to the log queue, the drain when the step submitted, the
  redeem, the fence on an uncertain outcome; returns the PLAN and the step's
  five outcomes.
- The loop (host/native/mux.lisp): `fnn-mux-step` hands the step the
  connection's class and turns `:defer` into the resume timer (the mux's
  own pre-step charge, `fnn-mux-charge`, is gone: one gate pass per read);
  `fnn-mux-queue-plan` renders the first window (`fnn-owner-render-next`:
  ACL2's size, a fresh buffer, `fn-splan-window`) and `fnn-mux-flush`
  renders each next window when the socket took the last, off the mutex; the
  record holds `plan` (the continuation) and `class`. The mux's host-list
  edits (clients, workers) moved from the raw owner mutex to the roster
  mutex. tests/native_owner_chunk_loop_raw.lisp drives the shipped loop and
  step against stubs (three clock readings for an open and two chunks now:
  the charge no longer costs a reading of its own).
- host/native/pull-service.lisp `fnn-pull-local-send` renders the plan into
  the pull's reply (it had read the step's first value as octets).
- The roster mutex protects the host lists (workers, clients, publisher, the
  stop flag's publication to the accept threads); their edits no longer
  queue at the gate.
- `health`: `fn-native-live-status-host-answer` takes the scheduler value
  and appends `fn-osch-health-lines` after the log-sink line
  (fn-nh-report-exit-of-render-and-more: the exit code is unchanged).

## 5. The deletion map (gpt-6 section 10: what replaced what)

| # | Removed | Replaced by | Where |
| --- | --- | --- | --- |
| 1 | `fnn-owner-exposure-wait`: a second critical section per read for the charge | the charge decided in the step's critical section; `(values :defer MS)` to the caller | host/native/owner.lisp |
| 2 | `fnn-owner-reply-from-buffer` and `fn-owner-reply-buffer`: the reply rendered into the live `fn-octets` and copied out under the mutex | the plan rendered into a fresh buffer per window off the mutex (`fnn-owner-render-next`, `fn-splan-window`, the loop's `fnn-mux-flush`) | host/native/owner.lisp, host/owner-host.lisp, host/native/mux.lisp |
| 3 | the six served-step mailboxes read by the host after `fn-owner-chunk-span` (`fn-owner-effects`, `-closep`, `-starttlsp`, `-submittedp`, `-consumed`, `-refusal-lines`) | one typed result, `fn-splan-step-make`, checked once (`fn-owner-chunk`, the Python bridge's list read, still installs them) | host/owner-host.lisp |
| 4 | `fn-owner-output` as a byte vector for the drain's completion (`fnn-owner-octets-global`) | the completion as the ACL2 octet list, a plan effect (`fnn-owner-list-global`) | host/native/owner.lisp `fnn-owner-drain-one` |
| 5 | `fnn-with-owner` around host bookkeeping (client and worker lists, the publisher slot, the stop flag's client shutdown) and around `fnn-control-live-status-answer` | the roster mutex; the live status as a gated :control quantum | host/native/owner.lisp, host/native/control.lisp |
| 6 | the runtime mutex's wake-up order as the scheduling decision | `fn-osch-next` (ACL2) with the host's per-class FIFO | host/native/owner.lisp |
| 7 | (owed, not done here) the arms' in-step rendering of ARTICLE/OVER bytes | the plan effects of section 3.3 | books/nntp-responses.lisp, books/nntp-overview.lisp: the arms' lanes |
| 8 | `fnn-mux-charge`: the loop's own gate pass for the exposure charge before every step | the charge decided in the step's quantum; `:defer` arms the resume timer | host/native/mux.lisp |
| 9 | `fnn-with-owner` around the loop's host lists (clients, workers, the publisher) | the roster mutex | host/native/mux.lisp, host/native/owner.lisp |
| 10 | `+fnn-owner-classes+`, `fnn-owner-class-index` by position, `(some #'plusp waiting)`: the host's copy of the class order and of the idle test | `fn-osch-classp`, `fn-osch-class-index`, `fn-osch-next`'s nil | host/native/owner.lisp |
| 11 | `+fnn-owner-render-window+` = 65,536 and `fnn-owner-write-plan` (the per-connection thread's window loop) | `fn-splan-window-size` (ACL2) and the loop's `fnn-mux-queue-plan` / `fnn-mux-flush` | host/native/owner.lisp, host/native/mux.lisp |

The socket writes were already outside the mutex (PRF-192); the FNFD feed
journal's write and fsync stay inside the POST's quantum (the authoritative
journal is not a log); the service log was already an offered queue
(PKT-508).

## 6. What this does not claim

- No step is smaller than before: a long OVER or XPAT still holds the owner
  for its arm's work; the bound is in quanta.
- The bound is proved over the scheduler's pick function and the host's
  waiting counts; that the host reports the counts correctly and serves the
  class's head ticket is the host's (a raw Lisp queue under a mutex, read
  by inspection and exercised by tests/test_native_owner_scheduler.py), not
  a theorem.
- The bound is on the control class's turn, not on one request's place in
  its FIFO: a control request behind N control requests (or a maintenance
  step) waits N + 1 turns, each at most three quanta of the other classes
  away. That is why no per-connection quantum is control.
- A materialized reply is one window: the loop's pass renders the whole
  list (tens of milliseconds for 3 MiB, on the loop thread that owns that
  connection) rather than retain the list sixteen-fold while a slow client
  drains. The fixed window W that bounds the loop's work per pass arrives
  with the pinned effect kinds (section 3.3); until then PKT-644 (a) is
  open with this reason.
- The rendering off the mutex assumes the effects are immutable and the
  pinned view outlives the connection's use of it, which is ACL2's value
  semantics and the pin policy (NNT-042); a reclamation that rewrote a row's
  bytes in place would break it, and the catalog design forbids that.
- The measurement is one box, loopback, shared with other lanes; its scope
  is stated with every number in the record.
