| Rank/id | Class | File:line | Finding |
|---|---|---|---|
| F1 | bug | host/native/owner.lisp:5756 | Reclaim can leave an ambiguously replaced checkpoint and continue serving without a recovery fence. |
| F2 | bug | host/native/owner.lisp:5011 | Extent retirement swallows close uncertainty and core/integrity faults that require fencing. |
| F3 | bug | host/native/mux.lisp:635 | A legitimate cold-line prefix in a TLS record faults the entire service. |
| F4 | bug | host/native/owner.lisp:4964 | Checkpoint discovery holds the global extent mutex across pread, indirectly blocking the owner too. |
| F5 | bug | host/native/owner.lisp:4580 | Logical web submissions can execute an inline commit in the reader class while another batch is in flight. |
| F6 | bug | host/native/owner.lisp:2964 | Feed-journal write/fsync still runs under owner exclusion, bypassing the asynchronous barrier's responsiveness. |
| F7 | bug | host/native/owner.lisp:4366 | Cold-read waits suspend a whole mux loop; settlement can exceed the dependency deadline indefinitely. |
| F8 | bug | host/native/owner.lisp:5977 | Empty cold reaping can park the primary accept/SIGTERM loop behind a stalled barrier. |
| F9 | bug | host/native/mux.lisp:1393 | Adoption can enqueue a socket after its loop has performed its final inbox drain and exited. |
| F10 | bug | host/native/owner.lisp:5147 | A publisher removes its joinable identity before unpinning and running another service action. |
| F11 | bug | host/native/mux.lisp:1182 | An ineligible, expired idle timer makes cursor-yield intervals busy-poll. |
| F12 | bug | host/native/owner.lisp:5272 | A known rotation refusal inserts NIL into the worker roster and breaks shutdown joining. |
| F13 | claim-gap | host/native/mux.lisp:1389 | Accepted-but-unadmitted sockets have no capacity bound or reservation. |
| F14 | claim-gap | host/native/owner.lisp:4300 | A bounded cold-reaper iteration contains an unbounded retirement walk; response pins and COMPLETE have further collection-wide costs. |
| F15 | claim-gap | host/native/owner.lisp:2015 | The host itself decides the semantic prepare-refusal mapping. |
| F16 | nit | host/native/owner.lisp:4862 | The old pending-close wrapper is unused and its completion-path comment describes a different call path. |

Source coordinate: `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9`. This is a source review of the whole owner and mux, not certification or a runtime reproduction. The stage-0 comparison adds `39f3ed4eb`'s persistent direct cold-worker ownership path; it does not repair the surrounding mux/scheduler composition. No tracked files were changed; no build, ACL2, make, SSH, or box command was run. No coordinator-directory material was consulted. Line numbers below refer to this revision.

## F1 [bug] host/native/owner.lisp:5756 fnn-owner-reclaim-pass

The checkpoint install/swap quantum does not fence failures in its body, and the caller treats its propagated uncertainty as if fencing had already happened.

Quoted source, owner:5745–5768:

```lisp
(let ((sw (fnn-owner-gated (service :control)
 ...
 (fnn-state-checkpoint-install store stage)
 (setq installed t)
 ...
 (fnn-owner-core 'fn-owner-orcp-swap rebuilt)
 ...
 (setq swapped t)
 (fnn-owner-reclaim-barriers store)
```

`io.lisp:2825–2830` replaces the file, fsyncs its directory, then converts an OS error into `fnn-store-indeterminate`. Thus an exception after replacement but before fsync completion leaves `installed` NIL. The cleanup at owner:5792 only raises its own recovery condition when `(and installed (not swapped))`. Even that condition is raised after the gated body has released exclusion. `fnn-owner-gated` at 1573–1605 fences gate-entry/check/leave errors; it does **not** wrap body errors in `fnn-owner-shared-action-locked`.

The served caller is admin:432–437, outside its earlier serialized request quantum. Control:369–377 says:

```lisp
;; The owner has already fenced itself ...
(fnn-store-indeterminate (condition)
  (fnn-err "control request uncertain; owner fenced: ~a" condition)
  :uncertain)
```

**Interleaving/reachability:** A live `store reclaim --recorded` control thread replaces the checkpoint; directory fsync fails. A unwinds the owner mutex without setting service stopping, and the control handler only logs. B, a served client/committer, subsequently enters the still-live owner and operates on the pre-swap state. A failure in the recovery barriers after `swapped = t` likewise escapes without this fence. This is a reachable maintenance operation, not a hypothetical new caller. The docstring at 5634–5637 promises that service stops after install failure; this path contradicts it.

**Fix:** Put destructive installation, swap, and barrier error classification inside the shared failure boundary before releasing owner exclusion. Track publication attempt/uncertainty, not just successful return from install; do not let the control transport infer that fencing happened.

## F2 [bug] host/native/owner.lisp:5011 fnn-owner-release-extents

The broad maintenance catch converts ambiguous physical close and core/integrity failures into a log-and-continue outcome.

Quoted source, owner:4995 and 5011–5012:

```lisp
(incf closed (fnn-owner-release-pending-extents-locked pin))
...
(serious-condition (e)
  (fnn-err "CHECKPOINT release failed (files stay retired): ~a" e))
```

The called `fnn-extent-close` at extent:1244–1247 explicitly relies on its caller:

```lisp
;; Any error escapes with the tables/lease intact. The
;; owner fences; ambiguous close never refunds and resumes.
(when fd (fnn-close fd) (incf closed))
```

This caller does not fence. It also catches `fnn-extent-fault` from discovery verification at extent:869–873 and `fnn-store-fault` from reseating/quiet-set core calls. Its `fnn-owner-gated` quanta supply no body-fault fence, as in F1. The publisher has another broad catch at owner:5130–5142 that also logs core failures.

**Interleaving/reachability:** A checkpoint publisher enters physical retirement; close returns an error whose physical outcome is ambiguous. A releases locks, logs, and returns. B can continue serving/opening files while the pending table still names the old descriptor. If that error released the descriptor, reuse followed by another pending-close pass can target a different descriptor. The exact close-error outcome is platform-dependent; the verified defect is continuing after an outcome the code itself classifies as requiring a fence. Alternatively, a corrupted newly written checkpoint frame raises an integrity fault and is merely logged. Both paths are in automatic publication and reclaim completion.

**Fix:** Distinguish safe maintenance refusal from core/integrity failure and physical uncertainty. Route the latter through a terminal owner boundary before resuming service; retaining a lease is not a substitute for fencing an ambiguous descriptor.

## F3 [bug] host/native/mux.lisp:635 fnn-mux-step

A protected connection's valid prefix return from the cold-line splitter is misclassified as a core fault.

Quoted source, owner:4168–4175:

```lisp
(let* ((line-end (first (fnn-call 'fn-oct-line-end 0 (fnn-live-octets))))
       (first-line (try line-end)))
 ...
 (if (eq (car first-line) :warm)
     (second first-line)
   (cons :fnn-extent-cold first-line)))
```

Quoted source, mux:635–638:

```lisp
(cond ((or closing (= consumed (length incoming))))
      ((or redeemed submitted)
       (setf (fnn-mux-conn-input conn) (subseq incoming consumed)))
      (t (fnn-fault "protected owner read left a TLS suffix")))
```

**Reachable sequence:** On an established TLS connection without COMPRESS, put `DATE\r\nARTICLE <cold-id>\r\nDATE\r\n` in one decrypted read. The full speculative span hits the cold article, so owner retries and returns only the warm DATE line. It is neither closing, redeemed, nor submitted. Mux raises the quoted fault; `fnn-mux-guarded` at 329–334 calls `fnn-owner-fault-service`, stopping the entire owner. The analogous plaintext pipeline already appears in `tests/test_native_slow_disk.py:273–333`; that test's warm reader on another connection does not establish TLS composition.

**Fix:** Preserve any valid positive-progress protocol suffix on established TLS. If a restricted continuation vocabulary is necessary, carry an explicit prefix/continuation reason from the owner and include cold/refusal splits in it.

## F4 [bug] host/native/owner.lisp:4964 fnn-owner-release-extents

The supposedly off-owner checkpoint read holds the global extent mutex during blocking disk I/O, creating a path back to a globally blocked owner.

Quoted source, owner:4963–4965:

```lisp
(multiple-value-bind (octets lease)
    (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
      (fnn-extent-entry-fresh new-id eoff elen))
```

`fnn-extent-entry-fresh` calls `fnn-extent-read-entry` and thus pread before returning (extent:867). The ordinary synchronous realizer has the same lock scope: extent:1043–1044 calls `fnn-extent-entry` under the extent mutex; a miss enters the synchronous direct reader at 791. The new persistent worker's unlocked pread does not remove these other paths.

**Interleaving/reachability:** A publishing thread holds the extent mutex and stalls in a fresh checkpoint-frame pread. B takes the owner mutex for a served command, then needs the extent mutex (a cached payload access, cold admission, or pending-close settlement suffices). B now holds owner exclusion waiting for A. C's otherwise cached read, health quantum, or stop cannot enter the owner. Automatic checkpoint publication reaches this path with ordinary extent-backed payloads. This is lock convoying, not an asserted ABBA deadlock.

**Fix:** Capture a physical descriptor lease under extent exclusion, perform the read/verification with private storage outside it, then transfer/settle under the lock. Apply the same contract to maintenance discovery and synchronous fallback callers, not only the cold-line worker.

## F5 [bug] host/native/owner.lisp:4580 fnn-owner-handle-chunk-read

The socket-less inline commit shortcut is reachable from a `:reader` web request even though its implementation assumes no batch is already in flight.

Quoted source:

```lisp
;; web-host.lisp:111
(fnn-owner-handle-chunk service cid pending nil :reader)
;; owner.lisp:4580–4581
(when (and submitted (fnn-owner-service-batching service) (null socket))
  (fnn-owner-commit-queued-locked service)
```

Owner:3262–3265 states that the inline helper runs only at an idle owner because the gate admits no class that commits inline during a batch. But `books/owner-commit-steps.lisp:164–181` explicitly admits `:reader` in flight. `fn-otm-admit-post` (owner-time-model:606) does not shed every in-flight batch: it sheds when disk/space posture requires it. The inline path supplies `:idle` to `fn-ocs-commit-step`, independently of the actual scheduler phase.

**Interleaving/reachability:** A ordinary network POST starts a batch and its syncer. Before that barrier becomes slow, B finishes a web POST through `fnn-web-feed`; the admitted reader step queues it and immediately invokes inline START. START seals through `fnn-log-seal-open-batch`, whose `fnn-log-await-sync` (io:8007–8022) waits for A while B still holds the owner. The normal committer cannot perform its timed owner observations or COMPLETE during that wait. After return, the inline path is also manipulating batch/credit machinery outside the actual gate phase; I do not claim a particular double-ack outcome without a run.

**Fix:** Give logical connections the same queued completion contract as socket clients. A caller can synchronously await its private completion outside the owner; it must not independently drive an assumed-idle batch machine.

## F6 [bug] host/native/owner.lisp:2964 fnn-owner-drain-one

A slow feed-journal append or fsync freezes owner exclusion even when the store's main barrier is correctly offloaded.

Quoted source:

```lisp
;; owner.lisp:2964, inside START's owner quantum
(fnn-owner-feed-flush service intent-publication)
;; owner.lisp:899–902, reached by flush -> feed-append
(fnn-write-all (fnn-owner-feed-journal-fd journal)
               (fnn-octets envelope))
(fnn-owner-feed-phase journal :written)
(fnn-fsync-file (fnn-owner-feed-journal-fd journal))
```

COMPLETE repeats this for resolutions at owner:3251–3255 before replying. Bound submissions use it under the same owner exclusion at 3789 and 3807. Flush loops over the peer frame plan; each append crosses its own barrier.

**Interleaving/reachability:** Configure a matching outbound feed. A commits a served article and stalls in the feed intent's fsync while holding owner exclusion. B cannot obtain even a `:reader` or `:inspect` quantum. The committer cannot update its stall posture through the owner, and stop waits for the same mutex. This requires neither a malformed request nor the web path in F5.

The intent-before-store and resolution-before-offer order is correct; the defect is the blocking implementation of those ordered effects.

**Fix:** Represent feed persistence as part of the pending commit protocol, with an immutable frame plan and completion receipt. Perform the physical barrier outside owner exclusion while preserving the current ordering and unresolved-intent semantics.

## F7 [bug] host/native/owner.lisp:4366 fnn-owner-cold-await

Cold dependency handling blocks the mux thread that called it, and its final settlement can wait beyond the dependency deadline without another deadline check.

Quoted source, owner:4382–4392:

```lisp
((eq decision :serve)
 (let ((got (fnn-owner-cold-settle service read)))
   (when (typep got 'serious-condition) (error got)))
 ...)
...
(fnn-extent-executor-wait worker (/ (second decision) 1000))
```

Settlement uses `fnn-owner-serialized ... :control` at 4324–4325. Mux:583 calls `fnn-owner-handle-chunk` directly on the loop thread; owner:4111/4398 reaches this wait synchronously. `fn-ocs-next` excludes `:control` while a batch remains in flight, and gate-enter's wait at owner:1362 has no timeout. The comment at owner:4187, “Other connections are served meanwhile,” is therefore only true for connections on other unblocked loops.

**Interleaving/reachability:** A mux loop serves a cold ARTICLE on connection X and waits for the worker; connection Y on that loop gets no reads, writes, or timer service for that interval. Separately, a committer starts a barrier. The cold worker returns before its 5-second dependency deadline, but X enters `:control` settlement while the barrier remains in flight. X and its entire loop now wait for barrier completion, even past the cold deadline. A late integrity failure waiting for this settlement is delayed too. Timing out physical I/O need not release its pin; this finding does not ask for that unsafe release.

**Fix:** Store the pending dependency on the connection and return to poll. Deliver readiness/deadline events to the loop, and make settlement a bounded action admissible independently of a store barrier (or a separate nonblocking owner request).

## F8 [bug] host/native/owner.lisp:5977 fnn-owner-accept

Primary accept and signal processing synchronously enter a control-class maintenance quantum even when there is nothing to reap.

Quoted source:

```lisp
;; owner.lisp:5977–5982, before the next accept-loop iteration
(fnn-owner-cold-reap service)
(fnn-owner-maybe-publish service)
(fnn-owner-maybe-reopen-log service)
(fnn-owner-maybe-retire service)
;; cold-reap: the empty-head check is INSIDE serialized :control
(let ((read (fnn-owner-service-cold-head service)))
  (when read ...))
```

**Interleaving/reachability:** A syncer remains in flight on a stalled disk. B, the primary accept thread, finishes an accept or its one-second poll and enters cold-reap's `:control` gate wait. Even with an empty cold queue it cannot enter. A SIGTERM sets the signal flag, but B cannot return to the check at owner:5964 or initiate the drain protocol. The stalled committer can tell its members uncertain (3519 onwards) without ending the actual in-flight phase, so this does not rescue B. The stated “consumed within one second” rationale at 5958–5961 is false for the composed loop. Extra listener workers may still accept; this finding is specifically the primary loop and its signal/retirement duties.

**Fix:** Separate accept/signal handling from scheduled maintenance. Submit maintenance opportunistically without waiting in the accept loop; checking for an empty cold queue alone does not fix the following blocking publication/retirement calls.

## F9 [bug] host/native/mux.lisp:1393 fnn-mux-adopt

Client registration and inbox publication are split across locks with no closing-state handshake, allowing publication to a dead loop.

Quoted source, mux:1389–1397:

```lisp
(push socket (fnn-owner-service-clients service))
... ; roster lock ends
(when loop
  (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
    (push (%make-fnn-mux-conn :socket socket :implicit-tls implicit-tls
                              :done done)
          (fnn-mux-loop-inbox loop)))
  (fnn-mux-wake loop))
```

**Interleaving/reachability:** A secondary TLS/additional-listener accept worker passes the stopping check and registers its socket, then pauses before taking the loop lock. B fences service and shuts down registered sockets (owner:1703–1730). C's mux loop takes its final inbox at 1312, finishes its known connections, closes its wake descriptors at 1333, and exits. A then enqueues to that same loop and wakes the closed pipe. Nobody owns the final close/removal of the socket or delivery of its optional done signal. The additional listener workers at owner:5928–5955 make this overlap reachable even though the primary accept thread itself also coordinates shutdown. Shutdown's `socket-shutdown` deliberately does not close descriptors.

**Fix:** Make ownership publication atomic with the loop's accepting/closing state. Use a consistent roster-to-inbox order or a loop-local closed bit checked under its lock; the losing adopter must close and settle the socket itself.

## F10 [bug] host/native/owner.lisp:5147 fnn-owner-publish-captured

Removing a worker from the only join roster before its last shared-resource operations makes “all workers joined” an invalid observation.

Quoted source, owner:5147–5162:

```lisp
(fnn-with-roster (service)
  (setf (fnn-owner-service-publisher service) nil
        (fnn-owner-service-workers service)
        (delete sb-thread:*current-thread*
                (fnn-owner-service-workers service) :test #'eq)))
...
(when pin (fnn-arena-unpin pin))
(fnn-owner-service-nursery)
...
(fnn-owner-maybe-publish service)
```

`fnn-owner-wait-workers` at 4808–4812 returns on an empty roster. Shutdown uses that observation before cold-worker shutdown, journal closure, store settlement, and payload-lifecycle joined (6213–6285). Export similarly deregisters before its unpin at 5408–5415.

**Interleaving/reachability:** A publisher deregisters and is descheduled before unpin/tail. B completes both worker-roster checks while A is absent and can advance shared settlement. A resumes and touches global pin state, GC policy, and the old service's publication entry; that entry observes filesystem space and enters the gate before its stopping check (5211–5214). The verified bug is premature join/settlement, not a demonstrated overwrite after restart. The same interval lets another publication start while A is still restoring the global nursery setting.

**Fix:** Keep a joinable thread record until an external reaper has observed termination. At minimum keep the worker registered through every cleanup and tail action; use a distinct publication-slot flag rather than worker disappearance to permit the next publication.

## F11 [bug] host/native/mux.lisp:1182 fnn-mux-timers

Timer selection includes an expired idle deadline when the idle handler is explicitly ineligible because a response plan or resume timer is pending.

Quoted source:

```lisp
;; mux.lisp:1169–1175: firing requires both to be absent
(null (fnn-mux-conn-plan conn))
...
(null (fnn-mux-conn-resume-at conn))
...
;; mux.lisp:1182–1185: scheduling omits both conditions
(:serving (note (fnn-mux-conn-resume-at conn))
 (unless (or (fnn-mux-conn-out conn) (fnn-mux-conn-input conn)
             (fnn-mux-conn-await conn))
   (note (fnn-mux-conn-idle-at conn))))
```

**Reachable sequence:** A long/sparse OVER response outlives its old idle deadline, then yields with no output/input/await. `fnn-mux-plan-yield` (403–419) retains the plan and arms a future resume time without clearing idle-at. Before resume is due, timers cannot run idle but select its past deadline. `fnn-mux-iterate` at 1244–1248 computes timeout zero and repeatedly scans/allocates/polls until resume. Repeated cursor yields repeat the spin. No concurrent mutation is needed.

**Fix:** Use the same eligibility predicate for firing and scheduling an idle timer, or explicitly disarm/rearm idle when entering/leaving response ownership.

## F12 [bug] host/native/owner.lisp:5272 fnn-owner-maybe-publish-quantum

A handled rotation refusal leaves a NIL “worker” that later makes join-thread fail and prevents normal shutdown settlement.

Quoted source:

```lisp
;; owner.lisp:5234–5239
(position (handler-case (fnn-log-rotate store)
  ((or fnn-store-fault fnn-store-indeterminate) (e) (error e))
  (fnn-store-error (e) ... :failed)))
;; owner.lisp:5254 and 5271–5272
(let ((thread (and (not (eq position :failed)) ...)))
  (setf (fnn-owner-service-publisher service) thread)
  (push thread (fnn-owner-service-workers service)))
```

**Reachability:** `fnn-log-rotate` can return a known refusal after the ready-spare check: for example `rename-no-replace` reports `:exists` or `:unsupported` (io:7376–7381). That is an ordinary `fnn-refuse`, caught as `:failed`, and no thread is made. Shutdown subsequently executes `(sb-thread:join-thread worker)` for every roster element at owner:4812, including NIL. Its conservative cleanup retains authority rather than proving a joined close, but a safe maintenance refusal should not poison the roster in the first place.

**Fix:** Register only an actual successfully constructed thread. Leave publisher and roster untouched on `:failed`.

## F13 [claim-gap] host/native/mux.lisp:1389 fnn-mux-adopt

The machine/connection capacity argument does not cover the unbounded accepted-socket inbox that precedes core admission.

Quoted source:

```lisp
;; mux.lisp:1389,1394–1396: no admission/reservation in either step
(push socket (fnn-owner-service-clients service))
(push (%make-fnn-mux-conn :socket socket :implicit-tls implicit-tls :done done)
      (fnn-mux-loop-inbox loop))
;; mux.lisp:1189–1195
(prog1 (nreverse (fnn-mux-loop-inbox loop))
  (setf (fnn-mux-loop-inbox loop) nil))
...
(fnn-mux-begin loop conn)
```

Admission occurs when the loop eventually begins the connection. During F7, or another loop stall, an extra accept worker can keep retaining sockets, socket objects, connection records and list cells without consulting the installed profile capacity. The kernel listen backlog no longer bounds these sockets after accept. A process FD limit may ultimately stop this, but it is not the advertised ACL2-selected connection/memory reservation (mux:46–49). No claim of unlimited physical RAM is necessary: allocation can exceed the admitted profile before any exposure refusal runs.

**Fix:** Reserve pending-accept capacity before retaining each accepted socket, include it in the same resource accounting, and settle that reservation when admission transfers or refuses ownership.

## F14 [claim-gap] host/native/owner.lisp:4300 fnn-owner-cold-result-locked

A fixed count of reaped jobs does not bound the work of a quantum that scans all pending extent groups and may synchronously close all newly eligible files.

Quoted source:

```lisp
;; owner.lisp:4300, on result settlement
(fnn-owner-release-pending-extents-locked)
;; owner.lisp:4849–4859
(dolist (entry *fnn-extent-pending*)
  (if (fnn-arena-clear-p (car entry) pin)
      (multiple-value-bind (count owned) (fnn-extent-close (cdr entry)) ...)
    ...))
```

The reaper docstring at 4331 promises “One bounded round-robin quantum”; `fn-pio-reap-work` bounds the outer job count, not this nested work. With P retained checkpoint/retirement groups and F files, settlement can do O(P + F) work/close calls under owner exclusion. Long-lived responses or publishers can retain groups across many publications.

Two adjacent collection costs also lack a local quantum bound:

- Every response capture/release calls `fn-rpin-step` under the global pins mutex (owner:501–509). Its `fn-rpin-owner` scans the R outstanding response owners; release scans again and copies the preceding list via `fn-rpin-remove` (books/response-plan-pins.lisp:11–45). R follows concurrent response ownership, not the incoming command's size.
- Every log COMPLETE calls `fnn-log-reseat-fenced` -> `fnn-arena-release-due` (io:6831–6859). `fn-arpn-split-acc` visits/copies all pending retirement rows (books/arena-reader-pins.lisp:169–179), even when the oldest response prevents all of them being released. With one long pin spanning P batches, cumulative visits can be quadratic in P; dropping the pin can release all their handles in one COMPLETE.

The cited `fn-rpin-step-preserves-funded-ownership` registry keystone establishes ownership, not bounded visits. I am **not** alleging that `fnn-entry-guard` evaluates `fn-arpn-okp`: io:1286–1310 and books/payload-kinds.lisp:64 select only listed kind recognizers, which exclude that invariant. The explicit function-body walks already establish this finding.

**Fix:** Carry indexed response ownership and ordered retirement cursors/counts. Advance a bounded number of retirements per scheduled quantum, with separate resumable physical closes; add visit/allocation bounds for the actual host-called boundaries.

## F15 [claim-gap] host/native/owner.lisp:2015 fnn-owner-prepare-refusal-word

The semantic mapping from prepare result to owner outcome is a host decision rather than an ACL2 result carried across the boundary.

Quoted source, owner:2016–2021:

```lisp
(case prepared
  ((:duplicate :conflict :clock-unusable :refused :unaffordable :memberships
    :article-numbers-exhausted :canonical-size-unavailable :invalid-binding)
   prepared)
  (:invalid :malformed)
  (t (fnn-fault "owner prepare returned ~a" prepared)))
```

This is not just kind checking: it chooses the outcome that subsequent ACL2 reply logic receives. It is used on served Store attempts. The mapping may be sensible; I found no contrary protocol outcome. The gap is the project's stated boundary, “ACL2 owns every decision,” and the absence of a core subject for this particular transformation. Host shape assertions such as validating consumed counts are a different matter.

**Fix:** Have the core return the complete outcome word, or introduce one guard-verified conversion entry and use it at every host attempt boundary.

## F16 [nit] host/native/owner.lisp:4862 fnn-owner-release-pending-extents

This unused wrapper documents a worker-completion path that now invokes the locked helper directly instead.

Quoted source:

```lisp
(defun fnn-owner-release-pending-extents (service)
  "Actual worker completion retries pending closes after dropping extent lock."
  (fnn-owner-gated (service :control)
    (fnn-owner-release-pending-extents-locked)))
```

Code-reference search in host/books/tests/tools finds no caller. Actual owner settlement calls the locked helper at 4300. `fnn-owner-run-admission` at 647 is also superseded by the run-authority claim path and has no code caller. Separately, the page-source read/release helpers at 4890/4920 have no caller, but specs/storage.md:1964–1968 explicitly calls that bridge unreachable until adoption; these are acknowledged staged APIs, not evidence of current service behavior.

**Fix:** Remove or explicitly retire the obsolete wrappers/comments after checking exported interfaces; keep staged APIs clearly marked and out of served-path completion claims.

## Checked, no finding

### 1. Locking and ordering

Read the owner and mux end to end, including gate admission/failure handling, worker startup/stop, commit loop, cold queue, publication, reclaim, export, handshake, compression, poll and timer paths. Followed the critical call chains into native io/extent/pull/web/admin/control/snapshot producer, host/owner-host, and the scheduler, cold-line, response-pin, arena-pin, intent/result and retirement books. The findings above are source-grounded; this is not an assertion of an exhaustive machine-checked transitive call-graph audit.

Lock/condition inventory and observations:

| Lock or wait | Observed ownership/order and work |
|---|---|
| Owner gate mutex | Ticket/pick/scheduler transitions at owner:1280–1569; condition predicate is checked in a loop at 1348–1363. Gate mutex is released before acquiring owner. Owner actions later acquire gate for phase/time/leave. Recursive gate entry is explicitly rejected. No ABBA cycle established here. |
| Owner mutex | `fnn-owner-gated` and direct shutdown/settlement acquisitions at 1590/1593,1746,4358,4884,6120,6284. Nested gate, roster, commit, wait, pin/lifecycle, extent and log locks occur. F1/F2 are failure-boundary holes; F4–F6 identify blocking I/O/waits, not merely long core work. |
| Roster | Worker/client/publisher/exporter lists and stopping flag; some thread creation occurs while held. Mux inbox is normally taken separately. F9/F10 concern release-to-use windows, rather than an invented lock inversion. |
| Commit lock/CV | Waiter/completion/queued/sparing bookkeeping, syncer result publication, loop-pass wakeups, drain observation. Syncer releases the commit lock before roster cleanup; mux releases its inbox lock before signaling the committer. The sync-result wait rechecks its predicate. No verified lost wakeup here. |
| Consumer wait lock/CV | owner:2801–2857 snapshots the commit counter before polling, then checks it again while holding the wait lock before sleep. The explicit grab has unwind release with `holding-mutex-p` for timeout behavior. No lost signal established. |
| Extent mutex / worker CV | Owner-to-extent acquisition at capture and settlement; worker prefetch does not acquire owner. Returned-job checks and condition-wait use the same extent lock. Persistent workers announce actual activation return before result settlement. F4 covers synchronous exceptions to unlocked I/O. |
| Arena pins / payload lifecycle | Owner-to-pin/lifecycle on capture; off-owner unpin uses their own locks. Snapshot holder records carry the actual arena identity and typed token. No new reverse owner acquisition found in those scalar transitions. Global list costs are F14. |
| Log kernel/spare/log sink | Log-kernel lock protects batch/sync fields; its condition wait releases only that lock, not any outer owner lock (F5). Spare preparation holds its spare mutex while allocating/fencing. Logging uses the recursive sink mutex and queue; the log writer owns physical emission. This does not make feed journals asynchronous (F6). |
| Mux inbox and once semaphore | Inbox/arrived transfers use the loop lock; done is signaled by finish or immediate reject. Atomic wake ownership is incomplete at adoption (F9). |

Acquisition/pin transfers whose release is **not locally protected by a cleanup form**, including non-bugs:

- Gate admission returns before the owner's `with-mutex` and its leave `unwind-protect` begin (owner:1591–1594). Ordinary body/gate failures inside that form are covered; asynchronous failure in the intervening acquisition window is **UNVERIFIED**, not a finding.
- Response pin at owner:4549 transfers to the response consumer. Mux releases via `fnn-mux-after`/`fnn-mux-finish` (505/274), not a lexical cleanup around capture. Pull/web install render unwind cleanup after the owner returns (pull-service:286–296; web-host:116–125). An exception between capture and consumer handoff relies on the service fault path.
- Mux finish sets phase `:done` before the fallible response-unpin (273–274). A failing unpin skips later resource cleanup and repeated finish returns immediately. **UNVERIFIED:** the eventual process/resource-settlement outcome after that injected core fault. Cleanup should be per-resource and resumable, rather than treating `:done` as a receipt for all releases.
- Cold token/worker issuance at owner:4221 transfers into the owner intrusive read queue at 4223–4225; it is deliberately **not** released on timeout. A failure allocating/enqueuing the small host job after successful issue has no local compensating cleanup. The shared fault fence limits further mutation; complete orphan-job settlement on allocation failure is **UNVERIFIED**. Do not refund a worker still executing.
- Snapshot root and payload-view acquisition (4867/1653) are transfer APIs. Snapshot-producer:609–628 covers construction failure, and its job cleanup at 475–507 settles the retained tokens after return. Page-read at 4890 hands its buffer token to its caller on success; local failure cleanup exists, but the successful consumer is currently uncomposed.
- Publisher/exporter generation pins are acquired before thread creation (5255/5305). Failed thread construction has unwind-unpin; successful creation transfers the pin to the worker's cleanup. Their premature roster removal is F10. Reclaim/dry-run pins at 5661/5469 have surrounding unwind-unpin at 5788/5504.
- Consumer waiter credit increments during admission (2819) before the outer wait-loop cleanup is established (2829). Gate failure in that interval fences service but has no local decrement. No ordinary successful-path waiter leak was established.
- Handshake/exposure admission is stored in connection fields and released by finish/handshake-release, rather than locally unwound across every call. This is the same asynchronous ownership pattern as response pins; cancellation and shutdown must preserve those fields until their particular release receipt.
- Accepted socket/client-roster ownership transfers to the loop; F9 identifies the missing atomic transfer. Worker roster registration transfers to shutdown/join; F10/F12 identify invalid receipts/entries.

### 2. Order of effects versus durability

Read attempt handlers, feed intent/resolution ordering, START/SYNC/COMPLETE, early stall replies, reclaim install/barriers, checkpoint write/drop, store settlement, and mux completion delivery. Normal served acceptance is released by COMPLETE after the log barrier; an early stalled batch is told uncertain and its late generation is not answered twice. Feed intent precedes Store attempt and resolution precedes enabled effects. I found no separate normal-path “socket write means durable” bug. F1/F2 are exceptions to the recovery boundary, not a refutation of all those ordering lemmas.

Host cut labels were inspected around checkpoint install, log append/fence/rotation/drop and reclaim. No additional unmatched process-death cut is asserted: the native-program checker was not run, and a label's existence alone does not establish composed crash refinement.

### 3. Claims and theorem subjects

Compared host dispatches against owner-host adapters and relevant book subjects: `fn-ocs-next`, `fn-ocs-commit-step`, `fn-otm-admit-post`, `fn-otb-dependency-step`, `fn-rpin-step`, `fn-arpn-step`, carried submission intent/resolution, and file ownership/retirement. Read the corresponding interface entries and storage/cold-read scope statements. The new direct worker path retains its file-incarnation row through actual return and the extent close path checks issued ownership; I found no evidence that timeout alone now drops that row.

No theorem about a pure scheduling step establishes that an enclosing native loop cannot block in a different gate class. Likewise the response-pin ownership theorem does not prove worker joins or runtime cost. F3/F5/F7/F8 show concrete composition failures. The funded-pool, window and snapshot-source specifications explicitly leave startup/native composition obligations open; I did not count those documented staging boundaries as secretly completed features or new bugs.

### 4. Cost

Read the mux's full-list timer/poll/TLS-ready/unsent scans, response ownership, pending arena and extent release, feed peer-plan traversal, log-member walks, checkpoint capture/walk/reseat and reclaim chunks. Mux allocates fresh lists and poll arrays across all connections each pass; slow-disk or timer-spin amplification matters more than a raw line count. F13/F14 name missing capacity/visit bounds. The 1024-row maintenance chunk is a per-call partition, not a proof that constructing the complete output or a nested payload operation is constant cost.

**UNVERIFIED:** exact executable-counterpart guard costs, current RSS, allocator peak factors, and whether list costs dominate a supported production profile. No image was started and no performance figure is claimed.

### 5. Host decisions

Examined refusal mapping, submission consistency checks, txid/config snapshots, cold result disposition, host timer scheduling, TLS suffix classification and ACL2 frame/reply calls. F15 is a concrete semantic host mapping; F3 is an incorrect host classification of a valid protocol continuation. Ordinary representation-shape checks are not automatically duplicated protocol policy.

**UNVERIFIED impact:** control submission captures next-txid at owner:4016 before `fnn-owner-complete-bound-submission` drains prior queued work at 3761, so the supplied coordinate can become stale. The feed reconciliation examined at books/owner.lisp:2518–2547 compares object identity/evidence, not that txid. I therefore do not promote this observation to a demonstrated lost-obligation/corrupt-recovery finding.

### 6. Dead or duplicated machinery

Reference-searched owner/mux defuns across host/books/tests/tools and checked documentation references for the unmatched names. F16 identifies obsolete wrappers; snapshot page helpers are explicitly staged. Physical file tokens, logical payload-view holders and response generation pins have different jobs and cannot simply be merged or removed because they all look like “pins.” The problematic duplication is multiple native execution/completion mechanisms with incompatible scheduling and failure conventions (F1/F5/F7), not the mere existence of those distinct resource types.

## What I would do instead

Make the native owner an executor of explicit request/effect/completion records. No mux or accept-loop callback should synchronously wait for a gate class, disk dependency, or logical commit completion. A single pending-operation contract should cover socket clients, web/pull logical clients, feed persistence and maintenance: capture under exclusion; execute leased I/O outside it; submit a typed completion; settle exactly once under exclusion. Keep caller deadlines separate from physical ownership settlement.

Make every mutating owner quantum use the same terminal failure boundary. A low-level “gated” helper that also looks safe for arbitrary core mutations is too easy to misuse. Safe refusal, integrity fault and ambiguous effect need different outcomes with fencing performed where the effect is still excluded.

Give each native resource an explicit transfer/settlement receipt. A thread is joined only after join/termination observation; a connection is done only after its owned resources have definite dispositions; a descriptor with ambiguous close cannot return to service. Keep scheduling flags separate from those receipts.

Use carried counts/indexes and resumable retirement queues. Prove bounds at the host-called operation including its cleanup and maintenance callbacks, not just at the outer loop that counts jobs. Preserve the useful new worker/file ownership model while replacing the synchronous adapters around it.

## Measurements I want

1. **Reclaim terminality:** fail directory fsync immediately after checkpoint rename, then separately fail each post-swap recovery barrier. Concurrently issue DATE/POST/status. Record stopping/fenced state before mutex release, control status, accepted writes, and reopened checkpoint/state. Expected correction: no later semantic mutation after uncertainty.
2. **Retirement failure containment:** inject discovery digest failure and an ambiguous close outcome during automatic publication. Track the retained fd/token table and whether any subsequent open/retirement uses the same integer. Confirm that failure fences service rather than merely logging.
3. **TLS pipeline:** use the existing cold-read pipeline over TLS without COMPRESS, with warm DATE before a cold ARTICLE in one decrypted input; repeat for cold-resource refusal. Observe complete replies, retained suffix, owner exit code and another client's liveness.
4. **Scheduling cross-product:** explicitly assign two clients to the same mux loop, then different loops. Stall a cold read; separately let it return while the log barrier remains in flight. Record read/write/idle/handshake deadline latency and cold-settlement gate wait. Existing two-client tests can accidentally choose different loops.
5. **Accept/signal:** with no cold reads queued, hold the disk barrier, wait for primary accept to enter reaping, then send SIGTERM and attempt another primary-listener connection. Record time to signal consumption/drain initiation separately from physical-worker join.
6. **Other disk dependencies:** independently stall checkpoint fresh pread and feed-journal fsync. Trace owner/extent lock hold and wait times, with cached reads and health requests active. The store fdatasync selector alone does not exercise these paths.
7. **Logical ingress:** overlap a web POST's final article slice with the start of a network POST barrier, before the slow-disk threshold. Trace scheduler phase, log sync-state, credit transitions and both completions; verify no inline START occurs while in flight.
8. **Ownership races:** pause adoption after roster registration and before inbox push, stop/join that loop, then resume adoption. Separately pause a publisher immediately after roster removal and check whether shutdown claims joined while the thread is alive. Count remaining sockets, pins, completion semaphores and live threads.
9. **Cursor timer:** run a sparse/long OVER past the idle deadline and record poll timeouts, CPU, allocations and timer eligibility during empty yields. Expected correction: sleep to the future eligible resume event, not repeated zero-time polls.
10. **Capacity and cost curves:** hold a loop while an additional listener accepts beyond configured exposure capacity; measure pending sockets/FDs/heap before admission. Hold an old response across increasing commit/publication counts; measure response-pin visits, pending-retirement visits, COMPLETE hold time and the cost when that pin drops. Use matched store/profile/cache conditions.
11. **Refusal/cleanup:** cause a ready-spare rotation to return a known refusal and inspect the worker roster before shutdown. Inject response-unpin failure during mux finish and verify that physical cleanup remains possible without falsely marking all ownership settled.

These are requested liaison experiments, not tests executed in this review.
