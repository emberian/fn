# Native pipeline boundaries

The kernel and OTM scheduler in X are canonical while attached. The log's
kernel and gate's scheduler are installed projections of each derived result.
The counted kernel and history projection has an unconditional commutation
proof; no growing committed-record list is retained on the served path.

- OPEN initializes X from the actual idle/recovered kernel and OTM value.
- START/START-NEXT call the corresponding begin arm under O, then reserve,
  take and member per actual Store attempt; seal names the job and write plan.
- Current seal reserves extent for both A and one profile-capped B. The current
  actor performs intents, extension, write, fence, resolutions off O/G/K.
- Every actual I/O phase has a short :commit receipt quantum. This prevents
  failure from interleaving between a taken record and its member registration.
- Next seal opens B's job. Its separately funded :append actor runs intents,
  extension and append only. APPEND-ISSUE waits for A's append receipt, freezes
  B and returns the exact offset/octets before the write syscall. B never
  fences before promotion; only one barrier is outstanding.
- The committer keeps observing deadlines while both actors run. Its wake
  refuses collection until both return and refuses another START-NEXT while
  the append role is occupied. Physical joins and operation receipts are
  distinct, consumed once; unwind retains each outstanding result consumer.
- COMPLETE ACKs/releases only the durable A prefix. Existing generation/told
  accounting prevents duplicate socket delivery after an early uncertain reply.
  Feed resolutions already ran after the fence; deferred log lines and replies
  leave under COMPLETE. Reader advance then promotes B's written custody and
  starts at its fence, with no duplicate write.
- Failure of either job aborts the composed machine, fences Store and answers
  affected members uncertain. A failure before a phase receipt uses the same
  abort arm at the collector. Late successful receipts cannot resurrect it.
- CLOSE returns the detached scheduler only at idle, or after external STOPPING
  at collected/stopped. Failed kernel/ACK evidence remains in the returned X;
  the irreversible service fence prevents any semantic continuation afterward.

The held path uses this SAME driver. Control, hybrid author and BP pass their
whole callback before any of its prior state changes. START enters with the
original poster/control/transit class; a nonempty drain uses SEAL-HELD. Its
caller monitors the job and consumes its joined result under the declared
:commit COMPLETE section. Only :submit runs the callback, in that same quantum;
:stop or STOPPING never runs it. An empty/no-frames drain submits in START.
A zero-record drain with pending feed frames stays staged until those receipts.
The committer's START predicate and held wake exclude a competing collector.

Resource-syncer funds one worker per bank. Two disjoint, role-tagged banks reuse
that ledger and its physical+operation retention, with no spare/rescue quota.
The startup thread count explicitly charges the additional append worker.
The role tests exercise a real stobj through wrong-role, pending and settlement
receipts. New heap witnesses account for exactly five additional MiB.

No batch :full path waits or commits: the encoded-octet preflight runs before
queue removal; exact fit is checked before publication. Import's explicit
flush remains an unpublished, off-owner route. The inline queued-commit helper,
its action helper/classifier and the batch-job's optional legacy arm are gone.

The original OCP admission/fairness and reader capture theorems remain unchanged.
Reader captures realize the existing fn-ocv operations only at dispatcher-approved
boundaries. Direct bound submissions' own Store I/O is a separate existing path;
removing queued-inline I/O does not remove every global fdatasync-under-O key.
Native integration is not READY until the current closure and host gates pass;
N owns the native POST p50/p99 gate. No images are built by this lane.
