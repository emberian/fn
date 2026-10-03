# TCB-SHRINK: how fn gets from 67k lines of host Lisp to ACL2 everywhere but a thin primitive layer

Decision plan, 2026-10-03. Author: the TCB-SHRINK architect (Claude Fable 5.1). Status: DRAFT for
adversarial review (an independent Opus reviewer; Codex returns 2026-10-08) and then sequencing by the
coordinator. Implements ember's decision in decisions/host-into-acl2-2026-10-03.md. Every path is relative
to /Users/ember/dev/fn at origin/dev 4aa332295; line numbers are of that revision and go stale, names do
not. No code was changed. Two inventories were produced by reading every line of host/native/owner.lisp
and host/native/io.lisp (15,041 lines; sections 1.3 and 1.4); the other 26,000 native lines were measured
by two reproducible scripts (a per-file signature census and a per-form signature classifier, both in the
session scratchpad and reproduced in appendix A) and by targeted reading of mux.lisp, extent.lisp, the
section wrappers, the committer, the cold executor and the service-log writer; where a number comes from
the classifier and not from reading it says so.

## 0. The answer in one page

THE SHAPE. Today the boundary between proved and unproved code sits at every DECISION: the raw host
calls 1,379 distinct ACL2 entries from 2,062 call sites (section 1.6) and sequences the answers itself,
under 394 lock sites, 15 thread sites, 30 condition-variable sites and 444 handler clauses that no
theorem covers. The plan moves the boundary to every EFFECT: a primitive layer of about 110 named host
operations (section 2), each specified as an oracle step of the host model, realized raw under the
existing trust tag exactly as `fn-sig-verify` and `fn-durable-realize-octets` are today; above it, every
actor of the node (the committer, the two I/O loops, the cold workers, the publisher, the exporter, the
accept loop, the control clients, the feed and pull workers, the log writer) is an ACL2 step function
over its OWN local stobj, run by one generic ~300-line host envelope (observe a primitive, step, perform
the action), and shared state is touched only inside a SECTION primitive whose body is an ACL2 function
over the live stobjs. "ACL2 decides, host does I/O" becomes "ACL2 decides and coordinates; the host
performs one primitive at a time and runs one envelope".

THE NUMBERS. host/*.lisp: 112 files, 25,909 lines, 1,550 defuns of which 1,089 (70%) are `:mode
:program` -- unproved ACL2 that runs in the image and is as much TCB as the Lisp below it (Astra section
2; this plan counts it). host/native: 78 files, 40,939 lines, 1,841 definitions. 92 of the 190 files
(about 8,700 lines) are loaded by no build (`tools/host_loaded_check.py`, section 1.8): the live TCB is
about 58k lines, not 67k. The per-form classifier over the natives (appendix A) puts 8,269 lines under a
syscall or FFI signature (the primitive candidates), 13,548 under a lock/thread/handler signature
(coordination), 7,960 under an ACL2-call signature (glue), and 7,433 under none of those (of which the
read-based inventories and the targeted reads identify about 1,800 lines of real computation that AGENTS.md
already says should be ACL2, section 1.5; the rest is declarations, build forms and small accessors).

AFTER (section 4): about 6,000-7,000 lines of host Lisp -- the primitives (3,000-3,500), the envelope and
the section/mailbox/thread registry (300-500), the dispatcher reduced to the raw-dispatch installer (200),
and build/startup/packaging (2,000) -- plus the 26k lines of host/*.lisp wrappers converted to logic-mode,
guard-verified books, which leave the TCB rather than shrinking it. The named assumptions become one row
per primitive family (A-PRIM-*, replacing the unused A-HOST) beside the existing crypto/TLS/SBCL/OS rows.

THE ORDER (section 3): the generic envelope and the failure-scope table first (FAILURE-SCOPE already owns
this; it should emit ACL2, not host macros); then THE COMMITTER as the first end-to-end actor (every one
of its decisions is already an ACL2 function in 3,500 lines of certified books; the host contributes eight
identifiable rules and four of this week's defects); then the I/O loop (the most host-only policy); then
the cold line, the accept/stop lifecycle, reclaim/publication, the log kernel, and the services. Pure
computation still in host Lisp (the DEFLATE encoder with its live bug S005, the cut tables, the status
lines) moves in parallel as small lanes.

THE HARD THINGS. (1) The `:program` layer is the larger hole, and the carrier move (STAGE-5B: the owner's
state globals into a stobj) is a precondition of the whole plan, not an option: ACL2 state globals are
shared SBCL symbol-values (one per process) and the extracted SBCL-core product keeps them in one
synchronized hash table, so per-thread state globals are impossible in the product (section 2.3). (2) The
first slice is the committer, not the I/O loop ember named: the loop has the most host-only policy and is
the most valuable second, but the committer is the smallest actor whose every decision is already proved.
(3) ACL2 cannot do threads, and "the code that runs is the code that is proved" is true above the envelope
only if every actor step is raw-dispatched with a carried invariant; on the counterpart path the step's
guard is served cost (stage 5's quadratics). TCB-SHRINK and raw dispatch are one program. (4) The honest
count of computation that should already be ACL2 is about 1,800 lines, not the classifier's 7,433; the
large number is coordination, and that is the point of ember's amendment.

## 1. Inventory

### 1.1 Totals, measured

| layer | files | lines | definitions | notes |
|---|---|---|---|---|
| host/*.lisp (ACL2-mode, `ld`-ed, not certified) | 112 | 25,909 | 1,550 defuns | 1,089 `:mode :program` (70%); 1,409 `definterface` forms (host/interfaces.lisp, 4,992 lines); 0 `:raw-with` in production; 357 `f-put-global` sites over 155 distinct globals; 43 `fn-hx-*` primitive stubs (44 uses) |
| host/native/*.lisp (raw SBCL under `:fn-native-host`) | 78 | 40,939 | 1,841 defun/defmacro | 394 lock-shaped sites (205 `with-mutex`, 25 `with-recursive-lock`, 1 `grab-mutex`, the rest the section/roster/kernel wrappers); 15 `make-thread`; 30 condition-variable sites; 444 `handler-case`/`ignore-errors`; 213 `unwind-protect`; 1,229 references to SBCL runtime packages; 2,062 ACL2 call sites naming 1,379 distinct entries; 337 `fnn-octet-list` conversions; 670 format/log sites |
| loaded by no build | 92 | about 8,700 | | 69 host/*.lisp (about 5,470 lines) and 23 host/native (about 3,250 lines): `python3 tools/host_loaded_check.py` lists them; section 1.8 |

Per-form signature classification of host/native (appendix A; a signature, not a reading):

| signature | lines | forms | meaning |
|---|---|---|---|
| PRIM | 8,269 | 452 | the form performs a syscall, FFI call, thread/mutex creation or pins memory |
| COORD | 13,548 | 505 | the form takes a lock, waits, joins, handles a condition, sleeps, or runs a section wrapper |
| GLUE | 7,960 | 477 | the form calls an ACL2 entry and routes the result, with none of the above |
| DIAG | 1,080 | 72 | the form only formats or logs |
| DEFS | 1,750 | 475 | declarations (defvar/defstruct/define-condition) with none of the above |
| PURE | 7,433 | 1,170 | none of the above: computation, build forms (`build*.lisp` 1,104 lines), small accessors |

Read-based inventories (every form read and classified; the categories of the brief):

| file | lines | PURE | COORD | GLUE | PRIM | BUILD | DIAG |
|---|---|---|---|---|---|---|---|
| host/native/owner.lisp | 6,392 | 75 (7 forms) | 3,300 (140) | 2,277 (98) | 230 (25) | 410 (17) | 100 (12) |
| host/native/io.lisp | 8,649 | 434 (66) | 2,587 (136) | 3,151 (237) | 1,141 (114) | 920 (56) | 363 (34) |

The two read-based files are 37% of the natives and hold 73% of the lock sites (owner 136 + io 38 of
the census's 394 wrapper-inclusive count; Astra counted 86 of 136 explicit acquisitions in them).

### 1.2 Pure computation still in host Lisp (should already be ACL2 under AGENTS.md)

Read-based, with the ACL2 twin where one exists. About 1,800 lines in total.

| where | lines | what it computes | twin / status |
|---|---|---|---|
| host/native/deflate.lisp:188-530 | about 340 | the OUTBOUND DEFLATE encoder: LZ77 match table, Huffman code lengths (`fnn-ldf-huffman-lengths` 253-301), canonical codes (302-321), RLE of lengths (331-348), block emission (351-421), the payload driver (422-507), the candidate selection (508-530) | NO twin. The inbound inflater is ACL2 (books/deflate-inflate.lisp) and CHECKS this encoder's output (`fn-lzr-append-decide`); S005 (a single-symbol Huffman tree padded with two symbols, an oversubscribed code, every such article refused forever) is a bug in host arithmetic that an ACL2 encoder with the decoder's round-trip theorem could not have. The one hard case in the tree where "a decision ACL2 cannot make yet" turned out to be a decision nobody wrote in ACL2 |
| host/native/io.lisp, 66 forms | 434 | cut-name tables duplicating ACL2's (`+fnn-init-model-cuts+` 3730, `+fnn-post-model-cuts+` 4836, `+fnn-log-model-cuts+` 6284, `+fnn-recovery-model-cuts+` 3795, `+fnn-export-/import-model-cuts+` 4198/4385, `+fnn-state-checkpoint-model-cuts+` 2740); file-name constants duplicating the initializer books (2065-2119, 3838-3845, 7270); status lines the host formats although `fn-nls` renders the same text (`fnn-open-report` 2725, `fnn-orphan-report` 3722, "pins=" 5220); report lines with no ACL2 renderer (5047, 5034, 5245, 5015, 4976, 4362, 4629, 3467, 6927, 5367); errno policy (`+fnn-fullfsync-unsupported+` 434, `fnn-eintr-p` 526, `fnn-would-block-p` 529); two host DECISIONS: `fnn-require-clone-activated` 2088 (refuses on a fence file plus an in-process flag) and `fnn-anchor-report` 4984 (picks "anchor=uncertain" and the exit code from a file's existence); `fnn-archive-name` 4184 (a safety rule over names ACL2 returned); `fnn-redeem-read-line` 8401 (CRLF framing with a 4096 bound); `fnn-release-version-word-p` 5962; hard-coded bounds (16384, 4096, 1024, 128, 1<<22, 1<<26, 65536, 1048576) and timeouts (10 s, 1 s, 0.05 s, ports 563/119, backlog 1) | twins for the tables and names exist in books/ (listed in section 1.4); the two decisions and the renderers have none |
| host/native/owner.lisp, 7 forms + embedded decisions | 75 + about 150 | `fnn-owner-prepare-refusal-word` 2015 (`:invalid` -> `:malformed`: Astra r71 item 15, a word mapping AGENTS.md says ACL2 owns); `fnn-owner-existing-verdict` 2054 (signals `fnn-owner-admission-pending`, which nothing catches: exit 4); feed journal names and peer order (942-1013, duplicating books/feed-filename.lisp `*fn-ff-suffix*`); the gate's FIFO-by-ticket within a class (1344-1355); re-checks of ACL2's staged values (2918, 3773-3776, 3842-3875, 4609); the release-to-completion mapping with a host fallback (3194-3204); the batch-close pass arithmetic (3669-3683); the outcome word set (3730); the cold verdict and fault-text tables (4237, 4292); the run-plan re-validation (6318-6341) | partial twins: `fn-post-store-refusalp` (books/nntp-post.lisp:529), `fn-lgc-rotate-needed-p`, `fn-lgs-next-segment`; none for the mappings |
| host/native/mux.lisp | about 500 (classifier PURE 484) | the I/O loop's POLICY: `fnn-mux-interest` 1101 (which poll events a phase waits for), `fnn-mux-timers` 1133-1185 (which timer is due, the next deadline: B4 / r71 F11 is a predicate mismatch here), `fnn-mux-arm-idle` and `fnn-mux-idle` (the idle deadline the exposure model should own: COMPOSITION section 2), the plan yield arithmetic (403-419), the batch-close pass counters (1254, 1284), the proxy/handshake/draining phase transitions (473-521, 807-941) | none; books/public-exposure.lisp owns `fn-exp-idle` but the host never feeds it the render loop's "reply written" |
| host/native/auth-admin.lisp:378-509 | 130 | `fnn-native-auth-admin-result-code` and `-execute-held`: the result-code mapping and the execution sequence of an offline credential command | the plans are ACL2's (books/native-auth-admin.lisp); the sequencing and the code mapping are host |
| host/native/control-transport.lisp:114-138 | 25 | `fnn-control-read-frame`: control-frame framing (length, bound) | ACL2 decodes the frame (`fn-native-control-admin-decode`); the framing is host |
| host/native/feed-service.lisp:441-495 | 55 | `fnn-feed-consume`: parsing the peer's reply lines in the push feed | books/feed-*.lisp own the protocol; this parser is host |
| host/native/tls.lisp:874-923 | 50 | `fnn-tls-peek-plaintext` / `-consume-plaintext`: the peek-then-consume equality check | a host check of a library (A-TLS-NATIVE); stays, but its equality decision is one line of ACL2 |
| host/native/bp-node.lisp:1097-1164, :339-357, :805-823 | 110 | the verb dispatch table, pending dispatch, expiry deletion | books/bp-node*.lisp own the machine; the dispatch and the deletion loop are host |
| host/native/heap.lisp:315-339, :38-48 | 36 | `fnn-heap-command-profile`, `fnn-heap-physical-octets` | books/heap-reservation.lisp owns the figure; these are the host's readers |
| host/native/tcpcl.lisp:673-697, :95-144 | 60 | trace-step rendering, log events, source escaping | host-formatted lines |
| host/native/checkpoint.lisp:328-372 | 35 | `fnn-clone-canonical-paths`/`-target`: path canonicalization for `store clone` | none |

Every host-formatted line (owner.lisp 5004, 5082, 5086, 5124, 5398, 5404, 5489-5501, 5646, 6258, 1177;
io.lisp's report lines above) is a decision about what the operator reads; `fn-nls` already renders
`status`/`health`. These move as one small lane (section 3.1, "pure").

### 1.3 Coordination (what moves): the actors and their host-side rules

The brief's categories, read from source. For each: what the host DECIDES today (the part that becomes an
ACL2 step function) versus what it PERFORMS (the part that stays a primitive).

OWNER.LISP (COORD 3,300 lines, 140 forms), by sub-kind:

| sub-kind | lines | forms | decides (moves) | performs (stays) |
|---|---|---|---|---|
| section wrappers `fnn-owner-gated` 1573, `-shared-action-locked` 1771, `-serialized` 1810, `-with-control-turn` 1826, `-transit-serialized` 1869, `fnn-with-roster` 1245 | 140 | 6 | refuse when STOPPING (1822, 1837); sort a failure into exit 3 / exit 4 / connection-scoped (1791-1808); whether `fn-owner-fault` is called for the cid; the control-turn shape checks (1848, 1865) | gate enter/leave, the owner mutex, `unwind-protect`, the fence, measurement |
| gate 1256-1385 | 126 | 9 | which class runs next is ACL2's (`fn-otm-next` 1324); the host adds FIFO by ticket within a class, "pick only when not busy and no turn pending" (1350), first-failure-wins abort (1275), re-entry fault (1342); `fn-otm-observe` folds the times (1380) | gate mutex, `ready` waitqueue, counters, the clock read |
| timers / disk time model 1411-1549 | 140 | 11 | every disk decision is ACL2's (`fn-otm-disk-step`, `-admit-post`, `-peer-read-class`, `-wait-ms`, `-disk-stalled`, `-space-due-p`); host: observe free space only when NEED is set and this is the time service (1418) | a monotonic clock read INSIDE the gate mutex (1458), statvfs, a journal offer under the gate mutex (1476) |
| committer / syncer 3018-3715 | 797 | 26 | ACL2: `fn-ocs-*`, `fn-otm-commit-event`, `fn-otm-committer-wake`, `fn-otm-stall-releases`, `fn-otb-*` (ledger, issue, complete, answer-early), `fn-osd-*`. HOST: wake when `queued>0` or stopping (3693); close the batch when every I/O loop passed its target pass (3697-3701, the pass arithmetic 3669-3683); START drains at most `bmax` members and keeps `queued>=1` at the bound (3132-3135); seal only if `seal`, members exist and none is uncertain (3141); settle credits when no member remains (3149); the stall fires once per barrier, when stalled OR drain-release (3519-3522); a timed-out wait becomes a clock event plus `:expired`; after COMPLETE the next action is forced `:none` if the body did not finish or the owner stops (3657); the next batch is promoted (3659); stopped during the barrier delivers every member `:uncertain` (3611-3620); the committer loop swallows every `fnn-store-error` as "stopped" (3704: S016/B1) | commit-lock and its waitqueue, the syncer thread and its join, the completion callbacks (`fnn-owner-deliver` 3031), the log seal/sync/collect calls (io.lisp 8007-8081), the developer sleeps |
| reclaim / extents / payload lifecycle 501-513, 1607-1685, 4849-5012, 5428-5799 | 521 | 21 | ACL2: `fn-rpin-step`, `fn-owner-orc*`/`orcp-*` (capture, decide, swap word), `fn-xrt-*`. HOST: chunk size 1024 (5428); 8 swap rounds with `thread-yield` on `:busy`/`:readers` (5518, 5777); the deferral names; "installed but not swapped" is indeterminate (5792); retired-id sort and dedupe (4950); release a pending group when `fnn-arena-clear-p`; OWNER STATE READ OFF THE MUTEX at 5738/5741 (COMPOSITION F9) | arena pins, the extent lock, `pread`, the stobj swap (`eval` of the creator at 5570, `setf` of `user-stobj-alist` 5581), checkpoint stage/install, log drop |
| publication / export 5014-5415 | 327 | 6 | ACL2: due, capture, setup (`fn-owner-sco-*`). HOST: at most one publisher (5214); try at most twice with a spare (5172); publish again when one finishes (5162); the GC nursery switch (4834-4847); the export outcome words (5394: `:owner-stopping` / `:archive-write`); self-removal from the roster BEFORE the unpin (5147-5152: B3) | threads, pins, writes and fsyncs, rename, rotation |
| accept / stop / lifecycle 29-238, 631-703, 1687-1751, 4681-4811, 5901-6312 | 833 | 38 | ACL2: `fn-ort-*` (start, claim, settlement, close, intake, window, exit), `fn-nret-*`, `fn-osd-drain-next`, `fn-owner-log-reopen`. HOST: first stop wins (1704); spared sockets (1711-1730); the per-tick order reap/publish/reopen/retire (5977-5981); a retiring node refuses new connections (4684); loop until SIGTERM or stopping; the "close joined" predicate over hooks, workers, cold head, cold workers, committer (6241-6269); which accept errors end a listener (5937-5985: S001/S004, fixed on lane/host-lifecycle) | listen, accept, shutdown, join, hooks, the signal flags |
| cold line 58-62, 4190-4394 | 222 | 12 | ACL2: `fn-otb-dependency-step` (serve / unavailable / wait ms), `fn-pio-reap-work`. HOST: direct vs pooled issue (4219); the verdict derivation (4237); the fault-text table (4292-4297); round-robin requeue; settle only when the worker is ready | the extent lock, worker wait and cancel, the cache store, the intrusive queue |
| failure handlers 50-56, 1001-1045, 1758-1923, 1962-2049, 3717-3734 | 194 | 11 | which condition class maps to which outcome word or exit code: eleven `handler-case` ladders, each hand-ordered (the full table is in the owner inventory: 1778, 1890, 1914, 1973, 2034, 2406, 3349, 3690, 3724, 4323, 4332, 4362, 5054, 5134, 5175, 5234, 5394, 5613, 5917, 5937, 5967, 6017, 6236) | re-signalling, the fence (`fnn-store-fenced`), cleanup closes |

IO.LISP (COORD 2,587 lines, 136 forms), by sub-kind:

| sub-kind | lines (about) | decides (moves) | performs (stays) |
|---|---|---|---|
| the record-log kernel: batch, seal, sync, rotate, recover (6289-6346, 6697-6766, 6837-6910, 7017-7086, 7217-7423, 7459-7481, 7538-8081) | 1,200 | commit timing (inline vs deferred, `*fnn-log-batch*`); on `:full` wait for the syncer then commit (7837); retry the take at most twice (7817); the sync-state machine `:idle/:syncing/:fenced/:failed` (8038, 8073, 8080); the pending count arithmetic (7900, 8071, 7988); members -> inflight -> fenced (6750-6766, 6899); the fenced flag saved and restored around a commit (7876, 7905); OS error from append to barrier = `fn-lgc-fence-failed` + uncertain, store refusal = fault; rotation: spare matches `next` (7302, 7361), the refusal reasons, closing the old fd, `dir-pending`; the head-segment condition (7474-7476); `fnn-recover-log`'s step order (7597-7786: load, position, plan, choose replay mode, chain three joins, three barriers with the phase check, sweep when writable, quarantine on a name) | kernel lock (recursive via `fnn-log-with-kernel`, non-recursive at 8010/8069/8079), `sync-cv`, `spare-lock`, pwrite, fdatasync, preallocate, no-replace rename, unlink, dir fsync, close. The VALUES (take verdict, append octets, frontier, rotation octets, plan, lineage) are all ACL2's |
| service-log queue and writer thread (863-1120) | 200 | run a writer or write directly (1141, 848); the journal-gap flag (959-965); routing by destination (1033-1044); any error -> `:failed`; the stop's `:absent/:joined/:timeout`; swap via the queue or under the log mutex. ACL2: queue-vs-drop (`fn-log-sink-offer`), counts (`fn-log-sink-take`), the close wait (`fn-log-sink-close-wait-seconds`), the journal plan (`fn-otm-jw-*`) | one thread (1078) with NO handler-case (COMPOSITION F11), one join with timeout (1097), the queue mutex/waitqueue, write, ftruncate, close |
| arena pins (6768-6835) | 70 | nothing: `fn-arpn-step` decides everything | one mutex around each step and the global `setq` |
| payload lifecycle (1555-1578) | 25 | `fn-pvl-runtime-step` decides; the host records the arena on `:reset`; NOTE: the step's answer is called "permission" but the phase global is never assigned from it here | one mutex |
| failure classification (74-158, 523-576, 792-825, 2179-2197, 2465-2470, 3541-3636, 5380-5382, 5653-5823) | 400 | errno -> class (EEXIST existing, ENOENT ignored, EWOULDBLOCK held, EINTR retry, EAGAIN would-block); "before the rename is known, at or after it is uncertain"; the fenced flag; which conditions re-signal (serve-client); TLS/connect classes for peer dials; the condition hierarchy itself (`fnn-store-error` > `fnn-store-fault` > {`fixed-callback-fault`, `entry-guard-fault`, `input-overbound`}, `fnn-store-indeterminate`, `io-refusal`, `usage-error`, `open-refusal` > `profile-refusal`; `fnn-os-error`; 74-130) | `error`/`signal`, `handler-case` (79 sites), `ignore-errors` (40), `unwind-protect` (70) |
| durable publication programs (2216-2419, 2778-2830, 3080-3123, 3896-3949, 3979-4039, 4278-4364, 4467-4489, 4529-4630, 4747-4826, 4913-4978) | 800 | the order of syscalls and cuts, MIRRORING ACL2's programs (`fn-bs-imp-program`, `fn-sxd-program`, `fn-bs-scp-program`, `fn-bsi-log-init-program`) by hand instead of interpreting the step list; the cleanup policy (unlink the stage on failure); node-secret rotation's keep-then-replace; whether a stop at a batch boundary refuses | mkdir, open O_EXCL, write, fsync, link, rename/renameat2, unlink, flock |
| startup, shutdown, store lifecycle (1984-2068, 2159-2177, 2421-2463, 3525-3539, 3702-3720, 5825-5877, 8457-8562) | 300 | the open order (safe-directory, clone check, format check, filesystem identity, staging, lock, config, log, journal); close-on-error; open-ms timing; in `redeem` the transport choice (`fn-redeem-step` picks the steps) | flock, open/close, socket, TLS |

The other coordinating files (classifier signatures; targeted reads for mux and extent):

| file | lines | COORD sig | locks / threads / cv / handlers | ACL2 calls | what the host decides (moves) |
|---|---|---|---|---|---|
| mux.lisp | 1,464 | 524 (+484 "PURE" policy) | 27 / 1 / 1 / 22 | 19 | the loop: `fnn-mux-iterate` 1222-1300 (take inbox, take arrived, waiting handshakes, timers, pending TLS, build the poll set, poll, dispatch, count unsent, bump passes), `fnn-mux-guarded` 318-374 (eight handler clauses: the per-connection failure envelope), `fnn-mux-stop-loop` 1306-1335, `fnn-mux-adopt` 1378-1398 (B2), `fnn-mux-await`/`-await-done` 240-300, `fnn-mux-flush` 421-470, the plan yield 403-419 |
| extent.lisp | 1,274 | 681 | 41 / 1 / 5 / 2 | 73 | the cold executor loop 500-640 (`fnn-extent-executor-loop` 512-523, `-start`, `-stop`, `-enqueue`, `-acquire`, `-observe-returned`, `-wait`, `-commit`; ACL2 decides assignment `fn-pxe-*`, death `fn-pio-worker-death-step`, settlement); the cache bookkeeping 700-760 (which entry to store/forget/drop); the issue/settle protocol 890-1032 (`fn-pio-direct-admit/-settle` decide); register/close 86-147, 1208-1272 (`fn-pio-file-clear-p` decides); the realizers 1039-1207 (`fn-durable-realize-octets`, `fn-pgs-fill-realize` with no lease: COMPOSITION F1) |
| control.lisp + control-transport.lisp | 1,223 | 208 | 7 / 2 / 0 / 17 | 51 | the control accept loop and per-client threads (456, 529), the client roster, the frame read, the consumer waits run on client threads (owner.lisp 2792), reclaim passes and TLS reloads |
| feed-service.lisp | 623 | 312 | 16 / 1 / 0 / 9 | 15 | the push worker (596), its runtime mutexes, backoff on error paths re-reading the live peer record (S036) |
| pull-service.lisp | 589 | 330 | 12 / 1 / 0 / 17 | 45 | the pull worker (568), its round, the logical transit connection (S007, fixed on lane/host-lifecycle) |
| web-host.lisp | 360 | 133 | 7 / 1 / 0 / 6 | 26 | the web face thread (312) serving every connection inline (S037), its stop, the browser session's logical feed (S003) |
| bp-service.lisp, bp-node.lisp, bp.lisp, bp-app.lisp, bp-obligation.lisp, bp-control.lisp, bp-listener-control.lisp, bp-contact.lisp | 4,772 | 1,214 | 7 / 0 / 0 / 46 | 361 | single-threaded BP loops on the accept thread: session state driven by the host (S024-S027), the serialized bp-node loop (S025), the listener loops (classified by HOST-LIFECYCLE) |
| tcpcl.lisp | 773 | 234 | 0 / 0 / 0 / 18 | 41 | the convergence-layer session over io.lisp's socket surface: 18 handler clauses, the deadline/retry policy |
| operator.lisp, operator-live.lisp, admin.lisp, hybrid-control.lisp, checkpoint.lisp, workflow.lisp, peer-invite.lisp, signature-command.lisp, auth-admin.lisp, anchor.lisp, keys.lisp, login-bindings.lisp, tls-reload.lisp, consumer-local.lisp, consumer-remote.lisp | 6,220 | 2,300 | 20 / 0 / 0 / 80 | 574 | verb executors: argv -> ACL2 plan -> a hand-sequenced run of effects with `handler-case` ladders mapping outcomes to exit codes (operator.lisp 540 COORD-signature lines; `fnn-operator-execute-run` operator-live.lisp:20) |

### 1.4 Protocol glue (what moves with the coordination)

GLUE is the host moving octets between sockets/files/buffers and ACL2 entries and routing the results.
io.lisp has 3,151 lines of it (237 forms): the dispatcher (section 2.4), the checkpoint plan steps
(`fnn-plan-write-all` executes `fn-sccb-plan-octets` per step), the store open and recover drivers, the
command verbs. owner.lisp has 2,277 (98 forms): `fnn-owner-handle-chunk-read` 4451-4636 (186 lines), the
transit and served attempts (2074-2360; S002: the article consed into a list twice under the owner mutex,
with the D27 buffer twins `fn-owner-login-gate-buffer` etc. written in host/owner-host.lisp:3765-3795 and
called by nothing), `fnn-owner-drain-one` 2875-2989, `fnn-owner-consumer-local-serialized` 2672-2775. The
width of the boundary is the measure: 2,062 call sites (1,397 `fnn-core`, 187 `fnn-owner-core`, 115
`fnn-core-state`, 72 `fnn-call`, 70 `fnn-owner-action`, 22+13 pool wrappers, 18 arena-state, 6
buffer-state) naming 1,379 distinct entries, and 337 `fnn-octet-list` conversions (io 102, owner 74,
operator 26, control 26, signature-command 19, bp-app 18, peer-invite 13, hybrid-control 13, bp-service
13, pull-service 11, bp 11, admin 11), each O(L) conses per call (planning/design-2026-09-25-representation.md:29).
After the move the glue is inside ACL2 (an actor step calls the next step by name) and the conversions
disappear where the data is already in a buffer stobj.

### 1.5 Primitives (what stays): the census

Every SBCL runtime symbol the natives reference (1,229 references; the distinct ones):

| family | distinct operations | where |
|---|---|---|
| POSIX files (sb-posix, sb-unix) | open, close, fstat, lstat, stat fields, fcntl (F_FULLFSYNC, O_NONBLOCK), fsync, fdatasync (alien), ftruncate, lseek, opendir/readdir/closedir, link, rename, renameat2 (alien, no-replace), unlink, mkdir, chmod, getcwd, realpath (alien), statvfs/statfs (alien), flock (alien), posix_fallocate (alien), syncfs (alien), unix-read, unix-write, pread (alien), tcgetattr/tcsetattr (the password prompt) | io.lisp (114 PRIM forms), extent.lisp (pread 151ff), peer-invite, checkpoint |
| sockets (sb-bsd-sockets) | inet/inet6 socket, reuse-address, bind, listen, accept, connect (non-blocking, operation-in-progress), shutdown, close, peername, name, file-descriptor, get-host-by-name, poll (alien), pipe, wait-until-fd-usable | io.lisp 5538-5823, mux.lisp 150-234, control-transport, tcpcl, bp-service |
| threads (sb-thread) | make-thread (15 sites: owner 5, io 1, extent 1, mux 1, control 2, feed 1, pull 1, web 1, parked 2), join-thread (10), thread-alive-p (10), thread-yield (5), make-mutex (31), with-mutex (205), with-recursive-lock (25), grab/release-mutex (1), holding-mutex-p, make-waitqueue (7), condition-wait (12), condition-notify (3), condition-broadcast (15), make-semaphore/wait/signal (the `once` mode), `*current-thread*` (18), `with-system-mutex`/`*make-thread-lock*` (parked) | |
| clock | get-internal-real-time (monotonic; 23 sites in io, 14 in owner), sb-ext:get-time-of-day (wall, ms), get-universal-time | HST-026 |
| entropy | sb-ext:seed-random-state t (/dev/urandom), `with-open-file "/dev/urandom"` (owner 2663), RAND_bytes (bpsec) | |
| memory and GC | with-pinned-objects (42), vector-sap, sap-ref-8/32/64, make-alien/free-alien, get-bytes-consed, bytes-consed-between-gcs, gc, dynamic-space-size, `*free-tls-index*`, atomic-incf (3, the lookup counters) | |
| process and signals | getpid, kill (SIGKILL: the developer cuts), exit, posix-getenv (14), `*posix-argv*`, enable-interrupt (SIGPIPE ignored, SIGHUP counted, SIGTERM flagged: io.lisp 8578-8590), run-program/process-wait (tests) | |
| FFI libraries (define-alien-routine 109, extern-alien 23, alien-funcall 17; about 110 distinct C functions) | OpenSSL libssl/libcrypto (about 60: SSL_CTX_*, SSL_*, X509_*, EVP_* digest/sign/keygen/AES-GCM, HMAC_*, ERR_*, RAND_bytes, OPENSSL_cleanse); libsodium (sodium_init, crypto_sign_keypair); libfn-blake3 (fn_b3_init/update/final/hash/hasher_size/version); libfn-mldsa65 (verify, widths, strerror, generate_pem); libfn-deflate (new/free/sync/bound/version); libc (pread, open, close, recv, shutdown, free, realpath, statvfs, flock, fdatasync, posix_fallocate, syncfs, renameat2, sysconf, pthread_self/kill); SBCL runtime symbols (dynamic_values_bytes, thread_control_stack_size, next_free_page, gencgc_alloc_profiler) | tls.lisp (610 PRIM lines), bpsec-crypto (213, parked), digest (143), signatures (169), crypto (97), deflate (121), heap, io |
| image (build only) | load-shared-object, save-exec, `*save-hooks*`, `*init-hooks*`, `*core-pathname*`, sb-int:encapsulate | build*.lisp, strip-world |

The tree ALREADY HAS a primitive interface in ACL2: host/store-open-host.lisp:30-75 and
host/store-write-host.lisp:40-70 declare 43 `fn-hx-*` stubs (`fn-hx-lstat`, `-list-dir`, `-open`,
`-open-ro`, `-open-rw`, `-create-excl`, `-close`, `-pread`, `-fill` (into the buffer stobj), `-pwrite`,
`-pwrite-zeros`, `-write-all`, `-fsync`, `-fdatasync`, `-fsync-dir`, `-sync-dir`, `-preallocate`, `-link`,
`-rename`, `-unlink`, `-mkdir`, `-lock-shared`, `-lock-exclusive`, `-unlock`, `-realpath`, `-statfs`,
`-read-file`, `-read-at`, `-list-bounded`, `-list-window`, `-lz4-candidate`, `-clock`, `-random-octets`,
`-random-hex`, `-getpid`, `-getcwd`, `-getenv`, `-strerror`, `-os`, `-out`, `-warn`, `-kill-self`), each
with its answer grammar in a comment (":ok | (:ok VALUE ...) | (:error ERRNO TEXT) | :locked |
:not-regular"), realized by tools/extract/hostio.scm for the CHICKEN product and NOT loaded by the SBCL
image (build.lisp loads neither file; tools/extract/world-host.lisp:52-53 does). `fn-xw-post-body`
(store-write-host.lisp:1552) and `fn-xo-open-store` (:581) sequence those primitives in ACL2 `:program`
mode and restate most of io.lisp's open, recover and post drivers. The primitive interface of section 2
starts from these 43, makes them logic-mode constrained functions, and adds the socket, thread, section
and mailbox families.

### 1.6 Build, startup, packaging (what stays, as build)

build.lisp 622, build-dtn.lisp 448, build-store-test.lisp 145, strip-world.lisp 334 (the saved world;
also resizes the hons space and memoize array: 168-180), heap.lisp 361 (the heap/stack figure probe over
ACL2's `fn-heap-*`), io.lisp BUILD 920 (`fnn-dispatch` 8224-8346 (123 lines: argv -> verb), `fnn-main`
8564-8627, `+fnn-developer-selectors+` 6007-6075, the developer fault seams `fnn-at`/`fnn-log-at`/
`fnn-pub-at`/`fnn-export-at`/`fnn-init-cut`, the version word), owner.lisp BUILD 410 (`fnn-owner-install`
1157-1243, the verb, the hold selectors), operator.lisp's verb registration. About 3,200 lines; it stays
host Lisp, outside the served path, qualified by the image identity and the natives.

### 1.7 host/*.lisp: the ACL2-mode layer is `:program` mode, which is TCB

| file | lines | defuns | :program | role |
|---|---|---|---|---|
| owner-host.lisp | 5,239 | 299 | 195 | the owner's entries: state threading (`f-get-global`/`f-put-global` of 155 globals, `fn-owner-install-ocfg`), SEQUENCING of logic functions (`fn-owner-take` :program: `fn-owner-step` then `fn-apc-take` then the carries), `fn-owner-io` (1551: the observation/effect protocol: `(fn-owner-io operation result state)` folds `(:store (:io op result))` into the owner -- the seed of the oracle-step shape) |
| interfaces.lisp | 4,992 | 0 | 0 | 1,409 `definterface` declarations (books/definterface.lisp checks class, kinds, keystones, raw-with against the world) |
| store-write-host.lisp, store-open-host.lisp | 2,573 | 209 | 209 | the extractor's ACL2 twins of io.lisp over the 43 `fn-hx-*` stubs; not loaded by the image |
| store-node-host.lisp, store-host.lisp, checkpoint-host.lisp, page-*-host.lisp, config-host.lisp | 3,900 | 300 | 185 | the Store open/recover/checkpoint/page wrappers |
| native-operator/-control/-admin/-live-status/-auth*-host, hybrid-signature, peer-invite, tls-reload, web, workflow, bp-*-host, tcpcl-host, anchor-*, consumer-remote-host, reader-host, feed-filename-host, topic-history-metadata-host, journal-publish-host, bp-receipt-journal-host | 3,700 | 420 | 390 | the verbs' plans, lines and transitions |
| 69 files no build loads (account-*, admission-*, index-*, history-*, receiver-*, recovery-*, ninep-*, snapshot-initial-*, allocation-epoch-host, post-identity-captured-host, payload-view-host, query-*, owner-exposure-host, store-checkpoint-context-host, ...) | 5,470 | 320 | 310 | parked by D46/stage 0 with their producers (build.lisp:364-372) |

What a `:program` wrapper is: unproved ACL2 that runs in the image through the `*1*` counterpart with
`guard-checking-on = t` (io.lisp:8606), its callees' guards checked at every call inside an
invariant-risk body (A-EXTRACT's text), its own body never verified. Astra: ":program host wrappers are
not guard-verified caller proofs". 1,089 such functions, 44 of which write the owner's globals (33 of them
:program; stage-5 lanedump). They are the ACL2-side half of the TCB this plan shrinks, and their
conversion is bounded by one fact: STAGE-5B's tier A converted 8 writers in one lane (f98e1ff1b: guard
hints from 21.9M steps to 662), so the rate is about ten per lane-week with minimal-theory hints.

### 1.8 Loaded by no build (not TCB; not to be migrated)

`python3 tools/host_loaded_check.py` (run 2026-10-03 at 4aa332295) lists 92 files: 23 under host/native
(snapshot-producer 631, receiver-turn-parked 504, bpsec-crypto 298, runtime-participants 246,
runtime-bootstrap 204, snapshot-startup 149, index-writer-turn 128, runtime-recovery-file 121,
runtime-construction-inventory 117, post-captured-parked 96, auth-adoption-parked 80, ninep 77,
runtime-image-policy 75, runtime-construction-recipe 73, extent-decoded 71, runtime-profile-envelope 71,
recovery-payload-view 63, account-adoption 62, runtime-collector 62, recovery-profile-read 55,
snapshot-initial-reader 35, runtime-u64-request-source 18, admission-preallocation 14: about 3,250
lines) and 69 under host/ (about 5,470 lines, section 1.7). They return with their producers (D46,
stage 0's "Completion (forward)") or are deleted and listed in planning/retired-paths.json; this plan
counts neither as TCB nor as migration work, and the figure "67k" should be quoted as "about 58k loaded".
(tools/extract/world.py also names host/native/lz4.lisp, which does not exist.)

### 1.9 Per-file verdicts

Verdicts: MOVE (coordination, glue and computation become ACL2; the file's primitives join the primitive
layer), KEEP-PRIM (the file is a primitive binding and stays, named), KEEP-BUILD (build/startup only),
DELETE/RETURN (no build loads it), SPLIT (a named part moves, the rest stays).

| file | lines | verdict | what moves | what stays | why |
|---|---|---|---|---|---|
| io.lisp | 8,649 | SPLIT | the log kernel's state machine, rotation and recover order (1,200), the writer-thread protocol (200), failure classification (400: the condition HIERARCHY becomes an ACL2 outcome classifier over a host-named class keyword), the durable programs' hand sequencing (800: replaced by an ACL2 program interpreter over the byte-store step lists), the 66 PURE forms, the dispatcher's glue (fnn-core wrappers) | 114 PRIM forms (1,141 lines: the `fnn-posix` wrappers, sockets, poll, pipe, clock, signals, flock, barriers), `fnn-call`/`fnn-install-raw-dispatch` (reduced), BUILD 920 | the kernel's values are already ACL2's; the host decides only the order and the state machine |
| owner.lisp | 6,392 | MOVE (actors) | committer+syncer (797), accept/stop/lifecycle (833), reclaim/publication/export (848), cold line (222), gate (126), timers (140), failure handlers (194), the glue (2,277), the 7 PURE forms and embedded decisions | the section PRIMITIVE (gate+mutex+fence: today's `fnn-owner-gated` body minus its decisions, about 80 lines), the thread spawns, the hold selectors (BUILD 410) | every sub-kind's decisions are listed in 1.3; eight actors live here |
| mux.lisp | 1,464 | MOVE (actor) | the loop's policy (interest, timers, idle, next deadline, passes, unsent), the per-connection phase machine, the failure envelope's eight clauses, adopt/stop | poll (150-234), the wake pipe, the socket read/write primitives, TLS channel calls | B4/r71 F11, B2, the idle class are host policy today |
| extent.lisp | 1,274 | MOVE (actor + stobj) | the cold executor loop, the cache bookkeeping, issue/settle, register/close, the realizers' routing | pread (151-170, 264), fd tables as a primitive-owned registry, `with-pinned-objects` | fn-pio/fn-pxe/fn-pio-direct already model it; F1 (`fn-pgs-fill-realize`, no lease) is the live gap |
| control.lisp, control-transport.lisp | 1,223 | MOVE (actor) | the accept loop, client roster, frame framing, the consumer wait, reclaim passes, TLS reloads run on client threads | the control socket primitives | |
| feed-service.lisp, pull-service.lisp, web-host.lisp | 1,572 | MOVE (actors) | the three worker loops and their runtime state, `fnn-feed-consume`, the logical connection feed | socket primitives | S036, S037, S003/S007 |
| bp-*.lisp (8 loaded files) | 4,772 | MOVE (actors, after the owner) | the session machines driven by the host, the dispatch tables, deletion loops | socket primitives | Astra 6.7: modules omitted by a profile are excluded from that profile's theorem |
| tcpcl.lisp | 773 | MOVE | the session, deadlines, retries, 18 handler clauses | io.lisp's socket surface | host/tcpcl-host.lisp already computes "every protocol value" (build.lisp:385) |
| tls.lisp | 1,073 | KEEP-PRIM | `fnn-tls-consume-plaintext`'s equality decision (one ACL2 line) | the libssl binding (610 PRIM lines), the context lock, the pair swap | A-TLS-NATIVE |
| crypto.lisp, digest.lisp, signatures.lisp, deflate.lisp (inflater half), bpsec-crypto.lisp (parked) | 1,672 | KEEP-PRIM | deflate.lisp's ENCODER (188-530, about 340 lines) moves to ACL2 | the FFI bindings, the self-checks at start (A-CRYPTO-NATIVE qualification), the pooled buffers | the encoder is pure arithmetic with a live bug (S005) and an ACL2 decoder to prove it against |
| operator.lisp, operator-live.lisp, operator-control-client.lisp, admin.lisp, hybrid-control.lisp, checkpoint.lisp, workflow.lisp, peer-invite.lisp, signature-command.lisp, auth-admin.lisp, anchor.lisp, keys.lisp, login-bindings.lisp, tls-reload.lisp, consumer-local.lisp, consumer-remote.lisp, auth.lisp, immutable-publish.lisp, auth-read.lisp, config.lisp, feed-filename.lisp, topic-local.lisp, acl2-session.lisp, owner-control-turn.lisp, receiver-parser-turn.lisp | 7,000 | MOVE (verb actors; last) | each verb's run: argv -> ACL2 plan -> ACL2 program of effects over primitives; the exit-code ladders | the verb registration (BUILD), file primitives | the verbs are offline or control-socket paths; they migrate on the same program interpreter as the durable programs (io.lisp COORD f) |
| heap.lisp | 361 | KEEP-BUILD | | the probe and its sysconf reads | |
| build.lisp, build-dtn.lisp, build-store-test.lisp, strip-world.lisp | 1,549 | KEEP-BUILD | | | |
| 23 parked natives | 3,250 | DELETE/RETURN | | | section 1.8 |
| host/*.lisp loaded (43 files) | 20,440 | MOVE (to logic mode) | every `:program` wrapper becomes a guard-verified, carried entry (def-entry/def-owner-writer); the sequencing wrappers become actor step bodies | host/interfaces.lisp (generated, shrinking) | section 1.7 |
| host/*.lisp unloaded (69 files) | 5,470 | DELETE/RETURN | | | section 1.8 |

## 2. The primitive interface

### 2.1 What a primitive is

A primitive is one host operation that ACL2 code calls and that may fail, complete partially, block, or
complete late. Its SPECIFICATION is a label of the host model HM (lanedumps/host-model.md, layer P: the
`(:io-begin ...)`/`(:io-complete TOKEN VERDICT)` pair, `(:acquire TID L)`, `(:fd-open ...)`, `(:crash)`),
extended by this section; its REALIZATION is a raw definition installed under `:fn-native-host`, the
mechanism A-SIG-NATIVE already uses (host/native/signatures.lisp:363 defines the raw `fn-sig-verify` and
its `*1*` counterpart; extent.lisp:1039-1207 does the same for `fn-durable-realize-octets`,
`fn-pgs-fill-realize`, `fn-arena-stored`); its LOGICAL side is a constrained function in ONE book,
books/host-primitives.lisp, declared by `encapsulate` with a local witness and its named constraints, the
pattern of books/assumptions.lisp (A-DURABILITY at :78, A-CRASH-IMAGE at :342), so that every actor step
is guard-verified and proved against the constraints and never against a definition. The constraints are
what the HM assumes of the label; the row in specs/failures.md is A-PRIM-<family>; functional
instantiation is the qualification hook, as docs/proofs.md already says of A-DURABILITY.

The 43 `fn-hx-*` stubs (section 1.5) are the file family's draft: same answer grammar, already consumed
by 2,573 lines of ACL2 (`fn-xo-*`/`fn-xw-*`), already realized once (tools/extract/hostio.scm). The
change is their mode (`:program` stubs that `er hard!` -> constrained logic functions) and their
realization in the image (raw defuns in host/native, where io.lisp's `fnn-posix` wrappers are today).

The CALLING SHAPE. A primitive takes and returns the calling actor's stobj (section 2.3) so that it is
single-threaded in the logic; it never takes `state` (there is one live state and it belongs to the
owner section; section 2.3) and never takes a shared stobj (the live arena/catalog/history are touched
only inside a section). Its answer is a tagged value: `:ok`, `(:ok V ...)`, `(:partial N)`, `:would-block`,
`(:error ERRNO)`, `:timeout`, `:stale`, `(:uncertain)` -- the vocabulary `fn-hx-*` already uses plus the
three the HM needs (`:would-block` for non-blocking sockets, `:timeout` for a timed wait, `:stale` for a
completion after cancel). The host maps SBCL conditions to that vocabulary and NEVER decides anything
else: the errno table that HOST-LIFECYCLE wrote for accept (`*fnn-accept-again-errnos*`,
`*fnn-accept-exhausted-errnos*`, io.lisp on lane/host-lifecycle) is the right shape with the wrong owner;
it becomes an ACL2 table `fn-accept-outcome` over the errno the primitive returns.

### 2.2 The set

About 110 primitives in nine families. Each row: the primitives; the oracle-step specification (what the
host may answer, including failures, partial results and late completion); the named assumption; the
existing realization.

| family | primitives | oracle step (may answer) | assumption | realized today by |
|---|---|---|---|---|
| F FILES AND DURABILITY (the 43 `fn-hx-*` plus `fn-hx-fdatasync-dir`, `-link-no-replace`) | open-ro/-rw/-create-excl, close, pread/fill (into `fn-octets-lg`), pwrite, pwrite-zeros, write-all, fsync, fdatasync, fsync-dir, preallocate, link, rename-no-replace, unlink, mkdir, lstat, list-dir(bounded, windowed), realpath, statfs, lock-sh/-ex/unlock | open: `(:ok H SIZE)` or `(:error ERRNO)`; pread: `(:ok OCTETS)` with FEWER octets only at end of file, `(:error EINTR)` (the caller retries: a decision), `(:error EIO)`; pwrite: `(:ok N)` with N < requested (partial: the caller continues or fences), `(:error ENOSPC)`; fsync/fdatasync: `:ok` or `(:error ERRNO)` after which the OS has landed a torn SUBSET and a retry fences nothing (crash-model-v2); rename: `:ok`, `(:error EEXIST)` (no-replace), `(:error ERRNO)` after which the namespace is UNCERTAIN; lock: `:ok`, `:locked`, `:not-regular`; a CRASH may follow any step at any point (HM `(:crash)`) | A-PRIM-FILE (the POSIX fd semantics: an open fd is readable until closed; a number is reused only after close -- why the fn-pio row exists), A-DURABILITY, A-WRITE-ISOLATION, A-CRASH-IMAGE, A-HOST-EXCLUSIVE-READ (all existing) | io.lisp `fnn-posix` wrappers 443-773, 2871-2963, 4228-4463, 6356-6385; extent.lisp 151-170; hostio.scm |
| S SOCKETS | listen(addr, port, backlog), accept, connect(non-blocking), recv(fd, n), send(fd, octets), shutdown, close, peername, set-nonblocking, pipe, poll(fds, events, timeout-ms), resolve(name) | accept: a socket, `:again` (EAGAIN/EINTR/ECONNABORTED/...), `:exhausted` (EMFILE/ENFILE/ENOBUFS/ENOMEM), `(:error ERRNO)` listener-level; recv: `(:ok OCTETS)` (possibly fewer), `:would-block`, `:eof`, `(:error ECONNRESET)`; send: `(:ok N)` partial, `:would-block`, `(:error EPIPE)`; poll: `(:ok REVENTS)` or `:timeout`, spurious readiness allowed (the accept may then answer `:again`); connect: `:ok`, `:pending`, `(:error ERRNO)` | A-PRIM-SOCKET (the kernel's socket semantics; no ordering promise beyond "bytes accepted by send are a prefix of what the peer may read") | io.lisp 5538-5823, mux.lisp 150-234 (poll, wake pipe), the accept classifier on lane/host-lifecycle |
| T TLS | ctx-new/free (the pair), accept(fd) -> channel, connect, read, peek, write, pending-p, shutdown, close-channel, verify-result, export-keying-material, version | read: `(:ok OCTETS)`, `:want-read`, `:want-write` (the retry direction: today `fnn-tls-retry-direction` tls.lisp:604), `:eof`, `(:error KIND TEXT)`; peek-then-consume: the consumed octets EQUAL the peeked prefix or `(:error :consume-changed)` (the one check the host makes today, tls.lisp:891-923); handshake: `:ok`, `:again`, `(:error :verify)`, `(:error :handshake)`, `:timeout` | A-TLS-NATIVE (existing row, unchanged) | tls.lisp (610 PRIM lines, about 35 libssl functions) |
| X THREADS, MUTEXES, CONDITION VARIABLES | spawn(actor-kind, actor-arg) -> tid, join(tid, timeout-ms) -> `:joined`/`:timeout`/`:absent`, alive-p, yield, current-tid; mutex-make, acquire(L), release(L); cv-make, wait(cv, L, timeout-ms) -> `:woken`/`:timeout` (and on timeout the mutex may NOT be held: owner.lisp:3496-3499), notify, broadcast; semaphore | spawn may fail (`(:error :resources)`); a thread may die (alive-p nil) without a result; wait may wake spuriously (the caller re-checks: a decision in the actor step); acquire blocks (no timeout) | A-SBCL-THREADS (new row, COMPOSITION section 5: `with-mutex` is mutual exclusion with release-acquire visibility; `condition-wait` returns only by notify, timeout or abort; word-sized slot writes are atomic; make/join as documented) | sb-thread calls at the 15 spawn and 394 lock sites |
| SEC SECTIONS (the one primitive that touches shared state) | `(fn-prim-section LOCK-CLASS CLASS STEP ARGS act)` where LOCK-CLASS in {:owner (gate+mutex), :extent, :pins, :kernel, :commit, :roster, :loop(mux inbox)}, CLASS the gate class, STEP an ACL2 function name over the live stobjs of that lock class | the host takes the gate (for :owner: `fn-otm-next` picks the class, the mutex is taken, the fence checked), applies STEP to the LIVE stobjs under the mutex with `*the-live-state*`, installs the fence on any serious condition BEFORE releasing (today `fnn-owner-shared-action-locked`), releases, returns STEP's value or `(:refused :stopping)` or `(:faulted CLASS)`; the HM label is `(:section TID CLASS EVENTS)`; a STEP that reaches a blocking primitive is refused at BUILD time (a world-level check over the call graph: the step's closure may call only the primitives its declaration lists as `:io`, which is R2 made syntactic) | A-HOST-IS-THE-MODEL's residue: "the envelope applies STEP exactly once per section, on the live stobjs, under the lock the declaration names" -- about 80 lines of host Lisp, checked by the natives and the LOCK-CHECK enclave, never a theorem | owner.lisp 1573-1872 (gated, serialized, shared-action, transit), io.lisp 6344 (kernel), extent.lisp:48, io.lisp:6768 (pins), mux.lisp:72 (inbox) |
| M MAILBOXES (typed handoff between actors) | mailbox-make, push(box, value) -> `:queued`/`(:closed)`, take(box) -> `(:ok VALUES)`/`:empty`, close(box) (no push after close: B2's fix by construction), wake(box) | values are ACL2 objects (immutable); a push after close answers `:closed` and the pusher keeps the value (the adopt-vs-stop protocol: the socket is then closed by the adopter); a take returns everything pushed before it in push order | A-SBCL-THREADS | the mux inbox/arrived lists (mux.lisp:72, 1189-1220, 1378-1398), the commit-lock's done/awaiting tables (owner.lisp 3043-3067), the log queue (io.lisp 916-972), the syncer's result cell (owner.lisp 3339-3361) |
| C CLOCK, ENTROPY, PROCESS | now-monotonic-ms, now-wall-ms (gettimeofday), random-octets(n), getpid, getenv, exit(code), kill-self (developer cut), signal observations: sigterm-requested-p, sighup-count | the monotonic clock never regresses (HST-026 counts regressions; the primitive reports `(:ok MS)` and the actor's clock step `fn-otm-clock-step` decides); wall time may jump; random-octets may fail (`(:error)`: a fault, never fewer octets) | A-PRIM-CLOCK (HST-026 plus the timer lateness bound L, host.md:753), A-PRIM-ENTROPY (/dev/urandom and RAND_bytes are a CSPRNG: today unnamed, COMPOSITION 1b), A-PRIM-PROCESS | io.lisp 518, 746, 1722, 2054, 5921, 8578-8590 |
| K CRYPTO AND COMPRESSION FFI | blake3 (stobj, prefixed buffer, prefixed range), mldsa65-verify, ed25519-keypair/sign, hmac, aes-gcm, evp-digest, deflate-sync (outbound zlib: AFTER the encoder moves to ACL2 this is the one compressor primitive, or none: ACL2's encoder with the host's zlib as a differential control), inflate stays ACL2 | pure functions of their inputs or `(:error)`; no partial | A-CRYPTO-NATIVE, A-SIG-NATIVE, the two missing rows (libsodium Ed25519 and the SHA-512 leaf; COMPOSITION section 5), A-DURABLE-LZ | digest, signatures, crypto, bpsec-crypto, deflate.lisp:62-187 |
| G MEMORY, GC, IMAGE | gc-nursery-set, bytes-consed, dynamic-space-size, thread-stack-octets (the heap probe), save-exec/load (build only) | observations | A-SBCL-RUNTIME (existing) | heap.lisp, owner.lisp 4834-4847, build.lisp |

Not primitives (decisions that live in the host today and move): errno classification into outcome words;
retry counts and backoff; deadlines and "due" predicates; which class or connection runs next; FIFO
within a class; the pass arithmetic; the sync-state machine; stage/cleanup policy; the exit code of a
condition class (`fn-outcome-code` exists, io.lisp:68-72, 152: the classifier takes the CLASS keyword the
primitive or envelope names); every line the operator reads.

### 2.3 How ACL2 code runs on several threads: the facts and the design they force

THE FACTS (read in the ACL2 8.7 sources the image is built from, /opt/homebrew/opt/acl2/libexec, SBCL
2.6.8; the launcher ~/tools/acl2-fn/acl2-literal-4g-tls64k names saved_acl2.core, so this is plain ACL2,
not ACL2(p)):

1. There is ONE live state. `*the-live-state*` is a token; a state global is the `symbol-value` of a
   special symbol in package ACL2_GLOBAL_ACL2 (axioms.lisp `put-global` 15977-15996: `(setf
   (symbol-value (global-symbol key)) value)`), i.e. a process-wide variable shared by every SBCL thread
   unless a thread `let`-binds it (SBCL dynamic bindings are thread-local; `*fnn-extent-no-io*` relies on
   this). The extracted SBCL-core product (tools/extract/clruntime.lisp:14-24) keeps every state global in
   ONE `:synchronized` hash table with no binding at all. Consequence: per-thread state globals are not a
   design option for the product, and the 155 `fn-owner-*` globals (357 put sites) must become a stobj
   before any owner step runs outside the owner thread -- STAGE-5B's carrier move is a precondition.
2. There is ONE live object per stobj name: `*user-stobj-alist*` (axioms.lisp:1044; basis-a.lisp:9444
   `the-live-var`: "the live stobj corresponding to st is stored on the raw Lisp alist
   *user-stobj-alist*"), found by io.lisp's `fnn-live-arena`/`-cat`/`-hist`/`-octets` (333-364) and
   updated destructively. Two threads updating one live stobj is a data race with no ACL2 meaning.
   `with-local-stobj` (basis-a.lisp:9711; `mv-let-for-with-local-stobj`) creates a FRESH object per
   evaluation through the creator: a private stobj per actor is sound, and ACL2 8.7's stobj-tables and
   child stobjs (basis-a.lisp:7962-8136) let an actor's stobj hold per-connection sub-stobjs.
3. hons and memoize are single-threaded. hons-raw.lisp's Essay on Hons Spaces: "separate threads may
   never access the same Hons Space"; `*default-hs*` (hons-raw.lisp:4118) is the one process-wide space
   unless a thread binds its own; "Cache Tables are not thread safe" (:347, :571); memoize-raw.lisp:111
   "Consider finer-grained way to make memoization thread-safe", :1899 "When memoized functions are
   executing in parallel, the value of *caller* ... may be meaningless". Six books use `hons-acons`/
   `hons-get`/`fast-alist-*`/`memoize`; books/served-catalog.lisp:2428-2478 does on the LIST route
   (`fn-stx`), which runs under the owner mutex today. strip-world.lisp:168-180 keeps a (small) hons space
   and the memoize array in the image.
4. Raw compiled ACL2 functions are reentrant: a guard-verified logic-mode function compiled by SBCL
   touches its arguments and fresh allocations and nothing else -- EXCEPT state globals (1), live stobjs
   (2), hons/memoize tables (3), and the raw specials of evaluation: `*aokp*` (axioms.lisp:5428, a global
   whose value t lets attachments run; never rebound on the served path), `*wormholep*`, and
   `guard-checking-on` read through the live state by every `*1*` counterpart (io.lisp:8606 asserts it is
   t). Attachments (`defattach`) are process-wide and immutable after the build. The `*1*` counterpart of
   a `:program` function with invariant-risk checks its callees' guards per call (A-EXTRACT's text).
5. ACL2(p) (parallel-raw.lisp: plet, pargs, pand, por, spec-mv-let; waterfall parallelism) is a separate
   executable (saved_acl2p, ACL2_PAR=t) and offers fork/join parallelism over pure functions with its own
   thread pool and per-thread hons spaces. It is not an actor model and the image is not built with it;
   nothing here depends on it, and it is the one place to look for how the ACL2 authors bind
   `*default-hs*` per thread if an actor ever needs honsing.

THE DESIGN THESE FORCE:

- One stobj per actor, created at thread start by the actor's `run` function (`with-local-stobj`, or a
  congruent copy from a `:congruent-to` family so that the step functions are shared), threaded through
  every step and every primitive; the thread's private memory is that stobj and nothing else. The mux
  loop's per-connection records (`fnn-mux-conn`, 36 fields) become child stobjs of the loop's stobj; the
  committer's locals (members, next, ledger, limits, need, stall-told, syncer token) become fields.
- Shared state is touched only by a section's STEP on the LIVE stobjs under the section's lock
  (primitive SEC). A step is a logic-mode function over `(fn-arena fn-cat fn-hist fn-owner$ state)` with a
  carried invariant (def-carried) so that it is raw-dispatched (D40); an actor stobj never crosses a
  section (it is passed by the envelope to STEP as a value only if it is a non-stobj projection).
- No state globals in actors: the only `state` user is the owner section (and that only until the
  carrier move retires the 155 globals; afterwards `state` carries nothing an actor reads).
- No hons, no memoize, no fast alists in an actor's closure: a world-level lint (the shape of
  `theory_check`/`reach_check`: every function reachable from an actor step must not call `hons`,
  `hons-acons`, `hons-get`, `fast-alist-*`, `memoize` or a memoized function); the LIST route's hons use
  stays inside the owner section (single-threaded) or is rewritten.
- The envelope (host, generic, about 300 lines): `(loop (let ((obs (perform-last-action))) (mv-let (act
  st) (fn-<actor>-step obs st) ...)))` -- observe, step, perform -- one per actor KIND, parameterized by
  the step function name; plus the thread registry (R4: every spawn names its registry slot, its join site
  and its failure policy, in ONE table the HM reads) and the mailbox primitives. A v2 moves the loop
  itself into ACL2 as a fuel-bounded `fn-<actor>-run` (def-loop's shape) whose primitives block inside
  it; v1 keeps the ~20-line raw loop because `with-local-stobj`'s scope is one function body and the
  measure of a loop that waits on a condition variable is the host's clock, not a term.
- The failure scope is a declared table, not a handler ladder: the envelope catches ONE class of
  condition at ONE place (the step's `perform`) and names it to the step as an observation
  `(:failed PRIM CLASS)`; the step (ACL2) decides fence / connection-local / retry / exit code through
  `fn-outcome-code` and the failure-scope table FAILURE-SCOPE is generating. The 444 handler sites become
  one.

### 2.4 The cost of the boundary, today and after

Today, every `fnn-call` (io.lisp:1372-1392) is: the entry guard (arity + kind conjuncts; measured 25 ns
with no kind, 60 ns for a Message-ID, 8.5 us for a 2 KiB list, lanedumps/entry-guards.md:15; the spec
cache is a `:synchronized` table filled lazily by whichever thread calls first, io.lisp:1278), a `catch`
plus `handler-case`, and the `*1*` counterpart under `guard-checking-on = t`, which evaluates the WHOLE
guard: `fn-sn-statep` of the live Store for every guarded owner entry (ORIENTATION: "the whole-state
revalidation AGENTS.md forbids"), measured 0.24 s and 8 MB at 1k successes and 23.2 s and 802 MB at 10k
for `fn-sf-success-listp` before the carry (stage-5 lanedump item 3), 1.01 s at 10k for `fn-retain-statep`;
raw dispatch (D40) is the cure and there are 0 raw-dispatched entries in production today (`FN_RAW_DISPATCH`
count; interfaces.json `raw_dispatched: []`). Plus the D27 conversions: 337 `fnn-octet-list` sites, O(L)
conses per call (the served POST conses its article twice under the owner mutex: S002).

After: the boundary is crossed at PRIMITIVES, not decisions. A primitive is a raw function call (no `*1*`,
no entry guard: its guard is verified in the actor's proof and its arguments are the actor's own stobj
and scalars) plus the syscall. The 2,062 decision crossings and their marshalling disappear into ACL2
calls between logic functions (a raw `funcall` after raw dispatch). The cost that REMAINS is the actor
step's guard IF it runs on the counterpart path: an actor step is therefore declared with def-entry
(`:carries` the actor stobj's row, `:raw-with (:carried ROW)`) from its first landing, and the cost-gate's
served fixture measures it (def-entry `:bench (:fixture served)`), with a VISIT bound per step (the mux
step is O(connections) per pass with no allocation beyond the plan windows; the committer step is O(1) per
wake plus O(members) per START/COMPLETE). Guard verification is the proof-time cost: STAGE-5B's numbers
(21.9M steps -> 662 with minimal-theory hints) are the per-step budget to expect.

## 3. The order

### 3.1 Ranking

Defects are the inspection sweep's (build/coordinator/inspection-sweep-2026-10-03.md, S-numbers), Astra
r71's (F-numbers) and the two whole-system answers' (B1-B4, F1-F16). Effort is lane-weeks at the swarm's
observed cadence (stage-5 tier A: 8 writers in one lane; host-lifecycle: 12 items in two days;
def-holder: 3,841 lines of books in three days).

| rank | subsystem | host lines moving | ACL2 already there | defects removed by construction | in-flight lane | effort |
|---|---|---|---|---|---|---|
| 0 | the envelope + failure-scope table + thread registry + mailbox primitives | replaces 444 handler sites and 15 spawn sites by one envelope and one table | `fn-outcome-code`, `fn-ort-*` | S015 S016 S017 S019 S020 S023 S028 S030 S031 (the fence class), S001 S004 S006 S007 S036 S037 (node-stopping), B1 B3, r71 F1 F2 F10 F12; B2 (adopt vs stop: the mailbox's close) | FAILURE-SCOPE (Fable), HOST-LIFECYCLE (Opus, 12 items landed on lane/host-lifecycle) | 2 |
| 1 | THE COMMITTER (owner.lisp 3018-3715: 797 lines; io.lisp 8007-8081 sync state) | about 950 | books/owner-commit-pipeline (286), -time-model (1,701), -time-bars (505), -commit-steps (641), -commit-fairness (608), -stop-drain (252): 3,993 lines, 110 step functions, keystones `fn-ocp-complete-only-after-the-barrier`, `fn-ocp-next-open-only-in-flight`, `fn-otb` consumed-once, `fn-osch-control-waits-at-most-the-bound` | S016/B1 (swallowed fault), S003 (inline commit from a :reader quantum), S014 (feed fsync under the owner), S015 (first-stop-wins drops an uncertain), r71 F5; the 8 host rules of 1.3 become theorems | OWNER-OFFLOCK (its queued-work+receipt helper is this actor's mailbox), STAGE-5B (the carrier) | 3 |
| 2 | THE I/O LOOP (mux.lisp 1,464) | about 1,200 | books/served-plan*.lisp (`fn-splan-cw-drain-is-the-expanded-reply`), public-exposure (`fn-exp-idle`), response-plan-pins, tls-proxy, connection-budget | B4/r71 F11 (next-deadline mismatch), the idle deadline not refreshed by a cursor reply (observation-as-event), r71 F3 F7 F13, S010, S021, B2's other half | HOST-LIFECYCLE items 9/11 (landed as hand fixes; the actor makes them structural) | 3 |
| 3 | the cold line (extent.lisp 1,274; owner.lisp cold 222) | about 1,100 | books/page-read-ownership, -executor, -direct, -ledger, page-file-lease (`fn-pio-direct-cancelled-read-still-pins-its-file`), the HM's T1(b) | F1 `fn-pgs-fill-realize` (no lease), S022, r67 F2, r71 F4 F6 (I/O under extent/owner), the two-writer `*fnn-extent-stats*` | HOST-MODEL (its first theorem is this actor's), DEF-HOLDER (the capability rows) | 2 |
| 4 | accept / stop / run (owner.lisp 833 + `fnn-owner-run` 256) | about 1,100 | `fn-ort-*`, `fn-osd-*`, `fn-nret-*`, books/owner-retire-settlement | S001 S004 S028 S030, r71 F8 F12, B3, the "close joined" predicate as a theorem | HOST-LIFECYCLE | 2 |
| 5 | reclaim / publication / export (owner.lisp 848) | about 850 | `fn-orcp-*`, `fn-owner-sco-*`, `fn-arpn`, `fn-rpin`, `fn-xrt-*`, DEF-HOLDER's capability rows | S017 S018 S019 S020 S038, F2 (response-pin liveness), F9 (owner state read off the mutex), F7 (hand-mirrored cuts) | DEF-HOLDER, HOST-MODEL | 3 |
| 6 | the log kernel and the durable programs (io.lisp about 2,000) | about 2,000 | books/store-log-kernel-concrete (`fn-lgc-*`), store-log-route-programs, byte-store-programs (the step LISTS already exist: `(:cut)`, write, fsync, rename steps), recovery-refinement-concurrent | G4 (spare S/O split), F10 `dir-pending`, S040, the hand-mirrored program order (native_program_check's two of six programs become unnecessary: the program is EXECUTED by one ACL2 interpreter over primitives) | SWEEP-STORE (S014 waits on this), Astra t40 | 4 |
| 7 | the services: control, feed, pull, web (2,795) then BP/TCPCL (5,545) | about 8,000 | books/feed-*, pull-*, web-*, native-control, bp-node*, tcpcl-session | S024-S027 S035 S036 S037, S025 | SWEEP-PEER, SWEEP-OPS | 8 |
| 8 | the verbs (operator, admin, checkpoint, workflow, peer-invite, auth-admin, ...: 7,000) | about 5,000 | books/native-operator, native-admin, the plans | S011 S012 S013 S033 S034 | SWEEP-OPS | 4 |
| P | pure computation (section 1.2): the DEFLATE encoder, the cut tables, the status lines, the errno tables, the word mappings | about 1,800 | the inflater (books/deflate-inflate), `fn-nls`, `*fn-bs-init-pub-cut-names*` etc. | S005, S002 (with the buffer twins called), S029, r71 item 15 | none; small lanes, in parallel from day one | 3 total |

Rank 1 before rank 2, against ember's example: the I/O loop holds the most host-only policy (about 500
lines with no ACL2 twin) and so is the most VALUABLE actor, but it is also the one whose model must be
written first (the timers, the interest mask, the idle class); the committer's model is certified and its
host contribution is eight rules and four defects, so it is the smallest actor that can land END TO END
with every decision proved. It also exercises every primitive family the loop needs except poll (section
primitive, mailbox, spawn/join, condition-wait with timeout, the clock, the kernel's seal/sync), so the
envelope is proved on it before the loop needs it.

### 3.2 What the in-flight lanes should already emit as ACL2

- FAILURE-SCOPE (Fable; the generated lifecycle/failure-scope protocol, decisions/whole-system-correctness
  10.6 step 2): emit the failure-scope TABLE (actor x primitive-class -> connection-local | shared-fault |
  durability-uncertain | private-job) as an ACL2 table and the classifier `fn-outcome-of (actor class)` as
  a logic function; emit the per-actor step's `:failed` observation arm from it. The host side is the ONE
  envelope (section 2.3), not a macro per site. The condition hierarchy io.lisp:74-130 stays as the host's
  naming of classes; its MEANING (which class fences) moves. Acceptance stays Astra's measurement 2
  (inject `fnn-entry-guard-fault` at `fn-otb-issue`; after START; at publication-done).
- OWNER-OFFLOCK (the queued-work+receipt helper for blocking-under-lock): write the receipt ledger as an
  ACL2 protocol book in `fn-otb`'s shape (issue -> generation; complete consumed once; late = :stale) and
  the queue as the mailbox primitive; the helper is then `(fn-prim-mailbox-push)` + a section STEP that
  consumes the receipt, not a host macro. Its first consumers are the inline commit of logical
  connections (S003) and the FNFD feed fsync (S014): both become "issue off the mutex, consume in the
  next section".
- HOST-LIFECYCLE (Opus; 12 items landed on lane/host-lifecycle): `fnn-accept-attempt`'s errno lists are a
  decision -> the ACL2 table `fn-accept-outcome` (the primitive returns the errno); `fnn-connection-scoped`
  (io.lisp, lane) is the per-connection failure envelope -> one instance of the generic envelope with the
  table's `connection-local` row; `fnn-owner-await-logical`/`-feed-logical` (owner.lisp, lane) are the
  first consumers of the mailbox primitive. Land them as they are (they fix live defects); the actor
  slices absorb them.
- DEF-ENTRY / DEF-COMMAND / DEF-HOLDER: they already emit ACL2. def-entry gains Astra's fields
  (`:actor`, `:locks`, `:blocking`, `:failure`, `:io`): an entry declared `:section :owner :io (fn-prim-fsync)`
  IS the section label, and the generated preservation theorem is over the live-stobj step. def-holder's
  capability rows `(kind object incarnation generation holder)` are the H component the HM and the
  cold-line actor share; def-command's served dispatcher is unchanged (it is inside the section).
- STAGE-5B (the owner carrier stobj): the precondition (2.3 fact 1). Keep the owner's stobj ONE object
  (the owner section's); do not design per-connection state into it -- that is the loop actor's.
- HOST-MODEL (the HM book): its layer P label set and books/host-primitives.lisp's signature list must be
  ONE generated table (the HM reads the primitive book; a primitive with no label or a label with no
  primitive is refused at certification); add the window-lease read (review M1), the section and mailbox
  labels, poll and the socket labels, and the actor as the TID's kind. Its T1(b) stays the first theorem;
  the committer actor's run theorem is T1(a)'s first instance.
- LOCK-CHECK (t41): its strict scope is the migrated enclave; its baselined scope shrinks per landed
  actor; its R2 rule becomes the world-level `:io` check inside the enclave (the step's call-graph closure).

### 3.3 The first slice: the committer actor, end to end

SUBJECT. host/native/owner.lisp `fnn-owner-commit-pipeline` 3407-3661, `fnn-owner-committer-loop`
3685-3708, `fnn-owner-start-committer` 3710-3715, `fnn-owner-start-syncer` 3337-3361,
`fnn-owner-commit-event` 3301-3314, `fnn-owner-commit-wake` 3316-3335, `fnn-owner-answer-early` 3369-3378,
`fnn-owner-complete-generation` 3380-3389, `fnn-owner-stall-release` 3391-3405, `fnn-owner-loops-snapshot`/
`-passed-p` 3663-3683, `fnn-owner-members-named` 3363-3367, `fnn-owner-deliver` 3031-3041, the done/awaiting
tables 3043-3067; host/native/io.lisp `fnn-log-await-sync` 8007, `fnn-log-seal-open-batch` 8015,
`fnn-log-sync-sealed-batch` 8043, `fnn-log-sync-collected` 8077. About 950 lines, two threads, three locks
(commit-lock, the kernel lock, the gate mutex taken under commit-lock at 3489/3504), one condition
variable, eleven handler clauses, four section bodies (`fnn-owner-commit-start-locked` 3069, the START-NEXT
body 3542-3573, `fnn-owner-commit-complete-locked` 3206, the stall's shed 3529).

THE ACTOR. books/committer-actor.lisp (prefix `fn-cmt-`; teeth `cmtt-`):

    (defstobj fn-cmt                      ; the committer's private state
      (phase    :initially :idle)         ; :idle | :started | :in-flight | :collecting | :stopped
      (members  :initially nil)           ; (CID REPLY WORD RENDER) ... of the batch in flight
      (next     :initially nil)           ; the next batch, prepared behind the barrier
      (deferred :initially nil) (next-deferred :initially nil)
      (ledger   :initially nil)           ; fn-otb's ledger (books/owner-time-bars)
      (limits   :initially nil) (need :initially nil)
      (stall-told :initially nil)
      (syncer   :initially nil)           ; the spawned thread's registry token, or nil
      (passes   :initially nil))          ; the loops' target passes at the wake

    (defun fn-cmt-step (obs fn-cmt) ...)  ; -> (mv ACTION fn-cmt)

    OBS (what the envelope observed since the last action):
      (:woken SYNCED QUEUED STOPPING DRAIN-RELEASE PASSES POLLING)   ; the commit-lock cell, read under it
      (:expired)                                                      ; the timed wait timed out
      (:section-result STEP VALUE)                                    ; a section's STEP answered VALUE
      (:section-refused :stopping) | (:section-faulted CLASS)         ; the envelope's fence words
      (:syncer-returned GEN WORD CONDITION-CLASS)                     ; the syncer's mailbox value, joined
      (:spawned TID) | (:spawn-failed)
      (:clock MS)
    ACTION (what the envelope performs next; one per step):
      (:wait-on-commit-lock MS)                       ; condition-wait with ACL2's fn-otm-wait-ms, or nil = untimed
      (:section :commit fn-cmt-start-section ARGS)    ; the live-stobj STEP (today's commit-start-locked)
      (:section :commit fn-cmt-start-next-section ARGS)
      (:section :commit fn-cmt-complete-section ARGS)
      (:section :reader fn-cmt-shed-section ARGS)     ; the stall's shed (today 3529-3533)
      (:spawn :syncer GEN)                            ; fn-log-sync-sealed-batch in the syncer actor
      (:join :syncer)
      (:deliver CID COMPLETION)                       ; the mailbox push to the connection's loop
      (:disk-event KIND) (:space-event NEED)          ; the gate-mutex observations (fn-otm-disk-step under the gate)
      (:exit WORD)                                    ; :stopped | (:fault CLASS)

The step's body is the decision table of section 1.3's committer row written as ACL2: `fn-otm-committer-wake`
decides `:collect`/`:start-next`/`:wait`; `fn-otb-issue` issues the generation before `:spawn`; a
`(:syncer-returned GEN ...)` is consumed by `fn-otb-complete` (another generation's is `:stale` and
answers nobody: the keystone lifted); `fn-ocs-commit-step` names `:barrier`/`:complete`/`:stop`; the
stall fires once (`stall-told`); `(:section-faulted CLASS)` answers `(:exit (:fault CLASS))`, never
`:stopped` (S016/B1 by construction; the fence is the envelope's, installed before the mutex is released
because the section primitive does it); `(:section-refused :stopping)` after an issue answers every member
`:uncertain` (3611-3620's rule); the "close the batch when every loop passed its target" rule is the
`PASSES`/`POLLING` observation against `fn-cmt-passes` (today 3669-3683).

THE SECTIONS. The four section STEPs are the bodies the host runs under the owner today, which are
already sequences of ACL2 calls (`fnn-owner-commit-start-locked` 3069-3154 calls `fn-owner-take`,
`fn-ocs-start-event`, `fn-owner-credits-*`, the seal); they become logic-mode functions over the live
stobjs with a def-carried row (the owner's, from STAGE-5B) and `:io (fn-prim-log-seal)` declared (the seal
IS a durable commit point; the design wants it under the owner: COMPOSITION R2's declared exception). The
inline commit of a logical connection (S003) is NOT a section body of this actor: a logical connection
submits to the mailbox and awaits like a socket one (HOST-LIFECYCLE's `fnn-owner-feed-logical` already does
this on its lane).

THE SYNCER. A second, trivial actor: `fn-syn-step` with one observation `(:spawned GEN)` and two actions
`(:prim fn-prim-log-fence GEN)` then `(:mailbox-push COMMITTER (GEN WORD CLASS))` and `(:exit)`;
`fnn-log-sync-sealed-batch` (io.lisp 8043-8075) is its one primitive, whose answer vocabulary is `:fenced |
(:failed :indeterminate) | (:failed :os ERRNO) | (:failed :other CLASS)`.

THEOREMS (each with teeth: a reached positive witness with the full antecedent, one removal per
hypothesis, a labelled mutation; the schedules of the natives as label lists):

    fn-cmt-run-keeps-invp                ; over EVERY observation sequence from (fn-cmt-init)
    fn-cmt-phase-trace-is-ocp            ; the phases the actor goes through are fn-ocp-commit-step's
    fn-cmt-a-stale-completion-answers-nobody  ; (:syncer-returned G' ...) with G' /= the issued G: members unchanged (fn-otb lifted)
    fn-cmt-a-fault-never-completes       ; (:section-faulted C) or (:syncer-returned _ (:failed :other C)): the next action is (:exit (:fault C)); no :deliver with a reply after it
    fn-cmt-stall-tells-once              ; at most one :reader shed section per issued generation
    fn-cmt-no-section-while-waiting      ; between (:spawn) and (:join) the only sections are :start-next (fn-ocp-next-open-only-in-flight's image)
    fn-cmt-every-member-is-answered-or-told  ; at :exit every member of the batch in flight has one :deliver or was told at the stall (fn-otb-complete + answer-early)

ACCEPTANCE (the lane reports these numbers; the coordinator's independent reviewer refutes):
1. The old committer loop, pipeline and syncer are DELETED in the same commit (fix forward, no twin kept);
   owner.lisp shrinks by at least 500 lines; `tools/lock_discipline_check`'s baseline for owner.lisp drops
   by the committer's 12 commit-lock sites (3020-3692) and 4 condition-waits (3491, 3494, 3695, 3700).
2. Natives on the developer, production and dtn-developer images: owner (19), log, commit_log,
   crash_model, state_checkpoint, over_pins unchanged; the stage-0 matrix unchanged.
3. tests/test_native_committer.py (new, the shape of tests/test_native_host_lifecycle.py on
   lane/host-lifecycle and the hold selectors FN_NATIVE_PAGE_READ_HOLD/FN_NATIVE_RECLAIM_HOLD): forced
   schedules through `FN_NATIVE_COMMITTER_HOLD=after-issue|before-complete|after-stall`; Astra's
   measurement 2 (a fault injected at `fn-otb-issue` and after START: the process exits 4 with the fence,
   the committer never "stops quietly", no later owner mutation is admitted); a stop during the barrier
   (every member uncertain, exit 0 only when the stop predicate holds: S015); two clients' uncertainty
   fences before later mutation (the existing test_native_owner case); a stale completion (a developer seam
   that delivers the syncer's mailbox value twice: the second is `:stale`, nothing is answered twice).
4. The HM's labels for the committer (`(:section TID :commit ...)`, `(:spawn)`, `(:io-complete)`) are
   generated from books/committer-actor.lisp's ACTION vocabulary into one table that LOCK-CHECK and the HM
   book both read; `reach_check --strict` reaches every `fn-cmt-*` keystone from the envelope's dispatch.
5. Cost: def-entry rows for `fn-cmt-step` (O(1) per wake; O(members) per START/COMPLETE) and the four
   section steps, measured on the cost-gate's served fixture with the counterpart path and raw dispatch
   both run (FN_NATIVE_DISPATCH_COUNTERPART) and identical replies; the POST throughput of the served
   fixture within 5% of today's.
6. Certification: books/committer-actor.lisp under 10 s (D26) on hbox; its closure adds no book above
   owner-commit-pipeline's; `green_check` on the affected roots; evidence filed, not committed.

Estimate: one Fable lane for the book and the envelope's first instance plus one Opus lane for the
natives and the deletion, 2-3 weeks wall, after FAILURE-SCOPE's table and STAGE-5B's tier A have landed
(the carrier move itself can follow: the committer's section steps take `state` through the existing
`fn-owner-*` globals until it does, with the def-carried row stated over them as STAGE-5B's tier A does).

### 3.4 The second and third slices

THE I/O LOOP (rank 2). `fn-mux-step` over a loop stobj with child connection stobjs; observations:
`(:polled REVENTS)`, `(:inbox CONNS)`, `(:arrived PAIRS)`, `(:clock MS)`, `(:read CID OCTETS|:would-block|:eof|:error)`,
`(:sent CID N|:would-block|:error)`, `(:section-result ...)`, `(:tls ...)`; actions: `(:poll FDS EVENTS MS)`
(the one blocking primitive; MS is ACL2's next deadline, so B4 is a theorem: the next deadline is the
minimum over the SAME eligibility predicate the timer fires on), `(:recv CID N)`, `(:send CID OCTETS)`,
`(:section :reader fn-owner-chunk-read ...)`, `(:render CID PLAN)` (off-lock, pure), `(:deliver-pin-release)`,
`(:close CID)`, `(:mailbox-take)`. The idle deadline becomes an observation the exposure model consumes
(`fn-exp-*`: the render loop's "reply written" is the activity event, COMPOSITION's model edit). Acceptance:
the mux natives, the OVER cursor yield trace, r71 F11's witness (a yielded cursor across an expired idle
deadline: no busy poll, measured poll counts), B2's forced adopt-vs-drain in both orders through the
mailbox's close.

THE COLD LINE (rank 3): `fn-cold-step` per worker over the executor stobj; the realizer's read is the
pread primitive under an issued row or a window lease (HOST-MODEL review M1); `fn-pgs-fill-realize` is
rewritten as an instance (F1 closes by construction); the cache bookkeeping is a step over the pool
stobj. Acceptance: Astra's measurements 5 and 6 (pause after fd capture while retirement runs; cancel then
close blocked until physical return), the HM's T1(b) teeth schedules executed as natives.

## 4. What the TCB is afterwards

| component | today | after | covered by |
|---|---|---|---|
| decisions | 1,379 ACL2 entries called from host Lisp, their sequencing in host Lisp and in 1,089 `:program` wrappers | logic-mode, guard-verified actor steps and section steps with carried invariants, raw-dispatched | theorems (per actor: the run theorem over every observation sequence; per section: def-carried's preservation; the HM's T1 over the labels) |
| coordination | about 21,500 lines of COORD+GLUE signature in the natives (locks 394, threads 15, cv 30, handlers 444) | the same decisions as actor steps; one envelope of about 300 lines; the thread registry and failure table as data | the actor theorems; the envelope by the natives and LOCK-CHECK (strict enclave) |
| primitives | spread over 8,269 lines of PRIM-signature forms in 30 files, undeclared, called from anywhere | about 110 constrained functions in books/host-primitives.lisp, realized in host/native/prim-*.lisp: files (about 900 lines, io.lisp's 114 PRIM forms), sockets and poll (about 500), threads/mutex/cv/mailbox (about 300), TLS (about 700), crypto/compression FFI (about 1,200), clock/entropy/process (about 100): 3,000-3,500 lines | A-PRIM-FILE, A-PRIM-SOCKET, A-TLS-NATIVE, A-SBCL-THREADS, A-PRIM-CLOCK, A-PRIM-ENTROPY, A-PRIM-PROCESS, A-CRYPTO-NATIVE, A-SIG-NATIVE, A-DURABLE-*, A-SBCL-RUNTIME, the OS rows (A-DURABILITY, A-WRITE-ISOLATION, A-CRASH-IMAGE, A-HOST-EXCLUSIVE-READ): each an encapsulate or a registered trust row; A-HOST's unused encapsulate retired |
| the dispatcher | `fnn-call` + entry guards + 9 wrapper shapes + 3 synchronized tables | the raw-dispatch installer at build and one `funcall` per step (the entry guard survives only for the verbs' argv entries, where the argument comes from outside) | HST-001, D40 |
| build, startup, packaging | about 3,200 lines | the same | image identity, the natives |
| parked | about 8,700 lines in 92 files loaded by no build | deleted or returned with their producers | host_loaded_check (fail-closed) |
| TOTAL host Lisp in the image | about 58,000 loaded (67k on disk) | 6,000-7,000 | |

What stays assumed and is NOT shrunk by this plan: SBCL (compiler, threads, GC), the OS (fds, sockets,
the byte model's durability rows), libssl/libsodium/BLAKE3/ML-DSA/zlib, the envelope's 300 lines and the
primitive realizations' 3,000 (qualified by the natives, the differential against the extracted product,
and LOCK-CHECK; never a theorem). The coordination defects of this month were not in any of those.

## 5. Risks and how to land without a fork

- CERTIFICATION TIME AND FAN-IN. The image world is 407 include-books (books/image-world.lisp); host-ld is
  179-230 s; a whole-tree freeze is 1:44 at 16 jobs (memory: fn-freeze-recipe); books should certify under
  10 s (D26). Actor books are LEAVES: they include the step books they already exist beside
  (committer-actor includes owner-commit-pipeline, -time-model, -time-bars, -commit-steps: 3,993 lines,
  all certified today) and nothing above; the primitive book includes assumptions only. The HM book
  includes the actor books, not the reverse. A changed primitive signature re-certifies every actor (the
  one real fan-in; signatures are frozen per release). The `:program` -> logic conversions of
  host/*.lisp are the expensive proofs (stage-5: 21.9M steps without hints); they are paid per entry with
  minimal-theory hints and never on the critical path of an actor landing (an actor's section step may
  call a `:program` entry through the counterpart path during migration, at today's cost).
- SERVED-PATH COST. Three traps: (a) an actor step on the counterpart path pays its guard per step --
  every step lands with a def-entry row, a carried invariant and raw dispatch, or its cost row says
  `:guard :paid` and the gate measures it; (b) the section primitive's `funcall` of a logic function over
  the live stobjs replaces today's `fnn-call` path for the same body -- no new cost, one fewer catch; (c)
  the mailbox copies ACL2 values between threads: values are immutable conses, no copy, and the plan
  windows are already values. The one place cost can regress is the mux step's per-pass work if it is
  written as a walk over all connections' child stobjs when poll reported one: the step's VISIT bound is
  O(ready) + O(timers due), stated and measured.
- ACL2 LIMITATIONS THAT KEEP CODE IN THE HOST (section 2.3): threads, mutexes, condition variables,
  sockets, poll, FFI, signal handlers, `save-exec`; one live state and one live object per stobj (so the
  envelope, not ACL2, allocates a private stobj per actor and hands the live ones to sections); hons and
  memoize (forbidden in actors by a lint); `with-local-stobj`'s lexical scope (so v1's loop is 20 raw
  lines per actor kind); the extracted product's single global table (so no per-thread state globals
  anywhere). None of these forces a DECISION to stay in the host.
- THE `:program` LAYER'S RATE. 1,089 functions at about ten per lane-week is a hundred lane-weeks if done
  one by one; it is not done one by one: def-entry/def-owner-writer generate the statements (STAGE-5B's
  tier A became "about 40 declarations" from 229 hand lines), and an actor slice converts the wrappers IT
  calls, so the conversion rides the actor order. The 69 unloaded files convert never (they are deleted or
  return with producers).
- LANDING WITHOUT A LONG-LIVED FORK. One actor per lane; a lane deletes the host loop it replaces in the
  same commit (fix forward: no twin kept, no selector between old and new beyond ONE batch's differential
  run on hbox, which the lane reports and then removes); the envelope lands first and alone (rank 0, small,
  with the committer as its first instance in the next lane); the HM label table, LOCK-CHECK's enclave and
  interfaces.json shrink per landing, so the migrated boundary is always the checked one; every landing
  keeps init/POST/read/restart green on the native matrix (MODE 2); the cut is held until the queue is
  empty, as today. A regression found by the cut blocks the affected claim, not unrelated actors.
- BEHAVIOURAL DRIFT. Each actor's observation/action vocabulary is a strict projection of today's host
  rules (section 1.3 lists them); where a host rule has no ACL2 twin the lane states it as a theorem
  BEFORE deleting the host line, so the diff is reviewable rule by rule; the natives are the control and
  the differential (counterpart vs raw) is run once per landing.
- WHAT THIS PLAN DOES NOT DO: prove SBCL, the OS, or a library; remove the natives; make the HM's T1 true
  by itself (the envelope is still the bridge, 300 lines instead of 21,500); or finish before the cut
  after wave 5 -- rank 0 and rank 1 are the pre-cut deliverables; the rest is the program that follows.

## Appendix A. Reproducing the measurements

Signature census (per file: lines, defuns, lock sites, threads, joins, cv, handlers, unwind, syscall
refs, ACL2 calls, sleep, clock, format, global setf) and the per-form classifier (PRIM > COORD > GLUE >
DIAG > DEFS > PURE by signature precedence) were two Python scripts of about 60 lines each over
host/native/*.lisp, skipping comment lines; the classifier's form boundary is a line starting with "(".
Both ran at 4aa332295 on 2026-10-03. The counts in sections 0 and 1.1 are theirs; owner.lisp's and
io.lisp's category lines are from reading every form. To re-run: `grep -c` per pattern reproduces the
census columns exactly (the patterns are the names listed in section 1.5); the classifier is worth
landing as tools/host_signature_census.py beside tools/owner_globals_check.py so that the inventory is
regenerated per push rather than read once (COMPOSITION's point about inventories going stale).

## Appendix B. Findings along the way (for the coordinator's routing; each read in source)

- B1 `fnn-owner-admission-pending` (owner.lisp:2048) is signalled by `fnn-owner-existing-verdict` (2054)
  and caught by nothing in host/ or books/; it is a `serious-condition`, so it reaches
  `fnn-owner-shared-action-locked`'s catch-all and exits 4.
- B2 host/owner-host.lisp:3765-3795's four `*-buffer` twins (`fn-owner-login-gate-buffer`,
  `fn-owner-control-filing-buffer`, `fn-owner-peer-carrier-form-buffer`, `fn-owner-peer-carrier-plan-buffer`)
  have no caller; the comment says the served POST calls them (sweep S002).
- B3 io.lisp:1555-1578: `fnn-payload-startup-reset` calls the lifecycle step as "permission" and never
  assigns `*fnn-payload-lifecycle-phase*` from its answer; `*fnn-payload-lifecycle-owner*` is read only in
  the parked recovery-payload-view.lisp.
- B4 io.lisp `fnn-log-parent` (6398) is a second copy of `fnn-parent` (762) with different edge cases.
- B5 Unreferenced in host/ and books/: `fnn-owner-run-admission` (owner.lisp:647),
  `fnn-connection-custody-retain` (218), `fnn-snapshot-source-read-page` (4890), `-page-release` (4920),
  `fnn-owner-buffer-action` (594), `fnn-cold-call`/`fnn-cold-guard-cache-prepare` (io.lisp 1316-1333).
- B6 The comments at owner.lisp:2141 and :2286 say `*fnn-owner-transit-detail*` is "never an input to any
  decision"; it is passed to `fn-owner-served-post-word` (2520) and `fn-owner-served-carried-word` (2871),
  which choose the outcome word.
- B7 tools/extract/world.py names host/native/lz4.lisp, which does not exist in the tree.
- B8 `tools/host_loaded_check.py` reports 92 unloaded files today; if it is in `make check` it is red; if
  it is not, it should be, fail-closed, before the parked files are counted anywhere.

## REVIEW 1 OUTCOME (coordinator, 2026-10-03; review: build/coordinator/lanedumps/tcb-shrink-review-1.md)
Sound direction; the committer is the first slice. Before the committer slice lands:
- M1: no :protect abstract-stobj exports in actor stobjs (the process-wide unsynchronized *inside-absstobj-update*
  cell; a THROW leaves it elevated), or a per-thread cell. M1b: every actor thread establishes fnn-call's catch tag.
  M1c: a condition mid-step leaves an actor stobj torn: the envelope faults that actor, never re-steps it.
- definterface's raw-with conjunct gap closed first (DEF-ENTRY, in progress); the envelope's ACTION-to-primitive
  interpreter generated table-driven from the vocabulary the HM reads.
- Primitive gaps: foreign close (A-PRIM-FILE); a syncer (:failed :os ERRNO) is UNCERTAIN.
- Acceptance adds: a forced web-POST-during-batch schedule (S003 / r71 F5) and a feed-stall native (S014).
- r72 F4 settled: the seal LEAVES the owner (OWNER-OFFLOCK's READY 1); the committer slice builds on that, no
  declared exception.
- TCB size is cited from tools/host_loaded_check.py + wc, never from the signature classifier.
