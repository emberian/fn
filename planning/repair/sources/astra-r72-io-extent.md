| Rank / id | Class | File:line | Finding |
| --- | --- | --- | --- |
| 1 / F1 | bug | host/native/io.lisp:7245 | Writable recovery can overwrite a committed log prefix on non-Linux hosts before inspecting it. |
| 2 / F2 | bug | host/native/owner.lisp:5130 | Automatic checkpointing consumes core/integrity faults as ordinary publication failures and leaves the service running. |
| 3 / F3 | bug | host/native/io.lisp:2549 | A repeated image header makes checkpoint discovery seek to the same offset forever. |
| 4 / F4 | bug | host/native/io.lisp:8027 | Served batch sealing performs blocking append I/O and extension barriers while holding the owner mutex. |
| 5 / F5 | claim-gap | host/native/io.lisp:4258 | The non-Linux export barriers never make the new archive directory's parent entry durable. |
| 6 / F6 | bug | host/native/io.lisp:3948 | A failed directory fence after node-secret replacement reports fault, losing the uncertain-publication outcome. |
| 7 / F7 | bug | host/native/io.lisp:1115 | SIGHUP descriptor swaps bypass log admission and can accumulate unbounded open descriptors. |
| 8 / F8 | bug | host/native/io.lisp:6717 | Recovery allocates the entire unused log tail in one vector. |
| 9 / F9 | bug | host/native/io.lisp:3227 | A diagnostic LENGTH makes checkpoint walking quadratic in the captured sealing rows. |
| 10 / F10 | claim-gap | host/native/io.lisp:4685 | Import enumerates/sorts whole directories and retains every configuration body before bounded record processing. |
| 11 / F11 | nit | host/native/io.lisp:6420 | Log descriptor constructors have fallible work outside failure cleanup, leaking the acquired descriptor. |

Source coordinate: `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9`. Read-only source review, 2026-10-02. The stage-0 comparison has one change in these files, `39f3ed4eb` (cold-read ownership, extent.lisp); the findings concern the whole current implementation. No build, ACL2, native execution, deployment or certification was performed. Small standard-library Python checks below are control-flow/arithmetic illustrations, not native witnesses. The six exclusions in REVIEW.md are not findings here.

## F1 [bug] host/native/io.lisp:7245 fnn-log-complete-rotation

A misaligned active segment is treated as an empty interrupted rotation, so writable recovery on the non-Linux implementation overwrites existing committed bytes before the damage scanner can preserve or classify them.

Quoted source:

```lisp
;; io.lisp:7245-7251
(unless (fnn-core 'fn-lg-extent-okp size unit)
  ...
  (progn (fnn-log-preallocate fd (fnn-nat (fnn-core 'fn-store-log-initial-extent)))
         (fnn-fsync-file fd))
;; io.lisp:6377,6390-6395
(defun fnn-log-preallocate (fd extent &optional (from 0))
  ...
  #-linux
  (let ((zeros (fnn-make-octets (min (- extent from) 65536))) (at from))
    (fnn-posix () (sb-posix:lseek fd from sb-posix:seek-set))
    ... (fnn-write-range fd zeros 0 n)
```

`fn-lg-extent-okp` only tests positive unit-aligned length (`books/store-log-programs.lisp:212`). It says nothing about whether a segment was newly created, whether it contains acknowledged records, or whether a growth was interrupted. `fnn-log-scan-segments:7510` applies this operation to the active segment, including segment 1, **before** `fnn-log-recover` scans it. The wrapper `host/store-host.lisp:416` supplies `fn-olr-initial-extent`, 1 MiB (`books/store-log-route.lisp:71`).

Concrete corrupted-state witness: a previously committed active segment 1 of at least 1 MiB, with no installed checkpoint and one extra trailing byte. This branch writes zeros over its first 1 MiB and fences them. Its length can remain misaligned and the subsequent open can still refuse; that does not undo the destruction. No repair authorization or quarantine precedes this write. This is a writable startup/recover path, not a remote-input claim.

A second route worth exercising is a partial non-Linux extension write followed by failure/death: `fnn-log-ensure-extent:7864` writes the extension in chunks and `fnn-write-progress` accepts non-unit-sized positive progress. **UNVERIFIED:** a real supported filesystem's resulting crash length. The source defect above does not depend on establishing that crash route. `fn-lg-extension-written-crash-reads-the-committed-records` (`books/store-log-extend.lisp:530`) describes the model state after the extension operation and explicitly concludes whole-unit length; it does not justify classifying every other observed length as an empty rotation.

Fix: preserve the bytes and refuse/quarantine an unrecognized partial segment; admit completion only with evidence that it is the empty rotation being completed. Model and implement interrupted extension separately, never restarting its zero fill at offset zero.

## F2 [bug] host/native/owner.lisp:5130 fnn-owner-publish-captured

The automatic checkpoint worker catches integrity and core-execution faults, logs them, and resumes normal service instead of installing the required store fault fence.

Quoted source:

```lisp
;; owner.lisp:5066-5067,5130-5131,5162
(fnn-core 'fn-owner-sco-next base base-payloads configs records
          (fnn-checkpoint-walk records) segment (fnn-live-arena))
...
(serious-condition (e)
  (fnn-err "CHECKPOINT auto failed: ~a" e))
...
(fnn-owner-maybe-publish service)
;; io.lisp:1385-1392
(serious-condition (c) (setq outcome (princ-to-string c)) nil)
...
(t (fnn-fault "ACL2 error in ~(~a~): ~a" name outcome))
```

The served path is the publication launched by `fnn-owner-maybe-publish-quantum`, with a correctly acquired arena pin. `fnn-checkpoint-walk` calls `fn-scka-srcs-n`; that calls `fn-row-wire-of` (`books/store-intern.lisp:118`), which realizes held payloads. A missing/short/damaged extent signals the fault documented at `extent.lisp:23-28`. `fnn-call` converts a thrown condition into a store fault; the publisher's broad handler then consumes it. Even a direct malformed core result at `owner.lisp:5077/5129` takes that same handler. The analogous export handler at `owner.lisp:5405-5407` labels all such conditions `:archive-write`.

Interleaving: A, the publication worker, encounters an uncached damaged durable payload during the walk; A's core call raises a fault; A logs it and exits the failed publication normally, releasing its pin; B, a served submitter, enters the still-running owner and can continue committing. There is no call to `fnn-owner-fault-service` on this path. That function (`owner.lisp:1758`) exists specifically to contain invalid core/store images. This finding is **before checkpoint installation**, independent of the excluded release-extents handler and reclaim-install issue. It does not claim corrupted bytes are successfully exported.

Fix: keep expected staging-space/write refusals recoverable, but route core/extent faults through the service fault boundary before another semantic operation is admitted; apply the same typed distinction to other maintenance workers.

## F3 [bug] host/native/io.lisp:2549 fnn-state-checkpoint-plan

The image-header branch never records that it consumed the one allowed image header, so another recognized header at its seek target causes an infinite read/seek loop.

Quoted source:

```lisp
;; io.lisp:2528,2549-2561
(frames nil) (total 0) (at 0)
...
(let ((np (and (= at 0) (null frames)
               (fnn-core 'fn-his-image-header-np ...))))
  (if (integerp np)
      (progn
        (sb-posix:lseek fd (+ header-octets (fnn-core 'fn-his-skip-octets np))
                        sb-posix:seek-set)
        (setq *fnn-checkpoint-image* (list path np (fnn-core 'fn-his-base-octets))))
      ...))
```

`at`, `frames` and `total` only advance in the other branch. `books/history-image-snapshot.lisp:256-270` accepts a 37-byte FNSI/version-1 header with NP=0 and base=16384; its skip plus header length is 16384. Put that header at offset 0 and offset 16384, with padding between: a 16,421-byte file. Every subsequent iteration reads the header at 16384 and seeks back to 16384. Segment admission and its profile bound are never reached. The small Python `BytesIO` mirror produced header-start positions `[0, 16384, 16384, 16384, 16384, 16384]`; this is a source control-flow witness, not a run of the saved image.

Reachability: `fnn-state-checkpoint-load -> fnn-state-checkpoint-plan` during ordinary store open, including owner startup. The store lock is already acquired by `fnn-open-live-store`, so the corrupt checkpoint prevents startup/recovery and keeps competing opens excluded. There is no concurrency precondition.

Fix: parse the optional image header exactly once and pass an explicit advanced cursor to the framed-segment reader. Have the core validate the image span against the observed file extent; a second FNSI is a refusal, not another absolute seek.

## F4 [bug] host/native/io.lisp:8027 fnn-log-seal-open-batch

The served START/COMPLETE quantum can block the entire owner on append writes and extension fsync, because only the later batch fence is moved to the syncer.

Quoted source:

```lisp
;; owner.lisp:3594,3634
(fnn-owner-gated (service :commit)
  ... (progn (fnn-log-seal-open-batch store) ...))
;; io.lisp:8027-8028
(fnn-log-ensure-extent log)
(fnn-log-append log)
;; io.lisp:7864-7866
(fnn-log-preallocate (fnn-log-fd log) next extent)
(fnn-log-at :log-extended)
(fnn-log-fdatasync (fnn-log-fd log))
;; io.lisp:6734-6740
(fnn-log-with-kernel (log)
  ... (fnn-log-pwrite (fnn-log-fd log) frontier octets))
```

`fnn-owner-gated:1593` holds the service mutex throughout its body. Both the initial START (`owner.lisp:3142`) and sealing the next prepared batch (`:3634`) reach these calls. The append also holds the log kernel lock while constructing the batch bytes, writing, and registering/reseating its in-flight places. The regular-file write path has no socket-style deadline. Extension can write a range proportional to the existing segment size and then wait for durability.

Interleaving: A, the committer, takes the owner mutex and seals a batch; its ordinary write stalls, or an extent-boundary append stalls in `fdatasync`; B, a reader or control request, reaches owner admission and waits for A's mutex; the separate batch syncer has not yet been launched for this seal, so its timeout/late-completion machinery cannot release A. This is reachable in the production served pipeline. The fairness gate cannot preempt the body it admitted. No claim of an observed latency is needed to establish this lock dependency.

The rotation path has the same architectural residue: `fnn-log-rotate:7385` writes the lineage head under the owner, despite the docstring at `owner.lisp:5169` saying the rotation there is a rename. Moving spare allocation off the mutex did not move every blocking operation.

Fix: give the ordered log writer an immutable sealed batch plus an owned descriptor generation, execute append/extension/fence off-owner, then install the observed result in a short owner quantum. Extend the existing generation/late-completion protocol to the write phase, preserving uncertain outcomes.

## F5 [claim-gap] host/native/io.lisp:4258 fnn-export-sync-data

On the non-Linux path, a successful export does not fence the parent entry naming its newly created archive directory, so `export-durable` does not establish durability of the archive's pathname.

Quoted source:

```lisp
;; io.lisp:4247-4251,4258-4259
"... Elsewhere
every file and directory under DIR is fenced (fnn-export-sync-tree): the
same postcondition, one barrier per file."
...
#-linux
(fnn-export-sync-tree dir)
;; io.lisp:4320,4360-4363
(fnn-mkdir dir #o700)
...
(fnn-fsync-dir dir)
(fnn-export-at fault "export-durable")
(fnn-out "exported records=~d configuration=~d" records (length configs))
+fnn-exit-ok+
```

`fnn-mkdir:725` is just mkdir. The tree sync fences descendants and DIR, never `(fnn-parent dir)`. In the project's byte-store durability semantics, that leaves the mkdir entry in the parent unfenced; a crash can lose the whole archive name after success. Linux's filesystem-wide sync has a broader scope, so this finding is limited to the fallback. The live export repeats the same sequence (`owner.lisp:5345,5370,5380-5384`), so it also applies to the served operator export.

`fn-sxd-program` begins **inside an existing model directory `:arch`**, with config/ and records/ creation (`books/store-export-durability.lisp:112`). Its incomplete-or-complete theorem remains useful for the manifest and contents; it does not establish publication of the host-created outer directory. The host's “same postcondition” and complete durability mapping omit this boundary. This is not a claim that the ACL2 theorem itself is false or a claim that every non-Linux filesystem loses the directory.

Fix: include creation/publication of the archive root and its parent fence in the host program and model; report success only after that fence. Share that sequence between offline and live export.

## F6 [bug] host/native/io.lisp:3948 fnn-node-secret-rotate

A directory-fence error after the node secret has been replaced escapes as a generic OS fault rather than the uncertain publication it represents.

Quoted source:

```lisp
;; io.lisp:3944-3949
(handler-case (fnn-replace stage path)
  (fnn-os-error (e)
    (ignore-errors (fnn-unlink stage))
    (fnn-indeterminate "node secret rotation outcome is indeterminate: ~a" e)))
(fnn-fsync-dir dir)
(fnn-core 'fn-ns-entry-epoch next)
```

After a successful rename, inject EIO into the following directory fence. The visible current key may already be epoch E+1 while crash durability is unknown. The handler covers only rename. `fnn-command-node-secret` and `fnn-main` let the raw `fnn-os-error` reach `fnn-exit-code-for:145`, whose default type is `:fault`; `books/outcome-class.lisp:79` maps that to 4, whereas `:indeterminate` maps to 3. This is the offline key-administration path, not a claim that the live owner changes keys concurrently. The create path has the same post-publication fence exposure at `:3911`.

Fix: classify the entire publication interval from rename/link through the directory barrier as uncertain on failure; retain the named old/new epoch evidence for recovery and use the common outcome model.

## F7 [bug] host/native/io.lisp:1115 fnn-log-swap-fd

Descriptor-swap messages bypass the bounded log sink, allowing repeated handled SIGHUP requests to retain arbitrarily many open descriptors behind a blocked writer.

Quoted source:

```lisp
;; io.lisp:950-951 (ordinary lines)
(fnn-core 'fn-log-sink-offer *fnn-log-sink* (length octets)
          (fnn-core 'fn-log-sink-pending-bound))
;; io.lisp:1113-1116 (swaps)
(sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
  (when *fnn-log-writer*
    (fnn-log-queue-push (cons :swap fd))
    t))
;; owner.lisp:5918-5921
(let ((fd (fnn-owner-open-log *fnn-owner-log-path*)))
  ... (fnn-log-swap-fd fd))
```

Interleaving: A, the logger, blocks writing its current item outside the queue mutex; B, the accept/control loop, observes a new SIGHUP count, opens a fresh log fd and enqueues `:swap`; B marks that count handled; another signal arrives after that poll and B repeats. Signals coalesced within one poll are harmless, but there is no limit across successive polls. Only A consumes the swaps and closes the old descriptors (`io.lisp:1058-1062`). The queue's sink counters never charge these cells or descriptors. Eventually other accepts/opens can fail from descriptor exhaustion although ordinary log lines are being dropped correctly.

Reachable with a configured service log and repeated operator signals while its writer stalls; this is not a remote unauthenticated signal-injection claim. `specs/host.md:1318` (HST-012/PRF-187) and `io.lisp:902-915` infer bounded backlog/service independence from `fn-log-sink-offer-preserves-okp`; that theorem counts lines, not these host control messages.

Fix: coalesce reopen intent into a bounded control slot before opening a new fd, or admit charged swap ownership through the same resource model. Preserve FIFO semantics for lines and close/refund every superseded private descriptor definitively.

## F8 [bug] host/native/io.lisp:6717 fnn-log-recover

Writable recovery allocates and writes the entire unused active-segment tail as one vector, making startup memory proportional to free log space rather than a bounded I/O quantum.

Quoted source:

```lisp
;; io.lisp:6716-6720
(destructuring-bind (offset count) (fnn-call 'fn-lg-recover-tail ks extent)
  (fnn-log-pwrite fd offset (fnn-make-octets count))
  (fnn-log-at :log-truncated)
  (fnn-log-fdatasync fd)
  (fnn-log-at :log-recovered))
```

The host-called `fn-lg-recover-tail` returns `EXTENT - FRONTIER` (`books/store-log-programs.lisp:234`); its concrete abstraction theorem preserves that value, not a memory bound. Extents grow to at least twice their previous size (`books/store-log-extend.lisp:59`). Immediately after a large growth, a lightly advanced frontier leaves roughly the old extent's size as zero tail. Automatic checkpointing may defer for budget/free space and cannot supply an unconditional small-segment bound. A physically supported, already allocated log can therefore require a multi-gigabyte transient allocation just to reopen, even though the scanner before it streams records. `fnn-log-scan-segments:7513` reaches this on owner startup.

This is a scaling failure for valid state, not a demand to cap the store or an assertion that a measured deployment exhausted memory. A count-sized vector can fail before any progress on the tail; chunking inside `fnn-write-range` would be too late because the vector already exists.

Fix: zero the ACL2-authorized interval with a reusable bounded buffer and carried cursor, then fence once; connect the chunked effects and intermediate crash states to P-LOG-RECOVER.

## F9 [bug] host/native/io.lisp:3227 fnn-checkpoint-walk

Every checkpoint walk quantum traverses all payload lengths accumulated so far merely to construct a stop diagnostic, introducing quadratic work before the stop predicate is even tested.

Quoted source:

```lisp
;; io.lisp:3224-3229
(let ((walk (list records nil nil)) (arena (fnn-live-arena)))
  (loop
    (when (atom (first walk)) (return walk))
    (fnn-checkpoint-yield "walk" (length (second walk)))
    (setq walk (fnn-core 'fn-scka-srcs-n (first walk) +fnn-checkpoint-batch-rows+
                         (second walk) (third walk) arena))))
```

`fn-scka-srcs-n` conses one length onto LACC for each sealing row (`books/store-checkpoint-arena-writer.lisp:398-400`); it does not reset LACC between calls. Common Lisp evaluates LENGTH before `fnn-checkpoint-yield`, including when there is no stop request. With N sealing rows and B=1024, this adds `B * k * (k-1) / 2` cell visits for `k=ceil(N/B)`: 4,867,072 for 100,000 rows and 488,218,624 for 1,000,000. These are arithmetic counts of this expression alone, not benchmark results or total checkpoint costs.

Reachable in the served automatic publisher (`owner.lisp:5067`) and maintenance callers. It runs off-owner but burns CPU and delays observing stop increasingly as history grows. The cited `fn-scka-srcs-n-compose` proves equality of the chunked logical walk; it says nothing about this surrounding repeated host walk.

Fix: carry a scalar progress counter (batch number suffices for this diagnostic), and evaluate the stop test before work proportional to any captured collection.

## F10 [claim-gap] host/native/io.lisp:4685 fnn-import-pass

The claimed chunk-bounded import has an unbounded prelude that materializes and sorts every archive filename and retains every configuration body before validating the profile or manifest contents.

Quoted source:

```lisp
;; io.lisp:4366-4367
(defun fnn-archive-read-dir (dir sub)
  (sort (copy-list (fnn-list-directory (fnn-join dir sub))) #'string<))
;; io.lisp:4685-4700
(config-names (fnn-archive-read-dir dir "config"))
(record-names (fnn-archive-read-dir dir "records"))
...
(decoded (fnn-core 'fn-store-metadata-config-decode profile))
...
(configs (mapcar (lambda (name) ... (fnn-archive-entry ...)) config-names))
;; io.lisp:4540-4541
"... the work and allocation per step are one chunk's."
```

`fnn-list-directory:659` retains all names. For R record files and C configuration files this prelude retains O(R+C) names, makes another list for each sort, and holds the sum of the configuration bodies (as octet lists), independently of the record chunk size. A regular but empty MANIFEST passes the initial presence check; an invalid small profile does not prevent either directory enumeration or the configuration-body reads. Thus hostile archive metadata can consume memory before the intended semantic refusal. Even valid million-record archives pay a whole-namespace prelude on each pass.

This is the offline import path. `fn-sxi-stream-plan-is-the-import-plan` (PRF-369, `books/store-import-stream.lisp`) proves semantic equivalence for supplied chunks; the host enumeration/sort is outside its subject. The record-body streaming improvement is real, but the global per-step allocation claim is not established.

Fix: validate the profile first and give namespace/head processing an ACL2-owned resumable cursor and resource accounting. Stream canonical names from a validated manifest or use bounded external ordering; do not fix the problem with an arbitrary archive-size ceiling.

## F11 [nit] host/native/io.lisp:6420 fnn-log-open-segment

Several log constructors leave an acquired descriptor unowned when a subsequent fallible operation exits before the enclosing caller can install its cleanup.

Quoted source:

```lisp
;; io.lisp:6420-6426
(let ((fd (fnn-open path ...)))
  (fnn-log-preallocate fd extent)
  (fnn-fsync-file fd)
  (fnn-fsync-dir (fnn-log-parent path))
  fd)
```

Failure of any of those three calls leaks FD. In the existing-file arm (`:6412-6417`), an error from `fnn-fstat` also bypasses close (the explicit close handles only a returned size mismatch). In `fnn-log-recover:6703-6721`, scanning has a closing handler but the subsequent tail allocation/write/fence does not; until the constructor returns, `fnn-store-close` cannot find this fd in `fnn-store-log`. At `fnn-log-scan-segments:7502-7504`, a second acquisition, `fnn-extent-register`, can fail after the scan fd was opened but before its unwind-protect starts.

Ordinary failing startup usually exits and the OS releases these fds, which limits the immediate impact; these are still real cleanup holes for in-process callers/retries, not a demonstrated long-running leak campaign. The first two constructors also serve the diagnostic log path.

Fix: wrap each constructor from its first successful acquisition in an unwind-protect with an explicit ownership-transfer flag; include all let-initializer work and post-scan recovery effects before transfer.

## Checked, no finding

“No finding” here means no additional established defect in the named checks, not a clean bill for the subsystem. F1–F11 describe the exceptions. Both complete target files were read, with searches and reads into their native callers, host wrappers, interfaces and the relevant books. This was not an independent recertification of every transitive ACL2 dependency.

### 1. Locking, ordering, ownership and waits

The new cold-read path is a substantive improvement. I followed `fnn-owner-cold-issue-locked`, transfer/result/reap/await/shutdown, `fnn-extent-issue-direct`, executor enqueue/job/actual-return, cancellation, settlement, and extent close through `books/page-read-direct.lisp`, `page-read-executor.lisp`, `page-read-ownership.lisp` and the page-read host wrappers. The issue happens before exposing work; cancellation does not remove the issued row; only actual return followed by exact-token settlement idles the worker and releases the file pin. Error after cancellation is still a fault. The global worker-count bound is a host construction fact, explicitly distinguished from a theorem over the worker set in the proof registry. I found no new fd-use-after-close interleaving on this path. I did not treat the staged window path as installed served funding.

Lock inventory and work under exclusion:

| Lock / boundary | Observed work and ordering |
| --- | --- |
| Owner/gate (`owner.lisp:1573`) | Admission releases the gate mutex before acquiring owner exclusion; body and gate cleanup hold owner. Calls into log kernel, extent table, pin/lifecycle and brief roster/commit operations follow from here. The blocking write/extension problem is F4. |
| Log kernel (`io.lisp:6345`) | Recursive lock for batch/kernel state, including append byte construction and write. Batch fence captures state, performs the barrier outside the kernel lock, then publishes the result. `:syncing` wait and completion broadcast use the same mutex (`:8010`, `:8069`). |
| Spare (`io.lisp:7299`) | Serializes staging creation, preallocation and file fence off-owner; the rotation consumes the prepared spare under owner admission. Do not add an owner-to-spare wait as a shortcut to F4. |
| Service-log queue (`io.lisp:916`) | Enqueue/dequeue, core sink transitions and writer identity under recursive lock; blocking output outside it. Writer's empty-queue predicate and wait share that mutex. Swaps are F7. The fallback log-output mutex intentionally covers synchronous output when no writer runs. |
| Extent (`extent.lisp:70` onward) | Tables, cache/lease transfer, issued rows and worker phase. Owner-to-extent ordering in admission/settlement; worker does not acquire owner while holding extent. Whole-entry verification at `:956-959` and full-payload list copying at `:1056-1065` still hold this global mutex. These are cost observations, not a new proof that the documented stalled-*disk* isolation is false. |
| Arena pins (`io.lisp:6787`) | Core generation/pin/retirement transition under its own mutex. Release returns the due items; it is not permission to release an older pinned generation. Source examined in `books/arena-reader-pins.lisp`. |
| Payload lifecycle (`io.lisp:1567`, owner lifecycle functions) | Owner precedes lifecycle exclusion for capture/start/drain. Join is outside owner/lifecycle exclusion; instance/state are retained through worker cleanup. |
| Guard-cache / random-state facilities | Entry guard cache is a synchronized table, dispatch fixed at image construction, with prepared cold guard-cache handling. Random-state creation is serialized; no new cryptographic-entropy finding was established from the separate temporary-name PRNG. |
| OS store/publication locks | Nonblocking flock; returned lock fds transfer to store/publication ownership. Normal command cleanup releases them. They do not make a check-then-act safe against an external writer that ignores the locking protocol. |

Condition variables checked: log queue predicate/notify; kernel sync-state predicate/broadcast; executor queued/returned/stopping predicates and broadcasts. Cold wait is followed by owner re-observation, not assumed to imply completion. Stop joins workers outside extent exclusion before descriptor retirement; a permanently stuck syscall can still prevent a definite join. That is an availability limitation, not evidence that cancellation may safely close the fd early. The logger's stop has its explicitly different bounded-join contract.

The commit delivery race is handled: `fnn-owner-deliver` and `fnn-owner-await-register` share the commit mutex and use the DONE table for early completion; callback invocation occurs after that mutex is released. The mux callback records arrival under the mux mutex, and the mux consumes that inbox outside it. I followed `fnn-mux-await[-done]`, queue/flush, plan yield, timers and finish to distinguish actual socket writes from semantic owner work. The ordinary `fnn-recv`/`fnn-send-all` helpers carry one absolute deadline across partial progress/EINTR/EAGAIN, with nonblocking descriptors; DNS is expressly outside the connect deadline. No new lost-wakeup or ACK-before-fence defect was established in these paths.

Acquisition audit — resources whose successful release is **not local lexical cleanup**, and exceptional gaps worth retaining in the inventory:

| Acquisition | Ownership/release route |
| --- | --- |
| `fnn-open-lock:2159`, `fnn-acquire:2421`, rebind at `:3136` | Returned/stored lock fd; `fnn-store-close` or enclosing initializer/rebind cleanup releases it. Constructors have explicit error handlers, not a local successful close. |
| `fnn-open-live-store:3702`, `fnn-reader-prepare:5825` | Return an acquired store; ordinary command/reader callers close it in cleanup. Developer `fnn-command-probe:5312` instead manually closes its first store after the workload, with no cleanup around that first run. |
| `fnn-publication-lock:4467` | Returned non-Linux parent-side lock; import/init publication callers use `fnn-publication-unlock` in their cleanup. Linux takes the no-replace primitive route. |
| `fnn-log-open-segment:6402`, `fnn-log-recover:6697`, `fnn-log-open-read-only:7077` | Fd transfers into the returned log, eventually closed by store cleanup/rotation. Pre-transfer holes are F11; open-read-only has scan-error cleanup but no cleanup around allocating the returned struct. |
| `fnn-log-prepare-spare:7289` / `fnn-log-rotate:7325` | Prepared fd transfers to the spare slot, then active log; failed preparation has cleanup, discarded spare closes/unlinks. Rotation removes the spare from its slot before head write and old-fd close; failures there have no lexical new-fd close. The service must stay fenced rather than reuse that partially changed state. |
| `fnn-extent-register:86`, `fnn-extent-register-at:141` | Success transfers fd/path/incarnation to tables; actual retirement/close releases it. Failed base registration has no wrapper cleanup after underlying registration. `fnn-state-checkpoint-adopt-image:2630`, replay registrations `io.lisp:7503/7511`, log-member registration `:6761`, and owner checkpoint registration `owner.lisp:4946` rely on that table ownership, not a lexical close. |
| `fnn-extent-issue-read:890`, `fnn-extent-issue-direct:988`, executor acquire/enqueue, staged `fnn-extent-issue-window:578` | Intentionally asynchronous ownership. Returned token is retained until owner observes physical return and settles. Caller unwind cancels publication; it must not refund physical ownership. Worker startup retains partial construction for stop/join on failure. |
| `fnn-extent-entry-fresh:851` | Success hands the discovery lease to its caller, which owes last-borrow release; before handoff there is cleanup. Its known blocking-I/O issue is excluded by REVIEW.md. |
| `fnn-extent-entry-direct:791` | Funded sync path cleans up before transfer; once cache transfer begins, exceptional uncertainty intentionally retains the lease. The common octets-rd buffer alias is cleared in `fnn-with-octets-rd` cleanup. |
| `fnn-arena-pin:6793` | Returns generation ownership. Publication/export acquire under owner before thread creation (`owner.lisp:5255/5305`), have creation-failure unpin, and worker unwind unpin (`:5152/:5415`). Reclaim dry-run/install pins (`:5469/:5661`) are inside enclosing unwind-protect. No missing unpin established at those four sites. |
| `fnn-owner-open-log:5895` / swap | Fd transfers to queue/writer; no caller cleanup after acquisition. F7 accounts for the unbounded successful transfers; an exception before successful handoff also needs constructor cleanup. |
| `fnn-listen:5560`, `fnn-connect:5620`, socket accept helpers | Success transfers the socket to its caller; listen/connect have failure cleanup and normal reader/mux shutdown owns later close. Accept helpers explicitly delegate ownership to the handler. |
| `fnn-mountinfo-best:2968`, `fnn-csprng-octets:887`, `fnn-state-checkpoint-plan:2527`, scan at `:7502` | There is fallible initialization/validation between open and cleanup establishment. Mountinfo computes the core limit and allocates buffers first; CSPRNG allocates its result first; checkpoint explicitly closes on an invalid frame-size result but its general guard precedes unwind-protect; scan's second acquisition is F11. These small constructor windows should be eliminated by the same acquisition discipline, not treated as proof of a served leak storm. |

### 2. Effect order and durability

Followed log append/fence/finish and owner START/SYNC/COMPLETE through `store-log-programs`, `store-log-kernel-concrete`, `store-log-extend`, `store-log-stream`, `store-log-segments`, lineage and damage classification; followed checkpoint staging/write/install, covered-segment drop, export and import publication. Ordinary accepted batch completion is delivered after the batch fence; an early known refusal is not a durable acceptance. Rotation makes the head/file and directory durable before a checkpoint names the new suffix or its first batch is acknowledged. F1, F5 and F6 identify gaps outside those successful sequences. I did not transfer the excluded reclaim-install conclusion into a new finding.

### 3. Claims, entry guards and proof subjects

Read the entry-guard extraction/recognizers, `fnn-call`, counterpart/raw dispatch and fixed callback paths, and checked cited interfaces against definitions in the relevant books. An explicit `:refused` is distinct from an escaped evaluator/guard condition. The publisher's handling of the resulting fault, rather than that dispatch distinction, is F2. No new unsupported raw-dispatch claim was established.

Compared the relevant PRF-187, PRF-369/370, log extension/recovery and direct-read registry statements with their host composition. The direct-read entry admits that worker-set boundedness and thread/mutex fidelity are host facts. `specs/extent-window-read.md` expressly says the served realizer still uses whole extents; its staged window component is not a claim of completed default integration. Functional chunk-composition theorems do not prove host allocation bounds (F9/F10), and a theorem rooted inside `:arch` does not establish its parent publication (F5).

### 4. Cost

Read per-entry log streaming, checkpoint reader admission, checkpoint walk/write loops, export/import loops, extent cache/issued-table retirement and arena-pin transitions. The incremental log scan avoids a whole active-segment byte array; recovery subsequently reintroduces a tail-sized allocation (F8). The admitted direct worker count is fixed, but each worker's legacy result remains whole-extent-sized. `fnn-extent-close` gathers issued rows and checks each requested id against them: O(files-to-close × issued-rows), with the latter constrained by the fixed worker set on the current direct cold line. This is not an unbounded thread-per-miss finding.

Other whole-collection work exists: active pin generations and pending retirements in `fn-arpn-step`, all mux connections in timer/poll bookkeeping, captured records during checkpoint setup, and configuration history during export setup. I have not asserted unsupported constant-time bounds for them. F8–F10 name concrete failures of streaming/quantum claims; the whole-entry verifier's effect on lock hold time is a measurement request below.

### 5. Host decisions

Traced framing/trailers, segment extents and tail positions, config/profile decoding, archive entries/manifest, SIGHUP policy and cold-read identity/settlement to ACL2 entries. No external Lisp reader/evaluator path was found in the reviewed parsers. Host byte/offset marshalling is not itself a semantic duplicate. The material host-policy gaps are the size-only interrupted-rotation inference (F1), off-model control-message admission (F7), and outcome decisions that erase the core/store distinction (F2/F6). Avoid adding another host-only repair policy to fix them.

### 6. Dead or duplicated machinery

The synchronous realizer, unfunded direct executor and funded/window executor are distinct reachable/staged modes; I would not delete one merely because another looks newer. Likewise, arena-generation pins protect retired staged arena pages, whereas issued-read rows protect physical file ownership; merging them without preserving both lifetimes would regress safety. Legacy reader/model/probe paths have explicit developer uses and are not proved dead by lack of an owner caller. Offline/live export duplicate a physical publication recipe and share F5; that duplication is a concrete consolidation opportunity. No additional dead-code finding is asserted from a textual call count alone.

## What I would do instead

Use a small family of typed physical-operation runners shared by offline and served callers: acquire an owned fd/generation, execute a core-described bounded effect, retain the observation, and settle exactly once. Give every constructor a cleanup-until-transfer scope. The cold executor's separation of cancellation from actual return is the right pattern to extend to writes; do not replace it with thread termination or closing a borrowed fd.

Move the **entire** append/extension/rotation-head write interval off the owner mutex, while the core carries the immutable batch identity and admissible next transitions. Owner exclusion should install decisions/results, not wait for a physical medium. Keep acceptance behind the definite file and namespace barriers.

Consolidate staged publication, rename/link, directory/parent fencing and failure classification into one effect vocabulary used by checkpoint/export/import/key administration. Its model must begin at the actual host boundary, including outer-directory creation and short-progress observations. Maintenance must distinguish expected output failure from a broken source store/core.

Make setup and diagnostics obey the same resource discipline as payload loops: scalar progress counters, bounded namespace cursors, bounded zero-fill buffers and worker-private verification state. Keep the store's scale independent of the scheduling quantum. Extend existing boundary theorems to these executable compositions rather than adding helper-by-helper restatements.

## Measurements I want

These are requests for the liaison; none was run here. Use expendable fixtures and the designated hosts/resource controls.

1. **F1, first:** on OpenBSD (and the non-Linux implementation where available), create a store with acknowledged records, copy it, append one byte to the active segment, and invoke writable recovery. Compare the first MiB and record digest before/after, including when recovery exits unsuccessfully. Separately inject a non-unit short extension write followed by EIO/death; record the on-disk extent. The latter crash route is **UNVERIFIED** until measured.
2. **F3:** feed the 16,421-byte duplicate-NP=0-header checkpoint to a developer image under a process timeout; record read/lseek offsets and verify named refusal after repair. Also test one legitimate image header followed by normal frames, a second image header with a different NP, and seek spans beyond EOF.
3. **F2:** corrupt an uncached captured extent after successful recovery, trigger automatic checkpoint and live export, and observe service fault state plus whether a subsequent POST can commit. Exercise a core-entry fault separately from an ordinary staging ENOSPC refusal; those outcomes must differ.
4. **F4:** independently stall append write, extension allocation/write, extension fence, rotation-head write and the existing batch fence. Record owner mutex hold/wait durations and control/reader response latency. Existing tests that only stall the syncer's batch fence cannot refute F4.
5. **F5/F6:** capture the non-Linux export syscall sequence and test the archive root's parent publication with the project's crash-medium harness; process SIGKILL alone does not establish power-loss namespace behavior. Inject post-rename directory-fence failure in node-secret rotation and inspect epoch files plus exit code.
6. **F7:** block the service-log writer, deliver separately observed SIGHUP requests, and count actual process fds, queue control cells and reported log-sink counters. Confirm that any replacement preserves ordered line routing while bounding control ownership.
7. **F8/F9/F10:** matched fixtures varying active extent/frontier, captured sealing-row count and archive namespace size. Record peak allocated/live bytes, longest quantum and stop latency. Count diagnostic LENGTH visits independently; include an invalid profile plus a present empty MANIFEST and a large irrelevant namespace.
8. **F11 and lifetime handoffs:** fail fstat, preallocation, file fence, directory fence, second extent registration and thread creation one at a time, repeatedly in the same process; compare descriptors/leases/pins before and after. Check errors during transfer without converting uncertain close into a refund.
9. **Cold executor regression and remaining cost:** hold every worker, cancel/retire their files, reuse request identities, deliver success/error/runtime-error late, and force an unexpected worker death. Verify no descriptor closes before actual return and exactly one settlement. Then measure whole-entry digest time under the extent mutex while another connection makes warm reads. **UNVERIFIED:** whether this CPU/GC lock hold is a practical latency failure at the supported profiles; source establishes the shared lock and O(ELEN) work, not its elapsed time.
10. **UNVERIFIED concurrency question, not a finding:** force overlapping publisher/commit calls to `fnn-log-make-durable` with rotation attempts and trace the fd generation and `dir-pending` transitions. The normal one-publication/pipeline gates obstruct the obvious stale-state story; I did not establish an allowed interleaving that loses a required fence.
