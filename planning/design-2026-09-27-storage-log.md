# The record log: one barrier per batch (design, 2026-09-27)

Lane `lane/storage-log-design` (Fable 5.1), from dev `1cd88918`, under ember's
priority 3 ("there's no reason to have THAT level of redundant durability")
and gpt-6's consolidation review §8 ("a focused storage redesign: choose a
batch/log publication abstraction, prove its logical per-operation outcomes
and crash behavior, then implement it; do not approach it as deleting one
fsync until a test passes"). Prototype: `books/store-log.lisp` (its record:
`planning/evidence/storage-log-design-2026-09-27.md`). Briefs:
`planning/briefs-wave5/w6-log-{core,owner,recovery}.txt`.

## 0. The sentence

A commit is one self-checking record appended to one file; a batch of
commits is made durable by one `fsync` of that file; a commit is
acknowledged only after its batch's barrier; recovery scans the file to the
last complete chained record and that is the frontier. Seven barriers per
POST become one per batch: at a batch of 8, one eighth of a barrier per POST.

## 1. What a commit costs today, and which contract each barrier serves

The served commit (`host/native/owner.lisp` `fnn-owner-publish-prepared`,
after `fnn-advance-frontier` and the prepare) runs three byte programs
(`books/byte-store-programs.lisp`, `books/byte-store-marker-program.lisp`):
P-FRONTIER (stage, fence, rename onto `allocation-frontier.json`, fence the
root), P-RECORD (stage, fence, link into `transactions/`, fence that
directory, unlink the stage, fence `staging/`), P-MARKER (stage, fence, rename
onto `committed-history.json`, fence the root), then P-FINISH (the
acknowledgement, no syscall). Measured 7 fsyncs, 2 renames, 1 link, 1 unlink
per commit on every image since 2026-09-24 (`commit-regression`,
`publish-program` §1.1, `group-commit` 7.00 to 7.03 per POST). The
publish-program record refused every cheaper marker program by theorem
(PRF-169) against the CURRENT objects: a fence drains one inode, and the
marker's content and entry are two objects that nothing else in the window
between the record's barrier and the acknowledgement shares.

| # | barrier (object) | the contract it serves today | in the log |
| --- | --- | --- | --- |
| 1 | frontier stage `fsync(fd)` | D1 safe rename: the reservation's content is durable before its name is; the txid is consumed before any record names it (STO-003's "stale completions cannot publish"; the burned-reservation keystones) | none: the txid is bound inside the record it allocates; a reservation that never reached the log had no effect (§3.3) |
| 2 | frontier root `fsync(dir)` | the reservation's entry durable (allocation non-reuse across a crash) | none: the same |
| 3 | record stage `fsync(fd)` | the record's bytes durable before they are reachable (STO-003 durable acceptance; A-WRITE-ISOLATION per file) | **the one barrier**: `fsync` of the log segment drains every record of the batch |
| 4 | `transactions/` `fsync(dir)` | the record reachable by name at the next open (STO-005: acknowledged records recovered) | none: the segment's entry is durable since init or rotation; a record's reachability is its offset in a fenced inode |
| 5 | `staging/` `fsync(dir)` (best effort) | hygiene: no orphan stage after a crash | none: no stage file |
| 6 | marker stage `fsync(fd)` | D31's M content: a witness written after the record so a lost committed suffix is refused by name (STO-009) | none: M := D, the last complete record (§3.4, PACKET 1) |
| 7 | marker root `fsync(dir)` | D31's M entry | none |

The seven were a property of the current publication program, as gpt-6 said:
three objects (frontier, record, marker), each needing its content and its
name fenced, plus the staging hygiene. The log has one object per store and
no names per commit.

**What batching inside the current program would cost.** Lane group-commit
(`planning/evidence/group-commit-2026-09-26.md`, PKT-636) found that no
interim exists: the host runs a POST's read and all seven fsyncs inside one
owner-mutex hold and faults on another connection's submission,
`fn-own-take-submission` admits one submission in flight, and the file
kernel and K0 hold one record per transaction file. Its shape C (N record
frames in one transaction file, the seven barriers unchanged) is weighed in
§7: it keeps 7 barriers per batch and every per-file object, and its file
layer (an N-wide frontier reservation, a run scan, K0's pending shape) is
discarded by the log; its owner-side work (a batch of prepared submissions,
the publication off the mutex) is exactly lane 2's here and is not
discarded. The log is therefore built directly; C is not a step on the way.

## 2. Reference designs

- **SQLite WAL** (`wal.c`): one append-only file of page-sized frames; each
  frame header carries a salt pair and a running checksum over the previous
  frame's checksum; a commit is the frame with the commit flag; `sqlite3WalFrames`
  issues one `fsync` per transaction (or none under `synchronous=NORMAL`,
  then one per checkpoint); recovery (`walIndexRecover`) reads frames while
  the salt and the chained checksum hold and stops at the first that does not:
  the last valid commit frame is the end of the WAL. The checkpoint copies
  the WAL's pages into the database and resets the WAL.
- **PostgreSQL** (`xlog.c`, `xloginsert.c`): records appended to WAL segments
  with a per-record CRC over the record and `xl_prev`, the previous record's
  LSN, so a stale valid record beyond a torn tail (from a dead incarnation
  that wrote further) is refused by its `xl_prev`; group commit
  (`XLogFlush` under the WAL write lock: the flusher flushes up to the
  furthest requested LSN and every waiter whose LSN is covered proceeds;
  `commit_delay` is an OPTIONAL wait, off by default); XIDs are assigned in
  memory and `nextXid` is restored at recovery from the checkpoint and
  advanced past every XID the WAL holds: an XID assigned and never logged is
  reused, soundly, because nothing observed it. Segments below the redo point
  are recycled after a checkpoint.
- **InnoDB / MySQL binlog group commit**: a leader thread writes and fsyncs
  once for every transaction that queued while the previous fsync ran.
- **The two hazards these designs name**, which the log carries: (a) a torn
  tail that VALIDATES (a checksum collision: quoted with its figure, §5); (b) a
  stale valid record beyond the tear from an earlier incarnation of the same
  file (the `xl_prev` / salt problem): the log's chain.

## 3. The log

### 3.1 Layout

```
config.json          the profile frame (format fn-store-9: the log lane takes the
                     number at launch), written once by init or import (D34)
journal/000001.log   log SEGMENTS, FNLG entries; the highest-numbered is active
checkpoints/         the pipeline's schema-3 files (design 2026-09-26 §2): unchanged
config/              configuration records: unchanged program (gpt-6 §8: not unified)
staging/             the pipeline's and config's stages only
```

Gone: `allocation-frontier.json`, `committed-history.json`, `transactions/`,
packs (`store reclaim`'s reclaiming pack, `pack-reclaim`, `pack-retire`,
chained packs).

### 3.2 The entry (the record's durable form)

An ENTRY is an `fn-frame` frame (`books/frame-fields.lisp`: MAGIC VERSION
KIND LENGTH, payload, the 32-octet trailer `fn-frame-digest` over the
protected prefix) with magic `FNLG`, version 1, kind 1, whose payload is the
previous entry's trailer (32 octets: the CHAIN) followed by the committed
record's FNST bytes unchanged (`fn-frame-store-encode`: the record codec,
its sequence, txid, generation, stamp, Message-ID, groups, provenance,
charge and payload are the same octets as today), padded with zeros to the
profile's write unit. The first entry of a segment names a GENESIS: 32 zero
octets for segment 1, the previous segment's last trailer for a rotated one
(recorded in the checkpoint's F row, §6).

Self-check: the frame's LENGTH field says where it ends; its trailer
validates its content (`fn-frame-open`); its chain field names its
predecessor. Padding to the write unit is what makes a new append never
share a unit with a committed record (A-WRITE-ISOLATION at the layout:
`specs/failures.md` FLR-001's "appending after a committed record in the same
physical sector may threaten that earlier record"). Cost: at unit 4096 a 2
KiB article's record (about 3.2 KiB) pads by about 22 percent; at 512 by
about 3 percent; a 32 KiB article by under 6 percent at either. The padding
lives only in the log, which holds the suffix since the last checkpoint; the
checkpoint's tables are the compact, unpadded form (§6).

The prototype (`books/store-log.lisp`): `fn-lg-entry`, `fn-lg-scan`,
`fn-lg-log`; keystones `fn-lg-scan-of-log-append` and
`fn-lg-scan-of-torn-entry` (§5.2).

### 3.3 The commit, the batch, the frontier

- **Prepare** (under the owner mutex, sequential): as today's
  `fn-owner-prepare` through the PreparedCommit token of
  `books/catalog-commit.lisp` (`fn-cat-prepare`, D33 §1.3), then the record's
  entry is appended to the BATCH BUFFER (an octet-buffer stobj, the
  publication buffer's kind) at the frontier the previous entry left, and
  the catalog row is PENDING: visible to no served version
  (`fn-view-sees` at the committed version excludes it; STO-002). A later
  prepare in the same batch sees the earlier one's Message-ID binding, so a
  duplicate within a batch is answered as a duplicate (`fn-pb-existing-action`:
  441 / 435 / 438 as today) and never enters the log.
- **Append** (the log thread, no lock): one `write(2)` loop of the buffer at
  the frontier (the model's `:write-all`, torn at unit granularity), cut
  `log-written`.
- **Barrier**: one `fsync(fd)` of the active segment, cut `log-fenced`. Its
  error is UNCERTAIN for every member of the batch (fsyncgate: a retry fences
  nothing, `fn-bs-refence-after-error-fences-nothing`): the store is fenced,
  the batch's members are answered `:uncertain`, recovery decides (STO-004).
- **Finish** (under the mutex, in order): the committed frontier advances
  past the batch; each member is completed by its token (`fn-cat-complete`)
  and acknowledged (`fn-own-finish`'s word), cuts `finish-consumed` /
  `finish-durable` per member as today.
- **The batch closes** when the log thread returns from the previous
  barrier ("barrier-paced": the members are everything prepared while that
  barrier ran), or at `B_max` records or `O_max` octets (a work bound per
  scheduling step, D27: the buffer's size; the operator's live configuration,
  not the profile). There is no timer: at one poster the batch is one entry
  and its latency is one barrier; under P posters the batch grows to P. The
  bounded delay a commit can wait for is the duration of one barrier (§8).
- **The frontier** (allocation) is derived: the next sequence is the count
  of complete records; the next txid is the largest txid the scan and the
  checkpoint's F row hold, plus one. A txid handed out in memory whose record
  never reached the log is reallocated after a crash: PostgreSQL's `nextXid`
  rule. It is sound because nothing observed it: no reply, no record, no
  feed or BP effect leaves the process before the batch's barrier (an
  obligation of lane 2, checked by `native_program_check`'s tie: no
  `:emit-success` before `log-fenced`). A known abort consumes the txid in
  the kernel for the incarnation (STO-002's "consumed even on a known abort"
  keeps its in-process meaning) and writes nothing. Non-reuse over the
  DURABLE history is a theorem (T5, §5.1): txids strictly increase along the
  scan and the recovered frontier exceeds every durable one.
- **Identity bindings**: the record's octets are today's, so sequence, txid,
  generation, Message-ID, content identity and payload keep their binding
  by the record codec (`fn-record-*`); the entry adds the chain and nothing
  else.

### 3.4 The marker: M := D

D31 fixes `A <= M <= D` (A the acknowledged prefix, M the durable marker's
count, D the durable reconstructable length). In the log the durable
reconstructable history IS the scan's result, and the barrier order (acks
after `log-fenced`) gives `A <= D` directly (T1); the marker's count M is the
same object as D. What today's separate `committed-history.json` detects and
the log's own tail cannot is a platform that loses a committed SUFFIX of one
object while another object survives (the marker's "history-short-of-marker"
refusal): a failure outside the crash model (A-DURABILITY is per barriered
object) which today's marker detects only when the marker itself survived
(STO-009's "Not detected" list: losing the marker with the files it covers
reads as `:unmarked`). gpt-6's mandate §5.6: "do not market a store-local
count as an external anti-rollback witness." The log keeps what a store-local
witness can honestly give: the chain refuses a splice, a reorder and a stale
tail; the checkpoint's F row records S, so a segment set that cannot reach S
is refused by name (`history-short-of-checkpoint`).

**PACKET 1 (for ember; no id taken).** Trace: D31, STO-009, STO-022, PRF-076,
PRF-169, this §. Constraint: one barrier per batch. Default: no second
object; `A <= D` proved over the batch; STO-009 restated as "the committed
history is the log's last complete chained record; a checkpoint's S bounds
the segments below". Alternative: a second appended MARKER LOG
(`journal/marker.log`, one 8-octet count per batch, its own chain), fenced
after the segment's barrier and before the acks: `A <= M <= D` with M an
independent object, at ONE more barrier per batch (at batch 8 on the pool,
about 6 ms per POST more; on the NVMe 0.4 ms). Rejected for the default
because the failure it detects is outside the crash model and its detection
was partial; the alternative is a one-file addition to lane 3 if ember wants
the independent witness. Affected: STO-009/022, `books/store-history-*`,
`byte-store-k0-marker`, `fnn-mark-committed`, `fnn-check-history-marker`.
What continues without the decision: the default.

### 3.5 Recovery (P-LOG-RECOVER)

Open the checkpoint the pipeline selects (`fn-sco-select`: S, the segment
and offset where the suffix starts, the genesis trailer), then for each
segment from that one: `fn-lg-scan` from the named genesis (range reads,
`fn-bs-read-ranges-concatenate`, one entry at a time: the open never holds a
segment as a list, D27), stopping at the first entry that does not validate,
chain or fit. The last complete record's aligned end is the frontier; the
segment is `ftruncate`d there and fenced (ONE recovery barrier, so the next
incarnation's durable content is exactly what it scanned; the chain is the
defence in depth for a crash before that fence) and the staging sweep runs
for the pipeline's stages as today. Refusals by name: `log-chain-broken`
(an entry that validates but names another predecessor: a splice or a stale
tail beyond a tear that the truncate did not reach), `history-short-of-checkpoint`
(the segments do not reach S), `checkpoint-damaged` as today. A torn tail is
not a refusal: it is the unacknowledged remainder of the last batch
(STO-005: unacknowledged complete commits may survive, a torn one may not).
Uncertain, refused and accepted stay distinct: the exit codes are today's.

### 3.6 What is not unified

Configuration records (`config/`, `fnn-publish-initial-file`'s program),
the FNBS journal, the feed journals and the checkpoint file keep their
programs and their barriers (gpt-6 §8). Their rates are operator- or
peer-paced, not POST-paced. A later design may move them; nothing here
depends on it.

## 4. The crash model over the log

The byte model is unchanged (`books/byte-store.lisp`: inodes, directories,
pending operations, `fn-bs-crash` landing a subsequence of the pending
operations with each write torn per unit into old / new / zeros / garble).
The programs change; the cut rule ("a :cut after every durable syscall")
holds.

**P-BATCH** (per batch, the log thread): `(:write-all :journal SEG entries)`,
cut `log-written`, `(:fsync-file :journal SEG)`, cut `log-fenced`; then per
member `(:observe (:core-completion seq txid))`, `(:observe (:emit-success seq
txid))`, cuts `finish-consumed`, `finish-durable`. No `:create`, `:link`,
`:rename`, `:unlink`, no directory fence. The cut points and the image at
each, from a related state whose durable segment content D scans to the
committed records:

| cut | pending | the image's scan | acknowledged? |
| --- | --- | --- | --- |
| before the append (`batch-open`) | nothing | committed | no member |
| mid-append and `log-written` | the batch's write, any subset of its units landed, torn | committed ++ a PREFIX of the batch's records (each record's units are its own; the first damaged record stops the scan; a validating damaged record is the forgery event, §5) | no member |
| `log-fenced` before any finish | nothing (drained) | committed ++ the whole batch | no member: every record durable, none answered: today's "durable, unacknowledged" (the retry is a duplicate) |
| `finish-k` | nothing | the same | members below k answered; all durable |
| `fsync` error | the torn selection landed, the rest discarded | as `log-written`'s | every member `:uncertain`, the store fenced |

So "crash is old or new" is, per batch, "old, or a prefix, or new", and per
member "old or new" in order: T2. **Every process-death cut is a model crash
point** (`transcribe_check`, `native_program_check`): the developer image's
`fnn-at` sites are `log-written`, `log-fenced`, and the two finish cuts per
member; the POST campaign's 23 cuts become these (lane 1's cut table).

**P-LOG-RECOVER**: reads (the scan) then `(:truncate :journal SEG frontier)`
(a NEW step kind: the model has no truncate today; it is `fn-bs-splice`'s
prefix and is the one in-place change the log makes, of octets beyond the
frontier that no complete record owns: discipline D2 is restated as "no
write below the frontier of an authority inode"), cut `log-truncated`,
`(:fsync-file :journal SEG)`, cut `log-recovered`, then the sweep. A crash
before `log-recovered` leaves the tail; the next open scans the same
records (the chain refuses the stale bytes) and truncates again.

**Rotation** (the pipeline's install step, §6): `(:create :journal NEXT)`,
`(:fsync-file :journal NEXT)`, `(:fsync-dir :journal)`: the new segment's
entry durable before the checkpoint's F row names it; then the checkpoint's
own program (`fn-bs-scp-program`, unchanged); then, after the checkpoint's
root barrier, `(:unlink :journal OLD)` per covered segment and `(:fsync-dir
:journal)`. Off the commit path; cuts named in lane 3's table.

**The test the design must pass** is lane power-loss's rig
(`tools/power_loss.py`, `planning/evidence/power-loss-2026-09-26.md`): power
cut to the block device (dm-log-writes over loop devices, ext4, barriers on)
at every recorded write boundary under a committing node, 1,281 cuts outside
`init`, the oracle "every `240` is served afterwards with the reference
octets; no `441` is ever served; a lost-reply POST is served whole or absent;
no Message-ID binding or local number moves or is handed out again; the
reclaim accounting holds" upheld with no violation, and the fsync assumption
shown LOAD-BEARING (`barrier=0`: 37 of 40 cuts lost acknowledged POSTs).
Under the log the same rig runs unchanged (its marks follow each `240`;
the `240` follows the batch's `fsync`, so every write the acknowledgement
depended on is logged before its mark): the log-core lane runs it over
P-BATCH and P-LOG-RECOVER, the owner lane over the served node. The rig's
one observation, "a lost POST's number is used again" (a POST with no reply
whose record never landed), is the derived frontier's rule stated in §3.3:
what never reached the log had no effect and is reallocated; what reached
it (a lost-reply POST, durable and unacknowledged) keeps its number, its
txid and its Message-ID binding, which the oracle checks.

**K0 over the log**: the relation R(bs, ks) between a byte store and the log
kernel `fn-lg` (lane 1): the active segment's DURABLE content scans, from
its genesis, to `ks.committed` with frontier = its aligned end; the pending
writes on that inode are exactly the open batch's entries at offsets at or
above the frontier and nothing else is pending on the journal directory
(outside rotation); `ks.acked` is a prefix of `ks.committed` (A <= D). R is
established by P-LOG-RECOVER's `log-recovered` (the truncate makes the
durable content exactly the scan), preserved by every step of P-BATCH (the
append adds pending writes above the frontier; the fence moves them into the
durable content, where `fn-lg-scan-of-log-append` reads them back; the
finishes change only `acked`), and every crash image of a related state
scans to committed ++ a prefix (T2). No whole-state revalidation on the
served path: R is carried, not re-checked.

## 5. The proof plan

### 5.1 The theorems, their hypotheses, their teeth

Names are the statements' subjects; lane 1 and lane 2 name the host lines
(`current_view.py` finds them).

- **T1 `fn-lg-acknowledged-record-survives-crash`** (durable acceptance).
  For every reachable owner state and batch, if member m is acknowledged
  (`:emit-success` observed) then in every admissible crash image of the
  store the scan of the durable segment reads m's record. Hypotheses: R at
  the cut; A-CRASH-IMAGE (`fn-assume-physical-crash`: the platform's crash
  is a model crash); the program shape (acks only after `log-fenced`:
  `native_program_check`'s tie, asserted on the constant program as D1-D3
  are today). Proof: `fn-bs-crash-keeps-fenced-content` (a fenced inode's
  durable content survives) and `fn-lg-scan-of-log` (a well-formed log reads
  back its records). Teeth: a ground batch of two records, cut `finish-1`,
  the lose-everything image; `must-fail` with the ack before the fence.
- **T2 `fn-lg-batch-crash-is-a-prefix`** (crash is old-or-new over the
  batch). At every cut of P-BATCH from a related state, every admissible
  crash image's scan is committed ++ a prefix of the batch's records, or the
  first damaged entry validates as a chained frame that is not the written
  one (`fn-lg-forgeryp`). Hypotheses: R; the SHIFT LEMMA (a crash of a
  pending write at a unit-aligned offset of an inode holding L is L
  followed by a torn variant of the write: `fn-bs-splice` at an offset at or
  past the end is an append, and `fn-bs-tear-write` at offset k·unit is the
  offset-0 tear shifted by k·unit); the prototype's
  `fn-lg-scan-of-log-then-torn-entry` for one appended entry and its
  induction over the batch's entries (each entry's units are its own, so
  the choices split per entry). Corollary under A-CRYPTO-TRAILER
  (`fn-assume-crash-tearp`, `fn-assume-crash-tear-never-validates-unless-exact`,
  instantiated at each entry's frame through a prefix-of-a-torn-variant
  lemma): the forgery disjunct goes. **The figure, pessimistically**: the
  forgery is a garbled unit whose 32-octet trailer equals the SHA-256 of its
  own garbled prefix; the pessimistic number is the collision figure of
  SHA-256, about 2^-128 per chosen pair, not the second-preimage figure
  (2^-256); the qualification is statistical, as A-CRYPTO-TRAILER's is
  today (the campaign's garble and truncate variants never validate). Teeth:
  the prototype test book's ground tears (a dropped last unit, a zeroed
  first unit, a garbled middle unit, the exact write, the exact write with
  garbled padding) and a `must-fail` per hypothesis.
- **T3 `fn-lg-recovered-frontier-is-the-last-complete-record`**. P-LOG-RECOVER
  from any durable content D answers (records, frontier) with frontier the
  aligned end of the last complete chained record, and after `log-recovered`
  the durable content scans to exactly those records (a fixed point:
  `fn-lg-scan-of-log` on the truncated content). Hypotheses: A-CRASH-IMAGE
  for the crash that produced D. Teeth: D = a log ++ garbage; D = a log ++ a
  complete stale entry with a wrong chain (refused as `log-chain-broken`
  when it validates, else the torn tail).
- **T4 `fn-own-batch-finish-is-the-sequential-finish`** (per-operation
  outcomes equal today's). The owner's outcome word for member m of a batch
  equals the word `fn-own-finish` gives m published alone after its
  predecessors in the same order: the batch step is the fold of the single
  steps. Hypotheses: the members' prepares were sequential under the mutex
  (each saw the previous one's catalog effect); `fn-cat-complete` by token;
  the context fixed between prepare and finish
  (`fn-sn-context-fixed-between-prepare-and-finish`). The served keystone
  `fn-own-240-follows-consumed-completion` is restated per member. Teeth: a
  batch of two with a duplicate Message-ID in the second (answered 441, not
  in the log); a batch of two distinct (both 240 after `log-fenced`).
- **T5 `fn-lg-txids-strictly-increase`** (allocation non-reuse over the
  durable history). Along the scan the txids strictly increase and the
  sequence is the position; the recovered frontier exceeds every durable
  txid. Hypotheses: the kernel's allocation rule (next = frontier). Teeth: a
  recovered log then a new batch; a stale entry with a lower txid (refused
  by the chain before the txid is even read).
- **T6 the identity bindings**: the record codec's theorems (`fn-record-*`,
  PRF-123, PRF-126) apply unchanged: the entry's payload after its 32-octet
  chain is the record's bytes (`fn-lg-slice-record-of-frame`). Not restated.
- **T7 `fn-lg-uncertain-batch-recovers-to-a-prefix`** (the uncertainty class
  unchanged). After an `fsync` error the store is fenced, every member is
  `:uncertain`, and the open after recovery holds a prefix of the batch; a
  retry of a member in that prefix is answered as stored (the visibility-join
  theorems, PRF-115) and one beyond it is admitted afresh. A reply lost after
  `log-fenced` (process death before the finish) is the same class: durable
  and unacknowledged. Teeth: the two ground cuts.
- **T8 `fn-lg-segment-drop-preserves-the-open`** (compaction). After a
  checkpoint at S whose F row names segment k+1 and its genesis, unlinking
  segments at or below k leaves the open equal to the full open:
  `fn-sn-recover-from-checkpoint-equals-full-recover` (checkpoint-cost) with
  the lemma that the scan of the remaining segments from the named genesis
  is the suffix at S. Hypotheses: the checkpoint's `fn-sct-load-of-publish-is-the-capture`
  (checkpoint-pipeline, on its branch). Teeth: a two-segment log, the
  checkpoint at the rotation, the drop, the open compared.

**Assumptions named**: A-CRASH-IMAGE, A-CRYPTO-TRAILER (both
`encapsulate`s in `books/assumptions.lisp` already), A-WRITE-ISOLATION at the
layout (padding to the unit: a theorem about the program, `fn-bs-tear-touches-only-its-inode`'s
shape restated per unit), A-HOST (the host's `fsync` is the model's fence:
the qualification profile, D14). No new assumption.

### 5.2 What is REPL-provable now, and what the prototype proves

`books/store-log.lisp` (prefix `fn-lg-`, registered in `docs/prefixes.md`),
admitted form by form in the hbox REPL (ACL2 8.7 w28, the closure's
certificates from `/tank/fn/certcache`; the record names the session and
the farm run):

- `fn-lg-scan-of-log-append`: the scan of a well-formed log followed by any
  octets reads every record and then scans the octets from the log's last
  trailer; `fn-lg-scan-of-log`: alone, exactly its records and its length
  (the frontier is the last complete entry's end).
- `fn-lg-scan-of-torn-entry`: the scan of a torn variant of one appended
  entry (`fn-bs-torn-variantp`, the byte model's crash of the one pending
  write) is the empty history, or exactly the record, or a forgery.
- `fn-lg-scan-of-log-then-torn-entry`: the composition (a log then a torn
  append, at offset 0 of the appended bytes: the shift lemma is lane 1's).
- `fn-lg-torn-variant-len`: a torn variant is no longer than the write.

Not in the prototype (lane 1): the shift lemma; the induction over a batch's
entries; the A-CRYPTO-TRAILER corollary (the prefix-of-a-torn-variant lemma);
the executable scan (fn-frame-decode with fn-frame-trailer, guard-verified,
range reads); the kernel and R; the host tie.

### 5.3 The migration path under D34

Fresh deploys, no migrations: format `fn-store-9` is the ONLY format the new
release opens; a format-8 profile is refused by name at open (`store-format`,
STO-028's sentence, unchanged in shape). The history moves by `store export`
on the old release (the committed records in sequence order, the profile,
the MANIFEST) and `store import` on the new, which writes segment 1 from the
genesis in one batch per `O_max` (PRF-205's "the import of an export replays
the same history" re-targeted to the log's scan: the export never reads the
frontier file or the marker, which no longer exist). No frontier-frame
translation, no marker catch-up (`fn-hmr-catch-up`, `fn-hmr-birth`, PKT-587
retired), no `history-marker` profile field (PACKET 1 decides whether a
marker log replaces it).

## 6. The checkpoint pipeline's tables are the log's compaction

The pipeline (design 2026-09-26 §2, lane checkpoint-pipeline on its branch)
captures a stable root S, writes P (payload extents), E (event metadata), R
(roots) and F (frontier) in bounded batches, validates each segment, installs
by rename and root fence. In the log design:

- **Capture** also ROTATES: the active segment is closed at S (its last
  entry's trailer is the next segment's genesis; the next segment is created
  and fenced, §4), so every record below S lies in segments at or below k.
  F gains: the first segment of the suffix, its genesis trailer, the log
  frontier txid at S.
- **P** copies each payload once from the arena (as designed; the arena is
  loaded from the log's entries at commit and from P at open). The padding
  and the entry overhead stay in the log; P and E are the compact form.
- **Install** then **drops** segments at or below k (unlink, fence the journal
  directory): STO-006/007's "the replacement becomes durable and reachable
  before old storage is reclaimed" is the order rename-fence-unlink. T8 is
  the theorem.
- **Content reclamation** (STO-014/017): a tombstone record is committed as
  today; the next checkpoint's P omits the released payload (the tombstone
  says so) and the drop returns its octets with the segment. The reclaiming
  pack, `pack-reclaim`, `pack-retire`, the chained packs (STO-012) and their
  books go (§9).
- **Open**: the checkpoint's tables into the arena and the catalog (the
  pipeline's loader), then P-LOG-RECOVER over the suffix segments (§3.5).
  `fn-sn-recover-from-checkpoint-equals-full-recover` transfers.
- **Under gpt-6's wave-5 review §2** (`planning/review-2026-09-26-gpt6-wave5.md`:
  one publication in flight, one coalesced request, bounded records AND bytes
  per step, the finished checkpoint bound to the prefix it captured): the
  rotation is part of that one publication (one rotation in flight; the
  segment boundary IS the captured prefix S, so the checkpoint is bound to
  S by construction and never to "the count when the final write returns");
  the drop is a bounded step after the install (one unlink per step). The
  log raises the commit rate lambda and does not change tau(S), so the
  review's arithmetic (a suffix of about lambda·tau(S) at the finish) is
  more likely to exceed K, not less: the promise to decide there (K as a
  fast-path threshold with full replay permitted, or a guaranteed maximum
  suffix by admission limiting) is the review's decision, and the log takes
  no position; its suffix is bounded by the profile's H (D27) either way.

## 7. PKT-636 (shape C) against the log

| | C: N frames in one `.txn` file | the log |
| --- | --- | --- |
| barriers per batch | 7 | 1 |
| per-POST at batch 8 on the pool (50 ms a barrier, node-disk medians 33 to 67) | about 44 ms | about 6 ms |
| objects per store | one file per batch, the frontier, the marker | one segment per checkpoint interval |
| open | one directory entry and one frame run per batch | one file, range reads |
| kernel | candidate = a run; the frontier reserves N | the log kernel `fn-lg` |
| K0 | the pending shape (one entry) restated for a run | one inode's pending writes |
| owner | a batch of prepared submissions; publication off the mutex | the same |
| what is discarded by the log later | the file layer and its proofs | nothing |

C's only advantage is that its crash argument is the existing per-file
keystone instantiated at a longer content; that argument is a fraction of
lane 1's work (the shift lemma and the torn-tail induction), and C leaves
every object the log removes. Recommendation: no interim; lane 2 (the owner
batch) is the shared work and is built once, against the log.

## 8. The expected numbers

Scope: hbox, the dev image of 2026-09-26, other lanes live. "Before" rows
are lane group-commit's (`planning/evidence/group-commit-2026-09-26.md`,
`gc_measure.py`: P posters, 2 KiB articles, load 24 to 37, `tank` 94 percent
full) and node-disk's per-fsync medians (`node-disk-2026-09-26.md`: NVMe
ext4 3.1 ms; `tank` 33.2 / 66.6 ms in two rounds, taken as 50; `rpool` 0.79;
tmpfs 0.001). c is the owner's CPU per POST: 3 ms at small N (group-commit's
tmpfs p50 2.7 ms is CPU plus seven free fsyncs), 10 ms at N = 10,000 today
(publish-program §1.4: the group-index term PKT-324 that the catalog slice
removes).

**Fsyncs per POST**: today 7.0 (6 with PKT-441, not merged). The log: 1/B:
**1, 0.125, 0.0156** at B = 1, 8, 64.

**Barrier time per POST** (f/B): NVMe 3.1 / 0.39 / 0.05 ms; `tank` 50 / 6.3 /
0.8 ms; today's 7f: NVMe 22 ms, `tank` 350 ms.

**Latency at low load** (one poster, B = 1): c + f: NVMe **6 to 13 ms**,
`tank` **53 to 60 ms**; today `tank` p50 0.42 s (group-commit), 160 ms median
at load 11.8 (publish-program). The added delay of the barrier-paced close is
at most one barrier (a commit that arrives during a barrier waits for it,
then its own): worst case c + 2f.

**POST/s** (the batch grows to the poster count P; the barrier overlaps the
next batch's prepares; the rate is min(1/c, B/f) per second):

| | today, measured | log, 1 poster | log, 8 posters | log, 32 posters |
| --- | --- | --- | --- | --- |
| tmpfs | 320 / 265 / 239 (1 / 8 / 32) | 1/c: 330 (c 3), 100 (c 10) | 330 / 100 | 330 / 100 |
| NVMe ext4 (3.1 ms) | about 30 estimated (node-disk, 7 barriers) | **164** (c 3), **76** (c 10) | 330 / 100 (CPU-bound) | 330 / 100 |
| `tank` (50 ms) | 2.25 / 2.04 / 2.23 | **19** (c 3), **17** (c 10) | **160** (barrier-bound at c 3), **100** (c 10) | 330 / 100 (CPU-bound) |
| `rpool` (0.79 ms) | about 64 estimated | 260 / 93 | 330 / 100 | 330 / 100 |

Read: the pool stops being the ceiling at 8 posters; after the log the
lever is c (the catalog slice, gpt-6 answers §3 "first, remove whole-history
work"), and the v1 envelope (10 POST/s sustained, 250 ms p95 unsigned) is met
on `tank` at one poster with margin where today it is not. These are
estimates from measured components, not measurements; the after rows are
`gc_measure.py` on lane 2's image (PKT-637), matched to the before rows.

## 9. The deletion map (the abstraction replaces; the lanes delete by name)

| goes | replaced by | lane |
| --- | --- | --- |
| P-FRONTIER (`fn-bs-frontier-program`), `allocation-frontier.json`, the FNSM frontier kinds 2 and 3 (`byte-store-frame`), `fnn-advance-frontier`, `fn-sf-start-frontier` and the phases `:frontier-staged`, `:frontier-data-durable`, `:frontier-attempted` | the derived frontier (§3.3), the log kernel | 1, 2 |
| P-RECORD (`fn-bs-record-program`), `transactions/`, `fnn-publish`, `fnn-transaction-name`, `fn-bs-txn-names`, the per-file scan (`byte-store-scan`'s name list), `:record-attempted` | P-BATCH, `fn-lg-scan` | 1, 2 |
| P-MARKER (`fn-bs-marker-program`, `byte-store-marker-candidates`, `byte-store-k0-marker`), `committed-history.json`, `store-history-marker`, `store-history-required`, `fnn-mark-committed`, `fnn-check-history-marker`, the `history-marker` profile field, PRF-076, PRF-169, PRF-174 | M := D (PACKET 1) | 3 |
| P-RECOVER's five fences, `fnn-recover`'s frontier and marker reads | P-LOG-RECOVER (one fence) | 3 |
| packs: `store-reclaim-pack`, `checkpoint-compaction-preservation` (PRF-073), `byte-store-compaction-correspondence`, chained packs (STO-012), `pack-reclaim`, `pack-retire`, `store reclaim`'s reclaiming pack | rotation and segment drop (§6, T8) | 3 |
| the K0 books' pending shape for one record entry (`fn-bs-pending-shape-okp`, `fn-bs-pending-matches-phase`), the POST campaign's 23 cuts | R over the log, 4 cuts plus 2 per member | 1 |
| `fn-own-inflight` as one submission, `fn-own-take-submission`'s one-in-flight gate, STO-003's "one commit in flight" | the batch of PreparedCommit tokens | 2 |
| the format-8 open, `fn-hmr-catch-up`, `fn-hmr-birth`, PKT-587 | format 9 only (D34), export/import | 3 |

Kept: the byte model, the FNST record codec, the frame codec, the arena, the
catalog, PreparedCommit and completion by token, the committed delta, the
checkpoint pipeline and its schema, `fn-bs-scp-program`, the configuration
records' program, the FNBS and feed journals, `store export/import`.

Requirement lines touched: STO-003 (a batch in flight), STO-009 and STO-022
(restated per PACKET 1), STO-012 and STO-017 (segments, not packs), STO-013
and STO-018 (the frontier frame goes; the u64 widths stay in the record),
STO-028 (format 9). Each lane changes the registry, the spec and the scenario
together (AGENTS.md).

## 10. The lanes (briefs in `planning/briefs-wave5/`)

1. **w6-log-core** (Opus 5.5; certifies itself: byte-store fan-in): the
   executable scan and entry, the log kernel `fn-lg` and R, P-BATCH and
   P-LOG-RECOVER as byte programs with the cut table, T2 (shift lemma,
   induction, the A-CRYPTO-TRAILER corollary), T3, T5, the host's
   `fnn-log-append`, `fnn-log-fence`, `fnn-log-recover` in `host/native/io.lisp`
   beside today's (no caller yet), `native_program_check`'s tie, the
   `truncate` step in the byte model. Deletes nothing yet (row 6 of §9 is its
   continuation's).
2. **w6-log-owner** (Opus 5.5; the coordinator may raise it to Fable: the
   owner books are the highest fan-in in the tree): the batch of
   PreparedCommit tokens, the publication off the mutex with the fence
   semantics carried, the barrier-paced close with `B_max`/`O_max`, T1, T4,
   T7, the format-9 profile and `init`, the commit sites (`store post`, the
   probe, `fnn-owner-publish-prepared`) onto lane 1's entry, the served
   crash campaign at the new cuts, the after rows with `gc_measure.py`.
   Deletes §9 rows 1, 2 (host half) and 7.
3. **w6-log-recovery** (Opus 5.5): P-LOG-RECOVER in `fnn-recover`, the
   checkpoint's F row extension and rotation in the pipeline's install,
   segment drop and T8, reclamation as checkpoint-then-drop, export/import
   over the log, the refusals by name, and §9 rows 3, 4, 5, 8 executed with
   proofs.json retirements. Runs after lane 1; can overlap lane 2.

Order: 1, then 2 and 3. Each lane's brief carries its deletion map, its
native modules, its theorem names and the ids the deputy assigns at launch.

## 11. What needs ember

PACKET 1 (§3.4): the independent marker witness or M := D. Everything else
here is within D31 ("the guarantee A <= M <= D is what is frozen, not the
syscall sequence"), D33, D34 and gpt-6 §8, and proceeds on the defaults.
