# checkpoint-capture-stream: the owner's automatic checkpoint publication through the octet buffer, decided by name before it is encoded (2026-09-26)

Lane `lane/checkpoint-capture-stream` from dev `a9d75c88`, Fable, wave 4
(deputy 4's brief `build/coordinator/queue/w4-checkpoint-capture-stream.txt`;
ground truth `build/coordinator/ground-truth-checkpoint-capture.md`).
Registry: PRF-183, STO-024, SCN-112, PKT-494, PKT-495; PKT-492 and PKT-315
ticked, PKT-191 narrowed. Commits: see the LANEDUMP and the final message.

**What a human or agent can now do that they could not before:** run one
owner past N of about 33,000 articles of 2 KiB with automatic checkpoints.
On the image before this lane the automatic capture encoded the whole
frozen checkpoint as octet lists (five to six copies at sixteen bytes per
octet) and killed the owner at N = 32,729 and again at 36,208 with SBCL's
32,000 MiB dynamic space exhausted inside `fn-scc-frames`
(`planning/evidence/service-envelope-2026-09-26.md`, "N = 100,000"): every
connection lost, one POST uncertain, no named refusal. Now the publication
thread encodes the frozen checkpoint once into its own octet buffer (one
byte per octet) and the host writes the file straight from that buffer;
before any encode ACL2 decides by name whether the file fits the profile's
checkpoint budget and, when it does not, defers the publication with the
file's length and the budget on the log line and in `status`, writes
nothing and keeps serving. The measured result is in section 5.

## 1. The assurance chain for the slice

native entry -> executed ACL2 subject -> refinement -> maintained relation
-> behavioural theorem -> observed result:

1. **Native entry.** `host/native/owner.lisp` `fnn-owner-maybe-publish`
   (under the service mutex, between accepts) asks `fn-owner-sco-due`, takes
   `fn-owner-sco-capture` (now seven values: base, configs, records, segment,
   count, suffix, BUDGET) and starts the thread `fnn-owner-publish-captured`,
   which OFF the mutex calls `(fnn-call 'fn-ock-publication-stream base
   configs records segment budget (fnn-live-octets-pub))`: the host line.
   The budget is `fn-ock-capture-budget` of the carried profile
   (`host/owner-host.lisp` `fn-owner-sco-capture`); on a developer image the
   selector `FN_NATIVE_CHECKPOINT_BUDGET_TEST=N` replaces it
   (`fnn-checkpoint-budget-test-override`, io.lisp), the comparison staying
   ACL2's.
2. **Executed ACL2 subject.** `fn-ock-publication-stream`
   (`books/owner-checkpoint-stream.lisp`, :logic, guard-verified, over the
   octets stobj), called with the PUBLICATION buffer `fn-octets-pub`, a
   second abstract stobj congruent to `fn-octets` (same foundation
   `fn-octets$c`, the same :logic/:exec pairs under new names, its own live
   object). It answers `(mv NEXT VERDICT fn-octets)`: NEXT by
   `fn-ock-next-checkpoint` (unchanged); VERDICT `:unencodable` when
   `fn-sccb-treep` fails of the frozen NEXT, else `(:deferred :exceeds-budget
   ESTIMATE BUDGET)` when `budget < (fn-ockb-file-len frozen seg)`, else
   `(:plan PLAN ESTIMATE)` with `(fn-sccb-plan frozen seg fn-octets)`.
3. **Refinement (the representation boundary).** `fn-sccb-plan-is-file-octets`
   (PRF-133, cited): the plan's octets over the buffer it leaves are
   `fn-scc-file-octets` of the same value. The new export
   `fn-octets-append-list` (PKT-315: :logic `append` on the logical list via
   the guard-free `fn-oct-cat`, :exec `fn-oct-write-list`, `:protect t`) has
   its `{correspondence}`, `{guard-thm}` and `{preserved}` proved before the
   `defabsstobj` from the existing `fn-oct-write-list-steps`; the opened view
   `fn-oct-append-list-is-append` has no hypothesis, so
   `fn-sccb-append-list-is-append` lost both of its (the per-octet writer's
   two hypotheses were dropped after the weakened theorem was proved).
4. **Maintained relation.** The buffer's `fn-octets$corr` is established by
   the creator and preserved by every export (octets-stobj); the congruent
   stobj is admitted by those same obligations (ACL2's `:congruent-to`,
   which requires the same foundation and the same tuples). The estimate is
   exact: `fn-ockb-file-len-is-len-file-octets` (`(implies (fn-sccb-treep c)
   (equal (len (fn-scc-file-octets c seg)) (fn-ockb-file-len c seg)))`),
   from `fn-ockb-len-acc-is-len-program` (no hypothesis beyond
   `fn-scc-treep`) and the frames' lengths (a header 37, a seal 32, a chunk
   its own length, the chunks a partition of the program).
5. **Behavioural theorems.** KEYSTONE `fn-ock-publication-stream-writes-the-file`:
   when the verdict is a plan, `(fn-sccb-plan-octets PLAN fn-octets')` equals
   `(cadr (fn-ock-publication base configs records seg))`, the list entry's
   file octets, byte for byte. `fn-ock-publication-stream-refuses-what-the-codec-refuses`:
   the `:unencodable` cases agree with `fn-ock-publication`'s.
   `fn-ock-publication-stream-defers-by-the-estimate` (PKT-492's refusal
   theorem): for an encodable frozen NEXT the verdict is deferred exactly
   when `budget < (len (fn-scc-file-octets frozen seg))`, names that length
   and the budget, and otherwise is a plan.
   `fn-ock-publication-blockedp-by-definition`: a deferred verdict blocks a
   later budget exactly while it is below the file's length (the due path,
   `fn-owner-sco-due`). `fn-ock-publication-stream-next-is-the-capture`:
   NEXT is `fn-sco-capture configs records` under the admitted-history
   hypothesis, by `fn-ock-next-checkpoint-is-the-capture` (PRF-104, cited),
   so `fn-ock-publication-is-the-capture-at-the-capture-point`,
   `fn-ock-published-segments-decode-to-the-checkpoint`,
   `fn-sccr-decode-of-plan` (PRF-135) and the crash keystone
   `fn-bs-scp-program-crash-is-old-or-new` stand as they were: the host
   writes the plan through `fnn-state-checkpoint-write` with the same five
   cuts (`fnn-write-staged-at` takes a byte vector or a writer,
   `fnn-plan-write-all`, between the same `created` and `written` cuts;
   `tests/campaign/native_cuts.py` `verify_state_checkpoint_cut_map` and
   `tools/native_program_check.py` PASS unchanged).
6. **Observed result.** Section 4 (the native cases) and section 5 (the
   measurement).

The relation is established at the owner's start (the buffer's creator; the
frozen checkpoint is a value) and preserved by every export the entry makes
(`fn-sccb-plan`'s writes, all through exports); no served transition touches
the publication buffer, and the publication touches no served state (it
writes only the four `fn-owner-sco-*` globals under the mutex, as before,
plus `fn-owner-sco-deferred`).

## 2. The hazard and the design chosen

The one served buffer `fn-octets` (`*fnn-octets*`, io.lisp) is filled by
`fnn-owner-attempt` and read by the served POST under the service mutex; the
publication runs off it. A shared buffer would race. The design: a second
abstract stobj `fn-octets-pub`, congruent to `fn-octets`, owned by the
publication thread; "one buffer, one thread" holds per buffer. ACL2's
`:protect` counter `*inside-absstobj-update*` is a process global, but the
served thread calls no `:protect`ed export (grep over host/ and books/
outside the two buffer books: none; it fills raw and reads by index), so
only the publication thread touches it, and nothing in the native host reads
it (only `ld` and `certify-book` do). Cost: a second byte array of the
largest file's size, one byte per octet, kept (cleared, not shrunk) between
publications; no served-path stall. Rejected: the encode under the mutex
(a stall of 90 s at N = 30,000 on the old codec, and a resumable encoder to
build).

## 3. The budget: what it is and what it is not (PKT-495)

`fn-ock-capture-budget profile` = `fn-sccr-file-read-bound H R` = 3 x
`max-history-octets` + one segment's framing (37 + R + 32): the file bound
the OPEN already refuses a checkpoint past (`fn-sccr-admit-segment`
`:exceeds-bound`, then `(:full-replay :checkpoint-exceeds-bound)`). The owner
never spends an encode on a file the open would refuse, and no profile field
or format changes. It is the operator's number (H) and bounds one
publication's WORK by the declared history (D27), never the data a store may
hold. It is a bound on the FILE (one byte per octet in the publication
buffer), not on the process heap: the frozen checkpoint value (the records
twice, PKT-314) and the live history at sixteen bytes per octet are the
arena's (PKT-293/PKT-167), and a profile whose H the configured dynamic space
cannot hold is refused by nothing yet (PKT-016). The scale-1m profile's
budget is 3 x 4 GiB + framing, about 12.9 GB: the N = 40,000 file (section
5) is far under it, so on that profile the decision only ever answers a
plan; the deferral is reachable on a profile whose H is close to its
history and whose per-record tree overhead exceeds the record (many groups,
tiny bodies), which no preset gives (the development preset's budget is
about 92 MB), so the native deferral case stands in a test budget through
the developer selector. The alternatives and their costs are PKT-495.

## 4. Teeth, certification and the native cases

**Teeth** (`tests/acl2/owner-checkpoint-stream-tests.lisp`, on
owner-checkpoint-open-tests' image: two retention events and two
configuration records, the capture of the whole history frozen and encoded
at segment size 64, which cuts it into more than one segment; the exec path
on a live local buffer and once on the publication buffer `fn-octets-pub`):
the keystone's positive witness at the budget boundary (budget = the file's
length: a plan of several segments whose octets equal
`fn-ock-publication`'s file, NEXT the capture, the estimate the file's
length, the buffer's fill the program's length, the unchanged reader
decoding the value); the same on the congruent stobj; the deferral one octet
below (deferred by name with both numbers, NOTHING encoded: the buffer's
fill is 0) and a plan far above; the blocked rule on that deferral (blocked
below the estimate, not at it; never on a plan); the budget from the
development preset; the refusal on a history holding 2^2040 (the codec's
atom writer lists it, no atom encodes it: `:unencodable` on both entries,
nothing encoded). Per hypothesis, a witness with every retained hypothesis
true, the omitted one false and the conclusion false, and the `must-fail`
(each closing the entry in its hint, so a doomed search costs nothing):
writes-the-file without a plan (the deferred verdict's octets are nil);
refuses-what-the-codec-refuses without the codec's refusal (an encodable
value answers a plan); defers-by-the-estimate without `fn-sccb-treep` (the
unencodable history: `:unencodable`, whose car is neither `:deferred` nor
`:plan`); file-len-is-len-file-octets without `fn-sccb-treep` (`:unencodable`
has length 0, the walk counts the rest); len-acc-is-len-program without
`fn-scc-treep` (2^2040: 0 against 258); blockedp-by-definition without a
deferral (a plan never blocks). Untoothed, as owner-checkpoint-open-tests
reports the same hypothesis: the admitted-history hypothesis of
next-is-the-capture (the identity fold's fault is absorbing). A tree the
list codec admits and the buffer codec refuses (a leaf of 2^2040 octets) is
not constructible, so `fn-sccb-treep` is toothed at the codec's refusal
only. The bulk export's teeth are in `tests/acl2/octets-stobj-tests.lisp`
(ost-w-18 to ost-w-21 and the exec run: the write lands at the fill, the
old cells stay, a 300 is refused by the concrete recognizer, the opened
view holds on improper values, a 3,000-octet write resizes past 1024) and
the hypothesis-free `fn-sccb-append-list-is-append` has its ground
instances on improper values in `tests/acl2/store-checkpoint-buffer-tests.lisp`
(the per-octet writer's two teeth went with its two hypotheses). The
status words have theirs in `tests/acl2/native-live-status-tests.lisp`
(a six-element observation prints the deferral on the checkpoint-file
line; a five-element one prints the line unchanged; live equals offline
with a deferral observed).

**Certification.** persvati, run `run-20260926T143854Z-252a`
(`--affected-by books/octets-stobj.lisp books/store-checkpoint-buffer.lisp
books/owner-checkpoint-stream.lisp books/native-live-status.lisp
tests/acl2/docs-operator-grammar-tests.lisp`, ACL2 8.7 w25/acl2-literal, 2
jobs, 300 s): 21 books certified (the four changed books, the regenerated
grammar book, the dependents of octets-stobj: payload-arena,
poster-bytes-buffer, sha256-buffer, store-checkpoint-reader,
store-reclaim-buffer, visibility-join, native-health, and their test books),
0 failed, 199 installed from the cache, **no book over 10 s**; manifest
`planning/evidence/manifests/certify-20260926T143919Z-2974417.json`.
Before the run every changed book and test book was certified in the
lane's REPL tree on persvati (`~/fn-gates/checkpoint-capture-stream-repl`,
discovery, not a claim); the whole stream book (43 forms) had been loaded
form by form in `proof_repl.py`. owner-checkpoint-open.lisp and its
closure to owner-invariants are untouched (the stream book is a leaf
beside it), so none of them recertified. The regenerated grammar book:
the docs paragraph on `status` grew by four lines, which renumbers the
quoted invocations `tests/acl2/docs-operator-grammar-tests.lisp` cites
(PKT-493); regenerated with `tools/docs_check.py --write` and certified in
the same run.

**Native, hbox** (`tools/hbox_native.sh`, `/tank/fn/scratch/checkpoint-capture-stream/`,
developer and production images built from this worktree under swarm-build;
SHA-256s below).

- `native-auto1` (the tree before the budget override was routed through
  both wrappers): `tests.test_native_checkpoint_auto`: the positive case
  PASSED on the first run (the owner logged `CHECKPOINT auto sequence=64
  suffix=64 octets=N ms=M`, the file had N octets, the next open read
  `open=checkpoint:64 suffix=0`, the observation equalled the full replay's
  with the file aside, and `store checkpoint` republished the same bytes);
  the deferral case found its `CHECKPOINT deferred reason=exceeds-budget
  estimate=E budget=1024 sequence=64` line and then FAILED at "no retry":
  the developer override applied only at the publication while the due
  path compared the deferral against the profile's budget (92 MB), so the
  owner retried and deferred again. Classification: implementation (of the
  test hook's plumbing), fixed by handing the one budget to both wrappers
  (`fn-owner-sco-budget`). `tests.test_native_checkpoint`: OK (skipped=3).
  `tests.test_native_state_checkpoint`: 5 of 6 passed (every cut of
  `fn-bs-scp-program`, SIGKILL and EIO, through both entries, reopened
  with the old or the new checkpoint as the cut map says); the one failure
  is `StateCheckpointSourceTests.test_the_host_calls_the_keystone_subject_and_writes_the_program`
  asserting `(fn-sco-store-open e config-records frontier)` in
  `fn-store-sn-open-extended`, a source line that dev's `2e25e21b` (PKT-444
  (1), `fn-sopc-classified-open`) replaced before this lane branched: stale
  on dev, unrelated to this lane's files (host/store-node-host.lisp is
  untouched here). Classification: harness (a stale source assertion).
  Logs: `test-tests.test_native_checkpoint_auto.log`
  4bd2eca16a340d3a2a245e9d934411e781175e1f0ef1203426de9a41c905f7d2,
  `test-tests.test_native_state_checkpoint.log`
  92d2493daeae351cb84b0c2eaf32a06a6a5204d6cdfd91085f1448d00f0bdc26,
  `test-tests.test_native_checkpoint.log`
  cd1328c0b8493fd7888c499f7c10dec43ef4db96c0f0fa96285e607fb265278d;
  images `fn-host-developer.core`
  8e35b3f00062afc9007e9d9cd788731c472a3fac3fa4130e2634b16c372337d3,
  `fn-host.core` bb88f000a3f200b4940b53595932e6204cda8d4a301c953e0fcafa6fc58241bf.
- `native-auto2` (the final tree, the budget override on both wrappers):
  `tests.test_native_checkpoint_auto` **OK, 3 of 3** (the source test; the
  automatic publication after 64 POSTs with the file's octets as logged, the
  reopen `open=checkpoint:64 suffix=0` equal to the full replay, the verb
  byte-identical; the deferral by name under a 1,024-octet test budget with
  the estimate above it, no file, two more POSTs accepted, no retry within
  five seconds of accepts, the running `status` line
  `checkpoint-file=absent deferred=exceeds-budget estimate=E budget=1024`,
  the offline `status` unchanged, and a fresh owner under the profile's
  budget publishing at 66). Log
  `planning/evidence/checkpoint-capture-stream-2026-09-26/test-tests.test_native_checkpoint_auto.log`
  65d7e63a88e583907f2dc4fa5a17fac49281f820426062f4d3883f7392e9a217; images
  `fn-host.core` 229a09efeae567061a8557573ea41f6dd28b0328284bace8390e969631d280ad,
  `fn-host-developer.core` 7b7371c8b399d98b7aec0c5641dd5a44ba2d10dfa11869e9ff5ded52293e7dee
  (`native-auto2-SHA256SUMS` beside the log). The cut map:
  `tools/native_program_check.py` PASS (0 mismatches over 6 programs) on this
  tree; `verify_state_checkpoint_cut_map` runs inside the module's source
  test.

## 5. The measurement: N = 40,000 x 2 KiB on tmpfs, dynamic space unchanged

The case that could not run: `tools/service_envelope.py measure --steps load
--load-to 40000` (the scale-1m profile, 2 KiB articles, one in 256
hybrid-signed, the envelope's own harness) on hbox, tmpfs (`/dev/shm`), ONE
owner process posting from 0 with no restart, in `ccs-t40k-load-a` under
`systemd-run --user -p MemoryMax=40G -p MemorySwapMax=0`, the production
image of `native-auto2` (`fn-host.core`
229a09efeae567061a8557573ea41f6dd28b0328284bace8390e969631d280ad) whose
launcher passes `--dynamic-space-size 32000` exactly as before (not raised;
the checkpoint interval K not raised; the store not built offline). Driver
`ccs-40k.sh` beside the JSON. The box carried a qualification
(`qual-dfa810fc`, three units at MemoryMax=24G, about 1 GB used each) and
its certify run; load average about 7.

**The owner reached N = 40,000 alive**: 40,000 POSTs in 669.8 s (14:47:00Z
to 14:58:10Z), 994 s of owner CPU, memory at the end RSS 4.25 GB, **VmHWM
5.55 GB** (`hwm_kib` 5,549,868); the unit's `MemoryPeak` 5.8 GB. Before
(same harness, the image after served-path-scale): the owner died at
32,729 with the heap at 31.7 GB and, restarted, at 36,208 with VmHWM 29.7 GB.
The high-water mark is 5.4 times lower and the two death points are passed
without a restart.

**Every automatic checkpoint** the owner published (its `CHECKPOINT auto`
lines, `t40k-load-a-owner.stderr`): sequence, suffix, octets, ms:

| sequence | suffix | octets | ms |
| ---: | ---: | ---: | ---: |
| 2,131 | 2,131 | 16,767,220 | 2,571 |
| 4,226 | 2,095 | 33,296,133 | 3,849 |
| 6,447 | 2,221 | 50,762,060 | 6,196 |
| 8,577 | 2,130 | 67,524,502 | 9,118 |
| 10,661 | 2,084 | 83,968,422 | 9,200 |
| 12,887 | 2,226 | 101,473,111 | 11,335 |
| 14,998 | 2,111 | 118,125,830 | 15,670 |
| 17,058 | 2,060 | 134,347,259 | 21,508 |
| 19,118 | 2,060 | 150,568,678 | 21,470 |
| 21,211 | 2,093 | 167,045,207 | 26,925 |
| 23,319 | 2,108 | 183,637,701 | 34,427 |
| 25,428 | 2,109 | 200,237,915 | 35,422 |
| 27,522 | 2,094 | 216,759,214 | 37,933 |
| 29,593 | 2,071 | 233,065,668 | 42,049 |
| 31,642 | 2,049 | 249,202,062 | 46,936 |
| 33,782 | 2,140 | 266,041,922 | 39,673 |
| 35,841 | 2,059 | 282,255,611 | 46,884 |
| 37,911 | 2,070 | 298,554,335 | 57,787 |
| 39,996 | 2,085 | 314,969,009 | 54,164 |

Nineteen publications, none deferred (the scale-1m budget is about 12.9 GB;
the largest file 315.0 MB), none refused, none failed; the octets column is
ACL2's estimate, which is the file's length (`fn-ockb-file-len-is-len-file-octets`)
and what `fnn-plan-write-all` wrote. The capture's time still grows with N
(2.6 s at 2,131 to 54 to 58 s at 37,911 and 39,996: the freeze's index-records walk, the
three walks over the tree and the encode are each linear in the history,
and the history is octet lists on the heap; before, 90.1 s at 29,453 with
the heap dying), and it runs on the publication thread while the served
path continues: the load's POST rate did not pause visibly at the captures
(1,000 POSTs every 15 to 30 s throughout). No `Heap exhausted` line; no
connection lost; no uncertain POST (the load's `uncertain_post_was_stored`
never set). Files beside this record: `t40k-load-a.json`
(0ab2a65304ce40ed2ce639e4c550216863b0c75338fda60703059a7d23c556a7, the
harness's rows: the open, the load row with `memory`), `t40k-load-a-owner.stderr`
(587dd761031f1b44c24b5fb9f6a97100744d02ae9b58f488298507e229e01193: the
owner's 40,000 `accepted` lines, its OWNER-OPEN and the nineteen CHECKPOINT
lines), `ccs-40k.sh` (the driver).

**The reopen from the automatic checkpoint** (`ccs-t40k-reopen-a`, the same
unit shape, `--steps restart`): the owner opened the 40,000-article store
with `OWNER-OPEN open=checkpoint:39996 suffix=5` in 63.4 s (63.3 s of owner
CPU), RSS 8.21 GB, VmHWM 8.45 GB, reading the 314,969,009-octet file the
owner had published (`t40k-reopen-a.json`
fc1c2cabf93374a3ae2a4200eb7d15fce7836e2a87b87388729d0036d75e68b3,
`t40k-reopen-a-owner.stderr`
803d1792b407f92c75adb8bf8deb6f8c88b01a0d44251aa591911182b4b171a4). The
reader is untouched by this lane (rep-wave-d-3's buffer decoder), and its
figure sits beside the old image's reopen at 36,208 (51.2 s from
`checkpoint:32730 suffix=3479`, VmHWM 8.2 GB): the decoded value is the
same value at sixteen bytes per octet, which is the arena's result, not
this lane's.

**The throughput gate's checkpoint phase** (`tools/throughput_gate.py run
--image <native-auto2 fn-host-developer> --revision d5b0cdf1 --label ccs
--under-load --wait-quiet 0`; JSON
`throughput-gate-d5b0cdf1c375-ccs-under-load.json`
29a8a9c5e01807c51adac075aea404a3c5799fb4d8f9bb9090e9da13039bf844 beside
this record, not under planning/evidence/throughput/, per the brief; the
box busy 0.523 with the 40k load, the qualification and its runs live): 64
POSTs of 31,744 octets on the development profile, the owner published at
K/2: `checkpoint_sequence` 64, `checkpoint_octets` 6,196,494,
`checkpoint_publish_ms` 670. Under load the gate compares only the
deterministic counter (PKT-477 (1)): `probe_bytes_consed_per_commit`
1,406,383 against the baseline's dev 1,651,892 and floor 262,144: passed
(the POST path is untouched here; the figure is the box's). The checkpoint
phase's wall-clock, 670 ms against the baseline's 350 (release) and 405
(dev) ms, is NOT compared under load and is not a comparison: the old
figure is the list codec on a quiet box, this one the buffer path on a box
at 0.52 busy; a quiet run of both is owed (PKT-494 (5)). What the buffer
path adds per publication is three linear walks before the encode
(`fn-sccb-treep`, the estimate, `fn-sccb-plan`'s own `fn-sccb-treep`) and
one concrete write per octet inside `fn-oct-write-list`; what it removes is
the five to six list copies of the file. At 6 MB either is well under a
second; at 315 MB only the buffer path finishes.


## 6. Not done (PKT-494), and the deferrals

- The publication buffer's array is kept at the largest file's size between
  publications (cleared, not shrunk): one file's bytes, one byte per octet,
  retained by the owner process.
- The deferral is per owner process: `fn-owner-sco-deferred` is nil at
  open, and lifts only when the budget covers the recorded estimate or at
  the next start. An operator raising `max-history-octets` live has no path
  (`store upgrade-profile` is offline, so the owner restarts anyway).
- The frozen checkpoint value still costs the records twice on the heap
  while it is encoded (PKT-314), and the three walks before the encode
  (`fn-sccb-treep`, the estimate, `fn-sccb-plan`'s own `fn-sccb-treep`)
  each touch every payload octet as a cons at sixteen bytes; the arena
  (PKT-293/PKT-167) removes both. The estimate is recomputed from scratch at
  each publication (O(N)); a carried per-record length would make it
  O(suffix).
- (5) The checkpoint phase's wall-clock on a quiet box, buffer path against
  list path at the gate's 6 MB (this run: 670 ms at box busy 0.52 against
  the quiet baseline's 405): not compared, owed.
- The natural deferral (a real profile whose admitted history's checkpoint
  exceeds 3H + framing) is not exercised natively: no preset reaches it and
  the geometry with tiny bounds is borderline (section 3), so the native
  case uses the developer selector; the ACL2 teeth exercise the boundary on
  both sides with the real function.
- The health reply (`fn-nh-verdict`, eight states with exit codes) does not
  carry the deferral; `status` does, on its checkpoint-file line.
- The docs paragraph on `status` grew, so the generated grammar book was
  regenerated (PKT-493 stands: the book still cites line numbers).
- `tests.test_native_state_checkpoint`'s source assertion on
  `fn-store-sn-open-extended` is stale on dev (section 4); not repaired here
  (another lane's file and test).
- PKT-495 (for ember): the budget's derivation, section 3.
