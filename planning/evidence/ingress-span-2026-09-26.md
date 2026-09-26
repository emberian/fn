# Ingress span: the wire machine's read over the octet buffer, 2026-09-26

Lane `lane/ingress-span`, from dev `dfa810fc`, under the Fable mandate
(`planning/handoff-2026-09-25-fable-mandate.md` §7; D27). Brief:
`build/coordinator/queue/done/w4-ingress-span.txt`. Registry: PRF-181,
REP-012, SCN-110, PKT-479, PKT-480. This is PKT-302 (iv), the ingress half of
rep-wave-d's program; its scope stops at the intern boundary (rep-wave-d-4's).

## 1. What a node does now that it did not before

A socket read no longer expands into a long-lived cons list on the served
hot path. Before this lane, `host/native/owner.lisp fnn-owner-handle-chunk`
coerced every socket read to a list (`fnn-octet-list`, a 512-element cons list
per read) and fed it to `fn-owner-chunk`, whose served fold
(`fn-scar-feed-counted` -> `fn-scar-feed-byte`) rebuilt the ten-field
connection record (`fn-served-make-conn-group-indexed`) once per byte and the
eight-field wire state once per byte. A 32 KiB POST allocated 20.8 MB, 635
bytes consed per payload octet, 59% of its CPU in that per-byte feed
(`planning/evidence/rep-wave-d-2026-09-25.md` §1.2).

Now the host fills the octet buffer (`fn-octets`) once from the socket byte
vector (`fnn-octets-fill`) and calls `fn-owner-chunk-span`, which reads the
range in place. `books/served-span.lisp fn-scar-feed-span` is the carried
served fold `fn-scar-feed-counted` reading the range's bytes by index
(`fn-octets-get`), so no octet of a read is ever a cons cell: the 512-element
per-read list (`fnn-octet-list`) and the list walk it drove
(`fn-ag-cdr`/`fn-wire-ag-cdr`) are gone from the served hot path. The wire
machine's own whole-span read over the buffer is proved in
`books/wire-span.lisp` (`fn-wire-feed-span`) and is the foundation the
per-framed-event served fold (PKT-479) calls.

## 2. The proof boundary

The subject the host calls is `fn-owner-chunk-span` (host/owner-host.lisp)
-> `fn-scar-ocfg-read-span` (books/served-span.lisp). The logical model stays
the octet-list byte machine of books/wire.lisp; the correspondence is proved,
not assumed.

- KEYSTONE `fn-scar-feed-span-is-feed-counted` (no hypothesis): the served
  buffer fold `fn-scar-feed-span conn i end ... fn-octets` reads the range's
  bytes by index and is EXACTLY the carried list counted fold
  `fn-scar-feed-counted conn (fn-oct-slice-list i end fn-octets)` -- byte for
  byte, the buffer's cell i being the slice's car and [i+1, end) its cdr. So
  the served read decides exactly what the list read decided. Guard-verified;
  `fn-scar-feed-span-consumed-is-natural`.
- Wire-level foundation (PKT-479): `fn-wire-feed-span (wire-state i end
  fn-octets)` (books/wire-span.lisp) is the fold of `fn-wire-feed-byte` over
  the buffer's range, and KEYSTONE `fn-wire-feed-span-is-feed-proper` (through
  `fn-wire-span-fold-is-feed-proper`) says its (state, events) equals
  `fn-wire-feed-proper` over `(fn-oct-slice-list i next)` -- the reference byte
  machine on exactly those octets, whose partition law
  `fn-wire-feed-proper-append` composes reads. This is the wire read the
  per-framed-event served fold will call; it is not on the live host path yet
  (the live fold is per byte).
- KEYSTONE for the host line
  `fn-scar-ocfg-read-span-is-reference-under-ocl-relation`: under the
  configured owner's relation (`fn-ocl-relation`) and its view trie's
  correspondence, the span read `fn-scar-ocfg-read-span oc id i end fn-octets`
  is `fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets)` -- the
  list read the existing served path already establishes as correct
  (`fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation`). The read
  keeps the store (`fn-scar-ocfg-read-span-keeps-store`) and its node premise
  (`fn-scar-ocfg-read-span-preserves-node-premise`).

Teeth (tests/acl2/wire-span-tests.lisp, served-span-tests.lisp): a ground
positive witness that a dot-stuffed line and a line split across two reads is
framed identically to the reference; the `:line-overlimit` refusal is the
reference's; one `must-fail` per guard hypothesis of each keystone (octets-p,
range-within-buffer, fast-statep; ocl-relation, view-indexedp, natp start).
`fn-scar-feed-span-is-feed-counted` has no hypothesis, so no must-fail; its
witness is the equality on ground.

## 3. Measurement

Done by the continuation: section 7.3 (the per-read list was 2.5% of a
32 KiB POST's allocation; 521,799 bytes per POST removed).

## 4. Native gate (SCN-110)

Done by the continuation: section 7.2 (SCN-110 byte-identical to the
reference image at 33 KiB, 200 KiB, 3 MiB and split dot-led lines).

## 5. Not done

- PKT-479 (the bulk of the measured win): (a) the served fold still rebuilds
  the ten-field connection once per byte -- dispatching per FRAMED EVENT
  instead (the wire already frames a whole body in one span) removes it, but
  the byte-stepping correspondence `fn-scar-feed-span = span+dispatch` runs
  over the connection machinery and exceeded the <10 s book budget; (b) the
  wire still rebuilds the eight-field state per byte -- a per-line index scan
  (next CRLF by `fn-oct-line-end`, line limit by subtraction) removes it, but
  its scan=fold keystone did not close under the ACL2 rewriter within budget.
  Both are lemma-engineering, not soundness gaps. This lane removes the
  per-read list and the list walk (D27) and proves the buffer read is the
  reference; (a) and (b) are the residual per-byte allocation.
- PKT-480: PKT-316's collection-trigger placement is the coordinator's call
  (one line, then a matched rerun); this lane does not decide it.
- The submission still holds the article body as an octet list; the seal to a
  buffer range is rep-wave-d-4's (§interface in the LANEDUMP).

## 6. Certification

farm persvati: run-20260926T143838Z-e0fd (served-span, served-span-tests)
and run-20260926T141822Z-1776 (wire-span, wire-span-tests). Manifests in
`planning/evidence/manifests/`.

## 7. Continuation (ingress-span-2, 2026-09-26)

Deputy 4's continuation on the same worktree: merge, native gate, the
measurement. No theorem and no span-book statement changed.

### 7.1 Merge and certification

`git merge dev` at `253fd623` was clean (merge commit `ab0fc69d`); the
host files carry exposure-reply-size's `fn-owner-exposure-observe` and
hot-path-scans-2's count beside `fn-owner-chunk-span`, which installs what
`fn-owner-chunk` installs. `tools/ledger.py --write` refreshed proofs.json
(`76c4a215`). REPL on persvati (`~/fn-gates/ingress-span-2-repl`):
wire-span (31 forms), served-span (25) and wire-span-tests (25) loaded to
the end; served-span-tests needed served-span certified at the merged bytes.
ONE farm run, persvati `run-20260926T150048Z-7f36`, over served-span,
wire-span and their test books: 2 certified, 157 from the cache, 0 failed,
no book over 10 s; manifest
`planning/evidence/manifests/certify-20260926T150139Z-3186820.json`.

### 7.2 Native gate on hbox (SCN-110)

Images built by `tools/hbox_native.sh --name ingress-span-2 --label after
--images developer,production --mem 40G` from the merged worktree
(`76c4a215` + the SCN-110 test): developer launcher `f8139d30...`, core
`0aff32f8...`; production `e0d2d453...`, core `0a50e0ae...`. The
reference image is dev's throughput-gate image at `f314a5a3`
(`/tank/fn/scratch/throughput-gate/native-img-f314a5a3/tree/build/fn-host-developer`,
core `fe6c8b22...`), whose owner still coerced every read to a list and
called `fn-owner-chunk`; `git log f314a5a3..253fd623 -- host/` is empty,
so the two images differ in the served read only. SHA-256 lists:
`ingress-span-2026-09-26/native-run1-SHA256SUMS` (first run, every module)
and `native-run2-SHA256SUMS` (rerun of the three repaired modules, the
measurement JSONs).

| module | result | log SHA-256 |
|---|---|---|
| tests.test_native_bounds_join.SpanReferenceTests (SCN-110) | OK (1 ran) | `cd9a7ee278379f88...` |
| tests.test_native_bounds_join.LargeArticleTests (33k/200k/3M, A+1 441) | OK (1 ran) | `35690802fa185b76...` |
| tests.test_native_bounds_join.LargeReplyTests (1/2/3 MiB ARTICLE, 4 MB OVER) | OK (1 ran) | `0be1a64380f5...` |
| tests.test_native_served_differential | OK (7 ran) | `189d8adc53a0...` |
| tests.test_native_public_exposure | OK (1 ran) | `17e3255785ae...` |
| tests.test_native_nntp_post_probe | OK (13 ran) | `873e8261007e...` |
| tests.test_native_served_cost | OK (4 ran) after the repair below | `f00e47032fc9...` |
| tests.test_native_owner | 16 of 18; the two failures classified below | `170b5552a9c6...` |

SCN-110's rows (SpanReferenceTests; the same POSTs to both images on
fresh 4 MiB-article stores, the ARTICLE octets compared with the injected
Date and Injection-Date values masked): 33,792 octets 240, served 33,895
octets, SHA-256 prefix `8aa62f45bf0b2aea` on both images; 204,800: 240,
204,903, `f576654dc7d23b46` both; 3,145,728: 240, 3,145,831,
`8645a3232de116ca` both; 200 dot-led lines (one to three leading dots)
written in 7-octet pieces, so dot-stuffed lines split across reads: 240,
4,307, `0c848926c3d353c1` both. Every POST reply and ARTICLE status line
agreed; each re-read the posted body. The first run differed only in the
injected `Date:` value (the wall clock; the test masked only
Injection-Date then): a harness defect, repaired in `83280a25`.

Failures, classified:
- `test_native_served_cost` (harness, this lane's): the check
  `test_span_fold_allocates_nothing_inside_a_line` asserted
  `fn-wire-span-scan`, the per-line scan that did not land (PKT-479 (b)).
  Replaced by the landed property: `fn-scar-feed-span` reads the buffer by
  `fn-octets-get` and never names `fn-oct-slice-list` or `fn-octets-list`.
- `test_the_chunk_loop_keeps_its_suffix_and_reads_a_clock_per_step`
  (harness, this lane's and dev's): its stubs knew only `fnn-owner-action
  'fn-owner-chunk`; the span handoff calls `fnn-octets-fill` and
  `fnn-owner-buffer-action 'fn-owner-chunk-span`. The stubs now record the
  range [start, end) as the step input (expected chunks unchanged), and the
  list arm is gone, so a return to the list entry fails the test. Dev
  fails the same test for another reason: friends-accounts-2's
  `fn-acct-host-owner-redeem-waitingp` had no stub (stubbed now). Passes.
- `test_developer_selectors_gate_arm_the_owner_and_stop_synchronously`
  (harness, dev's; not repaired here): `tests/native_developer_selectors_raw.lisp`
  loads host/native/io.lisp raw, whose `+fnn-exit-ok+` is
  `(fn-outcome-code :accepted)` since `cd64c1ea`; the raw script defines
  no `fn-outcome-code`. This lane changes neither file.
- `test_two_client_uncertainty_fences_before_later_mutation`
  (implementation, dev's; intermittent; not repaired here): the poster
  sometimes reads a bare close instead of `441 ... do not repost`.
  Measured on hbox, the single test 40 times per image: span image 7 of
  40 failed, reference image (`f314a5a3`) 6 of 40 failed (the same
  assertion; `ingress-span-2026-09-26/flake2.out`); an earlier 15-run pair
  read 4/15 and 0/15. The owner's stderr in a failing run: `uncertain post
  ... connection=0` then `owner connection-local fault; service continues:
  send-reply: [Errno 32] Broken pipe`. Cause: `fnn-owner-run`'s cleanup
  calls `fnn-owner-stop-service` again, and `fnn-owner-stop-service-locked`
  shuts every client socket but the `answering` one it is passed, and the
  cleanup passes none; when the main thread's cleanup wins the mutex before
  the answering worker sends, the reply meets EPIPE. The fix (for the
  coordinator; outside this lane's chunk-handoff scope): keep the answering
  socket in the service at the first stop and spare it on every later one.

### 7.3 The measurement (hbox, matched harness, box under load)

Bytes consed per 32 KiB POST: `tools/rep_measure.py` alloc phase (K = 32
POSTs of 32,768 octets bracketed by SBCL's `get-bytes-consed`, after 256
POSTs of load, default profile, store on /dev/shm), the same tree's
harness on both images, the heap hook `rep-wave-d-2026-09-25/heap.lisp`
loaded before the entry by a launcher copy (`--load` ahead of
`(acl2::sbcl-restart)`: the same core, no rebuild), alternating before,
after, before, after (`ingress-span-2026-09-26/alloc.sh`,
`{before,after}-r{1,2}.json`). Load average 12 to 14 throughout (a
qualification, a candidate's tests and other lanes' measurements).

| image | r1 | r2 | mean |
|---|---|---|---|
| before (`f314a5a3`, per-read list) | 20,969,476 | 20,969,380.5 | 20,969,428 |
| after (span) | 20,449,173 | 20,446,084.5 | 20,447,629 |

The span read conses 521,799 fewer bytes per 32 KiB POST: 15.9 bytes per
payload octet, one 16-octet cons per octet, which is exactly the per-read
list (`fnn-octet-list`) it removed. That list was 2.5% of the POST's
allocation; the other 97.5% (about 624 bytes per payload octet) is PKT-479.
The ARTICLE's allocation is unchanged (5,819,160 and 5,815,442 / 5,818,761
bytes per 32 KiB ARTICLE), as it should be: the read path of a reply is not
this lane's. The POST median in the same run, under that load: 27.4 / 27.1
ms before, 26.0 / 24.0 ms after (a timing under load, not a claim).

Owner CPU per 32 KiB POST (`ingress-span-2026-09-26/cpu32.py`, the
gate's served row on the default profile, which admits 32 KiB: 8 warm-up
POSTs, then 120 POSTs of 32,768 octets on one connection, the owner's
utime+stime over the window; /dev/shm; three alternating rounds;
`cpu32.json`), load average 15 (one-minute) throughout:

| round | before ms | after ms |
|---|---|---|
| 1 | 37.08 | 30.83 |
| 2 | 35.75 | 34.75 |
| 3 | 30.00 | 29.50 |
| mean | 34.28 | 31.69 |

The after mean is 2.6 ms (7.5%) lower, but the rounds spread 7 ms under
this load: no CPU claim beyond "not worse". The allocation figure above is
the deterministic one.

The throughput gate (`tools/throughput_gate.py run --under-load
--wait-quiet 120`; the JSONs are in `ingress-span-2026-09-26/`, not
planning/evidence/throughput/): after (`76c4a215`, run
`20260926T151817Z`, box CPU busy median 0.31, loadavg 9.1) and before
(`f314a5a3`, `20260926T152143Z`, 0.27, 10.2), both `quiet: false`. The
deterministic counter, bytes consed per store commit, is 1,406,515 on
both (the commit loop does not touch the served read: the control).
At the gate's 2 KiB POST: owner CPU 2.2 ms after against 2.0 before,
median 1.891 against 1.784 ms (the gate itself names post_owner_cpu_ms as
not comparable under load: 1.9 and 3.1 ms for one image); ARTICLE median
2.814 against 2.790 ms; signed POST owner CPU 80.8 against 84.4 ms.

### 7.4 PKT-479 restated, PKT-480

PKT-479 (ranked by the measurement; a Fable item, not this lane's): the
per-read list was 2.5% of a 32 KiB POST's 20.97 MB; the 20.45 MB left are
(a) the served fold rebuilding the ten-field connection once per byte
(dispatch per framed event instead) and (b) the wire rebuilding its
eight-field state once per byte (the per-line index scan), with the
record's own list after them (rep-wave-d §1.2: `fn-record-payloadp` 10% of
CPU). PKT-480 is decided by the coordinator: keep the 64 MiB trigger in
fnn-main as it is until the performance ledger ranks it.

### 7.5 Assurance chain for the slice

native entry `fnn-owner-handle-chunk` (host/native/owner.lisp; fills
`fn-octets` with `fnn-octets-fill`, the A-HOST fill boundary) ->
`fn-owner-chunk-span` (host/owner-host.lisp) -> executed subject
`fn-scar-ocfg-read-span` over the buffer range -> refinement
`fn-scar-ocfg-read-span-is-reference-under-ocl-relation` and
`fn-scar-feed-span-is-feed-counted` (the span read is the list read over
`fn-oct-slice-list start end`) -> maintained relation `fn-ocl-relation`,
established at the owner's open and preserved by the list read
(`fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation`, the
existing served path), which the span read equals; the store and node
premise kept (`fn-scar-ocfg-read-span-keeps-store`,
`-preserves-node-premise`) -> behavioural theorem: the reference served
read's -> observed result: SCN-110 byte-identical to the list image at
33 KiB, 200 KiB, 3 MiB and split dot-stuffed lines; 521,799 fewer bytes
consed per 32 KiB POST.
