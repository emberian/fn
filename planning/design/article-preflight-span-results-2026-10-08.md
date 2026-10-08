# s-xc2 span implementation evidence, 2026-10-08

NOT READY. Round 6 merges P and removes the last served scalar prefix read,
but two requirements remain open: the loop-call ratchet is 129 against 123,
and P's single span export can miss a later cached window after selecting
an earlier exhausted window. No push. The latter is recorded as
`planning/repair/items/EXTENT-CACHE-SPAN-COVERAGE.json`; P owns that book.

## Round 6 commits

- `390c1f177`: merge origin/lane/p-xc-span@95d685b69. The only conflict was
  planning/interfaces.json, restored from the incoming branch and regenerated.
  P's proof books were merged without edits.
- `04765fb2c`: prefix equality and teeth statement, committed before proof.
- `fd6f3bf2f`: proved span prefix, unchanged public guard, real-arena teeth.
- `6dbb26aea`: native fn-xc-span-at seam, duplicate/present uncached result,
  declared interface and generated host worlds/interface manifest.
- `3f4a6328f`: warm raw-cache host-path test and shared native closure loader.

Earlier accepted S1/S3 proofs and implementation are in 5e1aaea3f,
4b5cc6ad1, f9b52c012 and fc7817600. This round's affected certification
covers their current dependency closure, including the new prefix book.

## Prefix statement committed before proof

For the same arena state, handle H, prefix and offset I, the new span prefix
predicate equals the existing byte prefix predicate whenever `(natp i)`.
This is the existing premise of `fn-nntp-arena-prefixp-is-rcl-prefixp`, and
is already in the public prefix function's guard; no new caller premise
is added. Neither arena well-formedness nor prefix bounds are theorem
premises. The implementation checks the complete prefix's bounds locally
before its single `fn-arena-get-span` call; an empty prefix needs no read,
and a prefix that cannot fit returns nil. The public function keeps the
old byte predicate as its logical meaning, with the proved span predicate
as its executable arm. Its original guard stays unchanged.

The positive witness uses the actual eight-octet reclaim magic followed by
payload data in an arena. The negative witness changes the eighth octet:
the correct predicate refuses it, while a mutant that drops the last
prefix octet accepts it. A must-fail event asserts their false equality.

The theorem is `fn-nntp-arena-prefixp-span-is-byte`,
books/article-arena-reads.lisp:56. Persvati admitted it in 4,253 steps / 0.03 s;
its wrapper and consumers verified guards unchanged. The six-form teeth
session admitted every form (0 refused), including the must-fail. Positive,
changed-last-octet, insufficient remaining bytes and empty prefix cases are
in tests/acl2/article-arena-reads-tests.lisp.

## Served caller inventory

Original mechanism: host/native/owner.lisp:842 fnn-owner-render-next-quantum
-> :786 fnn-owner-ready-plan-step -> host/owner-host.lisp:4613
fn-owner-article-ready-plan-step -> books/article-stream-owner.lisp:620
preflight scan -> source-byte -> fn-arena-get -> durable scalar realizer
-> extent lock. Preflight now calls fn-ast-scan-step-span; a readable source
uses fn-arena-get-span. Its fallback cannot read a durable byte because the
source is unreadable. Render uses fn-ast-render-window (:926) -> aux-chunk
(:881) -> render-one-chunk (:797); readable payloads use spans (:807).
Metadata pieces are literals/decimal pieces, not the generic :span variant.
The generic byte renderer remains the model; readable served payloads are
intercepted by the chunk renderer.

ARTICLE/HEAD/BODY tombstone checks at article-stream-owner.lisp:358/:529,
OVER at served-columns.lisp:260/:266, and HDR Xref at
nntp-reader-compat.lisp:316/:475 all call fn-nntp-article-tombstonep.
Its arena arm now reaches article-arena-reads.lisp:70 (the MBE executable
arm) -> :53 fn-arena-get-span. The byte predicate at :19 is the logical
model and a test reference only. Public guards were not changed.
OVER/HDR column fallbacks read whole payloads through fn-arena-payload;
they do not call the durable scalar realizers. Thus the traced valid
ARTICLE/HEAD/BODY/OVER/HDR execution paths contain zero scalar realizer
calls. This is a source-chain inventory, not a new reachability theorem.

Remaining direct scalar-realizer references, excluding declarations,
comments, theorem terms and tests:

| Caller | File:line | Execution scope |
| --- | --- | --- |
| fn-arena$x-get -> fn-durable-realize-octet | books/payload-arena-extent.lisp:461 | Generic scalar arena API; no traced served command calls it after span routing. |
| fn-arena$x-get -> fn-durable-realize-lz-octet | books/payload-arena-extent.lisp:463 | Same generic scalar API. |
| fn-durable-span-spec -> fn-durable-realize-octet | books/assumptions-durable.lisp:106 | Logical raw-span model; native span overrides this seam. |
| executable counterpart -> fn-durable-realize-octet | host/native/extent.lisp:1720 | Scalar forwarding wrapper, no traced served caller. |
| executable counterpart -> fn-durable-realize-lz-octet | host/native/extent.lisp:1895 | Scalar forwarding wrapper and independent native test reference. |
| fn-durable-realize-octet -> fnn-extent-window-realize-octet | host/native/extent.lisp:1715 | Scalar window route, no traced served caller. |

Other generic scalar users: legacy-parser-cursor.lisp:266/:331 and
legacy-header-query.lisp:39 are unwired; nov-piece-window.lisp:70's :span
piece is unreachable-in-composition for the ARTICLE metadata producers
(article-stream.lisp:421/:525/:586). query-payload-scalar.lisp:33 belongs
to the parked captured POST adapter (host/native/post-captured-parked.lisp).
consumer-remote-visible-buffer.lisp:135 is an internal collection writer
whose report-advance adapter has no public issuer/native call. The native
current-octet acquisition helper at extent.lisp:797 has no native caller.

## Raw cache seam and cost scope

host/native/extent.lisp:744 fnn-extent-window-cache-run holds one extent
lock, obtains backing via ACL2's fn-xc-lookup result, and calls fn-xc-span-at
once. ACL2 computes j, copies bytes and touches recency. The host candidate
loop and j computation are gone. The new interface declares kinds in book
formal order and cites all three export keystones; the unused
fn-owner-page-window-cache-span-at definterface was removed.

fnn-extent-window-cache-insert (:832) returns the exact row token for release
and cachedp=nil on :present/:duplicate, without fault or backing replacement.
The raw release and decoded cache-attempt propagate cachedp; the already
cached ledger row is evicted through the existing exact release operation.
The kernel duplicate/disjointness teeth are P's tests/acl2/extent-cache-span-tests.
The warm fixture does not claim a new native exercise of P's duplicate branch.

A warm 2 KiB payload fitting one window and one owner quantum needs one
full-payload span realization for preflight and one for rendering: two locks
for those passes. The two owner tombstone checks each add one short span
lock when both execute: **four span-read lock acquisitions in that case**,
plus other control/ledger locks. This is O(1), not the W2L per-octet shape.
The two-lock whole-reply target is not measured or claimed; no W2L rerun or
rebuilt native image was made. Longer payloads count window/quantum/span
intersections. The coverage gap below prevents claiming all warm stretches
are served from cache by the current one-call export.

## Warm native host-path tests

On persvati, from /home/ember/fn-gates/s-xc2-repl:

```sh
FN_XC2_NATIVE_CORE=/home/ember/fn-gates/sxc-c3/native-sxc-9b6958f93/tree/build/fn-host-developer.core \
FN_XC2_SBCL=/tank/fn/sbcl/bin/sbcl \
timeout 45 python3 -m unittest tests.test_native_extent_cache_span tests.test_native_extent_decoded_span -v
```

Raw test ID:
`NativeExtentCacheSpanTests.test_warm_raw_extent_is_one_span_export_and_preserves_cold_miss`.
It admits the current P span definitions and guards in the warm developer
ACL2 session, then loads this tree's native function closure. It drives
actual pread/digest/return/cache transitions over a real 2048-byte extent,
compares every byte and observes exactly one fn-xc-span-at dispatch. Tail,
zero and exact cold-descriptor identity miss are checked. There is no
realizer, hit-decision or dispatcher stub; counting forwards every dispatch.

Decoded test ID:
`NativeExtentDecodedSpanTests.test_actual_compressed_extent_span_matches_scalar_across_window`.
Actual compressed preads and private decoder jobs feed slot-cache reads;
span = scalar = original bytes for 2048 bytes, [16380,16396) across a decoded
window boundary, tail and zero. Both tests use the warm core's existing
structure/startup layout and unchanged lookup/touch/window ABI plus current
native seams. They are not full-image integration evidence. The helper
native_extent_span_loader.lisp loads the complete current extent-function
closure rather than shadowing dependencies with stubs.

## Generators and gates

Commands run:

```sh
git show origin/lane/p-xc-span:planning/interfaces.json > planning/interfaces.json
FN_LAPTOP_OK=1 python3 tools/interface_emit.py --write
python3 tools/extract/world.py
FN_LAPTOP_OK=1 python3 tools/interface_emit.py --write
```

The world generator placed extent-cache-span in image-world-part-2,
image-world-dtn-part-2, image-world-store-test-part-1 and the two extraction
world files from host/page-read-host.lisp's include row. No generated file
was hand-merged. Interface generation was rerun after declaration changes.

Persvati REPL: prefix theorem/guards/teeth admitted; P's whole span book
loaded 16 forms in 5.56 s / 2,165,718 steps. The coverage witness below is
REPL evidence, not a new certified repository theorem.

```sh
timeout 180 python3 tools/farm.py submit persvati --lane \
  --affected-by books/article-stream.lisp \
  --affected-by books/payload-arena-extent.lisp \
  --affected-by books/article-arena-reads.lisp \
  --affected-by books/extent-cache-span.lisp --jobs 2
```

run-20261008T153641Z-62b0 / certify-20261008T153712Z-752406:
16 roots, 474 books in the affected dependency closure, 369 cached,
105 newly certified, 0 failures, 229.135 s. Current proof forms are covered;
the manifest's revision is the pre-commit dirty snapshot used for submission.
No laptop certification or image build. Triage: real 0 / cascade 0 /
must-fail 0 / limit 0 / killed 0 / other 0; echo 3, clean 102.

D26 overs at two jobs: article-select-index 12.143 s, article-stream-owner
11.286 s, heap-store-figure 10.349 s, history-paged 11.543 s,
owner-checkpoint-writer 12.558 s, owner-credits 22.221 s, page-read-startup
10.489 s, served-catalog 22.665 s. article-stream was 8.683 s;
article-arena-reads 0.767 s and its teeth 1.116 s. Payload-arena-extent was
cached in this run; its previous two-job 14.852 s D26 defect remains.

Filtered pytest discovery ran `rg -l "extent" tests/*.py | head` and the
article analogue. The selected pytest modules were bp_fragment_node_native,
def_loop_drain, harness_check, host_check_world, guarded_by,
host_check_tables, lock_discipline_check, lisp_rewrite, native_extent_identity,
native_extent_decoded_span, native_article_subject, native_article_slots,
native_article_quiet. Result: 496 passed, 26 skipped, 42 subtests passed.
The CLI/helper-only matches were not passed to pytest. The loop ratchet was
run separately: 1 failed, 4 passed. After the new raw fixture and shared loader,
the affected harness check plus both new seam modules gave 1 passed, 2 skipped
locally (native cores unavailable locally); both native tests passed on persvati.
No unfiltered suite was run.

Verbatim gate tails follow (all commands carried timeout; host/interface/keystone
used FN_LAPTOP_OK=1 for the explicitly requested local gates).

```text
host_check --load: 58 of 58 raw files loaded in one bare acl2 in 4.0 s; 0 finding(s); 77 undefined names and 28 load-time calls belong to the certified world (not loaded here); 46 other compiler warnings
interface_emit: 1844 declared; 1794 of the raw host's 1794 dispatched entries; 24 extraction roots, 6 EXTRA; 0 finding(s)
keystone_emit: 14 defkeystone form(s) in 4 book(s), 0 finding(s)
deleted-name rg: no output; exit 1 (no matches).
== certify triage certify-20261008T153712Z-752406: 105 book logs
   real 0 / cascade 0 / must-fail 0 / limit 0 / killed 0 / other 0
   (not failures: echo 3, clean 102)

test_warm_raw_extent_is_one_span_export_and_preserves_cold_miss (tests.test_native_extent_cache_span.NativeExtentCacheSpanTests.test_warm_raw_extent_is_one_span_export_and_preserves_cold_miss) ... ok
test_actual_compressed_extent_span_matches_scalar_across_window (tests.test_native_extent_decoded_span.NativeExtentDecodedSpanTests.test_actual_compressed_extent_span_matches_scalar_across_window) ... ok

----------------------------------------------------------------------
Ran 2 tests in 3.811s

OK

496 passed, 26 skipped, 42 subtests passed in 165.45s (0:02:45)
1 passed, 2 skipped in 1.03s
1 failed, 4 passed in 0.32s

loop_call_check: host/native/admin.lisp: 1 per-iteration call/lock loops, not in the baseline
loop_call_check: host/native/extent.lisp: 10 per-iteration call/lock loops, baseline 8
loop_call_check: host/native/immutable-publish.lisp: 2 per-iteration call/lock loops, baseline 1
loop_call_check: host/native/io.lisp: 33 per-iteration call/lock loops, baseline 32
loop_call_check: host/native/mux.lisp: 3 per-iteration call/lock loops, baseline 2
loop_call_check: 129 host loops that call ACL2 or take a lock per iteration in 30 files (baseline 123)
```

## Remaining host loops and stopping boundary

The ratchet counts 129, down from 130; it enforces per-file baselines, so
shrinking an unrelated file would not resolve the five file-level reds.
All remaining names are listed below. Extent has ten counted sites:
cache-take (two nested sites), window-run, executor-loop/start/stop,
cache-release, entry-direct, lz-buffer-span, close. The raw cache-run site
is gone. Decoded cache-run retains its candidate loop (P's export is kind 2).
The other excess file sites include admin's owner-limit-serialized retry,
immutable-drain-cleanups, log-drain-spare-discards, and mux-close-wake.
The latter three preserve off-lock physical effects and receipt settlement;
admin preserves re-observation after concurrent carry changes. Their bodies
were not moved into helpers to conceal the counted work. No ratchet baseline
or lock rule was weakened. Removing these sites needs their actual batching
or concurrency protocols addressed, beyond replacing the raw warm-cache seam.

```text
host/native/admin.lisp:fnn-owner-limit-serialized loop [call+lock]
host/native/auth-adoption-parked.lisp:fnn-native-auth-adopt-config loop [call]
host/native/bp-app.lisp:fnn-bpapp-accept-locked dotimes [call]
host/native/bp-control.lisp:fnn-bpnc-accept-loop loop [call]
host/native/bp-listener-control.lisp:fnn-bplc-drive loop [call]
host/native/bp-node.lisp:fnn-bpnode-forward-contact dolist [call]
host/native/bp-node.lisp:fnn-bpnode-forward-contact dolist [call]
host/native/bp-node.lisp:fnn-bpnode-queue-outboxes loop [call]
host/native/bp-node.lisp:fnn-bpnode-queue-reports loop [call]
host/native/bp-node.lisp:fnn-bpnode-observe-reports loop [call]
host/native/bp-service.lisp:fnn-bps-read-records dolist [call]
host/native/bp-service.lisp:fnn-bps-read-received-rows dolist [call]
host/native/bp-service.lisp:fnn-bps-send-effect-next loop [call]
host/native/bp-service.lisp:fnn-bps-publish-generation loop [call]
host/native/bp-service.lisp:fnn-bpc-drive-contact loop [call]
host/native/bp-service.lisp:fnn-bps-attempt-ready dolist [call]
host/native/bp-session.lisp:fnn-bp-session-loop loop [call]
host/native/catchup-spool.lisp:fnn-csp-worker-loop loop [lock]
host/native/control.lisp:fnn-control-live-pages loop [call]
host/native/control.lisp:fnn-control-live-status loop [call]
host/native/deflate.lisp:fnn-zin-inflate loop [call]
host/native/extent-decoded.lisp:fnn-extent-decoded-window-cache-run loop [call]
host/native/extent-decoded.lisp:fnn-extent-decoded-window-run loop [call+lock]
host/native/extent.lisp:fnn-extent-cache-take dolist [call]
host/native/extent.lisp:fnn-extent-cache-take loop [call]
host/native/extent.lisp:fnn-extent-window-run loop [call+lock]
host/native/extent.lisp:fnn-extent-executor-loop loop [lock]
host/native/extent.lisp:fnn-extent-executor-start dotimes [call+lock]
host/native/extent.lisp:fnn-extent-executor-stop dolist [call]
host/native/extent.lisp:fnn-extent-cache-release dolist [call]
host/native/extent.lisp:fnn-extent-entry-direct loop [call]
host/native/extent.lisp:fnn-extent-lz-buffer-span loop [lock]
host/native/extent.lisp:fnn-extent-close dolist [call]
host/native/feed-filename.lisp:fnn-feed-filename-components loop [call]
host/native/feed-service.lisp:fnn-feed-pump-quantum loop [call]
host/native/feed-service.lisp:fnn-feed-poll-wait loop [call]
host/native/feed-service.lisp:fnn-feed-worker-loop loop [call]
host/native/heap.lisp:fnn-heap-cgroup-observations loop [call]
host/native/heap.lisp:fnn-lim-print-values dolist [call]
host/native/history-root.lisp:fnn-owner-history-root-row loop [call]
host/native/history-root.lisp:fnn-owner-history-root-adopt loop [call]
host/native/history-root.lisp:fnn-owner-history-root-refresh loop [call]
host/native/hybrid-control.lisp:fnn-command-hybrid-key-history dolist [call]
host/native/immutable-publish.lisp:fnn-immutable-drain-cleanups loop [lock]
host/native/immutable-publish.lisp:fnn-immutable-publish-deferred loop [call]
host/native/io.lisp:fnn-log-writer-loop loop [call]
host/native/io.lisp:fnn-recover-record-chunks loop [call]
host/native/io.lisp:fnn-state-checkpoint-plan loop [call]
host/native/io.lisp:fnn-state-checkpoint-load-arena loop [call]
host/native/io.lisp:fnn-recover-suffix-intern loop [call]
host/native/io.lisp:fnn-history-image-readback dotimes [call]
host/native/io.lisp:fnn-state-checkpoint-verify loop [call]
host/native/io.lisp:fnn-checkpoint-walk loop [call]
host/native/io.lisp:fnn-checkpoint-write-arena-steps loop [call]
host/native/io.lisp:fnn-history-image-plan loop [call]
host/native/io.lisp:fnn-history-image-place-run loop [call]
host/native/io.lisp:fnn-history-image-write dotimes [call]
host/native/io.lisp:fnn-checkpoint-write-steps loop [call]
host/native/io.lisp:fnn-state-checkpoint-publish-steps loop [call]
host/native/io.lisp:fnn-command-store-journal loop [call]
host/native/io.lisp:fnn-init-admit loop [call]
host/native/io.lisp:fnn-log-history-each loop [call]
host/native/io.lisp:fnn-log-history-each dolist [call]
host/native/io.lisp:fnn-import-pass dolist [call]
host/native/io.lisp:fnn-command-live-pages loop [call]
host/native/io.lisp:fnn-command-probe dotimes [call]
host/native/io.lisp:fnn-log-probe-tail loop [call]
host/native/io.lisp:fnn-log-stream-segment loop [call]
host/native/io.lisp:fnn-arena-release-returned loop [call]
host/native/io.lisp:fnn-log-drain-spare-discards loop [lock]
host/native/io.lisp:fnn-log-scan-segments loop [call]
host/native/io.lisp:fnn-log-take loop [call]
host/native/io.lisp:fnn-command-log-scan-store loop [call]
host/native/io.lisp:fnn-command-log dotimes [call]
host/native/io.lisp:fnn-command-log dotimes [call]
host/native/io.lisp:fnn-redeem-read-line loop [call]
host/native/io.lisp:fnn-redeem-password-line loop [call]
host/native/io.lisp:fnn-command-redeem loop [call]
host/native/mux.lisp:fnn-mux-flush loop [call]
host/native/mux.lisp:fnn-mux-unsent loop [lock]
host/native/mux.lisp:fnn-mux-close-wake dolist [lock]
host/native/operator-live.lisp:fnn-operator-execute-post mapcar [call]
host/native/operator.lisp:fnn-operator-init-observed dolist [call]
host/native/operator.lisp:fnn-operator-execute-init mapcar [call]
host/native/operator.lisp:fnn-operator-execute-retire loop [call]
host/native/operator.lisp:fnn-operator-export-words mapcar [call]
host/native/operator.lisp:fnn-operator-execute-export-live loop [call]
host/native/owner.lisp:fnn-owner-feed-open loop [call]
host/native/owner.lisp:fnn-owner-feed-write-batch dolist [lock]
host/native/owner.lisp:fnn-owner-feed-barrier-batch dolist [lock]
host/native/owner.lisp:fnn-owner-feed-plan loop [call]
host/native/owner.lisp:fnn-owner-shed-queued-locked loop [lock]
host/native/owner.lisp:fnn-owner-taken-groups mapcar [call]
host/native/owner.lisp:fnn-owner-consumer-local-wait loop [call+lock]
host/native/owner.lisp:fnn-owner-commit-start-locked loop [call]
host/native/owner.lisp:fnn-owner-run-job loop [call]
host/native/owner.lisp:fnn-owner-commit-pipeline loop [call+lock]
host/native/owner.lisp:fnn-owner-commit-pipeline loop [lock]
host/native/owner.lisp:fnn-owner-committer-loop loop [lock]
host/native/owner.lisp:fnn-owner-await-logical loop [lock]
host/native/owner.lisp:fnn-owner-feed-logical loop [call]
host/native/owner.lisp:fnn-owner-feed-logical loop [call]
host/native/owner.lisp:fnn-owner-cold-reap dotimes [call]
host/native/owner.lisp:fnn-owner-cold-shutdown loop [lock]
host/native/owner.lisp:fnn-owner-cold-await loop [call]
host/native/owner.lisp:fnn-owner-release-extents dolist [call+lock]
host/native/owner.lisp:fnn-owner-release-extents loop [call]
host/native/owner.lisp:fnn-owner-export-write loop [call]
host/native/owner.lisp:fnn-owner-reclaim-walk loop [call]
host/native/owner.lisp:fnn-owner-reclaim-pass loop [call]
host/native/owner.lisp:fnn-owner-reclaim-pass dotimes [call]
host/native/owner.lisp:fnn-owner-journal-cut loop [call]
host/native/owner.lisp:fnn-owner-start-maintenance loop [lock]
host/native/owner.lisp:fnn-owner-drain-service loop [call+lock]
host/native/pattern.lisp:fnn-pattern-step mapcar [call]
host/native/pull-service.lisp:fnn-pull-journal-open loop [call]
host/native/pull-service.lisp:fnn-catchup-journal-open loop [call]
host/native/pull-service.lisp:fnn-pull-prune-journals dolist [call]
host/native/pull-service.lisp:fnn-pull-flight-quantum loop [call]
host/native/pull-service.lisp:fnn-pull-settle-leases loop [call]
host/native/pull-service.lisp:fnn-pull-flight-finish dolist [call]
host/native/pull-service.lisp:fnn-pull-retire-flights dolist [call+lock]
host/native/pull-service.lisp:fnn-pull-worker loop [call+lock]
host/native/snapshot-startup.lisp:fnn-snapshot-startup-measure loop [call+lock]
host/native/tcpcl.lisp:fnn-tcl-flush dolist [call]
host/native/tcpcl.lisp:fnn-tcl-pump-out loop [call]
host/native/web-host.lisp:fnn-web-semantic-body loop [lock]
host/native/web-host.lisp:fnn-web-semantic-body loop [lock]
host/native/workflow.lisp:fnn-app-read-records dolist [call]
```

## P export coverage gap: admitted counterexample

The API accepts one backing window, while its lookup searches only a start
bound (`extent-cache.lisp:267-282`). For p=C, the earlier window [0,C) is
selected before [C,C+3). The first export call computes j=C and misses; the
second, from the later slot with its matching backing, returns :span.
The host cannot choose that later backing or retry candidates without the
loop this brief explicitly removes. `fn-xc-span-at-answers-an-owed-hit`
requires the initially selected token/plan to supply a byte; this example
does not satisfy that premise for the first slot, so it does not refute P's
theorem. It refutes the sufficiency of that contract for the requested
all-warm-stretches host behavior. The cache still throws the full cold
descriptor; this is a false miss, not unauthorized bytes.

Replay in a persvati REPL on books/extent-cache-span:
`timeout 120 python3 tools/proof_repl.py send-file s-xc2-raw-span build/s-xc2-preflight/coverage-witness.lisp --host persvati`.
The file's exact form is below. Result: one form, zero refused, 322 prover
steps / 0.13 s. This is proof-search evidence, not a repository certificate.
P must supply a coverage-aware selection/backing protocol or an ACL2-directed
continuation before this lane can claim the required general warm behavior.

```lisp
(defthm xc2-full-window-can-hide-a-later-span
 (let* ((c *fn-ew-span-capacity*) (plen (+ c 3))
        (t0 (list :window 7 11 100 plen 100 plen 0 77))
        (t1 (list :window 8 11 100 plen 100 plen c 77))
        (s0 (list :verified 11 100 plen 0 c 77 0 7 47 t0 100 plen 0))
        (s1 (list :verified 11 100 plen c 3 77 0 8 47 t1 100 plen c))
        (ledger (list nil nil nil
                  (list (cons t0 '((300000 0 0 0 0) :cached nil))
                        (cons t1 '((300000 0 0 0 0) :cached nil))) nil))
        (slots (list (list 2 t 7 0 11 100 plen 100 plen 0 0 0 77 0)
                     (list 2 t 8 0 11 100 plen 100 plen 0 0 c 77 1)))
        (cells '(2 0 2))
        (window (list (append '(4 5 6) (make-list (- c 3) :initial-element 0))))
        (dst (list (make-list c :initial-element 0))))
   (and (fn-xcsp slots) (fn-xccp cells) (fn-xc-readyp slots cells)
        (fn-pwr-plan-matches-token s0 t0) (fn-pwr-plan-matches-token s1 t1)
        (fn-ewp-publication s0) (fn-ewp-publication s1)
        (fn-pwc-cachedp ledger t0) (fn-pwc-cachedp ledger t1)
        (equal (mv-nth 0 (fn-xc-span-at 0 ledger s0 11 100 plen 100 plen 77 c plen
                                     slots cells window dst)) :miss)
        (equal (mv-nth 0 (fn-xc-span-at 1 ledger s1 11 100 plen 100 plen 77 c plen
                                     slots cells window dst)) :span)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (enable fn-xc-span-at fn-xc-slot-token fn-xc-token)
                                            (executable-counterpart-theory :here)))))
```
