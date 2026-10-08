# s-xc2 span implementation evidence, 2026-10-08

NOT READY. Implementation stopped under Deputy S's explicit condition 2:
a served scalar tombstone-prefix read remains in `books/article-arena-reads.lisp`,
outside the approved proof-book set. No push. P's `origin/lane/p-xc-span`
was absent at every `timeout 30 git ls-remote origin lane/p-xc-span` poll,
including the final poll; JOB 2 and `:duplicate` handling remain pending.

## Commits and proved scope

- `5e1aaea3f`: S1 span scan, guards, exact scan-state/fuel equality, and real-arena teeth.
- `4b5cc6ad1`: owner preflight routing and profile-backed span size. Added
  `fn-ast-span-want` to host/interfaces.lisp; generated interfaces.json and
  tools/extract/roots.sh with `FN_LAPTOP_OK=1 python3 tools/interface_emit.py --write`.
- `f9b52c012`: A-DURABLE-LZ span seam, compressed arena dispatch/refinement,
  compressed concrete-arena witness, native decoded span realization and host-path test.
- `fc7817600`: native test closure loader; no realizer/decoder/cache decision stubs.

S1 (`books/article-stream.lisp:373`) has exactly `(natp fuel)` as premise.
Its standalone persvati admission was 230,605 prover steps / 1.59 s. Span
size normalizes arbitrary limits locally; the equality does not depend on
the selected profile. `fn-ast-span-want` at :777 reads :read-window-octets
(262144); native extent.lisp:625 calls that ACL2 accessor at host load.

S3's assumption is beside the existing A-DURABLE-LZ realizer in
assumptions-durable.lisp. The list of nth decoded answers equals the existing
scalar seam. `payload-arena-extent.lisp:488` returns nil without realization
for zero and uses one decoded-span realization for a positive compressed
span. `fn-arena$x-get-span-is-the-octet-loop` at :1303 proves the refinement;
`tests/acl2/payload-arena-extent-tests.lisp:425` is a ground witness on an
actual sealed compressed arena, including its well-formedness and bounds.

Native host-path evidence: tests/test_native_extent_decoded_span.py ran on
persvati using developer core native-sxc-9b6958f93 plus the current extent
function closure. Real compressed file preads drive actual private decoder
jobs, ledger return/cache transitions, slot lookup, and span/scalar reads.
The test compares every byte with the original 20000-octet payload for a
2048-octet read, [16380,16396) crossing the decoded-window boundary, a tail
and zero. No rebuild/full-node/W2L qualification is claimed. The warm core
retains its structure/startup capacity; these cases are below both its
16 KiB capacity and the new profile capacity.

## Served chain and residual scalar inventory

The original per-octet payload scan was owner.lisp:842
fnn-owner-render-next-quantum -> :786 fnn-owner-ready-plan-step ->
host/owner-host.lisp:4613 fn-owner-article-ready-plan-step ->
article-stream-owner.lisp:620 fn-ast-scan-step -> source-byte -> arena scalar
getter -> native extent lock. The owner call at :620 now calls
fn-ast-scan-step-span. It folds one arena span per chunk; its scalar fallback
is only taken when the source is not readable, in which case source-byte
cannot call fn-arena-get. Render enters article-stream.lisp:926
fn-ast-render-window -> :881 aux-chunk -> :797 render-one-chunk -> arena span.

Direct remaining scalar-realizer callers (excluding declarations, theorem
terms, comments, and test-only calls):

| Caller | Site | Status |
| --- | --- | --- |
| fn-arena$x-get -> fn-durable-realize-octet | books/payload-arena-extent.lisp:461 | Still reachable through served tombstone prefix; stop condition. |
| fn-arena$x-get -> fn-durable-realize-lz-octet | books/payload-arena-extent.lisp:463 | Same remaining served prefix on compressed extents. |
| fn-durable-span-spec -> fn-durable-realize-octet | books/assumptions-durable.lisp:106 | Logical specification of the raw span seam; native span overrides it. |
| executable counterpart -> fn-durable-realize-octet | host/native/extent.lisp:1724 | Scalar forwarding wrapper, still reachable via the prefix. |
| executable counterpart -> fn-durable-realize-lz-octet | host/native/extent.lisp:1899 | Scalar forwarding wrapper, still reachable via the prefix. |
| fn-durable-realize-octet -> fnn-extent-window-realize-octet | host/native/extent.lisp:1719 | The window-mode scalar route, still reachable via the prefix. |

**Residual served chain:** article-stream-owner.lisp:358
fn-asto-payload-preflight and :529 fn-asto-finish call
fn-nntp-article-tombstonep -> article-arena-reads.lisp:97
fn-nntp-arena-prefixp -> :25 fn-arena-get -> the scalar durable getter.
OVER's served-columns.lisp:260 tombstone fallback, and HDR's Xref
compatibility tombstone tests (nntp-reader-compat.lisp:316/:475), reach it too.
The magic is eight octets (`reclaim-tombstone.lisp:30`); an ordinary article
whose first byte is nonzero mismatches on the first scalar read. This is
bounded control work but violates the instruction to remove every served
scalar durable caller. No permission is inferred to change this extra book.

Other inventoried scalar components: legacy-parser-cursor.lisp:266/:331 and
legacy-header-query.lisp:39 have no current native served entry; the :span
arm of nov-piece-window.lisp:70 is unreachable-in-composition for ARTICLE's
produced metadata pieces (article-stream.lisp:421, :525, :586). The payload
branch is intercepted by render-one-chunk. query-payload-scalar.lisp:33 is
reached by the captured POST comparator in post-identity-captured-host.lisp:58;
its native adapter is explicitly parked and not loaded
(host/native/post-captured-parked.lisp:1). consumer-remote-visible-buffer.lisp:135
belongs to the internal collection writer; its report-advance adapter has
no public issuer or native call (consumer-remote-report-host.lisp:58).
The old native current-octet acquisition helper at extent.lisp:801 has no
native caller. These are source-chain findings, not new reachability proofs.

## Cost scope

For a warm 2 KiB payload fitting one cache window and one owner quantum,
preflight plus rendering now take **two data-span lock acquisitions**, one
per pass. The actual reply still includes the scalar tombstone checks: when
both owner checks run on an ordinary non-NUL-leading article they add one
lock each, before other control/ledger locks. Thus the whole reply is not
claimed to meet the two-lock target or condition 2. No new W2L result exists.
The accepted S4 statement remains a W2L target: sum the window/quantum/span
intersections per pass; byte-fold CPU work stays O(N). ACL2 visit bounds do
not alone prove a host mutex acquisition count.

## Gates

Certification command:
`timeout 180 python3 tools/farm.py submit persvati --lane --affected-by books/article-stream.lisp --affected-by books/payload-arena-extent.lisp --jobs 2`

Run `run-20261008T122812Z-4696`, manifest
`build/acl2/certify-20261008T122929Z-3240729/manifest.json`: 9 roots, 425 closure
books, 254 cached, 171 newly certified, 0 failures, 270.62 seconds. This
covers the changed proof closure at f9b52c012, including both new teeth books
and article-stream-owner; later fixture-only edits do not change it.
D26 overs at two jobs:

- `books/article-select-index`: 10.747 s
- `books/catalog-logic`: 13.345 s
- `books/history-records`: 10.202 s
- `books/owner-credits`: 18.714 s
- `books/payload-arena-extent`: 14.852 s
- `books/served-catalog`: 13.196 s
- `books/store-node-invariants-base`: 10.444 s

Verbatim gate tails:

```text
host_check --load: 58 of 58 raw files loaded in one bare acl2 in 3.4 s; 0 finding(s); 77 undefined names and 28 load-time calls belong to the certified world (not loaded here); 46 other compiler warnings
interface_emit: 1844 declared; 1794 of the raw host's 1794 dispatched entries; 24 extraction roots, 6 EXTRA; 0 finding(s)
keystone_emit: 14 defkeystone form(s) in 4 book(s), 0 finding(s)
== certify triage certify-20261008T122929Z-3240729: 171 book logs
   real 0 / cascade 0 / must-fail 0 / limit 0 / killed 0 / other 0
   (not failures: echo 6, clean 165)

----------------------------------------------------------------------
Ran 1 test in 0.172s

OK
.                                                                        [100%]
1 passed in 0.93s
=========================== short test summary info ============================
FAILED tests/test_loop_call_check.py::SiteTests::test_the_tree_is_at_its_baseline
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 455 passed, 42 subtests passed in 129.76s (0:02:09)
s.sssssssssssssss                                                        [100%]
1 passed, 16 skipped in 0.18s
loop_call_check: host/native/admin.lisp: 1 per-iteration call/lock loops, not in the baseline
loop_call_check: host/native/extent.lisp: 11 per-iteration call/lock loops, baseline 8
loop_call_check: host/native/immutable-publish.lisp: 2 per-iteration call/lock loops, baseline 1
loop_call_check: host/native/io.lisp: 33 per-iteration call/lock loops, baseline 32
loop_call_check: host/native/mux.lisp: 3 per-iteration call/lock loops, baseline 2
loop_call_check: 130 host loops that call ACL2 or take a lock per iteration in 30 files (baseline 123)
```

host_check --load exited 0; its bare-ACL2 limitation is in the tail above.
interface_emit --check and keystone_emit --check exited 0.
The deleted-name rg exited 1 with no output (the expected no-hit result).
The filtered Python run stopped at the existing loop baseline failure; the
remaining extent/article files ran separately. Native image-dependent tests
skip locally; the new seam test ran successfully on persvati with unittest
(the remote system Python lacks pytest). No unfiltered suite ran.

The required discovery command `rg -l "extent" tests/*.py | head` included
check_control_unwind_effects.py, a CLI checker rather than a pytest module;
it was not passed to pytest. Other discovered pytest modules plus explicit
native extent/article files were selected. Initial fixture-stub classification
failure was fixed and its exact tree check rerun successfully. No baseline
was raised. secrets_check reported zero findings before each commit.

## Every loop named by the remaining ratchet

`python3 tools/loop_call_check.py --list` reports 130 sites (baseline 123).
P's raw cache loop removal is pending; it cannot by itself remove all seven
excess sites. The complete current list follows, including repeated sites
inside the same function:

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
host/native/extent.lisp:fnn-extent-window-cache-run loop [call]
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
loop_call_check: host/native/admin.lisp: 1 per-iteration call/lock loops, not in the baseline
loop_call_check: host/native/extent.lisp: 11 per-iteration call/lock loops, baseline 8
loop_call_check: host/native/immutable-publish.lisp: 2 per-iteration call/lock loops, baseline 1
loop_call_check: host/native/io.lisp: 33 per-iteration call/lock loops, baseline 32
loop_call_check: host/native/mux.lisp: 3 per-iteration call/lock loops, baseline 2
loop_call_check: 130 host loops that call ACL2 or take a lock per iteration in 30 files (baseline 123)
```


## Round 6: prefix statement, before proof

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
