# Open depth (PKT-876, lane open-depth, 2026-09-28)

## 1. The harness runs at the deployed stack

Every native test ran the image's own launcher, which ACL2's save-exec writes
with `--control-stack-size 64` (MiB), while the installed launcher
(packaging/fn) gives every node thread the profile's figure
(books/heap-reservation.lisp fn-heap-stack-kib, 1,024 KiB). Now
tools/build_native_host.sh writes ACL2's figure into every image launcher it
builds (production, developer, DTN, reference; host/native/build.lisp and
build-dtn.lisp print `FN_NATIVE_STACK_KIB`, a build that prints none is refused
for those two entries), so a test that runs build/fn-host directly runs at
1,024 KiB and the frozen release launchers carry the same default.
`FN_TEST_CONTROL_STACK_KB` still overrides it, and only with
`FN_TEST_CONTROL_STACK_REASON` naming why (tests/test_native_operator_verbs.py
`deployed_stack`). test_native_image_floor's
`test_the_image_launcher_runs_at_the_decided_stack` checks the launcher's
figure against the probe's (`heap -- operator CONFIG run`).

Rerun at 1,024 KiB (hbox native-od1, 1d1733788, production + developer):
test_native_recovery 13, checkpoint 2 (+2 skipped, FN_RUN_NATIVE_CLONE),
checkpoint_auto 4, state_checkpoint, log_damage, older_release_open,
replay_determinism, commit_log, log_compaction, crash_model: OK.
New failures: none is a stack death.
- test_native_image_floor (3 of 11): GuardViolationTests x2 expect the
  pre-entry-guard line `ACL2 error in fn-sha256-of-string: (EV-FNCALL-GUARD-ER
  ...)`, the image now says `host-entry-guard: fn-sha256-of-string ...`
  (a stale expectation, not the stack); DeepInputStackTests' long-history
  replay phase deletes the checkpoint files and the reopen is refused
  `checkpoint-damaged: the log's segments do not hold the history` (the test
  predates the segment layout; it already ran at 1,024 KiB explicitly).
- test_native_owner (1 of 18): NativeOwnerHandlerStructureTests' chunk-loop
  raw harness calls FNN-CORE-BUFFER-STATE FN-OWNER-CHUNK-SPAN with 4 values
  where the span now takes 5 (log-leftovers' S); not the stack.
The launcher witness passed.

## 2. Does a checkpoint open avoid it? No.

syn100k-2k, the pre-fix production image (od1: the harness change and
thread-stacks' three loops, none of this lane's), checkpoint written by
`operator CONFIG store checkpoint` at 64 MiB (named reason; 119.7 s,
sequence=100000, 309,814,997 octets), then `operator CONFIG run` at the
launcher's 1,024 KiB: the owner stops at open, exit 4,
`fault operator run ACL2 error in fn-store-sn-recover-from-checkpoint:
Control stack exhausted`. The checkpoint open resumes the stored node and
runs the same whole-node recognizer (fn-sco-cpr-resume and fn-sco-cpr-finish,
fn-cnode-statep) over every retained article, so it dies where the full
replay does. syn1m-2k was not run on the pre-fix image: it is the same walk
ten times deeper. So the live node (opens from checkpoints) cannot restart a
store past roughly 30,000 retained articles on any build before this lane,
checkpoint or not; below that it is unaffected.

## 3. The walks (PRF-352)

Found by running the open at 1,024 KiB and reading where it died, then
extracting the closures of the functions it died under (lane extract-2's
tools/extract/frontend.lisp, tools/nontail_recursions.py) and fixing every
walk whose depth is the retained-article count R, in three waves, each
confirmed natively before the next:

| wave | died in (at 1,024 KiB, syn100k-2k) | loops |
|---|---|---|
| 1 | fn-retain-obligation-ids, 30,527 frames (fn-cnode-statep < fn-sco-cpr-finish) | fn-retain-obligation-ids, -release-ids, -sum, -remove-id; fn-node-binding-msgids, -ids; fn-replay-verdict-pairs; fn-stx-index-of-store; fn-mxc-build; fn-rii-kbuild-releases, -pins |
| 2 | fn-ctl-articles-withdrawals-in, 17,447 frames (fn-own-refresh < fn-ock-install < fn-owner-recover-from-store-open); the checkpoint verb in fn-store-sco-publish-setup | fn-ctl-articles-withdrawals-in, fn-ctl-drop-via, fn-ctl-visible-filter, fn-ctl-subseq-diff, fn-own-take, fn-gidx-build-entries, fn-index-build, fn-midx-build, fn-scka-canon-rows, fn-scka-enc-lens-sum, fn-sct-payloads |
| 3 | fn-sbud-record-octets (fatal, pseudo-atomic: the owner start) | fn-sbud-record-octets, fn-sbud-stored-octets, fn-pgc-obligation-ids, fn-pgc-release-ids |

Each is (mbe :logic <the recursion, unchanged> :exec <loop>), exec = logic by
its verify-guards event (a revappend, acc-is-plus or loop-of-rev-onto lemma,
the per-element function disabled). Witnesses in the books' test books, each
over 50,000 elements. Certified: persvati certify-20260928T045804Z-2021342
(748 passed, 0 failed) + hbox certify-20260928T045829Z-4075806 (283 passed,
0 failed), the union of the 22 changed books' affected roots (1,130) at the
lane head before the last origin/dev merge.

The whole-node check is still run at every open (fn-sco-cpr-finish and
fn-sco-cpr-resume's :exec run fn-cnode-statep once): O(R) time, now constant
stack. It goes when the node's records are on sealed pages and the open
checks each segment's seal (arena-store-3's direction) instead of
revalidating the node: that is the carried-invariant fix, not done here.
fn-retain-statep's `intersection-equal' over pins x releases is quadratic
(tail calls when the state is valid, so no stack; the time is the issue).

Not fixed here (PKT-877): the served reads that walk a group's whole article
list per command recurse per article. With the opens fixed, syn100k-2k at
1,024 KiB serves DATE, and `LIST ACTIVE' kills the owner in
fn-nntp-group-low (fn-nntp-active-line; GROUP's fn-nntp-group-result and a
reselect after a refresh reach the same fn-nntp-group-low/-high/-count). The
image's whole host-called closure has 585 non-tail recursions (hbox
extraction over every fn- symbol host/native names); this lane fixed the 26
the open and the owner's start run at depth R.

## 4. Native: syn100k-2k and syn1m-2k open at 1,024 KiB

hbox native-od5 (production image, the image launcher's 1024KB, 80G scope,
tests.test_native_open_depth: OK, 2 tests, both fixtures). Seconds from exec
to LISTENING:

| fixture | full replay | `store checkpoint' | open from that checkpoint |
|---|---|---|---|
| syn100k-2k (100,000) | 25.4 s | 56.5 s (309,814,997 octets) | 11.7 s |
| syn1m-2k (1,000,000) | 275.1 s | 926.0 s (3,101,697,971 octets) | 143.6 s |

Each open then greets a connection, answers DATE, and stops with exit 0 and
no stack exhaustion. Load 5-12 on 24 cores during the run.
