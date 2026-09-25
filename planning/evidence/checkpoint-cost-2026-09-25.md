# The checkpoint's cost: one open, a count in the file, linear list checks, the publication off the mutex (2026-09-25)

Lane `checkpoint-cost` (Opus 5.5), from dev `534a68d3`. PRF-104, STO-012,
SCN-050. Backlog PKT-141 and PKT-142. Follows
[owner-checkpoint-open](owner-checkpoint-open-2026-09-25.md) findings 1 to 3
and [bounds-p3](bounds-p3-2026-09-25.md) findings 3 and 4. D27.

Commits: f65396e0 (books, host, tests), c9099617 (registry; by-definition
bridges named as such), a99154d6 (source tests), 4f99e757 (the test book's
must-fails, manifests), and the evidence commit carrying this record.

## First, the profile

sb-sprof on hbox, N=4096, the owner-checkpoint image (b78326dc), `status`:

- From the checkpoint (S=2048, suffix 2048): 21.5 s. Full replay: 16.2 s.
  The checkpoint open was slower than full replay.
- `fn-node-statep` was 1683 of 2722 samples (62 %) of the checkpoint open.
  It ran about seven times per open: the exec checks in `fn-sco-cpr-resume`
  and `fn-sco-cpr-finish` (the Store open resumed the suffix twice, through
  `fn-sco-replay-result` and `fn-sco-open`), `fn-sco-finalize`'s own
  `fn-cnode-statep`, `fn-replay-advance-okp`, `fn-sn-statep` in finalize,
  and again in the host's `fn-sn-open-okp`. The owner then extended and
  finalized a third time.
- Each run is quadratic in the node: `fn-article-listp`,
  `fn-node-binding-listp`, `fn-subsetp`, `fn-retain-no-duplicatesp` are
  member-equal folds; `fn-node-articles-have-archive-bindingsp` and
  `fn-articles-freshp` search per element.
- Re-encoding the covered prefix (P3 finding 4) was 27 samples: negligible.

Profiles (hbox /tank/fn/scratch/checkpoint-cost/logs/, sha256):
prof-status-ckpt-n4096.txt ed9945c1…, prof-status-full-n4096.txt 4ffdd3f6…,
prof-after-status-ckpt-n4096.txt eea3c6df….

## What changed

- **(c) One Store open, and the owner installs from it.** Both host opens
  extend a checkpoint once: the decoded file over the suffix
  (`fn-store-sn-recover-from-checkpoint`), or the empty capture over the
  whole history (`fn-store-sn-recover`). Then `fn-store-sn-open-extended`
  (host/store-node-host.lisp) calls `fn-sco-store-open`, which computes the
  configuration fold's result once and passes it to `fn-sco-finalize-from`.
  The host tests the open's kind, which is `fn-sn-open-okp`
  (`fn-sco-finalize-okp-is-kind-ok`), instead of running the whole-state
  recognizer again. E, the fold result and the open stay in the global
  `fn-store-sco-open`. The owner (`fn-owner-recover-from-store-open`,
  host/owner-host.lisp; native `fnn-owner-recover-core`, owner.lisp) calls
  `fn-ock-install` on that pair and keeps E as its base. It no longer decodes
  octets, extends or finalizes.
- **(a) The file carries the count.** The checkpoint's event index maps each
  sequence below S to its record. `fn-sco-freeze` writes S in the record slot
  when `fn-sco-index-records` over the index gives exactly the record list,
  and `fn-sco-thaw` reads the list back out of the index. Past the index's
  u32 keys the list stays: nothing is capped. `fn-scc-value-sequence` reads a
  count slot, so the header's S is right in both forms. Old files (list form)
  thaw to themselves, so no schema change. `fn-store-sco-decode` thaws;
  `fn-store-sco-publish-octets` and `fn-ock-publication` freeze.
  `fn-store-sco-publish-octets` publishes the open's E when its records are
  the Store's (no second extension).
- **(d) Linear list checks.** `fn-keyset` (books/acceptance-alloc.lisp) is a
  stobj with one EQUAL hash table, local to each call (`with-local-stobj`),
  so it is safe from any thread. The `:exec` paths:
  - `fn-no-duplicatesp` and `fn-subsetp`: `fn-ks-distinctp` and
    `fn-ks-subsetp` for lists of eight or more;
  - `fn-article-listp` (acceptance.lisp:45-52 before): the shape, then the
    Message-IDs through `fn-no-duplicatesp`;
  - `fn-node-binding-listp`: the shape and two distinctness checks;
  - `fn-retain-no-duplicatesp`: `fn-no-duplicatesp`.
  Every `:logic` body is unchanged, so no statement about them moves.
- **(b) The publication off the mutex.** `fnn-owner-maybe-publish` asks
  `fn-owner-sco-due` and `fn-owner-sco-capture` under the owner mutex: the
  base, the configuration history, the record list, the segment size (ACL2
  values; the attempt is recorded). A thread (`fnn-owner-publish-captured`)
  then calls the state-free `fn-ock-publication` (extend and freeze-encode),
  writes through `fnn-state-checkpoint-write` (the P3 byte program), and
  installs the new base and durable S with `fn-owner-sco-publication-done`
  under the mutex. At most one runs; it is on the workers list, so the stop
  joins it before the Store closes. Errors in the thread are logged.

## Theorems (statements; ACL2 8.7)

- **`fn-sco-store-open-of-extended-capture`** (keystone of (c); hypothesis
  of its second conjunct only: the open is `:ok`):
  `(cadr (fn-sco-store-open (fn-sco-extend (fn-sco-capture configs P) configs Q) configs frontier))`
  is `(fn-cpo-open-observed configs frontier (append P Q))`, and when its
  kind is `:ok` the `car` is `(fn-cpr-replay configs (append P Q))`.
  P = NIL is the full path. Host: fn-store-sn-open-extended, reached from
  fn-store-sn-recover and fn-store-sn-recover-from-checkpoint.
- **`fn-ock-install-of-store-open-by-definition`**: fn-ock-install over that
  pair is `(fn-ock-recover-extended E …)`. A definition unfolded, named so;
  with PRF-083's `fn-owner-recover-from-checkpoint-equals-full-recover` and
  `fn-ock-recover-installs-ocl-relation` it makes those keystones hold of
  `fn-owner-recover-from-store-open`. `fn-sco-finalize-from-unfolds` is the
  same kind of bridge for finalize.
- **`fn-sco-finalize-okp-is-kind-ok`**, no hypothesis.
- **`fn-sco-thaw-of-freeze`**: `(implies (fn-sco-shapep c) (equal (fn-sco-thaw (fn-sco-freeze c)) c))`.
- **`fn-sco-freeze-of-capture-carries-the-count`**: a capture of at most
  2^32 records is written with `(len records)` in its record slot.
- **`fn-ock-published-segments-decode-to-the-checkpoint`**: under
  `fn-sco-shapep` and the codec round trip's tree and two width hypotheses,
  the FNSC segments of the frozen value decode and thaw to the value.
- **`fn-ock-publication-is-the-capture-at-the-capture-point`** (hypothesis:
  the captured history is admitted): the NEXT the thread computes from the
  capture of any prefix is `(fn-sco-capture configs records)` of the
  records captured under the mutex, whatever was committed meanwhile.
- **Linear forms, no hypothesis:** `fn-ks-distinctp-is-nodupp`,
  `fn-ks-subsetp-is-subset-logic`,
  `fn-article-listp-is-shape-and-distinct-msgids`,
  `fn-node-binding-listp-is-shape-and-distinct`; the bridges
  `fn-no-duplicatesp-is-ks-nodupp`, `fn-subsetp-is-ks-subset-logic`,
  `fn-retain-no-duplicatesp-is-no-duplicatesp` (identical definitions; not
  registry events). The mbe guard proofs make the `:exec` paths these.
  They are reached from `fn-cnode-statep` → `fn-node-statep` in
  `fn-sco-cpr-resume`, `fn-sco-cpr-finish` and `fn-sco-finalize-from`.

## Teeth

- **tests/acl2/owner-checkpoint-open-tests** (added):
  - freeze/thaw witness: the whole-history capture freezes to the count 2,
    differs from its list form, and thaws back; a value whose index does
    not hold its records keeps its list and round-trips.
  - `must-fail` for `fn-sco-thaw-of-freeze`'s shape hypothesis, with the
    concrete value `(:fn-store-checkpoint 2 nil nil nil nil nil)`.
  - codec witness: the frozen segments (segment 64, several segments)
    decode and thaw to the capture; `must-fail` without the tree hypothesis
    (a 1/2 in a slot makes the encoder refuse).
  - Store-open witness: from the prefix's capture over the suffix the open is
    the full open, `:ok`, `fn-sn-open-okp`, and the fold is the full replay;
    the owner from the pair is the full owner.
  - publication witness: NEXT is the capture of the captured history, the
    octets its frozen file; capturing at the prefix publishes the prefix.
- **tests/acl2/linear-recognizers-tests** (new): each linear path, on twelve
  elements (the hash path), against a quadratic reference evaluated in the
  logic: distinct keys pass, a duplicate far from its twin fails; subset in
  and out; pair keys; twelve cloned articles pass, one repeated Message-ID
  fails, a non-article and a dotted tail fail; bindings with a repeated
  identity and with a repeated Message-ID fail.
- **Untoothed:**
  - the `:ok` hypothesis of the Store open's replay conjunct: on three
    refused opens (a repeated history, a non-event prefix) the fold still
    equals the full replay (asserted). The host reads the configuration only
    after testing the kind.
  - the publication keystone's admitted-history hypothesis (PRF-083's,
    inherited).
  - the 2^32 bound of `fn-sco-freeze-of-capture-carries-the-count` and the
    codec's two u64 width hypotheses: a counterexample needs 2^32 records or
    a 2^64-octet program.

## Certification

- **hbox**, w28 `acl2-literal-4g`, `certify_books.py --incremental --jobs 8`
  over the default-profile roots of c9099617: rc 0, 231 certified, no
  failure. Manifest `planning/evidence/manifests/hbox-certify-20260925T101212Z-3125229.json`.
  At 8 jobs: acceptance-alloc 0.37 s, acceptance 0.97 s, node 1.12 s,
  store-checkpoint-codec 6.9 s, store-checkpoint-open 7.7 s,
  owner-checkpoint-open 6.5 s. The default profile has no test roots.
- **persvati** farm run-20260925T100711Z-b96e (w25 `acl2-literal`, 2 jobs,
  300 s; every book affected by acceptance-alloc or store-checkpoint-codec,
  test books included) at a99154d6: 633 certified, 0 failed. Manifest
  `planning/evidence/manifests/certify-20260925T100749Z-3672655.json`
  (sha256 85e72a52…). acceptance-alloc 0.22 s, acceptance 0.37 s, retention
  0.32 s, node 0.37 s, store-checkpoint-codec 4.8 s, store-checkpoint-open
  3.7 s, owner-checkpoint-open 5.9 s, linear-recognizers-tests 0.27 s,
  store-checkpoint-open-tests 4.5 s.
  - **owner-checkpoint-open-tests took 80.2 s**: its two new `must-fail`s
    searched. Both are now stated at their concrete values and ACL2 refutes
    them by evaluation (4f99e757).
  - Twenty other books were over 10 s in that run (10.1 to 14.0 s), none
    changed by this lane; persvati was shared with other lanes' 2-job
    runs throughout. `make check`'s D26 ratchet fails on six of them that
    are not in its baseline: bp-node-fragment-step 14.0, consumer-store-
    invariants 12.7, bp-node-progress-guards 12.6,
    bp-node-forwarding-teeth-tests 12.2, native-operator-tests 11.8,
    native-admin-peer 11.6 s.
  - **Rerun of those six** (run-20260925T183957Z-e42a, `--recertify`, 2
    jobs; manifest `certify-20260925T184018Z-4105289.json`, sha256
    126e36b5…): 10.0, 9.9, 8.0, 9.5, 8.3 and 10.4 s; bp-report-guards,
    a dependency, 11.1 s. native-admin-peer was 10.2 s at 2 jobs before
    this lane (083645Z). native-operator-tests was 4.9 to 6.3 s in the
    manifests of 2026-09-24 and is 8.3 s here: it includes
    store-checkpoint-open and may carry part of this lane's cost; not
    separated from the box's load. The ratchet still reads run 1's worst
    figures: this is for the deputy's merge batch, not hidden here.
- **persvati** run-20260925T183328Z-dae3 at 4f99e757 (affected by
  owner-checkpoint-open-tests): 3 certified, 0 failed.
  owner-checkpoint-open-tests 3.5 s. Manifest
  `planning/evidence/manifests/certify-20260925T183348Z-4032007.json`
  (sha256 64abd033…).

## Native (hbox, tmpfs, same stores, both images built here)

Images: base = dev 534a68d3, fn-host d9bc7bd7… (core a01dee81…); after =
c9099617, fn-host 1d877247… (core fbed170b…), developer 7f2e815b…. Stores
built once with the base image by build.py (scale profile, K = 4096, 2 KiB
articles): store-n1000 (no checkpoint), store-n4096 (its automatic
checkpoint at S = 2113). The owner-checkpoint stores no longer open on dev:
`ACL2 rejected durable configuration frame`. Every run under
`systemd-run --user --scope -p MemoryMax=40G`.

| N = 1000 | base | after |
| --- | --- | --- |
| `status`, full replay | 2.11 s, 1.70 GB | 1.46 s, 1.36 GB |
| owner start, full replay | 2.83 s | 1.10 s |
| `store checkpoint` | 3.02 s, 2.05 GB | 1.84 s, 1.67 GB |
| checkpoint file | 7,970,517 octets | 5,407,621 octets |
| `status`, checkpoint suffix 0 | 2.42 s, 1.81 GB | 1.29 s, 1.25 GB |
| owner start, checkpoint suffix 0 | 3.35 s | 1.36 s |

| N = 4096 | base | after |
| --- | --- | --- |
| `status`, checkpoint S=2113 suffix 1983 | 17.7 s, 2.62 GB | 7.67 s, 2.52 GB |
| owner start, same | 30.0 s | 9.27 s |
| `status`, full replay | 16.1 s, 2.60 GB | 7.77 s, 2.60 GB |
| owner start, full replay | 25.9 s | 7.28 s |
| `store checkpoint` | 23.9 s, 4.08 GB | 9.19 s, 3.30 GB |
| checkpoint file | 32,686,014 octets | 22,175,686 octets |
| `status`, checkpoint suffix 0 | 19.7 s, 4.08 GB | 7.72 s, 2.82 GB |
| owner start, checkpoint suffix 0 | 34.3 s | 8.94 s |
| automatic publication S=4096 | 7,254 ms, under the mutex | 4,609 ms, off it |
| first connection greeting after start (publication running) | 10.02 s | 2.85 s |
| each later greeting | 2.9 to 3.0 s | 1.35 to 1.53 s |
| STAT on an open connection, max during the publication | 5 ms | 558 ms (one; next 156 ms) |

The publication is due at the owner's first tick after a full-replay start
(no durable checkpoint, 2 × 4096 ≥ K). The greeting is ACL2's connection open
under the owner mutex; before, the first client waited for the whole
publication. The 558 ms STAT is the other thread's allocation (a collection),
not the mutex.

Logs (hbox /tank/fn/scratch/checkpoint-cost/logs/, sha256):
meas-base-n1000.log 54d82d46…, meas-after-n1000.log 8648b631…,
meas-base-n4096.log bc52dd77…, meas-after-n4096.log 8c158213…,
pub-base-n4096.log 5885edd0…, pub-after-n4096.log a91d4db0…,
build-n4096.log 0b88cfd4…, image-base.sha256 22a3b1f5…,
image-after.sha256 7adc78e0…, native-tests.log 9112dd2c…,
native-tests-source.log a626407f….

Native tests on the after images: tests.test_native_state_checkpoint and
tests.test_native_operator_cli, 11 tests; 10 passed and the one failure was
the source test the hbox tree had before a99154d6; with a99154d6's test it
passes (native-tests-source.log). All twenty kill/EIO cuts open the old
checkpoint before the rename and the new one at and after it.

## Findings

1. **Opens are 2.2 to 3.8 times faster; the checkpoint still does not beat
   full replay at N ≤ 4096.** After: checkpoint open 7.7 s against full
   7.8 s (`status`), owner 8.9 s against 7.3 s. The remaining fixed cost
   (profile of the after image, checkpoint open): `fn-node-statep` 591 of
   1695 samples, mostly `fn-node-articles-have-archive-bindingsp` (387,
   `fn-retain-find-id` per article) and `fn-articles-freshp` with
   `fn-all-article-memberships` (quadratic, rebuilt per article); the file
   decode 289; the history recognizer's `fn-record-p` 320. Those two
   recognizer pieces are the next linearization (same pattern: a keyed
   table for bindings and obligations, a pair set for memberships).
2. **Each connection's greeting costs 1.4 s at N=4096 (3.0 s before)**, under
   the owner mutex. That is a whole-state cost on a served path (the
   AGENTS.md rule), outside this lane: a new backlog item.
3. **The file is 32 % smaller** (22.2 MB against 32.7 MB at 4096); the
   Store state still holds the record list (below).
4. RSS at open fell 0.3 to 1.3 GB.

## Not done, and why

- **The kernel does not carry a count.** `fn-sf-records` is the Store
  state's record list: 61 books read it, a commit appends to it
  (store-files.lisp:437 and :508, `append` per commit), and the history
  recognizer and admission read it. Replacing it with a count moves
  statements in all of them. This lane took the list out of the file only.
- **Two quadratic node checks** (finding 1).
- **The covered prefix's octets are still re-encoded** for
  fnn-open-live-store's callers (pack, compact, verbs): 27 samples at 4096.
  The owner no longer uses them.
- K0 coverage of the publish program's `:root` rename stays open (P3
  finding 6).
