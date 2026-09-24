# M5 compaction: the reclaim keeps the served view (2026-09-24)

Lane `m5-compaction`, branch `lane/m5-compaction` from dev `00d291d0`.
Milestone item (planning/milestones.md §M5): "Implement GC and compaction
with protected dependency closure and temporary space accounting. Prove
preservation and crash behavior." Exit: "compaction does not weaken
acceptance or replay guarantees."

## What compaction is in fn today

Two offline developer verbs over one Store, both under the exclusive Store
lock (specs/storage.md, "Checkpointing and compaction"):

1. `checkpoint pack ROOT select` (host/native/checkpoint.lisp
   `fnn-pack-publish`): ACL2 captures every committed transaction record's
   exact canonical bytes into one immutable pack (`fn-cc-capture`, at most
   4096 events and 4 MiB), the host publishes it through the shared
   immutable-publication effect, then replaces the pack selection marker
   under ACL2's marker driver (file barrier, replace, directory barrier).
   The durable "pack is authoritative" mark exists: it is the selection
   marker, and `fnn-pack-selected-raw-and-coverage` fsyncs the packs
   directory before consulting it.
2. `checkpoint pack-reclaim ROOT` (`fnn-pack-prefix-reclaim`, line 151):
   opens the Store (full recovery, which compares every surviving covered
   file with the pack), asks ACL2 for the covered names
   (`fn-bs-pack-reclaim-plan`, line 159), unlinks them in order with a cut
   after each (line 170) and closes with a transaction-directory barrier
   (line 172).

Opening afterwards (`fnn-recover`, host/native/io.lisp 1481-1485) takes
the pack boundary from `fn-store-checkpoint-compaction-coverage`
(checkpoint.lisp 234), observes the namespace through
`fn-store-txn-observation-selected` (io.lisp 760, body
`fn-profile-txn-observation`), reads each issued pair, and hands the pairs
to `fn-store-checkpoint-compaction-observe` (checkpoint.lisp 258), whose
answer is the single record list given to `fnn-bridge-recover`.
`pack-retire` (older pack generations) is separate and unchanged.

Both steps existed. What did not: a preservation theorem stated over the
functions these lines call (the observe/coverage wrappers were program-mode
host code, so no theorem could name them), one owner of the namespace bound
in the reclaim plan, and a native check of the served view.

## Theorems (books/checkpoint-compaction-preservation.lisp)

The host wrappers are now one-line calls (host/checkpoint-host.lisp 184,
190) of `fn-ccp-observe-framed` and `fn-ccp-coverage-framed`, logic-mode
copies of the previous bodies.

- `fn-ccp-reclaim-keeps-namespace-observation`: if
  `fn-profile-txn-observation NAMES MAX LOWER` is valid and GONE is any
  subset of `fn-bs-pack-reclaim-plan NAMES MAX LOWER`, the observation of
  NAMES without GONE is valid and is the old one with exactly GONE's pairs
  left out. Every process-death image of the reclaim program deletes such a
  subset.
- `fn-ccp-covered-deletion-keeps-reconstruction`: when
  `fn-ccp-observe-framed` answers `:ok`, leaving out pairs below the pack
  boundary does not change its answer.
- `fn-ccp-reclaim-preserves-reconstructed-history` (the composition): with
  LOWER the pack boundary and the pre-reclaim open succeeding (the reclaim
  command's own open), the open after the reclaim, at any cut, sees a valid
  namespace and reconstructs the identical record list, the bytes of every
  surviving name being unchanged (for the suffix:
  `fn-bs-selected-reclaim-crash-preserves-suffix-payload`, existing).
- `fn-ccp-complete-observation-reconstructs-its-records`: for a complete
  observation from 0 at least as long as the boundary, that list is exactly
  the records read, which is what the open handed replay before any pack.
- `fn-ccp-profile-upgrade-keeps-reclaim-plan`: one owner.
  `fn-bs-pack-reclaim-plan` now reads `fn-profile-txn-observation` (the
  inline `(<= (len names) maximum)` is gone), so the plan is monotone under
  an offline profile upgrade. The unused host twin
  `fn-store-txn-prefix-reclaim-plan` (host/store-host.lisp, no caller) is
  deleted. The coverage check's field-4 use is monotone
  (`fn-ccp-larger-count-keeps-coverage`), closing finding 2 of
  m5-profile-upgrade.

The step from "identical record list" to "identical served view" is by
definition, not a theorem: `fnn-bridge-recover` is a function of the record
list, the frontier and the configuration records, and the reclaim program
(`fn-bs-pack-reclaim-steps`, shape `fn-bs-pack-reclaim-steps-have-reclaim-shape`)
only unlinks transaction names and fsyncs the transactions directory. So
GROUP counts and watermarks, ARTICLE by number and Message-ID, HDR,
retention pins, undertakings and releases (all Store events) are unchanged.

Teeth (tests/acl2/checkpoint-compaction-preservation-tests.lisp): a
reachable five-event store (record, undertaking, release, identity event,
enrollment); the open before the reclaim, after losing covered names 1 and
3, and after the whole plan all reconstruct the same five records. Each
composition hypothesis has a concrete counterexample and a must-fail:
a suffix gap is refused; losing the newest suffix name is accepted by the
gate and drops record 4 silently (a missing tail is not a gap, so the
byte-level suffix keystone carries this); a plan computed above the pack
boundary deletes name 4 and loses it the same way; a conflicting surviving
covered file is refused before and would be accepted after. The record,
completeness, namespace, plan and coverage theorems each have one must-fail
per hypothesis.

## Certification

- persvati, `run-20260924T213519Z-7956`, manifest
  `planning/evidence/manifests/certify-20260924T213534Z-827010.json`
  (ACL2 8.7, w25 toolchain, `--affected-by
  books/byte-store-compaction-correspondence`): passed. Wall seconds:
  byte-store-compaction-correspondence 3.47, checkpoint-compaction 1.87,
  checkpoint-compaction-preservation 3.32, the two test books 2.97 and 3.47.
- hbox, w28 toolchain (`tools/certify_books.py --incremental`, evidence
  `build/acl2/certify-20260924T213604Z-1961631` in the scratch tree):
  the correspondence book, the new book and its tests passed; published to
  /tank/fn/certcache for the image.

## Native (hbox, scratch /tank/fn/scratch/m5-compaction/src)

Images built from this branch's tree (source = commit below plus the HDR
test fix) with `proof_artifacts.py acquire --profile default` (290 books,
artifact set `7e952b8f`) and `swarm-build sh tools/build_native_host.sh`:
developer core sha256 `f6b05c94...2809`, production core `96d96992...9d7b`.

`python3 -m unittest -v tests.test_native_checkpoint
tests.test_native_compaction_crash_map tests.test_native_cut_map
tests.test_native_profile_upgrade tests.test_native_topic_local`:
41 tests, OK, 7 skipped (three clone tests needing FN_RUN_NATIVE_CLONE or a
parent-alias fixture, four topic-local tests needing a source-matched topic
image). Log: `planning/evidence/m5-compaction/native-modules.log`
(sha256 `54e68bab...19bd`).

New cases:

- `test_reclaim_keeps_served_view_watermarks_and_next_number`: four
  operator POSTs, `checkpoint pack select`, two more POSTs (the suffix),
  `pack-reclaim`; the reclaim removes exactly the covered names and the
  suffix files are byte-identical; through a restarted owner, GROUP (count,
  low, high), ARTICLE by every number and every Message-ID, and
  `HDR Subject low-high` are identical; `store retention` is identical; a
  new POST lands at high+1 and every old article rereads identically.
- `test_reclaim_cuts_keep_served_view_and_next_number`: the same at every
  reclaim cut (`pack-reclaim-unlink` at each covered occurrence, and
  `pack-reclaim-directory`), SIGSTOP then SIGKILL; after each cut the
  suffix is byte-identical, only covered names are missing, the served view
  and retention are unchanged, the next POST gets high+1, and a resumed
  reclaim completes.

`tests/campaign/native_cuts.py` `verify_checkpoint_cut_map` now also pins
the theorem subjects: the reclaim calls `fn-bs-pack-reclaim-plan`, its
unlink/cut/barrier/cut order is `fn-bs-pack-reclaim-steps`'s, and the two
bridge wrappers call `fn-ccp-observe-framed` / `fn-ccp-coverage-framed`.
The campaign runner itself still does not iterate `CHECKPOINT_CUTS`; the
native module above does.

## Findings and what is open

1. There is only one entry to reclaim: the developer `checkpoint` verb. No
   operator verb reaches `pack` or `pack-reclaim`, so a production node
   cannot compact. "Both entries" for the cuts does not exist yet.
2. The byte model proves survival of the uncovered suffix at every cut, not
   "old or absent" for a covered name; a surviving covered file that
   differs from the pack is caught at open (`:conflict`, fail closed),
   not excluded by a theorem.
3. A missing newest suffix file is invisible to the namespace gate (tooth
   above). Nothing in reclaim can cause it (the plan never names it, no cut
   loses it), but the gate alone would not detect it.
4. The pack is the exact canonical history: one pack holds at most 4096
   events and 4 MiB, so this cannot compact an arbitrarily large store,
   and it recovers transaction-file overhead only, not bytes. Temporary
   space accounting and protected article-object closure (RET-005's other
   half) remain open, as do guards of the framed observe (Store-event
   decoder chain).
