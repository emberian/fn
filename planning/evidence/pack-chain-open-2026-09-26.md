# pack-chain-open, 2026-09-26 (Opus 5.5): stopped at step 1, the fixture is gone

Lane `lane/pack-chain-open`, worktree build/lanes/pack-chain-open. Branched from
lane/bounds-p5 at 9e94523e, not from dev: at launch (09:07 UTC) lane/bounds-p5
(pack-chain-join, PKT-332) had not merged into dev, so dev held no
books/checkpoint-pack-chain.lisp and no tests/test_native_pack_chain.py.
Ids held, none taken: PRF-145, PKT-331, SCN-064 unchanged.

## Step 1: the classification cannot run on the chain-native-8 store

The brief's step 1 copies the compacted 13-generation, 20,000-record store of
chain-native-8 from /tank/fn/scratch/bounds-p5 and times `store recover` and
`operator CONFIG run` to LISTENING on it. That store does not exist.

- The scale test builds its store under `self.base`, a
  `tempfile.TemporaryDirectory` made in NativeCheckpointTests.setUp
  (tests/test_native_checkpoint.py:29); `tearDown` calls
  `self.temporary.cleanup()` (line 38) on failure as on success. The
  chain-native-8 run failed at 02:29 UTC 2026-09-26 after 6,693 s and its
  tearDown deleted the store.
- /tank/fn/scratch/bounds-p5/tmp holds only fn-native-checkpoint-otfly5bg (42 MB,
  a cut test's leftovers: a single generation-0 pack and loose transactions,
  not the scale store). measure/ and measure2/ hold stores of at most 4,000
  records. /tank/fn/scratch/fixtures does not exist. The pack-chain-join tree
  (/tank/fn/scratch/pack-chain-join) holds reclaim-harness work stores of 300
  and 100 records.

Per the brief, the five-hour build is PKT-168's "build once" item and this lane
does not repeat it. Nothing was built or run on hbox.

## What the classification still has (no new measurement)

- The failure is at test line 117 (assert_view_kept_and_next_number ->
  served_view -> run_owner -> wait_for_announcement with its default
  timeout=180, tests/native_process.py:17). `run_owner`
  (tests/test_native_checkpoint.py:965) does not pass the class's
  served_timeout (1,800 s) to it, while `stop_owner` and the socket reads do.
- The `self.recovered(store, N)` on the line before passed: `store recover` over
  the 13-link chain completed within the class's native_timeout, so the offline
  open over the chain terminates. Its duration was not logged.
- The class comment records 49.5 s for the owner's open-time checkpoint over a
  20,000-record suffix on hbox (pre-compaction). The owner after compaction
  pays the chain walk (every link held as octet lists, PKT-168) plus that
  checkpoint; whether that exceeds 180 s is the unmeasured question.

Classification: still open (harness deadline or open cost). No deadline was
raised.

## The next exact action (the fixture, built once and kept)

The obstruction is the harness, not the proof: a scale fixture that tearDown
deletes cannot be built once. The fixture-builder should be a step that
survives the test: either a `FN_P5_KEEP=DIR` option on the scale test that
copies `scale-chain` (store and config) to DIR right after `store compact`
and before the served views, or a standalone builder script
(probe 20000 article, BEFORE view saved as JSON, compact) that writes
/tank/fn/scratch/fixtures/chain-20000-<image-rev>/ with a sha256 manifest and
the before view. Then steps 1 to 4 of the brief run against a copy of it. That
build is about 1.5 to 2 hours on hbox (probe about 0.25 s a commit, plus the
before view and compact) and needs the coordinator's word under PKT-168.
