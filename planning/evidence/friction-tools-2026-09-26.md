# friction-tools (2026-09-26): the lane tools the friction review asked for

Brief: build/coordinator/queue/w2-friction-tools.txt, from
planning/review-2026-09-26-lane-friction.md (186 lane transcripts). Packets
PKT-277 to PKT-282 (planning/backlog-2026-09-25.md, section
`friction-tools (2026-09-26)`). No book, PRF, requirement or scenario changes.
This is harness work: no ACL2 decision moved; every tool below performs I/O,
formats what ACL2 or the runner already decided, or merges registry JSON.

## What changed

1. **tools/farm.py submit** (review section 2; PKT-277). A failed cache
   preflight now reports `exit N (meaning)`, `first error: <line>`, the whole
   stderr, then the stdout tail; before, it was the last 800 characters of the
   merged output, which was a book list. The preflight's stderr is captured
   separately (exit 13 and 14, the script's own codes, are named). Before any
   ssh or rsync, every book, `--affected-by` and `--recertify` word is checked
   against certify_books' `BOOK_NAME` rule and the tree: a word with
   whitespace (the zsh unsplit `$ROOTS`: 13 failed submits in 10 lanes), a
   leading `-`, an absolute or malformed path, or a missing `.lisp` is refused
   with the offending word and "no farm run started".
2. **tools/farm.py wait** (section 3; PKT-278). Ends with a fixed block,
   `== verdict RUN: exit N`, read from the fetched manifests: each manifest's
   status, certified-here passed/failed and installed-from-cache counts, each
   failing book with the first `ACL2 Error`/`FAILED`/timeout line of its own
   log (or the manifest's reason) and that log's local path, and the books
   over 10 s with the jobs they ran at. No manifest: "the verdict is unknown
   (not green)". The per-book `uncached:` and `unverified:` lists (hundreds
   of lines on an installed closure) are counts unless `--verbose`.
3. **hbox native** (section 5; PKT-279). tools/build_native_host.sh defaults
   `FN_OPENSSL_PREFIX` (and LD_LIBRARY_PATH) to
   /tank/fn/toolchains/openssl-3.5.8 when unset on hbox, and a failed build
   whose log mentions OpenSSL names the variable. The runtime refusal
   (host/native/signatures.lisp:117) now reads "OpenSSL 3.5 or newer is
   required for ML-DSA (set FN_OPENSSL_PREFIX)". New
   **tools/hbox_native.sh REV MODULE...**: ships `git archive REV` (or `.`,
   the worktree, rsynced with farm.py's excludes) to
   /tank/fn/scratch/NAME/native-LABEL/tree, then on the box, detached (nohup):
   install-partial from /tank/fn/certcache, `certify_books.py --incremental`
   under swarm-build, proof_artifacts acquire and validate, the requested
   images under swarm-build, each module under
   `systemd-run --user --scope --slice=swarm.slice -p MemoryMax=24G
   -p MemorySwapMax=0` (oom_score_adj reset as swarm-build does), logs in
   logs/, SHA256SUMS over the images and logs, `status` = first failing
   step's code. Locally it waits with tools/wait_for.sh and prints run.log
   (each module's `OK`/`FAILED`/skip line) and the sums.
4. **make check-lane** (section 6; PKT-280). `FN_LANE_CHECK=1` with one
   temp dir: tools/ledger.py's check writes planning/ledger.json and
   ledger.md there, tools/current_view.py --check writes current.md there,
   each prints whether it differs from the committed file, and only
   generation can fail. proofs.json's `events` arrays are still compared (a
   lane owns and commits its registry rows).
5. **Registry merge driver** (section 7; PKT-281). tools/merge_registry.py,
   routed by .gitattributes for planning/proofs.json, requirements.json,
   proof-events.json and tests/scenarios/catalog.json: id-keyed three-way
   (ours' order, theirs' new ids appended; a field changed on one side wins;
   both-changed lists union with ours' removals kept; proofs.json `events`
   keep ours for regeneration; an id both sides added differently is a named
   collision; any other both-changed field is `CONFLICT ID field`, exit 1,
   file left conflicted and valid JSON). Registration is per clone (git
   config), written as step 2a of build/coordinator/NIGHT.md's merge
   procedure for the coordinator to run after this lane lands; it is NOT
   registered now (a driver path absent from older trees would turn their
   merges into failures).
6. **tools/wait_for.sh** (section 8; PKT-282). `--log FILE REGEX`, `--file`,
   `--pid` (a zombie counts as exited), `--unit` (systemd --user), `--farm
   RUN REMOTE_ROOT` (exits with the run's code), `--host` to check over ssh,
   `--deadline` (default 3300 s). Exit 0 met, 124 deadline (uncertain), 4
   unobservable (ssh failed 5 times), 2 usage. No pattern matching of
   processes. BRIEF-COMMON's Shell section documents it, and its Deliverables
   gain "stop every watcher you started before your final message" (section 9).

build/coordinator/BRIEF-COMMON.md (untracked coordinator state) was edited:
Boxes (hbox_native.sh), Shell (wait_for.sh), Before a farm submit
(`make check-lane`; the OpenSSL line), Farm (the refusal and verdict block),
Deliverables (`make check-lane`; stop watchers). build/coordinator/NIGHT.md
gained merge step 2a (the driver registration and its replay numbers).

## What ran

- Laptop unit tests: `python3 -m unittest tests.test_farm tests.test_triage
  tests.test_merge_registry tests.test_ledger tests.test_current_view
  tests.test_wait_for`: 188 tests OK. New: 8 in test_farm (FrictionTests),
  9 in test_merge_registry (4 through real `git merge`, including the control
  that plain git conflicts on the same history), 2 in test_ledger
  (LaneCheckTests), 6 in test_wait_for. test_farm's fixture now seeds the
  book sources submit checks; test_triage's one submit test does the same.
- persvati, real submit: `farm.py submit persvati --affected-by
  tests/acl2/native-health-tests --jobs 2 --timeout-seconds 300
  --remote-root /home/ember/fn-gates/friction-tools-r1` ->
  run-20260926T015637Z-be24 (installed 165 of 165 from 16 origins, certify
  0); `farm.py wait` exit 0, ending with the verdict block (manifest
  certify-20260926T015700Z-3912426 status passed; certified here 0,
  installed 165; no book over 10 s), with the 165 `unverified:` and 754
  `uncached:` lines folded to one count line each. The same word-split
  `--affected-by "tests/acl2/native-health-tests --affected-by books/wire"`
  was refused locally with no ssh.
- hbox, real native run: `tools/hbox_native.sh --images developer,production
  --label r1 . tests.test_native_operator_verbs` -> status 0 in about 7
  minutes (certify 3 min 46 s: the books hbox's cache lacked at dev's
  bytes; both images; 22 tests, 0 skipped, OK), under
  /tank/fn/scratch/friction-tools/native-r1/. SHA-256:
  fn-host.core 70291e2853c0732bc32d1480cdf85db9a1f8a7fe1351f60726e18222844927d9,
  fn-host-developer.core 9c426da17be3af39d6a544932d6346f8d1745762ccf5ce5c1d3117591a161f6e,
  test log 6e833edae138cd2f0b2ac0558b1747ab06e06fd8b17be3e80bd27f35a25f9452
  (all sums in that directory's SHA256SUMS). The images include this lane's
  one-string change to signatures.lisp.
- Merge driver replay: the last 150 merges on dev re-merged with `git
  merge-tree --write-tree` in a scratch clone. Registry-file conflicts: 138
  with the text merge, 5 with the driver, all 5 real: three PRF id collisions
  (PRF-073, PRF-074, PRF-076 on 77683a08, d0603aa0, b021f7b7) and two
  concurrent edits of one `progress_note` (PRF-087 on d6db2dc0, PRF-014 on
  e8789315).
- `make check-lane` green (1 min 29 s); `make check` green.

## Before and after, one lane workflow (a red farm run)

Before: `submit` -> `wait` (hundreds of `uncached:` lines) -> `grep -v
uncached` -> find the run's evidence directory -> read manifest.json ->
locate `<book>.certify.log` -> read the failure: 3 to 6 calls per red run
(91 calls in 61 lanes). After: the `wait` notification's last lines are
`FAILED books/x: ACL2 Error [Failure] in ( DEFTHM ...)` and `log: <path>`;
one Read of that log. A native module on hbox went from a hand-written
rsync + image.sh + OpenSSL exports + polling loop (145 lanes, 1,035
ship-tree calls) to one background call.

## Not done

- The review's optional local reader check (3 "unbalanced close parenthesis"
  submits): not added; farm.py does not parse Lisp.
- merge_lane.sh still three-way-merges proofs.json itself; it can shrink
  once the driver is registered (the driver then does it inside `git merge`).
- The driver is not registered in git config (see 5).
- The zsh options themselves (`setopt no_nomatch sh_word_split; unsetopt
  equals`) are ember's shell configuration, not a lane's.
- hbox_native.sh builds only host/native/build.lisp images; the DTN images
  (build-dtn.lisp) are not an --images choice yet.
