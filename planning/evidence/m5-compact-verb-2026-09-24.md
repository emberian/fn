# M5: `operator CONFIG store compact`, the operator entry to compaction (2026-09-24)

Lane `m5-compact-verb`, branch `lane/m5-compact-verb` from dev `0e4b318e`.
Commits `4e8e88a7` (verb, decision book, host, campaign, tests), `08288a61`
(Makefile roots), `41451c3e` (native-operator proof cost, docs, PRF-073
events), `5181e0ea` (lower-case store-action subject), and the evidence
commit that carries this file. Follows
[m5-compaction](m5-compaction-2026-09-24.md), whose findings 1, 3 and 4 this
lane answers; finding 2 (covered files checked at open, not proved) is
unchanged.

## The verb

`fn operator CONFIG store compact` takes no argument. ACL2 parses it
(`fn-nop-parse-store`, `books/native-operator.lisp`) to the native action
`:compact`. `host/native/operator.lisp` `fnn-operator-execute-store-action`
calls `*fnn-compact-callback*`, which `host/native/checkpoint.lisp` sets to
`fnn-command-compact`. An image without checkpoint.lisp (the DTN image) has
no callback: `usage operator action compact needs the checkpoint surface,
which this image omits`, exit 5 (checked on the DTN image of `5181e0ea`).

`fnn-command-compact` opens the store with `fnn-open-live-store root t`
(exclusive lock, full recovery), so a running owner refuses it (`store is
already locked`, exit 1). `fnn-compact-steps` then observes once: the
selected pack's coverage boundary, the sorted transaction namespace (bounded
by profile field 4), the pack namespace plan, and the lstat size of every
transaction file and pack generation. It hands these, the decoded profile
and the reconstructed record list to `fn-store-compact-decide`
(`host/checkpoint-host.lisp`, a one-line call of `fn-cverb-decide`) and
carries out exactly the steps it returns, in its order:

| ACL2 answer | host calls |
| --- | --- |
| `(:compact (:pack :select :reclaim :retire))` | `fnn-pack-publish-generation`, `fnn-pack-select`, `fnn-pack-prefix-reclaim`, `fnn-pack-retire-older-generations` |
| `(:compact (:reclaim :retire))` | the last two; no pack is written |
| `(:refused REASON)` | nothing; exit 1, `refused operator compact compaction refused: REASON` |

Reasons: `profile`, `observation`, `empty-history`, `already-compact`,
`exceeds-compaction-unit`, `temporary-space`. Exit codes stay distinct: 0
done; 1 refused (a named refusal, the held lock, or a step's known failure
before its durable change); 3 uncertain (a step's I/O error after its durable
change: publication, selection, reclaim or retire); 4 fault. The report line
is `compacted steps=pack,select,reclaim,retire records=N generation=G
reclaimed=K retired=R`.

Host refactor: the pack's generation publication now passes the checkpoint
candidate observer, and the pack selection and the checkpoint selection share
one marker loop (`fnn-marker-replace`), so a pack reaches every
`candidate-*` and `selection-*` cut the checkpoint does.

## Theorems

`books/store-compact-verb.lisp` (prefix `fn-cverb-`):

- **`fn-cverb-pack-fits-the-profile-budget`** (temporary space). If
  `(fn-cverb-decide profile records lower names generations selected
  footprint)` is `(:compact (:pack :select :reclaim :retire))`, then for every
  frontier, `(fn-cverb-octet-sum footprint)` plus the length of
  `(fn-cc-encode (fn-cc-nth 1 (fn-cc-capture records frontier)))` plus
  `*fn-frame-trailer-octets*` is at most field 3 of the profile. The host
  seals exactly that encoding (`fn-store-checkpoint-compaction-capture`,
  called by `fnn-pack-publish-generation`; `fnn-seal` appends the 32-octet
  trailer). One hypothesis. Its lemma
  **`fn-cverb-capture-within-pack-octets`** has no hypothesis: whatever the
  capture returns, its encoding is at most `fn-cc-event-octets-size records`.
- **`fn-cverb-pack-decision-capture-succeeds`** (the unit covers the
  capture's refusals). If the decision is the pack steps, the frontier is a
  uint32, and the records are exact Store events from sequence 0 below it
  (`fn-cc-octet-event-listp records 0 0 frontier`), the capture the host then
  calls answers `:ok`. The capture's `(<= (len records) frontier)` is derived
  (`fn-cverb-event-list-within-frontier`), not assumed.
- **`fn-cverb-profile-count-within-pack-events`**: every named profile's
  field 4 is at most `*fn-cc-max-events*` (4096). A fact about constants: the
  pack's event limit never refuses a store the open admitted.
- `fn-cverb-covered-history-writes-no-pack-by-definition`: when the boundary
  equals the record count, the decision is never the pack steps (a retry
  after a cut at or after the selection writes no second generation).
- **`fn-cverb-open-history-gate-admits-a-lost-suffix`** (finding 3, below).

`books/native-operator.lisp`:

- **`fn-native-operator-run-store-compact-is-the-compact-action`**: argv
  texts `("store" "compact")` and an accepted result give native action
  `:compact`.
- **`fn-native-operator-run-compact-action-is-only-store-compact`**: native
  action `:compact` implies the argv texts are exactly `("store" "compact")`.
  The subject is `fn-native-operator-run`
  (`host/native-operator-host.lisp` `fn-native-operator-host-run`) and the
  projection `fnn-operator-dispatch-plan` dispatches on.

Teeth (`tests/acl2/store-compact-verb-tests.lisp`): the five-event
reachable history (record, undertaking, release, identity event, enrollment)
packs on a fresh development store, its capture succeeds, and the real pack
fits (accounted size within 57 octets of the real encoding); resume on
retry, `already-compact`, re-pack with new records, each refusal by name;
`temporary-space` with 24 MiB minus 100 of footprint, and a must-fail of the
budget conclusion there; a 4097-event valid history refused as
`exceeds-compaction-unit` by the decision and by the capture (must-fail of
the capture conclusion without the decision); the capture refused at
frontier 2^32 and on non-event bytes, each with the other hypotheses holding;
a 5000-transaction non-named profile; for finding 3, the history and its
prefix both admitted, the namespace with and without the newest name both
valid, and an improper prefix refused (must-fail). `native-operator-tests`:
the plan, `store compact now` is usage (5), and must-fails for each
hypothesis of the two operator theorems.

## Finding 3: a lost newest transaction file cannot be detected at open

The brief asked for an open check that the allocation frontier names the
next sequence. It does not, and no check over this observation can work:

- The frontier is a transaction ID, shared by the configuration and Store
  histories, reserved (written durably) before the record it names
  (`fnn-advance-frontier` before `fnn-publish`).
- A reservation abandoned by process death or by a known pre-publication
  failure leaves the frontier above the last record's txid, and replay
  accepts that gap by design (`fn-replay-advance-okp`, "a known-aborted
  transaction gap", `books/replay.lisp`). Several abandoned reservations in a
  row leave a gap of any size.
- So a store whose newest record file was lost and a store in which that
  record's reservation was abandoned present the same observation: the same
  names, the same bytes, the same frontier.
  `fn-cverb-open-history-gate-admits-a-lost-suffix` states the gate's side:
  `(fn-sn-observed-historyp frontier (append prefix suffix))` with a true-list
  prefix implies `(fn-sn-observed-historyp frontier prefix)`. The test book
  shows both observations concretely.

Detecting the loss needs a durable witness written after the record's
commit. Options, for ember (they change the per-article write path, so no
default is adopted here):

1. a committed-count marker rewritten after each record's directory barrier:
   one more replace and two fsyncs per article; detects any lost suffix;
2. the frontier frame carrying the committed record count at each
   reservation: no extra fsync, but a format change (migration of the
   deployed frontier), and it detects every loss except the newest record,
   which stays indistinguishable from an abandoned reservation.

## The compaction unit and temporary space

- The pack's 4096-event limit equals scale's transaction budget, so it never
  binds (`fn-cverb-profile-count-within-pack-events`).
- The 4 MiB octet limit is kept as the compaction unit. The open reads the
  selected pack as one bounded read and decodes it as one value before any
  transaction file, so the bound is the open's largest single allocation.
  Making it profile-sized (768 MiB at scale) has no measurement behind it.
  A history whose pack would exceed 4 MiB is refused as
  `exceeds-compaction-unit`, and it stays refused: each compaction repacks
  the whole history. Chained packs are open.
- Temporary space is accounted against the profile's aggregate record bound
  (field 3: 24 MiB development, 768 MiB scale). The pack is written beside
  every file it replaces, so their sum must fit. This is the profile's
  budget, not the filesystem's free space. ENOSPC during the pack write is
  the publication's known failure (exit 1, nothing selected); during
  selection it is the marker's outcome class.

## Certification

- persvati, `run-20260924T222327Z-e108`, manifest
  [`certify-20260924T222342Z-1269313`](manifests/certify-20260924T222342Z-1269313.json),
  passed, source `08288a61`: `books/store-compact-verb` 3.4 s,
  `tests/acl2/store-compact-verb-tests` 3.3 s,
  `books/byte-store-compaction-correspondence` 3.9 s,
  `tests/acl2/native-operator-tests` 5.1 s; `books/native-operator` 30.2 s.
  One lemma cost 25 s. It was split and re-proved; see the next run.
- persvati, `run-20260924T222750Z-e6f9`, manifest
  [`certify-20260924T222809Z-1310195`](manifests/certify-20260924T222809Z-1310195.json),
  passed, source `41451c3e`, `--affected-by books/native-operator
  --affected-by books/store-compact-verb` (5 roots, 2 already certified at
  these bytes by the first run): `books/native-operator` 4.2 s,
  `host/native-operator-host` 4.3 s, `tests/acl2/native-operator-host-tests`
  4.2 s, `tests/acl2/native-operator-tests` 5.4 s. ACL2 8.7, w25
  `acl2-literal`, 2 jobs, 300 s timeout.
- hbox, w28 `acl2-literal-4g`, `certify_books.py --incremental --jobs 6` over
  the default and DTN image roots plus the two new roots, in
  `/tank/fn/scratch/m5-compact/src2` (tree `git archive 41451c3e`):
  238 installed from `/tank/fn/certcache`, 56 certified, passed
  (`build/acl2/certify-20260924T222746Z-2059943` in that tree; not
  published to the cache).

## Native (hbox, images from `5181e0ea`)

`tools/runbooks/hbox-image-build.sh` in the tree above, with the two files
`5181e0ea` changed. Image hashes are in
[image-hashes.txt](m5-compact-verb/image-hashes.txt): production core
`df13b07b…`, developer core `b6c9ee00…`, DTN `3c131190…`, DTN developer
`33531cc9…`.

- The checkpoint cuts through both entries, developer image:
  `python3 -m tests.campaign.native_operator_campaign --checkpoint-only`,
  [campaign-checkpoint.json](m5-compact-verb/campaign-checkpoint.json)
  (SHA-256 `f257f6b33c2c99fa23adc3d8729bb5c2f3591a3d4d9df78b5703d622fd210aa6`):
  **10 of 10 `CHECKPOINT_CUTS` pass through both entries** (20 of 20).
  - The cuts: `candidate-file`, `-link`, `-directory`; `selection-file`,
    `-replace`, `-directory`; `pack-reclaim-unlink`, `-directory`; and the
    two retire cuts added here, `pack-retire-unlink`, `-directory`
    (`fn-cprt-retire-steps`).
  - Each entry is seeded with two articles, the first already compacted.
    The developer entry is `checkpoint pack ROOT select`, then
    `pack-reclaim`, then `pack-retire`; the operator entry is `store compact`.
  - Each is killed at the cut (SIGSTOP at the site, then SIGKILL), and
    `recover` exits 0. Both articles reread byte-identical through
    `store ROOT inspect`, before and after resuming through the same entry.
  - A further `store compact` is refused `already-compact` (1), and a new
    POST gets GROUP high+1.
- Modules, [native-modules-2.log](m5-compact-verb/native-modules-2.log)
  (SHA-256 `0e3b51227a8c387a1546f95facc8d7a35252561969019a11a28565b4298ab1a0`):
  `tests.test_native_checkpoint`, `tests.test_native_compaction_crash_map`,
  `tests.test_native_cut_map`, `tests.test_native_profile_upgrade` and
  `tests.test_native_operator_verbs`: 56 tests, 52 ok, 3 skipped (clone
  fixtures) and 1 failure.
  - **The production test passes:**
    `NativeProductionCompactTests.test_operator_compact_keeps_every_article_and_next_number`
    runs on the production image. It posts five articles. `store compact` is
    refused (1, `locked`) while the owner runs. With the owner stopped, it
    compacts: every transaction file is reclaimed. Through a restarted owner,
    GROUP, ARTICLE by every number and Message-ID, HDR and `store retention`
    are identical, and the next POST is at high+1. A second compaction packs
    six records, reclaims one and retires generation 0. A third is refused
    `already-compact`. `store compact now` is usage (5). The view is
    identical again, and the next POST is at high+1 again.
  - The one failure,
    `NativeOperatorCapacityTests.test_the_default_profile_budget_is_reported_and_refused_by_name`,
    expects the old duplicate wording (`this article is already stored here`).
    The image answers a Message-ID conflict (`a different article with this
    Message-ID is stored here`). This lane did not touch that path; it
    follows D25 on dev.
- Production refuses a checkpoint selector:
  `FN_CHECKPOINT_TEST_STOP=pack-reclaim-unlink fn-host --fn operator … store
  compact` exits 5 before any store is opened.

## Procedure: compact the deployed node's store offline (the coordinator runs it)

The deployed image (`18c91321`) has no `store compact`. First install an
image built from a dev containing this branch, qualified the usual way,
beside the current one as `/tank/fn/node/fn-<rev>` (`packaging/install-native.sh`).
Do not repoint `ExecStart` yet.

1. Record the state. Run
   `/tank/fn/node/fn-<rev>/bin/fn operator /tank/fn/node/fn.toml status`
   (expect `headroom transactions-used=N transactions-budget=4096 …`, with N
   about 9). Also record `ls -l /tank/fn/node/store/transactions` and
   `sha256sum /tank/fn/node/store/transactions/*`. Copy the store aside:
   `cp -a /tank/fn/node/store /tank/fn/node/store.before-compact-<stamp>`.
   It is small, and the copy is the rollback.
2. Stop the node's unit and confirm the process is gone.
3. Run
   `/tank/fn/node/fn-<rev>/bin/fn operator /tank/fn/node/fn.toml store compact`.
   Expect exit 0 and
   `compacted steps=pack,select,reclaim,retire records=N generation=0 reclaimed=N retired=0`.
   - Exit 1 `already locked` means an owner still runs; go back to step 2.
   - Exit 1 with another reason: nothing was written. Record the reason and
     stop.
   - Exit 3 means uncertain. Run `recover`, then step 3 again: it resumes
     (`steps=reclaim,retire`) or reports `already-compact`.
4. Run `status` again. `transactions-used` must equal N: compaction removes
   files, not transactions. `store/transactions` should now be empty, and
   `store/packs` should hold generation 0 and the selection marker.
5. Start the unit on the new release (repoint `ExecStart` to `fn-<rev>`).
   Run the LAN probe (`tools/node_probe.py … --group fn.agents`). Every
   earlier article must read back.
6. Rollback: stop the unit, move the compacted store aside, restore
   `store.before-compact-<stamp>`, and start. Before starting an older release
   on the compacted store, open it read-only with that release
   (`fn-<old>/bin/fn operator fn.toml status`). Only an image that loads the
   pack path can open it.

## Findings and what is open

1. Finding 3 is not detectable from the open's observation (above). A
   post-commit witness is a decision for ember.
2. Compaction is not a headroom tool. The transaction budget counts committed
   records, and they are unchanged; the pack holds the same bytes as the
   files. What it reclaims is the transaction-file count and per-file
   overhead. Admission headroom beyond the budget needs D13 history pruning.
3. At open, the aggregate replay bound counts only the suffix files read.
   The pack's events are bounded separately by the 4 MiB unit, so the open's
   input is at most field 3 plus 4 MiB.
4. The unit keeps compaction to histories whose pack is at most 4 MiB, and
   that limit is permanent per store (each compaction repacks everything).
   Chained packs are open.
5. The retire step is a step of the verb (the brief named pack, select and
   reclaim). Without it, generations accumulate, each counting against the
   temporary-space budget.
6. Finding 2 of m5-compaction (covered files checked at open, not proved)
   and the unverified guards of the framed observe are unchanged.
7. `test_native_operator_verbs` duplicate wording (above), not this lane's.
8. Store actions now report their subject in lower case
   (`accepted operator status`, `… upgrade-profile`, `… compact`), as
   `test_native_v0_matrix` already expected. Before this they printed the
   keyword (`STATUS`).
