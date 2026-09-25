# D31: the committed-history requirement and the retry resolution (2026-09-25)

Lane `marker-required`, branch `lane/marker-required` from dev `c8e1e9c1`.
It answers D31 and [the review of 2026-09-25](../review-2026-09-25-gpt6-decisions.md)
§3: the invariant A <= M <= D (A the committed prefix covered by success
answers a client may rely on, M the durable marker's count, D the durable
reconstructable length), its two open cases, the deployed store's migration,
and the design of a cheaper publication program.

## The field

- `config.json` format 8 gains a thirteenth frame natural, `history-marker`
  (`books/byte-store-frame.lisp`, position 14): 0 `unmarked`, 1 `required`.
  `fn-bs-profile-invalid-reason` refuses anything else
  (`history-marker-not-a-word`). The format-7 translation, both presets and
  the D27 defaults are `unmarked`. `fn-bs-profile-marker-requiredp` reads it
  through `fn-bs-profile-of`, so a format-7 store is `unmarked`.
- `init` never writes `required`: `fn-bs-profile-init-verdict` refuses it
  (`history-marker-required-before-a-marker`).
- The upgrade relation (`fn-profile-upgradep`) adds the field to its
  monotone list, so it rises and never falls (`not-an-upgrade history-marker`).
- Operator: `--history-marker unmarked|required` (a word, never a decimal;
  `fn-nop-profile-flag-value`, `books/native-operator.lisp`); `status` prints
  `history-marker=unmarked|required` (`fn-bs-profile-report-value`).
- Format 8 changed its layout; no format-8 store was deployed (the node
  runs c3420013, format 7). The two preset frames the profile-upgrade test
  pins are now development `a725e81e…` and scale `55960f4b…`.

## The catch-up point: recovery

Chosen: **at recovery**. After `fnn-recover`'s fifth barrier (the
reconstructed records are durable) and its staging sweep, and before the
open returns, a writable open writes `fn-hmr-catch-up`'s frame (the
reconstructed count, when the marker is absent or behind it) through
`fnn-mark-committed`, the same program and five cuts as a commit's. Why
there and not before the resolution: every answer a process gives about a
held record (NNTP POST's duplicate, `operator post`'s `DUPLICATE`, the
developer `duplicate`, BP `:duplicate`, an owner journal resolution) comes
from a process whose open has returned, so one site covers all of them, and
the cost is paid once per open rather than on the served path. An error in
the catch-up is uncertain (exit 3); the next open catches up again. A
shared-lock reader writes nothing and answers no submission (limit below).
The recovery and profile developer selectors accept the marker cut names;
`tools/native_program_check.py` maps the call as a sequel program
(`fn-bs-marker-program`) of `fnn-recover`: PASS, 0 mismatches over 6
programs; `native_cuts.verify_recovery_order` checks barriers, sweep,
catch-up, unfence in that order.

## The two-step migration

`store upgrade-profile --history-marker required` opens the store as
`recover` does, so its open writes the covering marker first (the marker
program); `fn-hmr-upgrade-verdict` then grants `required` only when the
marker is present and counts exactly the reconstructed history
(`history-marker-not-covering` otherwise); then the profile program writes
`config.json`. A format-7 store takes the 7-to-8 step and the requirement in
the same command.

## Theorems (`books/store-history-required.lisp`, prefix `fn-hmr-`)

The model state is (D marker A profile live); `fn-hmr-step` covers burns,
uncertain publications, commits in a live process crashed at any marker
cut or finished (`:marker-durable`: A covers the record), opens (the
catch-up crashed at any cut or completed; live only then), resolutions of
a held record in a live process (A covers it), and migrations whose
profile crash image is old or new. The host-called subjects and their
callers (`host/native/io.lisp`): `fn-hmr-open-verdict` and `fn-hmr-catch-up`
from `fnn-check-history-marker` (called by `fnn-recover-full-replay` and
`fnn-recover-from-state-checkpoint`); the catch-up frame written by
`fnn-recover`; `fn-hm-after-commit` from `fnn-mark-committed` at the three
commit sites (the finish path); `fn-hmr-upgrade-verdict` from
`fnn-command-upgrade-profile`.

- `fn-hmr-step-preserves-the-invariant`: `(fn-hmr-invp st)` implies
  `(fn-hmr-invp (fn-hmr-step op st))` for every op; the invariant is: the
  open admits under the profile, A <= M, and a live process's marker counts
  exactly D. (`fn-hmr-run-preserves-the-invariant` lifts it to runs.)
- `fn-hmr-open-refuses-below-every-answered-record` (A <= M over the finish
  and resolution paths): if `(fn-hmr-invp st)`, `(natp k)` and `k` is below
  A of `end = (fn-hmr-run ops st)`, then
  `(fn-hmr-open-verdict (nth 3 end) (nth 1 end) k)` is
  `(:refused :history-short-of-marker M)`.
- `fn-hmr-required-store-never-admits-an-absent-marker`: if the profile of
  `st` is required and `(natp k)`, then after any run the open of
  `(:absent)` at `k` is `(:refused :marker-missing)`.
- `fn-hmr-requirement-follows-a-covering-marker`: a step that makes an
  unmarked profile required is `(:migrate ...)`, from a live state whose
  marker counts D, and leaves that marker unchanged.
- `fn-hmr-legacy-store-migrates-by-the-two-step`: from an unmarked store no
  process holds, if two steps reach required then the first is an `:open`
  (the catch-up), the second a `:migrate`, over the covering marker.

## Teeth (`tests/acl2/store-history-required-tests.lisp`)

- Reachable witness of case 2 from a fresh store: open (marker 0), commit
  answered, next commit's record durable with the process killed at
  `marker-created`, open (catch-up), retry resolved (record 1). A = M = D
  = 2; with the newest file lost the open is
  `(:refused :history-short-of-marker 2)`. The same end is reached when the
  catch-up itself crashes at `marker-written` and `marker-replaced` first;
  no resolution is answered while no process is live.
- Migration witnesses: from that end, open then migrate gives the required
  profile, and an absent marker is `marker-missing`; a legacy state with the
  marker behind (M 2, D 3) is caught up to 3 before the migration, and a
  migration crashed with the old profile leaves it unmarked with the
  covering marker.
- Decisions: the verdicts, the catch-up (none when covering, count 0 on an
  empty store, none on a refusal), the upgrade gate (covering, behind,
  absent), the downgrade refused by name, the 7-to-8 step with the
  requirement, `init` refused, a third word invalid.
- Per keystone, the positive witness asserts every hypothesis and the
  conclusion; each hypothesis-removal witness asserts the retained
  hypotheses, the failure of the removed one, and `must-fail` of the
  conclusion. Keystone 1 and 2's invariant removal is a corrupted-state
  witness: a live process over a marker behind D (an open that skipped the
  catch-up) answers the retry and the lost newest file is then admitted.
  Keystone 2: `natp k` (−1 gives `:observation`), `k < A` (k = A admits).
  Keystone 3: unmarked admits; −1. Keystone 4: a required store answering a
  retry; a burn. Keystone 5: a live process; a required store; an open then
  a burn.

## Certification

- persvati, `run-20260925T083617Z-d5d9`, manifest
  [`certify-20260925T083645Z-2689158`](manifests/certify-20260925T083645Z-2689158.json),
  passed, source `b299cab4`, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s,
  `--affected-by books/byte-store-frame` (199 roots; 239 installed, 203
  certified), 497 s wall. `books/store-history-required` 5.7 s, its tests
  2.6 s, `byte-store-frame` 3.4 s, `store-profile-upgrade` 4.1 s,
  `native-operator` 6.3 s, `native-operator-tests` 4.6 s. `proof_cost`:
  every book under 10 s except `native-admin-peer` 10.2 s and
  `bp-report-guards` 10.2 s (warnings, bytes unchanged by this lane).
  `green_check --changed-since c8e1e9c1`: 7 changed books, 193 books include
  one; 0 not green.
- hbox, w28 `acl2-literal-4g`, `certify_books.py --incremental --jobs 12`
  over the 136 default image roots in `/tank/fn/scratch/marker-required/src`
  (the `b299cab4` tree): 205 installed, 119 certified, passed
  (`build/acl2/certify-20260925T083954Z-2932652` there).
- The test-only commit after `b299cab4` changes no book.

## Native (hbox, images of `b299cab4`)

Images [image-hashes.txt](marker-required/image-hashes.txt): `fn-host.core`
`4005d947…`, `fn-host-developer.core` `6b65a57c…`; run under
`systemd-run --user --scope -p MemoryMax=24G`.

- [native-required.log](marker-required/native-required.log) (sha256
  `4fbc933a…`): `tests.test_native_history_marker` and
  `tests.test_native_history_required`, 12 tests, OK:
  - developer entry, 5 marker cuts × kill/EIO: record durable at each; the
    retry prints `duplicate`, no new file, the marker equals a two-commit
    store's; newest file deleted: `history-short-of-marker marker=2
    records=1`, twice.
  - served owner, 5 × 2: the owner dies (SIGKILL) or exits 3 (EIO); a new
    owner answers the retry `accepted operator post DUPLICATE` (exit 0), no
    new file, the marker is the covering one; newest file deleted: refused,
    twice.
  - the catch-up's own cuts (`FN_NATIVE_RECOVERY_FAULT`), 5 × 2: the marker
    is the old or the covering one, the next open completes it, the retry
    is `duplicate`, the loss is refused.
  - migration: `status` `unmarked`, `init --history-marker required`
    refused, the upgrade prints `history-marker=required` and the marker
    counts the history; the downgrade `not-an-upgrade history-marker`
    (exit 1, config unchanged); marker deleted: `marker-missing` exit 4
    twice; restored, a post, newest file deleted: refused.
  - migration cuts (`FN_NATIVE_PROFILE_FAULT`), 10 cuts × kill/EIO: every
    marker cut reopens `unmarked`; `profile-created/-written/-staged-durable`
    reopen `unmarked` (EIO exit 1, known), `profile-replaced/-durable`
    `required` (EIO exit 3); in every case the reopened marker is the
    covering one, and after a retried upgrade a deleted marker is
    `marker-missing`.
- [native-neighbours.log.gz](marker-required/native-neighbours.log.gz)
  (uncompressed sha256 `9b22a2dd…`): `test_native_profile_upgrade`,
  `_cut_map`, `_crash_correspondence`, `_operator_verbs`,
  `_state_checkpoint`, `_profile`: 52 tests, 48 pass. This lane's one
  failure there (`ProfileUpgradeSourceTests` still named the old verdict) is
  fixed in the test commit and passed alone on the same image. Three are
  source-text drift in files this lane does not touch:
  `test_native_observation_wrapper_calls_composed_subject` (`fn-sn-io`),
  `test_peer_list_is_a_query_and_the_host_asks_acl2_which`
  (`fn-native-admin-peer-report`), and
  `test_the_uncertain_word_is_acl2s_control_vocabulary` (non-ASCII in
  `books/native-control.lisp`).
- Found on the way: `test_native_history_marker`'s source test looked for
  the open's check in `fnn-recover`, whose body never contained it (it is
  in `fnn-recover-full-replay`); the test now reads that function.

## The deployed store's migration

[migrate-c3420013.sh](marker-required/migrate-c3420013.sh), log
[migrate.log](marker-required/migrate.log) (sha256 `5c4aa6cc…`). The live
node was not used.

| step | result |
|---|---|
| c3420013 production: init, three posts through its owner | 3 transactions, marker 43 octets (`7ae1647f…`), format 7 |
| copy; new image `status` | `format=7 … history-marker=unmarked` |
| `operator store upgrade-profile --history-marker required` | rc 0, `format=8 … history-marker=required`; marker bytes unchanged (it already covered D) |
| downgrade | rc 1 `not-an-upgrade history-marker` |
| c3420013 opens the migrated store | rc 4 `ACL2 rejected durable configuration frame`: no in-place rollback |
| new production owner, one post | rc 0, 4 transactions, marker `652649b9…` |
| newest file deleted | developer and production `recover` rc 4 `history-short-of-marker marker=4 records=3` |
| marker deleted | rc 4 `marker-missing records=4` |
| contrast: unmigrated copy, marker deleted | rc 0, the open rewrites the marker (legacy) |
| c3420013 store with the marker one behind (its developer image killed at `marker-created`) | the upgrade's open catches up (`7451831e…` to `7ae1647f…`), then `required`; the retry is `duplicate`; the newest file deleted: `history-short-of-marker marker=3 records=2` |
| originals | untouched |

### Procedure for the hbox node

1. Deploy an image of this lane's bytes (after merge and the wave's
   qualification) as today; the first owner start opens the store and its
   recovery catches the marker up. Nothing else changes: the store stays
   format 7, `unmarked`.
2. Stop the owner (`systemctl --user stop` the unit): the upgrade takes the
   exclusive writer lock and is refused while an owner runs.
3. Snapshot the store directory (`zfs snapshot` of its dataset, or `cp -a`):
   the migration writes format 8, which a c3420013 image cannot open, so
   the snapshot is the rollback.
4. `fn-host --fn operator CONFIG store upgrade-profile --history-marker required`
   (production image). Expect `history-marker=required` and the unchanged
   budget. Exit 3 is uncertain: run `operator recover`, read `status`, and
   rerun step 4 if it still says `unmarked`. Exit 1 names the refusal.
5. `operator status`: `format=8 … history-marker=required`; `operator
   recover`: rc 0.
6. Start the owner. From here a missing `committed-history.json` is exit 4
   `marker-missing`, never a legacy open.

## Stated limits

- An unmarked store still admits a deleted marker with the files it
  covers; migrate it.
- A shared-lock reader (`serve` over a store under the shared lock) may
  serve a record above the marker until the next writable open; it answers
  no submission.
- Whole-store replacement by an older valid copy (D14), the configuration
  history and the BP stores are outside the marker.
- The model's profile crash image is "old or new" at every profile cut (a
  superset of the byte model's table); K0 at the catch-up cuts is not
  stated separately (the catch-up is the marker program from a quiet root
  after the recovery barriers; `fn-bs-k0-marker-cuts-relation` is stated
  in the completion window of a publication).

## Profile of the commit path on ZFS (with the marker)

[probe-zfs.sh](marker-required/probe-zfs.sh), [probe.log](marker-required/probe.log)
(sha256 `338050d6…`), [strace-c.txt](marker-required/strace-c.txt); developer
image of `b299cab4`, `store ROOT probe 120`, 32 KiB payloads, `/tank`.

- Three plain runs: 39.5, 30.4, 31.7 s, so 329, 253 and 264 ms per commit
  (the m5 figure with the marker was 388 ms; the ZFS spread is wide and
  these runs are not interleaved with a no-marker image, so they are not a
  before/after comparison).
- Per-fsync wall under `strace -T` (one run, 435 ms per commit under
  strace; 7 fsyncs per commit, 40.4 s of fsync over 120 commits = 336 ms
  per commit): store root directory 250 calls, mean 44.8 ms (two per
  commit: the frontier's barrier and the marker's); record stage file 56.9;
  transactions directory 48.5; marker stage file 45.1; staging directory
  45.2; frontier stage file 44.5 ms. The marker's two fsyncs are about 90
  ms of the 336 ms of fsync per commit under strace (27%); every fsync costs
  about the same on this pool (a ZIL commit each), so the cost of the path
  is the number of barriers, not which file they fence.

## A cheaper publication program (design, not code)

The contract to refine is D31's: an acknowledgment (240, or a resolution)
of record n is given only when M >= n+1 durably, M never exceeds D, and a
crash at any point leaves a store the open admits. Moving the count into
the allocation barrier is excluded (the frontier is reserved before the
record exists). Three candidates, from the measurement that each barrier
is one ~45 ms ZIL commit:

1. **Shared later barrier (frontier n+1 with marker n).** After record n's
   transaction-directory barrier, stage both the marker frame (n+1) and the
   next frontier (n+2 reservation), fsync both stage files, rename both
   into the root, one root fsync, then acknowledge n. The marker still
   follows the record's barrier (M <= D), and the acknowledgment still
   follows the marker's root barrier (A <= M); the next commit starts with
   its reservation already durable and skips its own frontier program. It
   saves one root fsync per commit (of seven). Model: a composite program
   (marker ∥ frontier renames, one barrier) whose crash image is, per
   entry, old or new independently; the frontier-ahead case is a burn,
   which keystone 1 already admits. Cost: an idle node holds one reserved
   number.
2. **Bounded group commit.** The owner collects up to G prepared
   submissions (or waits at most T ms, a work bound, never a data bound),
   links their G record files, fsyncs the transactions directory once,
   writes one marker of the last count, and acknowledges all G. Per commit
   the directory and marker barriers become 1/G. The history model needs a
   commit step of G records with a marker program at the end; A <= M holds
   because no member is acknowledged before the one marker barrier; a crash
   before it leaves up to G durable, unacknowledged records above M, which
   the recovery catch-up then covers. It needs the owner to hold more than
   one prepared submission, which today's serialized owner does not.
3. **Two-slot marker in place.** Replace the stage/rename/root-fsync with
   an overwrite of one of two fixed 43-octet slots (alternating), each with
   its count and digest, and one `fdatasync` of the marker file; the open
   takes the larger valid slot. It saves the stage file, the rename and the
   root fsync (one barrier of two). It needs a crash-model primitive the
   byte model does not have (an in-place overwrite that may tear within
   the written range); a torn slot fails its digest and the other slot
   (the previous count, still >= A) is read, so the invariant holds, but
   the primitive and its assumption must be added to crash model v2 first.

Recommendation: (1) first (no new crash primitive, a composition of two
programs the model already has, one barrier fewer per commit); (2) when
the owner pipelines submissions; (3) only with a crash-model extension.
Each lands as a program of the byte model with its crash theorem and the
same `fn-hmr` keystones re-proved over the new step, and is measured
interleaved against this image on `/tank`.
