# M5: history classes and lifetimes, and the committed-history boundary (2026-09-24)

Lane `m5-history-lifetimes`, branch `lane/m5-history-lifetimes` from dev
`19709182`. It answers the [direction review](../review-2026-09-24-gpt6-direction.md)
§M5 and finding 3 of [m5-compact-verb](m5-compact-verb-2026-09-24.md).

## Contract

`specs/storage.md` §"History classes and lifetimes" (STO-010) names the
three capabilities that may remove state: packing, history compaction and
content reclamation, each with its own obligation. It then gives a table
of every class of durable state. The classes come from the Store record
kinds: article `fn-r`; `fn-e` undertake and release; `fn-stxe`, `fn-stxk`
and `fn-stxa`; consumer `fnce`; and the three topic kinds. The table also
covers the metadata frames, the configuration history, packs, checkpoints,
staging and the FNBS rows. For each class it names the future decision that
needs it, its lifetime, and which capability may remove it and on what
condition.

Today's compaction relieves the file count and per-file overhead only. The
headroom line should say so beside `transactions-used`; that wording is
specified, not printed (open). The section also states what chained packs
need (six items) and adds the committed-history boundary below. The M5 exit
clause in `planning/milestones.md` is restated per the review.

## The committed-history boundary (finding 3, design 1)

`committed-history.json` is an FNSM kind-3 frame that holds the
committed-record count.

- **Decision** (`books/store-history-marker.lisp`, prefix `fn-hm-`):
  - `fn-hm-after-commit SEQUENCE` is the frame of `SEQUENCE + 1`, or NIL at
    the end of uint32.
  - `fn-hm-open-verdict OBSERVATION RECORD-COUNT` returns one of:
    `(:admitted :unmarked)` when the marker is absent;
    `(:admitted :marked M)` when M is at most the record count;
    `(:refused :history-short-of-marker M)`;
    `(:refused :marker-damaged)`, for anything that is not a kind-3 frame,
    including a copied frontier frame;
    `(:refused :observation)`.
  - `*fn-hm-marker-program*` and `fn-hm-marker-cut-names` are the byte
    shape and its five cuts.
- **Host** (`host/native/io.lisp`):
  - `fnn-mark-committed` calls `fn-hm-after-commit`. It stages a `.stage-`
    file, writes it, fsyncs it, renames it onto the marker and fsyncs the
    root, with an `fnn-at` at each cut. Any OS error is uncertain: the
    store stays fenced and the transaction is not acknowledged.
  - It is called after `fnn-publish` returns `:durable` and before
    `fnn-finish`, at all three sites: `fnn-command-post`,
    `fnn-command-probe` and `owner.lisp` `fnn-owner-publish-prepared`.
  - `fnn-check-history-marker` calls `fn-hm-open-verdict` once, from
    `fnn-recover`, with `(length records)`: pack events plus suffix files.
    A refusal is a fault (exit 4) that names the reason, the marker and the
    record count.
  - `FN_NATIVE_POST_FAULT=<marker cut>:kill|eio` selects a cut, validated
    against ACL2's table.
  - `tools/native_program_check.py`: PASS, 0 mismatches over 5 programs.
- **Keystones:**
  - `fn-hm-run-keeps-every-open-admitted`: if `(fn-hm-admittedp st)` and
    `(car st) + (len ops) <= 2^32-1`, then `(fn-hm-admittedp (fn-hm-run ops st))`.
    The ops are any mix of `(:burn)`, `(:uncertain B)` and
    `(:commit CUT C)` at any cut, with the crash image old before the
    rename, old or new after it, and new after the barrier.
  - `fn-hm-open-refuses-a-lost-acknowledged-record`: for
    `end = (fn-hm-run post (fn-hm-step '(:commit :marker-durable c) st))`,
    if `(natp (car st))`, `(car st) + 1 + (len post) <= 2^32-1`,
    `(natp k)` and `k <= (car st)`, then
    `(fn-hm-open-verdict (cdr end) k) = (:refused :history-short-of-marker (fn-hm-marker-value end))`.
  - `fn-hm-decode-of-encode` is the codec round trip.
- **Teeth** (`tests/acl2/store-history-marker-tests.lisp`):
  - A reachable seven-step history: commit; burn; a commit crashed after
    its rename with the old marker kept; an uncertain publication whose
    record survives; commit; burn; an uncertain publication whose record
    does not survive. It is admitted at every prefix checked. With its
    newest record lost it is refused as `history-short-of-marker 4`, and
    further burns leave it unchanged.
  - An unacknowledged survivor above the marker is admitted. That is the
    stated limit.
  - For each hypothesis of both keystones, a `must-fail` of the
    conclusion's assertion at an instance where the other hypotheses hold.
- **Native** (hbox, a developer image of `7023c777`, core `a84dc2d9…`,
  [image-hashes.txt](m5-history-lifetimes/image-hashes.txt)):
  - `tests/test_native_history_marker.py` ran 6 tests, all OK
    ([native-marker.log](m5-history-lifetimes/native-marker.log)).
  - Two posts, then the newest transaction file deleted: `recover` exits 4
    with `committed history refused at open: history-short-of-marker marker=2 records=1`
    ([refusal-transcript.txt](m5-history-lifetimes/refusal-transcript.txt)).
  - A `prepublish` known abort and a SIGKILL at `record-staged-durable`
    each burn a reservation. The frontier moves, the marker bytes do not,
    `recover` succeeds, and the next post is sequence 2.
  - A store with no marker opens, and its next commit writes one.
  - A frontier frame in the marker's place is refused as `marker-damaged`.
  - All five marker cuts, under both SIGKILL and EIO (exit 3), recover.
    After each, the next post commits and a lost newest file is refused.
  - Neighbouring modules
    ([native-modules.log](m5-history-lifetimes/native-modules.log),
    [native-profile.log](m5-history-lifetimes/native-profile.log)):
    `test_native_cut_map`, `test_native_compaction_crash_map`,
    `test_native_crash_correspondence`, `test_native_checkpoint` and
    `test_native_profile_upgrade` pass. The last was rerun with
    `FN_NATIVE_HOST` set to the developer image, because no production
    image was built; its owner POSTs pass through the marker. There are
    four failures, none from this lane:
    - `test_native_and_python_frames_cross_open_byte_identically` needs
      `acl2` on PATH for the Python checkpoint tool.
    - The three `test_native_nntp_post_probe` failures expect the old
      duplicate wording. The compact-verb record lists this as its
      finding 7 (D25).
- **Cost** ([probe.txt](m5-history-lifetimes/probe.txt), `store ROOT probe 120`,
  32 KiB payloads, before = developer image of `5181e0ea`, interleaved, three
  runs each):
  - tmpfs: 109.9 ms per commit before and 108.1 after, which is within
    noise.
  - ZFS `/tank`: 325.7 ms before and 387.8 after, +62 ms per commit
    (+19%). The fastest runs are 279 before and 358 after. The ZFS spread
    is wide (before 279 to 360).
  - The marker is written in every profile, not behind `scale`. On the
    deployed kind of filesystem, 62 ms buys detection of a lost
    acknowledged record, and a commit there already costs about 330 ms.
    If ember prefers design 2 (the frontier carries the count, no extra
    fsync) or scale-only, the decision book is unchanged; only the call
    sites move.

## Certification

- persvati, `run-20260924T230612Z-64bc`, manifest
  [`certify-20260924T230629Z-1648710`](manifests/certify-20260924T230629Z-1648710.json),
  passed, source `7023c777`, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s:
  `books/store-history-marker` 2.5 s,
  `tests/acl2/store-history-marker-tests` 2.2 s. `--affected-by` on the new
  book selects only these two roots. The host includes it from the image
  build files, not from a certified host book.
- persvati, `run-20260924T232158Z-fa11`, manifest
  [`certify-20260924T232218Z-1792716`](manifests/certify-20260924T232218Z-1792716.json),
  passed, source `72d40647` (the export also withdraws the two accessor
  equalities), `--affected-by books/store-history-marker` (2 roots):
  book 2.6 s, tests 2.3 s.
- hbox, w28 `acl2-literal-4g`, `certify_books.py --incremental --jobs 6`
  over the default and DTN image roots (`proof_artifacts.py roots`) in
  `/tank/fn/scratch/m5-hist/src` (`git archive 7023c777`): 298 of 299
  installed from `/tank/fn/certcache`, `books/store-history-marker`
  certified, passed (`build/acl2/certify-20260924T230931Z-2146350` in that
  tree).

## Findings and what is open

1. The crash table is transcribed (rename atomicity), not a program of the
   `fn-bs` byte model. Adding the marker to `fn-bs-record-program` or as its
   own program would put it under crash model v2.
2. An absent marker is admitted. Deleting the marker with the newest files
   is not detected. Neither is replacing the whole store with an old valid
   copy (D14).
3. An unacknowledged record that survived above the marker is not covered
   (proved scope, and shown in the teeth).
4. The Python host (`tools/run_store.py`) neither writes nor checks the
   marker. A store it writes opens natively as `:unmarked`.
5. The configuration history and the FNBS stores have no marker.
6. History compaction and content reclamation remain unimplemented and
   need D13. The class table gives their obligations. The headroom
   wording is open.
7. The owner path writes the marker (`fnn-owner-publish-prepared`), and
   owner POSTs pass through it in the profile-upgrade and checkpoint
   modules. No test here yet asserts an owner-written marker's refusal.
