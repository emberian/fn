# The NNTP probe's unit tests under D25: 2026-09-25

This lane changes only `tests/test_native_nntp_post_probe.py`. The judge
(`tests/campaign/native_nntp_post_probe.py`), the node and the books are
unchanged. Nothing was certified, nothing ran on hbox or the farm, and no
probe was run against an image.

**Result.** Before: 3 of 11 fail on dev `ec6d1fdc`
([p10-marker-model](p10-marker-model-2026-09-25.md), finding 3;
[m5-history-lifetimes](m5-history-lifetimes-2026-09-24.md)). After: 13 of 13
pass.

## What failed, and why

D25 ([decisions](../decisions.md)) keys duplicate versus conflict on the
poster's bytes, so a repost of a present article must be answered
`441 posting failed; this article is already stored here`. The judge's
`_repost_ok` was already changed to that rule (lane d25-dup-conflict); the
tests were not.

- `test_swallowed_arm_needs_one_log_line` built its passing row with the
  conflict line as the repost of a present article. Today's judge rejects
  that row.
- `test_the_6c0626c5_runs_fail_only_on_the_silent_swallow`, two subtests
  (the 6c0626c5 run and the probe-tables rerun), re-judged recorded runs
  made before D25. In those runs the owner's key held Injection-Date, so a
  repost in a later clock second got the conflict line (campaign 47bdb9a4,
  K1). Today's judge fails 8 and 7 rows of those runs, not 1.

## What the tests check now

- The swallowed-arm teeth expect the duplicate line on the repost. They also
  add a must-fail row: the same row with the conflict line.
- `RecordedRunTests` states in its docstring that the runs predate D25. The
  judge keeps no pre-D25 rule, so none is added. It re-judges four recorded
  runs with today's judge: 6c0626c5, the probe-tables rerun, and the
  47bdb9a4 run and its repeat (these two were not covered before). A row is
  *wording-affected* when its candidate was present and its recorded repost
  is the conflict line. Per run the test asserts:
  - the total is 40, and the count failing today is pinned at 8, 7, 9 and 5;
  - every wording-affected row carries exactly the repost-wording failure,
    and no other row does;
  - with that one failure removed, the only failure left in any row is
    `record-stage-unlinked eio`, `swallowed cleanup error 0 times`
    (probe-tables S1), which is itself wording-affected in all four runs;
  - the count failing today equals the number of wording-affected rows.
- The marker cuts are already in the pinned table: `EXPECTED_ARMS` holds
  all 23 post cuts, with the five marker cuts `uncertain`, and it is equated
  with `native_cuts.POST_CUTS`. The p10-marker-model merge put them there.
  Two new tests give them teeth:
  - `test_the_marker_cuts_are_uncertain_by_program_order` checks that all
    five marker cuts derive `uncertain`. With `fn-bs-marker-program` moved
    first in `POST_PROGRAMS`, `marker-created` derives `refused`, because it
    precedes the marker's rename, and `verify_post_arms` then refuses the
    table's `present`. So the arm comes from the program-order rule, not
    from the step position.
  - `test_marker_arm` checks that a `marker-created` EIO row answering
    uncertain, owner exit 3, article present, repost duplicate passes. The
    refused answer fails, and so do 240, exit 0, absent, and a conflict
    repost.

## Mutation checks

Each mutation was made to the judge, run, and reverted, with the file
restored and verified by diff:

- The pre-D25 repost rule (`{DUPLICATE, CONFLICT}` for a present article)
  fails `test_marker_arm`, `test_swallowed_arm_needs_one_log_line` and all
  four recorded-run subtests.
- Dropping the swallowed-arm log requirement fails
  `test_swallowed_arm_needs_one_log_line` and all four recorded-run
  subtests.

## Invocation

- `python3 -m unittest -v tests.test_native_nntp_post_probe` (Python
  3.14.7, macOS, in the lane worktree from `ec6d1fdc`): 13 tests OK.
- `make check`: exit 0. The warn-only ledger teeth-form lints are
  pre-existing.
- The test file's sha256 is `f9d1015e07fb84b127414551d74aea7df3fb43d509d212c1dfb85effe2a0e9dd`.
- The judge is unchanged. Its sha256 is
  `623736981b53cecf494d65dc2ad25cd58b34e72a828ea3230b527da0a5b67576`.

## Limitations

- The recorded runs have 18 post cuts. No recorded run covers the marker
  cuts at the wire, so the probe on a current image is still owed for them.
- The silent swallow (S1) remains a node defect. The tests pin it; they do
  not fix it.
