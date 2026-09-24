# The NNTP probe and the crash-model differential with derived expectations: 6c0626c5, 2026-09-24

This lane fixes the two test-tooling defects found by the 6c0626c5 campaign
([campaign-6c0626c5](campaign-6c0626c5-2026-09-24.md), H1 and H2) and reruns
both tools on the same frozen developer/production pair. It certifies nothing
and proves no theorem. The node was not changed.

**Result in one line.** Probe: **39 of 40** rows pass. The failing row is
`record-stage-unlinked` EIO, which answers `240` with the article durable. The
host swallows that EIO and writes no log line, and the probe now requires one
(finding S1 below). Differential: **7 of 7** tests OK, including all 18 post
cuts. At every cut the model's programs now write the frames ACL2 derives from
the article the test sent. At every cut past a program's write, the octets on
disk are exactly those frames.

## What changed in the tooling

- **H1, the probe's expectation, derived from the model coordinate.**
  `post_arm` (`tests/campaign/native_nntp_post_probe.py`) reads the cut's
  program from `books/byte-store-programs.lisp` (`native_cuts.model_steps`)
  and puts the cut in one of four arms:
  - **refused**: before the program's first rename or link into a directory
    other than staging. EIO answers exactly `441 posting failed; the store
    could not write the article, nothing was stored`, owner exit 0, article
    absent, and a repost must be made and answered `240`.
  - **swallowed**: between two best-effort staging steps after the published
    directory's barrier. EIO answers `240`, owner exit 0, article present, and
    the owner log must name the swallowed cleanup error exactly once:
    `SWALLOWED_LOG`, one line naming `staging`, `cleanup` and `EIO`/errno 5.
  - **consumed**: a program with no syscall (P-FINISH). EIO answers `240` or
    the uncertain line, owner exit 3, article present.
  - **uncertain**: every other cut. EIO answers the uncertain line, owner exit
    3, fate per the table.

  Kill rows now also take their fate from the table's candidate column
  (`either` is unconstrained). The hand list `PRE_PUBLICATION` is gone. There
  are two cross-checks. `verify_post_arms` refuses a table whose candidate
  column contradicts an arm. `native_cuts.verify_swallowed_cuts` (in
  `verify_native_cut_map`) checks that the `fnn-at` of exactly the swallowed
  cuts lies inside `fnn-publish`'s `ignore-errors` (`host/native/io.lisp`).
  The derived arms: refused = frontier-created, -written, -staged-durable,
  record-created, -written, -staged-durable; swallowed = record-stage-unlinked;
  consumed = finish-consumed, -durable; uncertain = the other seven.
- **H2, the differential's program octets derived from the post.**
  `tests/test_native_crash_model.py` no longer builds the model programs from
  octets read at the cut. ACL2, in the bridge, derives the following:
  - **The next frontier frame.** `fn-bs-frontier-encode (fn-bs-frontier-next
    (fn-bs-frontier-decode <pre-post frontier>))`.
  - **The candidate's FNST frame.** `fn-sn-article-record` is the constructor
    `fn-store-sn-prepare` calls. It runs over the opened pre-post state with
    the Message-ID, payload and group the test sent,
    `fn-id-subject-of-payload`/`fn-id-obligation-of`/`fn-id-text` identities,
    and `fn-charge-for-payload`. The result goes through
    `fn-frame-store-protected (fn-store-event-encode …)` and is then sealed
    with `fn-frame-trailer`, as `fnn-frame` does.

  Two inputs do not come from the article:
  - **The record stamp.** This is the owner's wall-clock second on the DTN
    epoch. The test brackets the post with `time.time()` and tries each POSIX
    second in `[t0, t1]`, shifted by ACL2's `fn-nntp-unix-dtn-ms`.
  - **The release evidence.** This is the local-post provenance of the
    store's configuration, taken from the prior record that the same
    configuration wrote.

  The observed staged or published frame must be a prefix (possibly empty)
  of the intended frame for one stamp in the window. Past the program's
  `write-all` step it must equal that frame. At `record-created` the stage
  must be empty. The model program then writes the intended frame.

  The teeth are in `test_the_frame_is_the_sent_articles_not_anothers`: at
  `record-written` a one-octet-different article fails, and so does the
  right article with the window shifted 100 s.
- `tests/test_native_nntp_post_probe.py` (11 tests) does four things. It pins
  the 18 arms. It shows that moving the model's link moves the arm. It shows
  that a moved `fnn-at` and a contradicting table column are both refused. It
  covers each arm's must-fail rows, including the stale pre-H1 answer at
  `frontier-created`. Finally it re-judges both recorded 6c0626c5 probe runs:
  each fails only `record-stage-unlinked eio`, and only on the log line.

## Invocation

| what | value |
| --- | --- |
| images | `/tank/fn/gates/qual-6c0626c5-20260924/build/images/6c0626c5/`, read-only; `sha256sum -c image.sha256` all OK ([`image-check.log`](probe-tables/image-check.log), same SHA-256 `a2d6da08…` as the campaign's) |
| env | [`env.sh`](probe-tables/env.sh): `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, `LD_LIBRARY_PATH`, `FN_NATIVE_SOURCE_ROOT` = the gate tree, `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g`, Python 3.12.7 |
| driver tree | `/tank/fn/scratch/probe-tables/tree`: a `cp -a` of `/tank/fn/scratch/campaign-6c0626c5/tree` (the gate's `host/ tests/ tools/ books/` with certificates) with this lane's four test files over it ([`tree.sha256`](probe-tables/tree.sha256): `host/native/io.lisp` `df042ce8…`, the gate's) |
| script | [`run.sh`](probe-tables/run.sh), once, 16:26:54Z to 16:29:12Z: the image check; `python3 -m unittest -v tests.test_native_nntp_post_probe`; `python3 -m tests.campaign.native_nntp_post_probe --images $G --work $S/probe-work --out $S/nntp-probe.json` (1:08, peak RSS 320 MB); `FN_NATIVE_CRASH_HOST=$G/fn-host-developer python3 -m unittest -v tests.test_native_crash_model` (1:09, peak RSS 468 MB) |
| ports | kernel-assigned on 127.0.0.1; nothing touched `/tank/fn/node` |

## Probe: per cut, EIO rows (kill rows: 18 of 18 pass)

| cut | arm | reply | owner exit | candidate | repost | verdict |
|---|---|---|---|---|---|---|
| frontier-created, -written, -staged-durable | refused | `441 … nothing was stored` | 0 | absent (`inspect` 1, `430`) | `240` | pass ×3 |
| frontier-replaced, -attempted, -durable, -reserved | uncertain | `441 … the outcome is uncertain, do not repost` | 3 | absent | `240` | pass ×4 |
| record-created, -written, -staged-durable | refused | `441 … nothing was stored` | 0 | absent | `240` | pass ×3 |
| record-linked, -attempted, -durable, -completing | uncertain | uncertain line | 3 | present, identical | duplicate/conflict | pass ×4 |
| **record-stage-unlinked** | swallowed | `240 article received OK` | 0 (SIGTERM) | present, identical by both readers, `recover` `2 2 0` | conflict | **FAIL**: `owner log names the swallowed cleanup error 0 times, not 1` |
| record-staging-cleaned | uncertain | uncertain line | 3 | present | conflict | pass |
| finish-consumed, finish-durable | consumed | uncertain line | 3 | present | duplicate/conflict | pass ×2 |
| controls (dev accepted+SIGKILL, dev no-From, prod accepted+SIGKILL, prod mid-article SIGKILL) | control | as the campaign | | | | pass ×4 |

**39 of 40.** Across the 18 EIO rows the arms give 6 refused, 8 uncertain,
1 swallowed and 2 consumed, and the node's bytes match every arm except the
swallowed row's log line. `record-linked`'s `either` was observed present.
The owner log of the failing row, in full
(`probe-work/record-stage-unlinked-eio/owner-*.err`):

```
accepted post path=control message-id=<prior@campaign.invalid> time=2026-09-24T16:27:47Z
accepted operator run
accepted reader connection=0 time=2026-09-24T16:27:47Z
accepted post path=served connection=0 message-id=<candidate@campaign.invalid> agent=fn.example.invalid time=2026-09-24T16:27:47Z
accepted operator run
accepted reader connection=0 time=2026-09-24T16:27:48Z
…
```

### S1: the host swallows a cleanup error without a trace (finding, host)

`fnn-publish` runs `(ignore-errors (fnn-unlink stage) (fnn-at store
:record-stage-unlinked) (fnn-fsync-dir (fnn-staging store)))`. The error of
the best-effort staging cleanup after `record-durable` is discarded, and it
leaves no line in the owner log. The client's `240` is correct (P-RECORD
swallows it: the record is durable). But an operator cannot see that a
staging unlink or the staging-directory barrier failed. A persistent EIO
there would be silent on every post. Neither the model nor the host has an
observation for it (p10-k0-b: "the host swallows cleanup errors where the
model stops"). The probe now requires exactly one owner-log line naming the
staging cleanup and the error. The host lane may choose the other words of
that line. That lane has not been opened. The assertion was not weakened.

## Differential: `tests.test_native_crash_model`, 7 of 7 OK

| test | result |
|---|---|
| `test_all_native_post_process_death_cuts` (18 subtests) | OK: at every cut the observed frontier and record octets are a prefix of the ACL2-derived frames, equal past the write, and the scan, open, served image, directories and transaction names equal the model image of the programs writing those frames |
| `test_the_frame_is_the_sent_articles_not_anothers` (new; 2 subtests) | OK: at `record-written`, a different article and an out-of-window stamp each fail `prefix of no intended frame` |
| `test_recovery_stage_unlink_process_death_scans_and_reopens`, `test_injected_outcomes_stay_refused_or_uncertain_and_recover`, 3 source tests | OK |

At `frontier-created` and `record-created`, the check is no longer made
against a program that writes zero octets. The model program writes the
derived frame, and the staged file on disk is the empty prefix of it. The
derivation was first checked on its own at `record-durable`. There the
published `.txn` (365 octets) equals the ACL2 frame for the article sent,
byte for byte. The first attempt differed only at the 4-octet stamp:
`0x32480b90` against `0x6ab54f10`, the DTN and POSIX epochs. That is why the
stamp goes through `fn-nntp-unix-dtn-ms`, not Python arithmetic. No cut failed.

## Logs and their SHA-256

Copies are in [`probe-tables/`](probe-tables/). Bulk data stays on hbox under
`/tank/fn/scratch/probe-tables/`. The copy of
`tests/test_native_nntp_post_probe.py` committed here differs from the run's
(`ea3a27d5…`) only in `RecordedRunTests`, which now also re-judges this run's
`nntp-probe.json.gz`.

| file | SHA-256 |
| --- | --- |
| `nntp-probe.json` (hbox) / `nntp-probe.json.gz` | `0df761d162566706de65e63d7d870aa88bf5e953c2ded8a0686f31a0e209bd63` / `3cd194c41a7f298c6e0ec270d492007e3fabd793b8e2e13146805dd66cf05d60` |
| `nntp-probe.log` | `dde2985fd3d5a2747cc7d3273776e0dea4ac0d714a1bd75a0a3222a6ca3077a3` |
| `crash-model.log` | `6c1a5c1a251734e8f4799907f6cb01abf9634120fef6a27ab86e346c08602386` |
| `probe-unit.log` (10 OK, 1 skipped: the tree has no `planning/`) | `4d1ec2167ad75c582eca739f893c0e4face72cb720e52e02beee6e57ac6effd8` |
| `owner-logs.tgz` (641 `owner-*.err`) | `e82fdabfc108016c93825b925c4b7cda448f14fbaf3cedd21daf413a45a42b69` |
| `image-check.log` | `a2d6da08c87de572f864e1184b1df4b0236d10253f4a93cc711759cab7938554` |
| `run.sh` / `tree.sha256` | `0d13c823276ef86414f2992ccb3b7301df1f483289ba45de78cc5c0a71747b8d` / `1710f5b53c4492e0ffdf815a802f5c50cfddef834e91c1545ff0842dddf811ae` |

## What this does not show

- It shows no power loss, only process deaths and injected EIO on ZFS.
- It gives no production-image cut rows: production refuses every selector.
- The release evidence and the stamp are not derived from the article (see
  H2 above). The evidence is derived from the before-state, and the stamp is
  bracketed.
- S1 is not fixed.
