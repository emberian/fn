# Staging cleanup errors: swallowed, now logged: 03bdd105, 2026-09-24

This lane fixes finding S1 of [probe-tables](probe-tables-2026-09-24.md).
`fnn-publish` swallowed any error from its best-effort staging cleanup after
the record was durable, and it wrote nothing to the log. The outcome does not
change: the wire answer is still `240` and the outcome is accepted, because
P-RECORD (specs/crash-model-v2.md) makes the cleanup best-effort. What changes
is that each swallowed error now leaves one line in the owner log. ACL2
renders the line.

**Result in one line.** On a developer/production pair built from `03bdd105`,
the probe passes **40 of 40** rows. The `record-stage-unlinked` EIO row
answers `240` with owner exit 0. The article is present and its owner log
holds exactly one line naming the swallowed cleanup error. The six `refused`
EIO rows and the four controls pass unchanged.

## The change

- **The line** is `books/owner-log.lisp` `fn-olog-staging-cleanup-line
  (step name sequence errno text)`. It has the first word `failed`, which is
  not an outcome word, so the submission's own line still says what the
  reply said. It also has these fields:
  - `step=` is `unlink` or `directory-barrier`.
  - `sequence=` is the durable record's sequence.
  - `name=` is the stage path.
  - `errno=` is the errno, or `none` when the condition carried none.
  - `error=` is the condition's report as SBCL gives it.

  Every field goes through `fn-olog-visible`.
- **The theorem** is `fn-olog-staging-cleanup-line-is-one-line`: no CR or LF
  appears, whatever the stage path or error text held. It has the same shape
  as the other lines and is registered under PRF-054.
  `tests/acl2/owner-log-tests.lisp` gives the following teeth:
  - the exact line the probe row reads
  - the `errno=none` case
  - an error text holding CR LF that still renders on one line
  - a `must-fail` showing that the raw `error=` field, built without the
    visible filter, is not one line
- **The host.** In `host/native/io.lisp` `fnn-publish` (lines 1668-1679),
  the `ignore-errors` still holds exactly the unlink, `(fnn-at store
  :record-stage-unlinked)` and the staging barrier, so
  `native_cuts.verify_swallowed_cuts` and the cut table are unchanged. A
  `handler-case` inside it hands the error to `fnn-log-staging-cleanup`
  (line 1604). That function renders the line through `fnn-core` and writes
  it with `fnn-log-line` (line 570). `fnn-log-line` is the service-log
  writer, moved here from `host/native/owner.lisp`, and `fnn-owner-log` now
  calls it. The descriptor `*fnn-owner-log-fd*` moved with it.
- **Failure handling.** If rendering or writing the line fails, stderr says
  so and names both errors. Because the logging is itself inside the
  `ignore-errors`, the outcome is unchanged either way. The store-test and
  DTN images do not include `books/owner-log`, so there the render faults
  and the stderr fallback applies (see What remains).
- **Test witness fix.** `tests/acl2/owner-log-tests` did not certify on
  `a61c9ddc` (manifest `certify-20260924T164157Z-1631104`), for a reason
  this branch did not cause. The failure-8 refused transit witness was built
  over the owner whose completion was consumed. Over a consumed completion,
  `fn-own-outcome-completion` reads `:refused` as uncertain, so the line
  said `uncertain transit … code=436`. The witness now uses the unconsumed
  owner, as the ingress refusal is, and the consumed case is asserted
  separately.

## Operator attention beyond the line: decided, no status change

`operator status` (`fnn-command-status`) already opens under the shared lock
without sweeping, and prints `staging-orphans=N[+] [names]`. That count comes
from the bounded staging listing whose limit ACL2 sets
(`fnn-staging-orphans`). The two failure modes are covered as follows:

- **A persistent unlink failure** leaves `.stage-*` entries behind. `status`
  already reports them, and the writer's sweep at the next open collects
  them. If the sweep cannot unlink them either, it goes indeterminate, which
  is loud.
- **A persistent staging-barrier failure** leaves no entry behind, so a
  listing cannot see it. The log line is the only signal, and it is now
  there.

A status count added here would repeat an existing report. The next packet,
if wanted, is a count of swallowed cleanup errors since start, in the
running owner's state. That needs a model of where that count lives. It is
not done here.

## Certification

| run | books | result | manifest |
| --- | --- | --- | --- |
| run-20260924T164146Z-8233, `a61c9ddc`, hbox, 2 jobs, w28 | books/owner-log, tests/acl2/owner-log-tests | owner-log passed; tests failed on the pre-existing transit witness | `planning/evidence/manifests/certify-20260924T164157Z-1631104.json` |
| run-20260924T164355Z-6f2f, `03bdd105`, hbox, 2 jobs, w28 | same | **passed** (owner-log installed at these bytes, tests certified) | `planning/evidence/manifests/certify-20260924T164408Z-1633715.json` |

The remote roots were `/tank/fn/gates/cleanup-error-log-a61c9ddc` and
`-03bdd105`. No other book changed. The farm reported the 120 other books of
the closure as installed from the cache.

## Images and probe run

| what | value |
| --- | --- |
| tree | `git archive 03bdd105` into `/tank/fn/scratch/cleanup-error-log/tree` |
| build | [`build.sh`](cleanup-error-log/build.sh): `proof_artifacts.py acquire/validate --profile default` (281 books, `rejected=0`), production and developer images under `swarm-build`, `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, w28 ACL2 |
| `fn-host.core` / `fn-host-developer.core` | `e0f5568d5a8a49d006eed334f5f0906d145333e08deb8413b24b1f0de862097b` / `0d5c1bf705e5b1fbe147d752d766e2ead25fe67c076e034f53d8f3e0c65ed76a` |
| image dir | `/tank/fn/scratch/cleanup-error-log/images/03bdd105…`. `freeze-native-image.sh` stopped at `missing fn-host-dtn` after copying the two images; no DTN image was built. `image.sha256` was written over the directory by `sha256sum` and checked in the run ([`image-check.log`](cleanup-error-log/image-check.log), rc=0) |
| run | [`run.sh`](cleanup-error-log/run.sh), 16:46:23Z to 16:47:30Z: `tests.test_native_nntp_post_probe` (11 OK); the full probe (1:06, peak RSS 320 MB), kernel ports, nothing touched `/tank/fn/node` |

The line in `probe-work/record-stage-unlinked-eio/owner-2.err` is the only
match of `SWALLOWED_LOG` in that row. No other row's owner log holds a
`failed staging cleanup` line.

```
failed staging cleanup step=directory-barrier sequence=1 name=/tank/fn/scratch/cleanup-error-log/probe-work/record-stage-unlinked-eio/store/staging/.stage-1638304-1ab91141c831850adf591129 errno=5 error=[Errno?5]?Input/output?error
```

The step reads `directory-barrier` because the injected EIO fires after the
unlink returned (the `record-stage-unlinked` cut) and before the staging
barrier.

| row | arm | reply | owner exit | present | verdict |
| --- | --- | --- | --- | --- | --- |
| record-stage-unlinked eio | swallowed | `240 article received OK` | 0 | yes | **pass** (was FAIL: 0 lines) |
| frontier-created, -written, -staged-durable eio | refused | `441 … nothing was stored` | 0 | no, repost `240` | pass ×3 |
| record-created, -written, -staged-durable eio | refused | `441 … nothing was stored` | 0 | no, repost `240` | pass ×3 |
| all other cut rows (kill ×18, uncertain ×8, consumed ×2) and 4 controls | | as probe-tables | | | pass |

`python3 -m tests.campaign.native_nntp_post_probe --judge
planning/evidence/cleanup-error-log/nntp-probe.json.gz` re-judges the run
as 40 of 40.

| file | SHA-256 |
| --- | --- |
| `nntp-probe.json` (hbox) / `nntp-probe.json.gz` | `93490c92749caf5835a783342e8bce72fe993965e0887bc2a8527f63acf6021a` / `95136d5dd87f555c0cd1809dc157c4f286af5e5cab2d708be7a66d161da3c377` |
| `nntp-probe.log` | `66ec50e5fc7c18f28228ea2f19db706425120f4cb75860d5ef5e9af343309708` |
| `probe-unit.log` | `a4fff7e90d920fa85f3b441d8a18dd5dab4a89ed4a2b3a10ca3ef2aba3bae0d0` |
| `owner-logs.tgz` | `c148493c8d8409be2e22f5336f89df970af40ca3bdd9882c98bc4f1780228009` |
| `image-check.log` | `390c269fda89683c86df4448f1b3a8d9823bca0f9c113753dd712aa13894fc04` |
| `run.sh` / `build.sh` | `cfef4cf50d9a2bb207265d03d8be9adac462f514810bd4b9012dd5c1bb083507` / `b8e96d012fe1bf571f1a7d88dffdfa6368bb4a2492e3f329346413d3076fc197` |

## What remains

- **Once per error is measured, not proved.** That the host writes the line
  exactly once per swallowed error is measured by the probe row. The ACL2
  claim covers only the rendered octets.
- **Two images cannot render the line.** The store-test and DTN images
  (`host/native/build-store-test.lisp`, `build-dtn.lisp`) do not include
  `books/owner-log`. A swallowed cleanup error there gets the host's stderr
  fallback, not the ACL2 line. The DTN image was not built or run here.
- **A persistent staging-barrier failure is visible only in the log.** No
  status field counts it (see the decision above).
- **Only process death and injected EIO were run.** There was no power loss.
