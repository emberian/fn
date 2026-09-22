# The native cut campaign on the dabebb84 image — 2026-09-22

The 14 cuts of `tests/campaign/native_cuts.py` run against the developer
image built from `dev` at `dabebb84`, through the public operator verb, for
the first time since the owner repair of 2026-09-22. Recovery went through
`operator CFG recover` and the reread through `store ROOT inspect` and a
restarted owner's NNTP `ARTICLE`. The same run ran the developer image's
faults once each and the same selectors against the production image. This
is a runtime record. It certifies nothing and proves no theorem, and the
ACL2 differential against the byte model did not run (see "What this does
not show").

## The image and the run

| what | value |
| --- | --- |
| image directory | `/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/` on hbox |
| source revision | `dabebb845adc3e3d6e8dc93c620782f54e6b106a`; build-source manifest `build-source.sha256`, sha256 `56f7e3d013e457633ea0b0fa86bf06ed6fa69179ed4408f2385aeb340c57ba12` |
| developer launcher / core | `fn-host-developer` sha256 `7c176eda44bba39b131175a25c520c13d9ea5dada26725f08a40c9276fc569ee`; core sha256 `e5030c4711375a43c5898f2fbba95ce531293d5b599c4b2ad50fff0ded0caabe` |
| production launcher / core | `fn-host` sha256 `21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32`; core sha256 `6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf` |
| launcher note | the frozen launchers exec `--core /tank/fn/gates/freeze-dev-28fb4bd0/build/<name>.core`, not the copy beside them (the freeze record says so). Both copies of both cores were hashed at the run and are identical. |
| runtime | `/tank/fn/sbcl/bin/sbcl` (SBCL 2.6.8), `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, `ACL2_CUSTOMIZATION=NONE`; Linux 6.11.0-29-generic, the store on ext4 (`/dev/nvme0n1p4`) |
| host source against the image | `host/native/{io,owner,control,operator}.lisp` at lane head `16c1bbfa` hash the same as the frozen tree's; `git diff dabebb84 dev -- tests/campaign tests/test_native_*.py` touches only the live-reconfiguration, protected-peering and v0-matrix tests. No change to the dev harness needed a host change the image lacks. |
| driver | `tests/campaign/native_operator_campaign.py` (new in this lane), from the lane tree rsynced to `/home/hbox/fn-campaign/tree` |
| invocation | `cd /home/hbox/fn-campaign/tree && FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 python3 -m tests.campaign.native_operator_campaign --images <image directory> --work /home/hbox/fn-campaign/work --out /home/hbox/fn-campaign/campaign.json`; run a second time into `work2` / `campaign-repeat.json` |
| records | [`campaign.json`](campaign-dabebb84-2026-09-22/campaign.json) and [`campaign-repeat.json`](campaign-dabebb84-2026-09-22/campaign-repeat.json): every argv, environment selector, exit code, the last 2000 octets of stdout and stderr, and the sha256 of every file in `transactions/` and `staging/` at each step |
| repeatability | the per-cut table below comes out byte-identical from both runs, and every fault row has the same exit codes and transaction counts in both |

Each cut uses two fresh stores. `operator CFG init fn.letters` creates each
one. An `operator CFG run` owner is started, the prior article is posted
through `operator CFG post --message-id --payload --group` (accepted, 0), and
the owner is stopped by SIGTERM to its recorded pid (exit 0).

- **served**: the owner is restarted with the cut's selector in its
  environment and the candidate goes through `operator CFG post`. This is
  the path the node serves.
- **cut**: the candidate goes through `store ROOT post MSGID PAYLOAD - -
  fn.letters` with the selector. This is the only entry that reads it (see
  F1). Then come `operator CFG recover` and `store ROOT inspect` of both
  Message-IDs, then a restarted owner that serves `ARTICLE <id>` for both,
  then a resubmission of the candidate through `operator CFG post`, and the
  owner is stopped.

An exit code of −9 is SIGKILL, the process death the cut selects. Exit codes
follow D13: 0 accepted, 1 refused, 3 uncertain, 4 fault, 5 usage.

## Per cut

"table" is the candidate column of `native_cuts.py`. "candidate after" is
whether `00000000000000000001.txn` exists after recovery. The recover counts
are `transactions articles staging-orphans` as `fnn-command-recover` printed
them. `staging-orphans` counts what is left after the sweep
(`host/native/io.lisp:1186`), so a `.stage-` orphan the sweep removed prints
0. The directory columns show the removal.

| cut | coordinate | table | served: owner post exit / owner | cut exit | at death: txns, staging | recover exit: transactions articles staging-orphans | staging after recover | candidate after | prior identical (inspect, NNTP) | candidate identical (inspect, NNTP) | resubmit | agrees |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `frontier-staged-durable` | `fn-bs-frontier-program` | absent | 0 / alive, stopped 0 | -9 | 1, .allocation | 0: 1 1 1 | .allocation | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |
| `frontier-replaced` | `fn-bs-frontier-program` | absent | 0 / alive, stopped 0 | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |
| `frontier-attempted` | `fn-bs-frontier-program` | absent | 0 / alive, stopped 0 | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |
| `frontier-durable` | `fn-bs-frontier-program` | absent | 0 / alive, stopped 0 | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |
| `frontier-reserved` | `fn-bs-frontier-program` | absent | 0 / alive, stopped 0 | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |
| `record-staged-durable` | `fn-bs-record-program` | absent | 0 / alive, stopped 0 | -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |
| `record-linked` | `fn-bs-record-program` | either | 0 / alive, stopped 0 | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `record-attempted` | `fn-bs-record-program` | present | 0 / alive, stopped 0 | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `record-durable` | `fn-bs-record-program` | present | 0 / alive, stopped 0 | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `record-completing` | `fn-bs-record-program` | present | 0 / alive, stopped 0 | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `record-staging-cleaned` | `fn-bs-record-program` | present | 0 / alive, stopped 0 | -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `finish-consumed` | `fn-bs-finish-program` | present | 0 / alive, stopped 0 | -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `finish-durable` | `fn-bs-finish-program` | present | 0 / alive, stopped 0 | -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | DUPLICATE | yes |
| `recovery-stage-unlinked` | `fn-bs-recover-stage-cleanup-program` | n/a | owner started over the orphan, LISTENING, stopped 0 | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | ACCEPTED | yes |

In every row the prior transaction's bytes were unchanged by the process
death and by recovery. Recovery changed no name or byte in `transactions/`
and did not rewrite the frontier file. The candidate is where the table puts
it in all 14 rows, and read back byte-identical wherever it is present. The
resubmission answers `DUPLICATE` exactly when the candidate survived and
`ACCEPTED` exactly when it did not. So on the `store post` subject the table
agrees with the image in every row. The served column holds for every row,
and that is finding F1.

## The faults, once each (and a second time in the repeat)

| row | image | selector | what ran | exit | store after | recover |
| --- | --- | --- | --- | --- | --- | --- |
| developer post fault | developer | `FN_NATIVE_POST_FAULT=record-attempted:eio` | `store ROOT post` | **3** `store: transaction publication outcome is indeterminate` | 2 transactions, one `.stage-` left | `operator recover` 0, `2 2 0`, stage swept; candidate byte-identical by inspect and NNTP; resubmit `DUPLICATE` |
| developer control fault | developer | `FN_NATIVE_CONTROL_FAULT=postpublish` in the owner | `operator CFG post` | **3** `uncertain operator post UNCERTAIN`; owner alive, fenced, exit 3 on SIGTERM | 2 transactions, one `.stage-` left | `operator recover` 0, `2 2 0`; candidate byte-identical; resubmit `DUPLICATE` |
| developer control stop, then SIGKILL | developer | `FN_NATIVE_CONTROL_TEST_STOP=after-submit` | `operator CFG post`; owner SIGKILLed once in state `T` | client **0** `ACCEPTED` (both runs; see F3); owner −9 | 2 transactions, staging empty | `operator recover` 0, `2 2 0`; candidate byte-identical; resubmit `DUPLICATE` |
| production post fault | production | `FN_NATIVE_POST_FAULT=record-attempted:kill` | `store ROOT post` | **4** `store: FN_NATIVE_POST_FAULT requires a developer image` | 1 transaction, nothing written | — |
| production control fault | production | `FN_NATIVE_CONTROL_FAULT=postpublish` in the owner | `operator CFG post` | **3** `uncertain operator post UNCERTAIN` (see F5); owner exit 4 `fault operator run` | 1 transaction, nothing written | — |
| production control stop | production | `FN_NATIVE_CONTROL_TEST_STOP=after-submit` in the owner | `operator CFG post` | **4** `fault operator post FAULT`; owner alive, exit 0 on SIGTERM | **2 transactions: the article is durable** (see F4) | — |
| production recovery fault | production | `FN_NATIVE_RECOVERY_FAULT=recovery-stage-unlinked:kill` | `operator CFG recover` over a `.stage-` orphan the developer image left | **−9**: the production image killed itself at the cut (F6) | orphan unlinked | clean `operator recover` 0, `1 1 0` |
| production inject argument | production | `store ROOT post ... - postpublish fn.letters` | `store ROOT post` | **3** `store: indeterminate injected failure after final publication` (F6) | 2 transactions, one `.stage-` left | `operator recover` 0, `2 2 0` |
| production init fault | production | `FN_NATIVE_INIT_FAULT=init-config-written:kill` | `operator CFG init` | **−9** (F6) | an `.init-` stage and no transactions | — |

What the brief asked for is confirmed as follows. The developer image's two
faults each give exit 3 and a clean recover. The production image faults
with exit 4 on `FN_NATIVE_POST_FAULT` and honours none of it. The production
image does **not** give exit 4 on `FN_NATIVE_CONTROL_FAULT`: it answers 3 and
then stops (F5). Its exit 4 on `FN_NATIVE_CONTROL_TEST_STOP` comes after the
article is already durable (F4). This is the first time the owner-defects
lane's fourth fix has been witnessed on an image.

A follow-up on the production control fault, by hand, same image
(`work/prod-control-fault-fence`): the first post exits 3. A second post
right after it exits 1 `refused`, because the owner has already stopped
(`kill: No such process`, owner exit 4). Recovery then reads 0 transactions
and exits 0.

## Findings

**F1 — the table's cuts do not reach the served node (a fidelity defect of
the table; the remedy is a host seam this image lacks).** Only two entries
read the selectors. `FN_NATIVE_POST_FAULT` is read by `fnn-command-post`
(`host/native/io.lisp:1692-1696`), the `store ROOT post` entry.
`FN_NATIVE_RECOVERY_FAULT` is read by `fnn-command-recover`
(`host/native/io.lisp:1754`). The served node is `operator CFG run`
(`host/native/operator.lisp:123` to `fnn-control-owner-run-normalized` to
`fnn-owner-run-normalized`). It installs its store with no fault:
`host/native/owner.lisp:1368-1369` passes `nil` as `fnn-owner-run`'s fault,
and `fnn-owner-install` (`host/native/owner.lisp:451-452`) passes that to
`fnn-open-live-store`. On the image all 13 served post rows accepted the
candidate with exit 0 and the owner stayed alive. The served recovery row's
owner started over a `.stage-` orphan with `FN_NATIVE_RECOVERY_FAULT` set,
swept the orphan and listened.

Every process death in the table above is therefore a death of
`fnn-command-post` or `fnn-command-recover`, not of the owner. That is a
sibling of the served subject `fnn-owner-attempt`
(`host/native/owner.lisp:685`). Both reach the same `fnn-advance-frontier`,
`fnn-publish` and `fnn-finish`, so the `fnn-at` coordinates are the same
functions. The owner's context is a different matter, and no cut touches
it: the ACL2 owner state, the fence, the control reply, the feed flush. By
the assurance rule "the theorem subject is the function the host calls",
this campaign is evidence for the served node only together with a named
equation between the two entries. T5's "POST durable end to end" needs the
owner armed. The `owner run ... INJECT` developer verb
(`host/native/owner.lisp:1371-1387`) takes only the four `+fnn-cli-faults+`
exceptions, not the kill cuts.

*Fixed on dev at `371ba851` (lane t5/host), unwitnessed on an image.*
`fnn-post-entry-fault` (`host/native/io.lisp`) reads the positional FAULT,
`FN_NATIVE_POST_FAULT` and `FN_NATIVE_RECOVERY_FAULT` into the store's one
fault slot; `fnn-command-post`, `fnn-owner-run-normalized` (the `operator
CFG run` callee) and the developer `owner run` verb all call it, so a
developer image kills the served owner at the same `fnn-at` line in
`fnn-recover`, `fnn-advance-frontier`, `fnn-publish` or `fnn-finish`.  No
equation between the two attempts is claimed: they are driven by different
ACL2 subjects (the store-node bridge, `fn-owner`), and the campaign driver
now runs every row against the served owner itself.

**F2 — a death between the allocation stage and its rename leaves a file
that recovery never removes, and 65 of them make the store unopenable (a
defect of the model's sweep policy; the host follows it faithfully).**
`fnn-advance-frontier` stages the next frontier as
`.allocation-<pid>-<hex>` (`host/native/io.lisp:1396`). The sweep removes
only names under `*fn-sn-staging-prefix*` = `.stage-`
(`books/store-sweep.lisp:39`, `fn-sn-sweep-removals` at `:101-108`). After the
`frontier-staged-durable` kill, `operator recover` exits 0, reports
`staging-orphans=1 [.allocation-...]` and leaves the file, and the
resubmission leaves it too. Measured on the developer image
(`work/alloc-orphan-accumulation`): 65 consecutive `store post` deaths at
that cut left 65 `.allocation-` files. The 66th post exited 4 with
`staging namespace exceeds ACL2 observation bound`
(`*fn-sn-max-staging-observation*` = 64, `books/store-sweep.lisp:45`;
`host/native/io.lisp:463`). After that, `operator recover`, `operator run`
and `operator status` each exit 4 with the same message. A node that dies
in that window over its lifetime (a power cut is enough; SIGKILL is only how
the test selects it) ends up unopenable without someone deleting files by
hand. The table's candidate column cannot see this, because it records only
the transaction.

**F3 — the developer control stop is not the cut it names (a host defect
of the developer cut).** `fnn-control-test-after-submit`
(`host/native/control.lisp:141-146`) sends a process-directed
`(sb-posix:kill (sb-posix:getpid) sb-posix:sigstop)` from the worker thread,
then returns into `fnn-control-send-reply` (`host/native/control.lisp:202`).
A process-directed SIGSTOP is a group stop, which whichever thread dequeues
it initiates. It does not stop the calling thread synchronously, unlike the
SIGKILL `fnn-at` sends (`host/native/io.lisp:962-964`), which marks every
thread at once. The reply therefore sometimes leaves before the stop. Both
driver runs saw the owner stopped (`T`, `CONTROL-SUBMITTED` printed) while
the client had already exited 0 `ACCEPTED`. Five repetitions by hand (`work/teststop-rep1..5`): 2 clients got
`ACCEPTED` in about 0.1 s and 3 got `UNCERTAIN` (exit 3) at the 10-second
control deadline. Under `strace` the client waited. So
`tests/test_native_control.py:324`, which asserts exit 3, is
nondeterministic on this image. The store is the same either way: two
transactions at the stop, which is the image at the end of
`fn-bs-finish-program`. The byte model has no coordinate for the control
reply.

*Fixed on dev at `371ba851` (lane t5/host), unwitnessed on an image.*
The stop is `pthread_kill(pthread_self(), SIGSTOP)` from the worker that
holds the reply (`fnn-control-stop-calling-thread`), so that thread takes the
stop on its return from the call and the reply cannot leave first.
`tests/native_developer_selectors_raw.lisp` observes this twenty times in
forked children on macOS; the Linux image has not run it.

**F4 — the production image reports a durable article as a fault (a host
defect against D13).** With `FN_NATIVE_CONTROL_TEST_STOP=after-submit` in a
production owner, the article is committed (2 transactions) and the caller
gets exit 4 `FAULT`. The refusal lives in `fnn-control-handle-client`'s
reply expression (`host/native/control.lisp:202-210`). That runs after
`fnn-owner-control-submit-serialized` has returned `:accepted`, and it turns
the status into `:fault`. So "the production image refuses the variable"
holds in the sense that the owner does not stop. What it costs is that an
accepted article reaches its caller as a non-outcome. The owner has refused
nothing: it accepted.

*Fixed on dev at `371ba851` (lane t5/host), unwitnessed on an image.*
A production image refuses to start with `FN_NATIVE_CONTROL_TEST_STOP` set
(exit 5, `fnn-developer-selector-gate` in `fnn-main`, before dispatch), and
the reply expression no longer converts the owner's status.

**F5 — the production image's control-fault refusal answers uncertain and
stops the node (a host defect against its own stated contract).** The
comment at `host/native/owner.lisp:909-913` says a production image refuses
the variable. The comment at `host/native/control.lisp:205-209` says the
caller learns `FN_NATIVE_CONTROL_FAULT`'s refusal "as `:fault`, which ...
projects to exit 4". On the image, with
`FN_NATIVE_CONTROL_FAULT=postpublish`, the caller gets exit 3 `UNCERTAIN`
although nothing was written (1 transaction, empty staging). The owner then
exits 4 and a second post is refused because no one is listening. The
`fnn-fault` is raised by `fnn-owner-control-test-fault`
(`host/native/owner.lisp:915-924`) through `fnn-owner-control-arm-fault` (`:925`),
called at `:951` inside `fnn-owner-serialized`,
where a fault fences the owner and stops the service. It is not raised at
the reply. An environment variable on a production node thus turns the next
post into an uncertain answer and a stopped service.

*Fixed on dev at `371ba851` (lane t5/host), unwitnessed on an image.*
A production image refuses to start with `FN_NATIVE_CONTROL_FAULT` set (exit
5, before any store or socket is opened); the serialized action has no
production branch.

**F6 — three more developer selectors are honoured by the production image
(host defects, the class of the owner-defects lane's fourth).**
`fnn-recovery-test-fault` (`host/native/io.lisp:1622-1640`) and
`fnn-init-test-fault` (`host/native/io.lisp:1597-1616`) have no
`fnn-developer-image-p` gate. On the production image, `operator recover`
under `FN_NATIVE_RECOVERY_FAULT=recovery-stage-unlinked:kill` and
`operator init` under `FN_NATIVE_INIT_FAULT=init-config-written:kill` each
SIGKILLed their own process. The `store` verb is registered in every image
(`host/native/io.lisp:2318-2330`), and its `post` honours the positional
fault argument from `+fnn-cli-faults+` (`host/native/io.lisp:1651-1659`,
`:1692-1696`). `postpublish` gave exit 3 on the production image with the
article durable. `FN_NATIVE_AUTH_ADMIN_FAULT`
(`host/native/auth-admin.lisp:20-45`) has the same ungated shape in source.
It was not run.

*Fixed on dev at `371ba851` (lane t5/host), unwitnessed on an image.*
Every selector, including these four, is in `+fnn-developer-selectors+`
and read through `fnn-developer-selector`; a production image refuses to
start with any of them, or with a `store post` FAULT argument, with exit 5
naming it.

**F7 — the recovery cut has no position in the recovery program (a fidelity
defect of the table's coordinate).** `recovery-stage-unlinked` names
`fn-bs-recover-stage-cleanup-program` (`books/byte-store-programs.lisp:256`),
a two-step program of its own. The comment above it (`:252`) says "Recovery
removes bounded staging orphans before replay barriers". The host sweeps
after all five barriers have reached `:ready` (`host/native/io.lisp:1358-1366`,
and its comment says the model enables the sweep only then). The coordinate
therefore does not say where in `fn-bs-recover-program`
(`books/byte-store-programs.lisp:227`) the death falls, and the one comment
that does say disagrees with the host. The recovery program's own cuts,
`recover-replayed` and `recover-barrier`, are `fnn-at` points
(`host/native/io.lisp:1337`, `:1352`) that the developer image cannot
select: `+fnn-recovery-model-cuts+` (`host/native/io.lisp:1619-1620`) lists
only the cleanup cut.

*Fixed on dev at `371ba851` (lane t5/host), unwitnessed on an image.*
`+fnn-recovery-model-cuts+` now lists `recover-replayed`, `recover-barrier`
(the first of its five sites) and `recovery-stage-unlinked`;
`tests/campaign/native_cuts.py` places `recovery-stage-unlinked` after the
whole of `fn-bs-recover-program` (`follows`) and checks that `fnn-recover`
still sweeps after its barriers; the comment above
`fn-bs-recover-stage-cleanup-program` says so (commit `9cbd53b9`).

No cut contradicted its record expectation, and every process death in the
table has an `fn-bs-*-program` coordinate. The contradictions are about
reach (F1, F7), about what the table does not record (F2), and about the
developer and production seams (F3 to F6).

## What this does not show

- **No ACL2 differential.** `tests/test_native_crash_model.py` compares each
  killed store with the byte model's image at the cut through
  `books/byte-store-keystones`. That book is outside the frozen image closure,
  and at the current digest it is red (`planning/proofs.json`, PRF-041
  progress note; T0 re-establishes it). The rows above are observations
  against the table's candidate column and the host's own recovery. They are
  not model-image membership.
- **Nothing on the served path** beyond the control stop (F1, F3).
  `record-linked`'s "either" was observed only as present.
- **Process death, not power loss.** SIGKILL leaves the kernel's dirty state
  in place. No row says anything about unsynced data (D14).
- One filesystem (ext4 on hbox) and one image. The DTN image was not run.
  `FN_NATIVE_AUTH_ADMIN_FAULT` was read in source only.
- Every hbox store was under `/home/hbox/fn-campaign/` and has been removed.
  The node at `/tank/fn/node` and the matrix stores were not touched.
