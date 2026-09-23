# The native cut campaign on the da5fd8cb image — 2026-09-23

The second run of the native cut campaign, on the first image that carries
every fix the [first campaign](campaign-dabebb84-2026-09-22.md) asked for:
one startup gate for every developer selector, the served owner armed with
the post and recovery selectors, the control stop taken by the calling
thread, the recovery program's own cuts, and the staging sweep of
[F2's fix](sweep-allocation-orphans-2026-09-22.md). The 16 cuts of
`tests/campaign/native_cuts.py` ran twice. Each cut was taken once by the
served owner (`operator CFG run`) and once by the `store` entry. The same
two runs covered the developer faults, the control stop five times over,
F2's reproduction, and every developer selector against the production
image. This is a runtime record. It certifies nothing and proves no theorem,
and the ACL2 differential against the byte model did not run (see "What this
does not show").

## The image and the run

| what | value |
| --- | --- |
| image directory | `/tank/fn/gates/freeze-dev-2e53fae2/build/images/da5fd8cb5929601679bdb71c3be6986d430f05ed/` on hbox |
| source revision | `dev` at `2e53fae2`, byte-identical to `da5fd8cb` outside `planning/` (`git diff --stat da5fd8cb 2e53fae2` lists only `planning/` files); build-source manifest `build-source.sha256`, sha256 `36627a436e8710bc5fdfb9d36ccb8f0965f6a7a4021b3e5cf6c5635acd553ab1` |
| developer launcher / core | `fn-host-developer` sha256 `73050050d1701f037815eaf155366ac6bd25908d7c11e41e28e5bf5f08c57cc2`; core sha256 `c53ca0cc7cea8ddbbe0796aebaec3762acb88d8b25f4882b583f8318bb498fca` |
| production launcher / core | `fn-host` sha256 `9597f3b90fb06087e1e36ef9ae097b90f89a0a95c6c9046f0979d9e5d0835718`; core sha256 `a6e5437e23fc74a743f07c21e46e7876b42f132de2a558f9db4142a781ab5cca` |
| DTN launcher / core (not run) | `fn-host-dtn` sha256 `df18c2f735d3e1408b7b9c7de689124530e86e439fed520ae64dc770c99771af`; core sha256 `e6d236a561933f214742ee804553d4d2e3b11b19f514ec36154a394249b6fb4d` |
| launcher note | as in the first record, the launchers exec `--core /tank/fn/gates/freeze-dev-2e53fae2/build/<name>.core`, not the copy beside them. Both copies of the developer and production cores were hashed at the run and are identical. |
| runtime | `/tank/fn/sbcl/bin/sbcl` (SBCL 2.6.8), `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, `ACL2_CUSTOMIZATION=NONE` (set by the driver); Linux 6.11.0-29-generic, the stores on ext4 (`/dev/nvme0n1p4`) |
| host source against the image | `host/native/{io,owner,control,operator}.lisp` in the lane tree (branched from `dev` at `376660e9`) hash the same as the frozen tree's; `git diff 2e53fae2 376660e9 -- host tests books` is empty |
| driver | `tests/campaign/native_operator_campaign.py` as committed on `campaign/da5fd8cb` with this record (sha256 `60a6d6d743c1900d4f4e7ab171dadd7f6bf313277f9399d4e9bb98ec591e1de4`), rsynced to `/home/hbox/fn-campaign/tree`. It is the frozen tree's driver (`bb0affe6`, byte-identical to `dev`) plus the harness fix H1 below |
| invocation | `cd /home/hbox/fn-campaign/tree && FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 python3 -m tests.campaign.native_operator_campaign --images <image directory> --work /home/hbox/fn-campaign/work --out /home/hbox/fn-campaign/campaign.json`, then again into `work2` / `campaign-repeat.json` (51.3 s and 51.2 s wall) |
| sweep fidelity | `FN_NATIVE_HOST=<image directory>/fn-host-developer FN_NATIVE_DEVELOPER_HOST=<same> python3 -m unittest -v tests.test_native_recovery.NativeRecoveryFidelityTests.<six tests named below>`, same tree: [`sweep-fidelity.log`](campaign-da5fd8cb-2026-09-23/sweep-fidelity.log) |
| image-gated test | `FN_NATIVE_IMAGES=<image directory> python3 -m unittest tests.campaign.test_native_operator_campaign`, same tree, before the two runs: 10 tests, OK |
| records | [`campaign.json`](campaign-da5fd8cb-2026-09-23/campaign.json) and [`campaign-repeat.json`](campaign-da5fd8cb-2026-09-23/campaign-repeat.json): every argv, environment selector, exit code, the last 2000 octets of stdout and stderr, and the sha256 of every file in `transactions/` and `staging/` at each step |
| repeatability | both tables below come out byte-identical from both runs. Every fault row has the same exit codes, outcome words and transaction counts in both |

Each cut uses two fresh stores. `operator CFG init fn.letters` creates each
one. An `operator CFG run` owner is started, the prior article is posted
through `operator CFG post` (accepted, 0), and the owner is stopped by
SIGTERM to its recorded pid (exit 0). The prior's stored octets are read
back once through `store ROOT inspect` and kept as the reference.

- **served**: the owner is restarted with the cut's selector in its
  environment (`FN_NATIVE_POST_FAULT=<cut>:kill`, or
  `FN_NATIVE_RECOVERY_FAULT=<cut>:kill` for a recovery cut), and the
  candidate goes through `operator CFG post`. A recovery cut's store first
  gets a `.stage-` orphan from a `store post` killed at
  `record-staged-durable`. The served owner takes that cut in its own
  recovery at start. The candidate is resubmitted through `operator CFG
  post`.
- **cut**: the candidate goes through `store ROOT post MSGID PAYLOAD - -
  fn.letters` with the selector, or `operator CFG recover` with it for a
  recovery cut. It is resubmitted through `store ROOT post` after the reread
  owner stops.

Both then run `operator CFG recover`, `store ROOT inspect` of both
Message-IDs, and a restarted owner that serves `ARTICLE <id>` for both. After
that comes the resubmission through the entry that first submitted the
candidate, and the owner is stopped by its recorded pid. An exit code of −9
is SIGKILL, the process death the cut selects. Exit codes follow D13: 0
accepted, 1 refused, 3 uncertain, 4 fault, 5 usage.

**What "identical" means now (harness fix H1).** Since `a0b6d41f` the owner
injects the article `operator CFG post` hands it
(`fnn-owner-control-submit-serialized`, `host/native/owner.lisp:996`, over
`fn-own-operator-submit`, `books/owner.lisp:893`). It prepends `Path`,
`Injection-Date`, `Injection-Info` and, when the payload has none, `Date`,
all under the owner's clock. The frozen driver compared every reread with
the payload file. On this image that judges every operator-posted article
"not identical": a smoke run of one cut showed `False` for the prior in both
columns and for the served candidate. The driver now checks three things.
The prior must equal its own stored octets as read back after seeding. A
candidate the owner wrote must be the payload's injected form
(`injected_from`: the payload's header lines and body kept octet for octet,
as the tail of the stored header, and only those four fields added ahead,
none twice and none the payload already had). A candidate `store post` wrote
must equal the payload. Both readers must also return the same octets
(`same_as_inspect`). The unit tests are in
`tests/campaign/test_native_operator_campaign.py` (`InjectedFormTests`: the
image's own injected shape is accepted; a changed body, a foreign added
field, a dropped or reordered payload field, a doubled injection field, an
injected field the payload already had, and a headless string are each
rejected).

## Per cut

"table" is the candidate column of `native_cuts.py`. "candidate after" says
whether `00000000000000000001.txn` exists after recovery. The recover counts
are `transactions articles staging-orphans` as `fnn-command-recover` printed
them. `staging-orphans` counts what is left after the sweep, and the
directory columns show what the sweep removed. "agrees" is computed from the
records, not typed. It means all of the following. The table's column holds.
The prior transaction's bytes are the seeded bytes at death. Recovery exits 0
and changes no name or byte in `transactions/`. The prior rereads equal to
its reference by both readers. A surviving candidate rereads as its
reference by both readers, the readers agree, and the resubmission answers
duplicate without adding a transaction. An absent candidate is `inspect`
exit 1 and NNTP 430, and the resubmission is accepted.

### Served: the owner dies at the cut

"served" is whether the owner reached `LISTENING`, then the exit of the
`operator CFG post` client, then the owner's exit.

| cut | coordinate | table | served: owner ready / client exit / owner exit | at death: txns, staging | recover | staging after | candidate after | prior (inspect, NNTP) | candidate (inspect, NNTP) | resubmit | agrees |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `frontier-staged-durable` | `fn-bs-frontier-program` | absent | True / 3 / -9 | 1, .allocation | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 ACCEPTED | yes |
| `frontier-replaced` | `fn-bs-frontier-program` | absent | True / 3 / -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 ACCEPTED | yes |
| `frontier-attempted` | `fn-bs-frontier-program` | absent | True / 3 / -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 ACCEPTED | yes |
| `frontier-durable` | `fn-bs-frontier-program` | absent | True / 3 / -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 ACCEPTED | yes |
| `frontier-reserved` | `fn-bs-frontier-program` | absent | True / 3 / -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 ACCEPTED | yes |
| `record-staged-durable` | `fn-bs-record-program` | absent | True / 3 / -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 ACCEPTED | yes |
| `record-linked` | `fn-bs-record-program` | either | True / 3 / -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-attempted` | `fn-bs-record-program` | present | True / 3 / -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-durable` | `fn-bs-record-program` | present | True / 3 / -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-completing` | `fn-bs-record-program` | present | True / 3 / -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-staging-cleaned` | `fn-bs-record-program` | present | True / 3 / -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `finish-consumed` | `fn-bs-finish-program` | present | True / 3 / -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `finish-durable` | `fn-bs-finish-program` | present | True / 3 / -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `recover-replayed` | `fn-bs-recover-program` | n/a | False / — / -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `recover-barrier` | `fn-bs-recover-program` | n/a | False / — / -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `recovery-stage-unlinked` | `fn-bs-recover-stage-cleanup-program` after `fn-bs-recover-program` | n/a | False / — / -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |

| cut | cut exit | at death: txns, staging | recover | staging after | candidate after | prior (inspect, NNTP) | candidate (inspect, NNTP) | resubmit | agrees |

In all 13 post rows the owner died at the cut (−9), and the client answered
**3 `UNCERTAIN`**. That held when the candidate turned out absent and when it
turned out durable, so no death was reported as an accepted or a refused
outcome. The first campaign's served column was `0 ACCEPTED` with the owner
alive in every row, because nothing armed it (F1). In the three recovery
rows the owner died in its own recovery at start, before `LISTENING`,
having printed nothing. In `recover-replayed` and `recover-barrier` the
`.stage-` orphan is still there at death, since the sweep had not run yet.
In `recovery-stage-unlinked` it is gone, since the cut falls after the
unlink. A later `operator recover` swept the rest in every row.

### Cut: the `store` entry dies at the cut

|---|---|---|---|---|---|---|---|---|---|
| `frontier-staged-durable` | -9 | 1, .allocation | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `frontier-replaced` | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `frontier-attempted` | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `frontier-durable` | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `frontier-reserved` | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `record-staged-durable` | -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `record-linked` | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-attempted` | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-durable` | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-completing` | -9 | 2, .stage | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `record-staging-cleaned` | -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `finish-consumed` | -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `finish-durable` | -9 | 2, none | 0: 2 2 0 | none | present | True, True | True, True | 0 DUPLICATE | yes |
| `recover-replayed` | -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `recover-barrier` | -9 | 1, .stage | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |
| `recovery-stage-unlinked` | -9 | 1, none | 0: 1 1 0 | none | absent | True, True | n/a (inspect exit 1, NNTP 430) | 0 COMMITTED | yes |

The `store` column matches the first campaign's table in all 13 shared rows
(candidate placement, recover counts, rereads, resubmission) with one
exception. `frontier-staged-durable` now reads `0: 1 1 0` with staging empty
after recovery. The first campaign read `0: 1 1 1` with the `.allocation-`
stage left (F2). Its resubmission was then made through the other entry;
this run resubmits through `store post`, see N1. The two new rows are the
recovery program's own cuts (F7).

Across both runs and both columns, recovery never rewrote the frontier file
(`recovered.frontier == killed.frontier` in all 64 observations), and the
frontier at death equals the seeded one only at `frontier-staged-durable`.
`record-linked`'s "either" was observed only as present, four times.

## The faults

| row | image | selector | what ran | exit | store after | recover and reread |
| --- | --- | --- | --- | --- | --- | --- |
| developer post fault, `store` entry | developer | `FN_NATIVE_POST_FAULT=record-attempted:eio` | `store ROOT post` | **3** `store: transaction publication outcome is indeterminate` | 2 transactions, one `.stage-` | `operator recover` 0, `2 2 0`, stage swept; candidate equal to the payload by both readers; `store post` resubmit `duplicate` (0) |
| developer post fault, served owner (new) | developer | the same, in the owner's environment | `operator CFG post` | **3** `UNCERTAIN`; owner alive after the post, exit 3 on SIGTERM | 2 transactions, one `.stage-` | `operator recover` 0, `2 2 0`; candidate the injected payload by both readers; resubmit `DUPLICATE` (0) |
| developer control fault | developer | `FN_NATIVE_CONTROL_FAULT=postpublish` in the owner | `operator CFG post` | **3** `UNCERTAIN`; owner alive after the post, exit 3 on SIGTERM | 2 transactions, one `.stage-` | `operator recover` 0, `2 2 0`; candidate the injected payload; resubmit `DUPLICATE` |
| developer control stop, ×5 per run | developer | `FN_NATIVE_CONTROL_TEST_STOP=after-submit` in the owner | `operator CFG post`; the owner seen in state `T`, then SIGKILLed | client **3** `UNCERTAIN` in 5 of 5, both runs; the client had not exited when the owner was seen stopped (5 of 5, both runs); owner −9 | 2 transactions at the stop, staging empty | `operator recover` 0, `2 2 0`; candidate the injected payload; resubmit `DUPLICATE` |
| F2 reproduction, then `operator recover` | developer | 65 × `FN_NATIVE_POST_FAULT=frontier-staged-durable:kill` | 65 `store ROOT post` | −9 all 65 | **one** `.allocation-` stage (the last death's), 1 transaction | `operator status` 0 `staging-orphans=1 [.allocation-…]`; `operator recover` 0 `1 1 0`, staging empty; an owner starts and the candidate posts `ACCEPTED` |
| F2 reproduction, then `store post` | developer | the same | the same | −9 all 65 | one `.allocation-` stage, 1 transaction | the 66th, unfaulted `store post` 0 `committed sequence=1`, staging empty; an owner starts, and the operator post of the same candidate is refused (1), see N1 |
| cross-entry retry (new) | developer | none | `store post` then `operator post` of one payload; and the reverse | first 0; second **1** (`refused operator post REFUSED`; `store: conflicting immutable Message-ID`) | 2 transactions after the first, unchanged by the second | — |
| production: every developer selector at start | production | each of the 8 names in `+fnn-developer-selectors+` set to `x` | `operator CFG run`, `operator CFG recover`, `store ROOT post`: 24 starts | **5** in all 24, each naming its variable: `fn-host: error: <VAR> is a developer-image selector; this production image does not start with it` | the store's `transactions/`, `staging/` and frontier snapshot equal before and after | — |
| production: `store post` FAULT argument | production | `store ROOT post … - postpublish fn.letters` | `store ROOT post` | **5** `the store post FAULT argument is a developer-image selector` | unchanged (same snapshot) | — |
| production: init fault | production | `FN_NATIVE_INIT_FAULT=init-config-written:kill` | `operator CFG init` | **5** | no store directory created | — |

The sweep fidelity tests ran on the same developer image, six of them by
name: `test_sixty_five_allocation_orphans_are_swept_in_rounds`,
`test_every_host_staging_prefix_is_swept`,
`test_over_limit_unrecognized_names_refuse_without_removing_them`,
`test_orphans_beyond_one_observation_go_with_foreign_names_kept`,
`test_sigkill_after_one_unlink_restarts_and_reconciles_remaining_stage` and
`test_post_unlink_eio_is_uncertain_then_a_new_process_recovers`. All six
passed. The first builds the 65-name directory F2 described from files. A
reader reports `staging-orphans=64+` and still opens, and `recover` empties
the directory with the frontier unchanged. The class's seventh test needs an
ACL2 bridge for its fixture and was not run.

## The first campaign's findings, now

| | finding | status on this image |
| --- | --- | --- |
| F1 | the table's cuts did not reach the served owner | **Witnessed fixed.** The served owner died at every one of the 16 cuts in both runs: 13 during `operator CFG post`, with the client answering 3, and 3 in its own recovery at start. The owner read its selector through `fnn-post-entry-fault` (`host/native/io.lisp:1757`), called from `fnn-owner-run-normalized` (`host/native/owner.lisp:1438`, the `operator CFG run` callee) and from the developer `owner run` verb (`fnn-command-owner`, `:1451`). Recovery, both rereads and the resubmission agree with the table in every served row. No equation between the owner's attempt and `fnn-command-post` is claimed, as before. |
| F2 | `.allocation-` stages were never swept; 65 deaths made the store unopenable | **Witnessed fixed, and changed.** 65 deaths at `frontier-staged-durable` no longer accumulate. Each writer's open sweeps the previous death's stage, so the directory holds exactly one `.allocation-` name after 65 deaths, and `status`, `recover`, a plain `store post` and an owner all open the store. Because deaths no longer produce the over-the-bound directory, that case was measured from files. The sweep fidelity tests on this image swept 65 orphans in rounds and 100 orphans beside 10 kept foreign names, and refused 65 foreign names with exit 1, removing nothing. `recover` does not print how many it removed: its line reports what is left (`staging-orphans=0`), and the before and after counts come from `status` and the directory snapshots. |
| F3 | the control stop was a racy group SIGSTOP | **Witnessed fixed.** Client exit 3 in 10 of 10 repetitions (5 per run), and in none of them had the client exited when the owner was seen stopped (`fnn-control-stop-calling-thread`, `host/native/control.lisp:137`). The first image gave 3 in only 3 of 5. |
| F4 | production reported a durable article as a fault | **Witnessed fixed by refusal at start.** `FN_NATIVE_CONTROL_TEST_STOP` in a production environment is refused with exit 5 by `operator run`, `operator recover` and `store post` (`fnn-developer-selector-gate`, `host/native/io.lisp:2436`, called at `:2521` before dispatch), and the store is unchanged, so no article becomes durable under it. The reply path that converted `:accepted` to `:fault` was not exercised, because a production image never reaches it with the variable set. |
| F5 | production answered a refused control fault as uncertain, then stopped | **Witnessed fixed by refusal at start.** `FN_NATIVE_CONTROL_FAULT`: exit 5 at all three entries, store unchanged, no owner started. |
| F6 | three more developer selectors were honoured by production | **Witnessed fixed.** `FN_NATIVE_RECOVERY_FAULT`, `FN_NATIVE_INIT_FAULT` (`operator init`: exit 5, no store directory created), `FN_NATIVE_AUTH_ADMIN_FAULT`, `FN_NATIVE_OWNER_TEST_SIGTERM`, `FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP` and the `store post` FAULT argument each give exit 5 naming the selector. None of them killed the production process. The gate refuses on the variable's presence, and this run set each to `x`, not to a real cut. |
| F7 | the recovery cut had no position in the recovery program | **Witnessed fixed.** `recover-replayed` and `recover-barrier` are selectable on the developer image, through both `operator recover` and the served owner's start. Both die with the orphan still in `staging/`, which puts them before the sweep, where the table puts them (`fn-bs-recover-program`). `recovery-stage-unlinked` dies with the orphan gone, which puts it after the unlink, where `follows` puts it. The image does not show which of `recover-barrier`'s five sites fired. The table says the first one reached, and the store after death cannot tell the sites apart. |

## New findings

**H1 — the frozen driver judged injected articles against their payload (a
harness defect, fixed here).** See "What 'identical' means now" above. With
the frozen driver, every row on this image would have reported the prior as
not identical. The fix and its unit tests are in `tests/campaign/`. The
image-gated `test_native_operator_campaign` now also asserts that the served
candidate is the injected payload by both readers, that the same-entry
retry is a duplicate, F2's opened store and accepted post, and the
cross-entry refusals. It passed on this image.

**N1 — the two write entries store different octets for one payload, and
`store ROOT post` writes an uninjected article in every image (a question
for the owner of `a0b6d41f`, not a crash defect).** `operator CFG post`
injects: `Path`, `Injection-Date`, `Injection-Info`, and `Date` when absent.
`store ROOT post` (`fnn-command-post`, `host/native/io.lisp:1787`) stores
the payload as read. The `store` verb is dispatched in every image,
production included (`fnn-dispatch`, `host/native/io.lisp:2459`, not a
developer verb). So one payload through the two entries gives two articles
under one Message-ID. Whichever is second is a conflict and is refused (1)
without a second transaction (`cross-entry-retry-*`, both orders, both
runs). That is the right outcome given the model's reinjection rule
(`fn-inj-reinjectionp`, `books/injection.lisp`, used by
`fn-own-operator-decision`, `books/owner.lisp:860`): the stored article is
not an injection of the payload. It changes two things. First, an operator
who retries through `operator post` an article that `store post` wrote,
after an uncertain answer, is refused, not told duplicate. Second, the
first campaign's cut column, which resubmitted through `operator post`,
would now read `1 REFUSED` wherever the candidate survived. An intermediate
run of this campaign did read that, which is why the driver now resubmits
through the entry that first submitted. `store post` also still writes the
shape INN refused 437 (`a0b6d41f`'s motive) on a production image. Whether
`store post` should inject, become a developer verb, or stay a raw
store-level entry is not decided here.

## What this does not show

- **No ACL2 differential.** The rows are observations against the table's
  candidate column and the host's own recovery. They are not membership in
  the byte model's image at the cut. `tests/test_native_crash_model.py` did
  not run.
- **Process death, not power loss.** SIGKILL leaves the kernel's dirty
  state in place. No row says anything about unsynced data (D14).
- One filesystem (ext4 on hbox) and one image. The DTN image was not run.
- `FN_NATIVE_AUTH_ADMIN_FAULT`, `FN_NATIVE_OWNER_TEST_SIGTERM` and
  `FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP` were run only against the production
  gate, not as developer faults.
- F2's over-the-bound directory on this image comes from files, not from
  deaths, because deaths no longer produce it. The readdir-order question in
  the sweep record's "Open" list is not addressed.
- Which of `recover-barrier`'s five sites fired (F7) is not observable from
  the store.
- Every hbox store and the tree were under `/home/hbox/fn-campaign/`, which
  has been removed. Every owner the driver started was stopped by its
  recorded pid. The node at `/tank/fn/node`, the matrix stores and persvati
  were not touched.
