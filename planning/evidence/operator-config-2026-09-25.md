# Operator configuration — 2026-09-25 (PRF-094)

Lane `operator-config` from dev `9034f767`, merged with dev at `535ae3b2`
(pbb-d32 is needed for images). The input is the spike operator record
(`spike/mega:planning/evidence/spike-operator-2026-09-25.md`, deferrals 1
to 3 and 10 to 11) and control-c1 finding 4. This record is **partial**. The
lane reached its tool budget with one keystone book (`books/native-mission`)
timing out under certification and with no native run. The last section
lists what a continuation has to do.

## PKT-096: `[alerts]` and `[ops]` belong to ACL2, and `show` renders them

- **Grammar** (`books/native-config.lisp`). Two new tables are admitted.
  - `[alerts]` keys: `command` (optional, must be an absolute path),
    `headroom_min_percent` (0 to 100, default 10), `refusal_rate_per_minute`
    (default 30) and `cooldown_seconds` (default 900).
  - `[ops]` keys: `mission` (optional; one of small-community, relay,
    archive), `unit`, `scope` (user or system, default user), `keep_releases`
    (at least 1, default 3), `log_max_bytes` (at least 1, default 67108864),
    `log_keep` (default 7) and `memory_max`.
  - Decimals may now have up to 20 digits, because the u64 fields need them.
    That is a work bound; each key's own ceiling is applied at normalization.
  - The owner consumes none of these rows, and `fn-native-config-unsupported-key`
    is unchanged.
- **Rendering** (`books/native-config-show.lisp`). `fn-native-config-show-octets`
  prints every table and every key that is set, in one canonical order, with
  defaults filled in. The verb is `operator CONFIG show` for the whole file,
  or `show TABLE KEY` for one value word (`fn-native-config-show`,
  `fn-nop-parse-command`). The host (`fnn-operator-execute-show`) only prints.
- **KEYSTONE `fn-native-config-show-round-trip`**:
  `(implies (fn-native-config-show-wfp c) (equal (fn-native-config-load (fn-native-config-show-octets c)) (list :accepted c)))`.
  The subject is `fn-native-config-load`, which `fn-native-operator-run`
  reads fn.toml through (host/native-operator-host.lisp:19).
- **Not proved:** that every configuration the loader accepts satisfies
  `fn-native-config-show-wfp`. `show` checks it at run time and refuses
  `:not-renderable`. The tests witness it for a full configuration and for a
  minimal one.

## PKT-097: missions

- **Mission table** (`fn-native-mission-row`, `fn-native-mission-config`,
  `fn-native-mission-plan`). A mission's fn.toml is the rendering of its
  configuration. The verb `operator NODE/fn.toml mission NAME [--host H]
  [--port P]` refuses an existing file (`fn-native-operator-mission-outcome`
  over the host's lstat), creates `log/` and `tls/`, and writes the file
  with O_EXCL (`fnn-operator-execute-mission`).
  `fn-native-mission-plan-loads-back` (a corollary of the keystone) says the
  written text loads back as the mission's configuration.
- **Profiles** (`fn-native-mission-request`, in books/native-operator.lisp).
  They use the D27 defaults, with the article bound and groups per article
  taken from the spike: 1 MiB, and 8 groups (small-community) or 16 groups
  (relay and archive). `fn-native-mission-profiles-valid` says each request
  resolves to a valid profile with no history requirement.
- **Init under a mission** (`fn-nop-parse-init`):
  - the mission fixes the profile, so a flag is refused `:mission-fixes-profile`;
  - small-community's default groups are local.general and local.test;
  - relay and archive have no default groups, so they need GROUP words.
- **KEYSTONE `fn-native-mission-store-opens-with-its-profile`**
  (books/native-mission.lisp). For each mission, the profile is admitted, and
  the config.json frame `init` writes decodes to that profile at every later
  open: `fn-bs-config-frame-for-profile`, the host's
  `fn-store-metadata-config-frame`, then `fn-bs-config-decode`, under
  A-CRYPTO through `fn-bs-config-decode-of-encode`.
- **KEYSTONE `fn-native-operator-run-init-under-a-mission`**. Under a loaded
  configuration naming a mission, an accepted `init` plan's profile is the
  mission's request.
- Both keystones and all their lemmas were admitted in the persvati REPL.
  The book does **not** certify:
  - the local lemma `fn-native-mission-run-init` does not return in 300 s;
  - in the REPL the chain was fed from source and its local events leaked,
    so the REPL admission did not carry over to certification;
  - the log is `persvati:/home/ember/fn-gates/operator-config-r5/build/acl2/certify-20260925T200630Z-731077/books--native-mission.certify.log`.

## PKT-101: the owner reopens its log on SIGHUP

- **Host.** The SIGHUP handler (`fnn-main`, host/native/io.lisp) only
  increments `*fnn-sighup-count*`.
  - At each accept poll, at most one second apart,
    `fnn-owner-maybe-reopen-log` (host/native/owner.lisp) asks
    `fn-owner-log-reopen` (host/owner-host.lisp) under the owner mutex.
  - It opens the path again with O_APPEND|O_CREAT|O_NOFOLLOW and 0640, as at
    run, and swaps the descriptor under the log mutex.
  - `fnn-log-line` writes under that same mutex, so a line lands whole in
    the renamed file or whole in the new one.
  - It then writes ACL2's line `reopened log signal=hup requests=N time=T`.
  - If the reopen fails, the old descriptor stays.
- **KEYSTONE `fn-olr-reopen-iff-requested`** (books/owner-log-reopen.lisp).
  For natural counts, `fn-olr-decide` answers `:reopen` exactly when a log
  path is configured and `handled < requested`, and the handled count
  becomes `max(handled, requested)`.
- **Node probe.** `tools/node_probe.py` is already on dev and gives assertion
  verdicts (held, violated or undecided) in place of the spike's grepped
  codes. native.sh runs it against the small-community node. It has not been
  run.

## PKT-069: file first on the bound commit route

- **Host.** When `fnn-owner-complete-bound-submission` (host/native/owner.lisp)
  is given a commit callback, it now asks `fn-owner-bound-commit-gate` first,
  which is `fn-obc-commit-gate` over the owner's domain.
  - It calls the callback only on `:commit`.
  - A refusal resolves the submission as `:refused` and never touches the
    Store.
- **KEYSTONE `fn-obc-commit-only-after-filing`**: `:commit` implies
  `(fn-pa-filing-plan received groups domain) = (list :file groups)`.
- **With C1's keystone**, `fn-obc-control-commits-only-in-its-filing-group`
  (rule-classes nil): a control article commits only in its filing group,
  and that group is in the domain.
- **Certified:** the book and its tests, in run 4.

## Teeth

- **tests/acl2/native-config-show-tests.lisp.**
  - Every `[alerts]` and `[ops]` relation refuses a bad row: over-100
    headroom, a relative command, a u64 overflow, an unknown key, a bad
    scope, an unknown mission, 0 releases, 0 bytes, a boolean log_keep and a
    repeated table.
  - The boundary values are accepted.
  - The round trip has two witnesses. Its `must-fail`s are a quoted store
    path and a port of 70000.
  - `show` answers a word, `:unset` and `:unknown-key`.
  - The three mission plans are witnessed, with each plan's refusals.
  - The load-back corollary has a `must-fail` (a refused plan).
- **tests/acl2/native-mission-tests.lisp.**
  - Profile witnesses, and a `must-fail` for the name "moon".
  - The verb, with an outcome under an existing file.
  - Init under relay, and small-community's default groups.
  - One `must-fail` per hypothesis of the run keystone: a plain config, a
    `status` command, a refused init, and an unloadable configuration.
- **tests/acl2/owner-log-reopen-tests.lisp.** Four witnesses, and one
  `must-fail` per hypothesis plus one for the `iff` part.
- **tests/acl2/owner-bound-commit-tests.lisp.**
  - Witnesses: an ordinary article, and a filed cancel.
  - The finding's route: a cancel under fn.test is refused `:not-filed`.
  - A `must-fail` without the gate.

## Certification (persvati, w25 acl2-literal, 2 jobs, 300 s)

| Run | Rev | Result | Manifest |
| --- | --- | --- | --- |
| run-20260925T192556Z-808d | 7c80e4f6 | 30/34. native-operator timed out: the grammar unfolded the show rendering. Its dependents failed. native-config 0.4 s, native-config-show 5.5 s | `manifests/certify-20260925T192621Z-358284.json` |
| run-20260925T195329Z-4e95 | 535ae3b2 (merged dev) | 71/75. native-operator and its tests passed. native-mission timed out; owner-bound-commit failed (the keystone needed the plan opened) | `manifests/certify-20260925T195354Z-615305.json` |
| run-20260925T200252Z-0d77 | 3ecf4b3f | owner-bound-commit 0.9 s and its tests 0.8 s passed. native-mission failed (a lemma leaned on a leaked REPL rule) | `manifests/certify-20260925T200325Z-703340.json` |
| run-20260925T200543Z-e10c | 189906f7 | native-mission timed out at `fn-native-mission-run-init` | `manifests/certify-20260925T200630Z-731077.json` |

The first failing event for continuation is `fn-native-mission-run-init`
(books/native-mission.lisp). Its `:expand` of `fn-nop-parse-command` on the
help branch unfolds the whole grammar under certification. Expected fix:
- prove "the plan is `fn-nop-parse-command`'s whenever the configuration
  loads and the first word is not help or mission" with
  `fn-nop-parse-command` disabled;
- then derive "a help result's command is help" separately.

## Native: NOT RUN

- The image did not build. `proof_artifacts.py acquire` on hbox found no
  complete certificate set.
- The hbox cache misses 134 books of the merged dev's image closure, and
  `farm.py submit hbox --closure` refused at its cache preflight. I did not
  work out why before the budget ran out.
- The native script is written:
  `planning/evidence/operator-config-2026-09-25/native.sh TREE`. It covers:
  - the three missions, run twice each, the second refused;
  - `show` equal to the written file, and single keys;
  - init and the profile in `status`;
  - each mission node started under systemd-run with MemoryMax=24G, on
    loopback ports 11961 to 11963;
  - two rename-and-SIGHUP rotations during 60 control POSTs, counting
    accepted lines across the three files and the reopen lines;
  - the relay's posting refusal;
  - `node_probe.py` against small-community.
- No log SHA exists yet.

## Not done / deferrals

- The native-mission certification fix above.
- Native runs, which need an image built from this lane.
- The theorem that load-accepted implies show-wfp.
- packaging/fn (the spike's bash wrapper) is not ported to dev. It would
  read `operator CONFIG show TABLE KEY` in place of its awk and `mission`
  in place of `mission_values`. PKT-098, PKT-099 and PKT-100 are out of
  scope.
- `make check`: green except `planning/ledger.*` being stale. Those files
  are generated, and the deputy regenerates them on merge.
