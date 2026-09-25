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
- That every configuration the loader accepts satisfies
  `fn-native-config-show-wfp` was first checked at run time. It is now
  proved (`fn-native-config-load-renderable`, below), and the run-time check
  is gone.

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

| run-20260925T202652Z-e94a | d9e4fe07 | native-mission 1.6 s and its tests 1.6 s passed | `manifests/certify-20260925T202718Z-923276.json` |
| run-20260925T203905Z-0d37 | a98b754d | 8 failed: an event-order slip in native-config-show (parse-value lemma before the string lemma it uses) | `manifests/certify-20260925T203915Z-1033045.json` |
| run-20260925T204030Z-e0b9 | 459259b9 | 8/8 passed: native-config-show 4.9 s, native-operator 3.6 s, native-mission 1.6 s, native-operator-host 1.4 s, and their tests (0.5 to 1.6 s) | `manifests/certify-20260925T204052Z-1048804.json` |

hbox (w28 acl2-literal-4g, 2 jobs, 300 s), after merging dev at 0578c60d:

| Run | Roots | Result | Manifest |
| --- | --- | --- | --- |
| run-20260925T202844Z-ca2f | `--affected-by` the six lane books | 93/93 passed. Over 10 s at 2 jobs, none of them lane books: owner-invariants 16.9 s, store-reclaim 11.1 s, peer-authored-accept 11.1 s, native-admin 10.8 s | `manifests/certify-20260925T202954Z-3802121.json` |
| run-20260925T203530Z-07d5 | the 153 default image roots (`proof_artifacts.py roots --profile default`), plain incremental | 73/73 passed; config-owner-live 10.5 s | `manifests/certify-20260925T203553Z-3818799.json` |

The affected-by run did not make the image's closure complete: `acquire`
still found no complete set, because `--affected-by` names the Makefile roots
whose closure contains a changed book, not the image roots. Submitting the
image roots themselves did.

## fn-native-mission-run-init (the continuation's fix)

The old proof `:expand`ed `fn-nop-parse-command` on the preflight's help
branch, which unfolds the whole grammar under certify. It now needs one shape
fact, `fn-native-mission-help-command` (local): a plan whose first word is
`help` is named `help`. That proof opens only the first cond arm. The run-init
lemma opens `fn-native-operator-run` and the preflight, and keeps these
disabled: `fn-nop-parse-command`, `fn-nop-parse-init`, the init-command
rewrite and `fn-native-mission-request`. It takes 0.08 s in a REPL started
from certified includes on persvati. Book: 1.6 s.

## Every loaded configuration renders (PRF-094, the brief's item 3)

- **KEYSTONE `fn-native-config-load-renderable`** (books/native-config-show.lisp):
  `(car (fn-native-config-load octets)) = :accepted` implies
  `(fn-native-config-show-wfp (cadr (fn-native-config-load octets)))`.
  - The subject is the loader that `fn-native-operator-run` reads fn.toml
    through. The host calls it at host/native-operator-host.lisp:19.
  - The local lemmas behind it:
    - `fn-ncfg-parse-lines-parsed`: every value the parser keeps is a boolean,
      a string whose octets are printable, or a natural.
    - The field lemmas: string, boolean and natural fields, and the
      store-derived defaults of auth and control paths.
    - `fn-ncfg-normalize-renderable` (0.07 s). It goes through the exported
      `fn-ncfg-show-wfp-of-make`. A direct proof took 21 s.
- **`fn-native-config-loaded-show-round-trip`**: with the existing round trip,
  the rendering of every loaded configuration loads back as itself.
- **Host effect.** `fn-native-config-show` no longer refuses
  `:not-renderable` at run time. For a configuration from the loader, the
  keystone makes that branch unreachable. The mission plan keeps its own
  wfp test, because it builds its configuration from arguments, not from the
  loader.
- **Teeth** (tests/acl2/native-config-show-tests.lisp):
  - Witnesses: the full and the minimal file load to renderable
    configurations, and `show` renders the full one.
  - `must-fail`s for the one hypothesis: a load refused `:invalid`
    (headroom 101) and one refused for a missing store path are not
    renderable.
  - The old `:not-renderable` assertion is gone.

## Native (hbox, developer image, 2026-09-25)

- **Image.** `build/fn-host-developer` in /tank/fn/scratch/operator-config/tree
  (`git archive` of 0578c60d), built by /tank/fn/scratch/operator-config/build.sh
  under `swarm-build`, with FN_OPENSSL_PREFIX and
  LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib.
  - Artifact set dfbbd771c3e9f44d: 360 books, 153 roots loaded.
  - Core SHA-256 d67160de9a09c53fee40df3f9bbb5c74d051f39bef8005ddbae8b819569d4e8e.
  - Launcher SHA-256 0ff61dc6d778f0e05d7262884337ded558db10225eaaf47223d21e6e49485ffe.
  - The image predates a98b754d/459259b9 (show without its run-time check).
    For a loaded configuration the two behave the same, by the keystone.
- **Run.** `native.sh` (now: the developer image, and the file-first case
  added). Outputs and SHA256SUMS are in
  `planning/evidence/operator-config-2026-09-25/native-out/`
  (summary.txt 33804cbe...).
  - Missions. Each of small-community, relay and archive wrote its fn.toml
    (exit 0). The second run was refused CONFIG-EXISTS (exit 1). `show` is
    byte-identical to the written file for all three, and single keys
    answer. `init` exits 0. `status` shows each mission's profile:
    8 groups per article for small-community, 16 for relay and archive.
    Each node started under systemd-run (MemoryMax=24G) and listened on
    its loopback port.
  - SIGHUP. Two rename-and-HUP rotations ran during 60 control POSTs. All
    60 exited 0, and 60 `accepted post` lines lie across fn.log.1, fn.log.2
    and fn.log, so no line was lost. There are 2 `reopened log` lines, and
    the live file begins `reopened log signal=hup requests=2`. SHA-256:
    fn.log.1 a78008bc..., fn.log.2 9dce0a39..., fn.log 843c0ee8....
  - Relay. POST was refused POSTING-DISABLED (exit 1).
  - node_probe.py against small-community: every assertion held (STARTTLS,
    483 before TLS, login, post, a fresh-connection reread). Exit 0.
    node-probe.out 43012c62....
  - File first (PKT-069).
    `tests.test_native_control_filing...test_signed_author` ran with
    FN_RUN_HYBRID_E2E=1. The signed-author ingress commits through
    `fn-owner-bound-commit-gate`. The signed cancel was filed only in
    control.cancel, before and after a restart. The signed ordinary
    article was filed in fn.test. Exit 0. file-first.out 03dc618e....
    The gate's refusal route (`:not-filed`) is not reachable from this
    ingress, which passes the filed groups. It is witnessed only in the
    ACL2 test book.

## Not done / deferrals

- packaging/fn (the spike's bash wrapper) is not on dev. It would read
  `operator CONFIG show TABLE KEY` in place of its awk and `mission` in
  place of `mission_values`. PKT-098, PKT-099 and PKT-100 are out of scope.
- The image was not rebuilt after 459259b9 (see above).
- Four non-lane books certify above 10 s at 2 jobs on hbox (listed above).
  They are pre-existing debt and not this lane's.
- `make check`: see the LANEDUMP. `planning/ledger.*` is generated on merge.
