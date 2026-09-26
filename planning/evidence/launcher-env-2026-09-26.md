# launcher-env: an installed bin/fn runs its own release (PKT-481 (a)), 2026-09-26

Lane launcher-env, branch lane/launcher-env from dev 48a21162. Theorem-free
host/packaging work: no PRF, no SCN, no book changed (the regenerated docs
grammar book is byte-identical). IDs taken: PKT-481 (a) (ticked), PKT-559.

## 1. Where a developer variable chose the image of an installed launcher

- `packaging/fn` (installed as every release's `bin/fn` by
  `packaging/install-native.sh` line `install -m 0755 packaging/fn "$bindir/fn"`,
  and so into every release tarball and every `upgrade-native.sh` release)
  tested `FN_NATIVE_HOST` FIRST and exec'd it, before its own
  `../libexec/fn/fn-host`. That is the only place. A qualification shell
  sources `env.sh`, which exports `FN_NATIVE_HOST=$I/fn-host` (the candidate),
  so "the old release's `bin/fn`" ran the candidate. qual-dfa810fc's
  run1-contaminated and qual-b6759850's `upgrade-live.log` show it.
- No other `FN_NATIVE_*` or `FN_RUN_*` variable changes which image or tree an
  installed launcher runs: `FN_NATIVE_DEVELOPER_HOST`, `FN_NATIVE_*_HOST` and
  `FN_RUN_*` are read only by the tests and tools (tests/native_process.py,
  tools/native_env.py, tools/hbox_native.sh). Inside the image,
  `FN_NATIVE_PROFILE` is read only while the image is being built
  (`fnn-select-image-profile`), and the fault selectors
  (`+fnn-developer-selectors+`) are refused by a production image
  (`fnn-developer-selector-refusal`, host/native/io.lisp).
- The frozen image launcher (`packaging/freeze-native-image.sh`, every
  release's `libexec/fn/fn-host`) sets its own `SBCL_HOME` and
  `FN_OPENSSL_PREFIX` and puts its own libraries first. It still splices the
  caller's `${SBCL_USER_ARGS}` into the runtime options. That cannot change
  which image `bin/fn` picks. Whether it can displace the core was not tested:
  PKT-559 (3).
- `packaging/install-native.sh` takes its input image as `FN_NATIVE_HOST`.
  That chooses what gets installed, not what an installed launcher runs.
  `release-tarball.sh` and `upgrade-native.sh` pass it explicitly. A bare
  `install-native.sh` run from a shell that exported it would install that
  image: PKT-559 (2).

## 2. The mechanism chosen

The launcher decides by where it is:

- **Installed:** a `libexec/fn/` directory sits beside its `bin/`. It always
  runs that directory's `fn-host` and ignores `FN_NATIVE_HOST`. A missing
  installed image is exit 4 and names that path. It never falls back to the
  variable or to a tree.
- **Developer:** `packaging/fn` in a checkout, which has no `libexec/fn/`
  beside it. It runs `FN_NATIVE_HOST` when set, else the tree's
  `build/fn-host`.

Why this and not a differently named variable or an opt-in file:

- The callers that use the override already call it through the checkout's
  `packaging/fn` or `packaging/fn-native`. These are
  tests/test_native_cli_launcher.sh and the v0 matrix invocations
  (`env FN_NATIVE_HOST=... packaging/fn-native operator ...`).
- tools/hbox_native.sh, tests/native_process.py and the qualification runners
  exec the image path they are given directly, not through an installed
  `bin/fn`.
- So nothing that uses the variable changes meaning, and no new name or file
  exists that a production install could carry by accident. The install
  layout that `install-native.sh` writes is what makes a launcher an
  installed one.
- tests/test_native_friends_feed.py still pops the variable for the friend's
  `bin/fn`. That is now belt and braces, and its comment says so.

## 3. Checks

- tests/test_native_cli_launcher.sh, extended. It builds a fake installed
  layout (`opt/fn/bin/fn` = packaging/fn, `opt/fn/libexec/fn/fn-host` prints
  `installed image`) and checks three cases:
  - `FN_NATIVE_HOST=<other stub> bin/fn --version` prints `installed image`.
  - The same without the variable prints the same.
  - With the installed image removed and the variable set, exit is 4 with
    `native host image missing: .../opt/fn/libexec/fn/fn-host`, and nothing
    is run.

  The test passes on the laptop. The same test run against dev's launcher
  (`git show HEAD:packaging/fn`) fails at the first new assertion: `native
  argv: <--version>` against `installed image`.
- tests/test_native_image_profiles.py: the launcher test now asserts that the
  installed branch comes before the `FN_NATIVE_HOST` branch. 12 ran, OK, 5
  skipped (the saved-image class needs built images).
- tests/test_native_distribution.sh passes on the laptop.
- `python3 tools/docs_check.py --write`: 0 failures. It rewrote
  tests/acl2/docs-operator-grammar-tests.lisp with identical bytes.
- `make check-lane`: see LANEDUMP.

**Native case (hbox, /tank/fn/scratch/launcher-env/, script
planning/evidence/launcher-env/native_case.sh).**

- **Setup.**
  - `packaging/release-tarball.sh` from this lane's tree packages the existing
    frozen dfa810fc production image
    (/tank/fn/gates/qual-dfa810fc-20260926/build/images/dfa810fc...). No image
    was built.
  - The tarball is c0c7090d8e85e2948c7f5f5dc425ea952f92995b0650f7d385f5f372f0df49a3.
  - It was unpacked and summed under `install/` the way
    docs/peering-with-a-friend.md says. Its `bin/fn` is byte-equal to this
    lane's packaging/fn (sha256 97254299...).
- **The two outputs.**
  - with-var.log (sha256 2fb60536a23301a31a552a4cb3c602b03c0a8dfd9472d61c9ad95bdb360b472c).
    With `FN_NATIVE_HOST=<bbf52159's fn-host>`, `bin/fn --version` printed
    `fn dfa810fceabedde937ba7e4bfa46b43fd599ac62`, rc 0.
  - without-var.log (sha256 47a591a1ae01afa01305cd9c30da1a4f305d3cfdfd773eb9b9d5cf1da6875900).
    `bin/fn --version` printed `fn dfa810fceabedde937ba7e4bfa46b43fd599ac62`,
    rc 0.
- **Control.** control-old-launcher.log (sha256
  5ead6b5ba2bd19f425a25daa66f6b6a7aa90baea32e97cf05b259965f172c59d).
  - This used qual-dfa810fc's own installed tarball, whose `bin/fn` is the old
    launcher (sha256 61f6f464...), with the same variable.
  - The output was `fn-host: error: unknown verb --version`, rc 5. That is
    bbf52159's image answering: it predates `--version`.
  - Without the variable, the same tarball printed
    `fn dfa810fceabedde937ba7e4bfa46b43fd599ac62`.
- **The native module.** No module was run by this lane. The batch runs
  tests/friends_tarball.sh (the friend's node on the tarball's `bin/fn`, the
  author on `FN_NATIVE_HOST`). That is where the new launcher and the
  harness variable meet in one process tree.

## 4. What is not done, and the qualification step

- **The rehearsal step (for the deputy's qualification checklist).**
  - Every upgrade or rollback rehearsal step runs an installed release's
    `bin/fn` with every `FN_NATIVE_*`, `FN_RUN_*` and `FN_TEST_*` popped from
    that child's environment. This covers `status`, `store needs-upgrade`,
    `upgrade-profile`, `rollback-check`, and the old release's restart.
  - It is still required after this fix. Every release cut before it
    (bbf52159 on the live node, b6759850, dfa810fc, and 69046a76 unless it is
    re-cut) carries the old launcher.
  - The rehearsal record prints each release's `bin/fn --version` first. Its
    revision must be that release's.
- **PKT-559** records what remains:
  - (1) The releases above carry the old launcher (the step above).
  - (2) Renaming install-native.sh's input variable.
  - (3) `${SBCL_USER_ARGS}` in the frozen launcher.
- **Assurance chain.** Not applicable in the ACL2 sense. The launcher decides
  nothing about data. The image selection is a host packaging fact, checked
  by the shell test and observed in the native case.
- **docs/operator.md.**
  - The install paragraph states the rule.
  - The rollback paragraph on checkpoints now says "older images reject a
    newer checkpoint file and fall back to a full replay". This comes from
    qual-dfa810fc item 1 (c) and served-path-scale-2's PKT-395 fix.
