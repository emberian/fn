# Stale native tests, second batch, and the refused-start hang

This batch covers the class (c) failures 1 and 3 and the finding in failure 5
of [native-subsets-47bdb9a4](native-subsets-47bdb9a4-2026-09-24.md). The
method is the one in [stale-native-tests](stale-native-tests-2026-09-24.md):
each test is checked against the current machine and keeps the property it
asserted. Lane `lane/stale-tests-2`, from dev `1b734868`. Logs, runners and
the diagnostic are in [`stale-tests-2/`](stale-tests-2/), with
[`SHA256SUMS`](stale-tests-2/SHA256SUMS).

## Invocation

The runs were on hbox, 2026-09-24, 17:48Z to 18:03Z. Scratch directory:
`/tank/fn/scratch/stale-tests-2/`.

- **Test-only changes, on the frozen 47bdb9a4 images.**
  - `tree47` is a copy of native-subsets' `tree-dev`: 47bdb9a4 books and
    host with their certificates. Its `tests/` was replaced by this lane's.
  - `build/` links read-only to
    `/tank/fn/gates/qual-47bdb9a4-20260924/build/images/47bdb9a4/`.
  - The runner is [`run.sh`](stale-tests-2/run.sh): the native-subsets
    runner with only the scratch and tree paths changed. The image's SBCL is
    first on PATH, the same `FN_*` variables are set, and each module ran as
    `timeout 3600 python3 -m unittest -v tests.<module>`, one at a time.
- **Host change, on images built from this lane.**
  - `treelane` is the lane tree without `build/` or `.git`.
  - `proof_artifacts.py acquire` and `validate --profile default` took a
    composed certificate set from `/tank/fn/certcache` (artifact set
    `5e7e4678…`, 283 books, rejected=0). Both passed, and nothing was
    certified.
  - `fn-host` (production) and `fn-host-developer` were built with
    `swarm-build sh tools/build_native_host.sh`.
  - `packaging/freeze-native-image.sh` froze both, with
    `FN_FREEZE_VARIANTS="fn-host fn-host-developer"`, into `img-lane/`.
    `image.sha256` passed before and after each run
    ([copy](stale-tests-2/img-lane.image.sha256)).
  - Core SHA-256: `fn-host.core` `fcce42ad8072be79…`,
    `fn-host-developer.core` `feee2901ae0ae2fe…`. The launchers are
    byte-identical to 47bdb9a4's, since the template did not change.
  - [`reloc.sh`](stale-tests-2/reloc.sh) runs `test_native_frozen_relocation`
    from `treelane` with stdin `/dev/null`. It unsets `LD_LIBRARY_PATH`,
    `FN_OPENSSL_PREFIX` and `SBCL_HOME`, as native-subsets' `reloc.sh`
    does.

## Results

| module | before (log SHA-256/16) | after (log SHA-256/16) |
| --- | --- | --- |
| test_native_served_crash_model | 18 subtest errors ([native-subsets](native-subsets-47bdb9a4-2026-09-24.md), `138e3616fd67f363`) | 3/3: 18 cuts, 3 teeth, 5 recovery barriers, 122 s (`ad5091db51bdc75c`) |
| test_native_crash_model (operator caller of the changed helper) | 7/7 (native-subsets, `ca28ea379c7ea0e2`) | 7/7, 70.6 s (`d27b49c3452e030c`) |
| test_native_raw_scripts | 7/9 with dev tests (native-subsets, `0969902e7043d157`) | 9/9 on the 47bdb9a4 host source (`f72e5b7f5b465156`); 9/9 locally on the dev host |
| test_native_frozen_relocation, 47bdb9a4 `fn-host` | 1/2: both new subtests fail (`0d21e64737722911`) | not applicable |
| test_native_frozen_relocation, lane `fn-host` | not applicable | 2/2 (`d17d66bdbf9983b3`) |
| test_native_frozen_relocation, lane `fn-host-developer` | not applicable | 2/2 (`e6dd7d73bcb138d1`) |

Before the fix, 47bdb9a4 failed both new subtests:
- **stdin closed:** exit 1, with `* ` on stdout;
- **stdin held open:** still running after 10 s, with the unhandled
  `FNN-TLS-UNAVAILABLE` backtrace through `(LP)` on stderr.

## What each test checked, and what it checks now

- **served_crash_model, `test_served_prepare_publish_finish_cuts`.**
  - **Before:** the caller passed no `sent`, frontier or prior frame to the
    shared helper, which probe-tables `9e76b236` had changed. Every cut
    errored.
  - **Now:** each served cut is judged against frames derived by ACL2 from
    the article the owner stores, as the operator differential derives them.
    That article is not the file that was posted. For `fn operator CONFIG
    post`, `fnn-owner-control-submit-serialized` takes one clock reading.
    Under that reading, ACL2 decides `fn-own-operator-decision` with the
    posting configuration `fn-oag-post-config cfg *fn-store-max-payload*`
    (fn-owner-post-config's body), over the node `fn-cpo-open-observed`
    opens. The stored octets are `fn-own-sub-stored-octets cfg` of the
    submission `fn-own-operator-submit` makes.
  - **Inputs:**
    - `cfg` is the configuration `fn-owner-recover` builds:
      `fn-store-cfg-decode-records`, the host function, over the `config/`
      files in name order, replayed by `fn-cpr-replay`.
    - The events are the byte-store scan's decoded records.
    - One bracketed second both stamps the record and dates the injection,
      because the host takes a single reading.
    - The form yields nil unless the open is `:ok` and the decision is
      injected.
    - Only the config inputs are read from disk. The article octets are
      never read.
  - **Shared helper (`tests/test_native_crash_model.py`):**
    - The payload may be an ACL2 form with a `{unix_ms}` hole.
    - The charge is ACL2's `(len payload)`.
    - The caller can add bridge setup forms.
    - The operator caller is unchanged in behaviour.
  - **The caller now passes** the Message-ID, the stored-payload form,
    `("fn.letters",)`, the clock bracket, the pre-post frontier and the prior
    frame. It also asserts that the prior frame is kept at the cut.
- **served_crash_model, new teeth:
  `test_the_served_frame_is_the_injected_articles_not_anothers`.** At
  `record-written`, the frame on disk must be a prefix of no intended frame
  in each of three cases:
  - the injection of a source differing in one octet;
  - the candidate file stored as read (the pre-injection derivation);
  - this injection 100 s outside the bracket.

  All three fail as required.
- **raw scripts, `native_owner_bound_commit_raw.lisp`.**
  - **Before:** it stubbed the Store conditions without the `:message` slot
    and had no `fnn-err`, which `000c6b6e` added to the uncertain arm.
  - **Now:** it loads these forms from `host/native/io.lisp` by name, and a
    missing form is an error:
    - the four conditions;
    - `*fnn-stderr*`, `fnn-concat`, `fnn-string-octets`, `fnn-emit` and
      `fnn-err`.
  - `*fnn-stderr*` is a scratch file. The uncertain case must log
    `Store outcome uncertain` and the condition's message.
  - Mutation check: removing that `fnn-err` from `owner.lisp` fails the
    script ("did not log its reason").
- **raw scripts, `native_owner_consumer_raw.lisp`.**
  - **Before:** the capacity case was driven by a stub
    `fnn-config-max-transactions` and a stubbed preflight. Since
    `ce27b18d`, neither decides anything.
  - **Now:** it loads the deployed `fnn-owner-preflight-publication` and
    `fnn-owner-consumer-commit`. The only ACL2 call recorded is
    `fn-owner-publication-verdict`.
  - The verdict word at capacity is read, never evaluated, from ACL2's
    definitions:
    - `host/owner-host.lisp` `fn-owner-publication-verdict` must answer
      `fn-sbud-verdict`;
    - `books/store-budget.lisp` `fn-sbud-verdict` must have exactly two
      words, one of them `:admissible`;
    - the other word drives the refusal.
  - **Property kept:** the capacity refusal takes no transaction id,
    advances no frontier and prepares nothing. The only call is
    `(:core fn-owner-publication-verdict :consumer)`.
  - Mutation check: removing the preflight call from
    `fnn-owner-consumer-commit` fails the script.
  - **Correction to the brief:** the consumer (and topic) budget is
    `fn-sbud-verdict`, asked by the preflight. `fn-sbud-prepare` is the
    article's prepare-time gate.
- **frozen_relocation, `test_missing_bundled_openssl_refuses_startup`.**
  - **Before:** nonzero exit and "OpenSSL" on stderr, with stdin whatever
    the runner gave it.
  - **Now:** the launcher runs with the OpenSSL prefix hidden, once with
    stdin `/dev/null` and once with a pipe held open. Each run must:
    - exit 5 within 10 s;
    - write nothing to stdout, so no `*` prompt;
    - put `refused start` and `OpenSSL` on stderr;
    - create no store.

## The host change

The image's per-process facility checks ran in `fn-native-entry`
(`host/native/build.lisp`) before `fnn-main`, so they were outside its
handlers:
- `fnn-crypto-startup`;
- `fnn-tls-reset`;
- `fnn-hsig-reset`;
- `fnn-hsig-initialize`.

An error there reached SBCL's `--disable-debugger` hook. That hook's
non-aborting exit was caught by ACL2's `LP`, which printed the prompt and read
stdin.

The checks now run under `fnn-native-startup` (`host/native/io.lisp`). A
serious condition there opens the streams, writes `fn-host: error: refused
start: <reason>` to stderr and ends with `fnn-exit +fnn-exit-usage+` (5).
That exit is an aborting exit, so no loop resumes. The launcher template needed
no change. `make check` passes on the lane.

## Limitations

- The served cuts were judged on 47bdb9a4 images, whose host and books are the
  image's. The lane images were used only for the relocation module.
- `test_bp_contact_relay_native` was not touched.
