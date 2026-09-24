# Stale native tests (class (c)) on the 6c0626c5 images

The class (c) failures of [native-subsets-6c0626c5](native-subsets-6c0626c5-2026-09-24.md)
(failures 3, 7, 9 and the MRU count in failure 1) brought up to date with the
machine, each check keeping the property it asserted about fn. Test commit
`d03410ff` on `lane/stale-native-tests` (from dev `57cc5659`). Logs, the
runner and the diagnostic are in [`stale-native-tests/`](stale-native-tests/),
with [`SHA256SUMS`](stale-native-tests/SHA256SUMS).

## Invocation

On hbox, 2026-09-24 16:23Z to 16:43Z. The lane tree (dev plus `d03410ff`) was
rsynced without `build/` to `/tank/fn/scratch/stale-native-tests/tree`, whose
`build/` links to the frozen image directory
`/tank/fn/gates/qual-6c0626c5-20260924/build/images/6c0626c5/`, read only;
`sha256sum -c image.sha256` there passed first. The runner
[`run.sh`](stale-native-tests/run.sh) is the native-subsets-6c0626c5 runner
with only its scratch directory changed: same `FN_*` variables, the image's
SBCL 2.6.8 first on `PATH`, every opt-in flag set. One module, or one test
id, at a time: `timeout 3600 python3 -m unittest -v tests.<target>`.

The source-text tests read the lane tree (dev), and the process tests drive
the 6c0626c5 images. Dev differs from 6c0626c5 under the source these tests
read only in `books/native-operator.lisp`, `host/native/owner.lisp` and
`tests/test_native_operator_verbs.py`, which gained reserved-name cases.

## Results

"Before" is the native-subsets-6c0626c5 run: the same images, with the tests as
they were at 6c0626c5.

| module | before (log SHA-256/16) | after (log SHA-256/16) | the stale case |
| --- | --- | --- | --- |
| test_native_raw_scripts | 8/9 (`6646769678dfc678`) | 9/9 (`c267115bcb90f77c`) | `owner_group_codes_raw` passes |
| test_native_control | 13/14 (`489c44e644f481c6`) | 14/14 (`4c62289269f813ca`) | passes |
| test_native_operator_cli | 5/6 (`981d86b298440444`) | 6/6 (`91449a6cad70e0e4`) | passes |
| test_native_operator_verbs | 11/13 (`8abe6adbf81d7064`) | 13/16 (`0504aa69ea7efbe4`) | STORE-EXISTS passes; the 3 failures are not class (c), see below |
| test_native_storage_codec | 10/11 (`59275058499bc3d6`) | 11/11 (`0b9ed5c78b0d75d7`) | passes |
| test_bp_node_native, MRU case only | FAIL `6 != 7` (module log `b9d21fc69db50d2a`) | OK (`aaa9369396ae8753`) | passes; the other 15 cases were not re-run |
| test_bp_app_native | 1/4 (`6ecbbb4de6e22306`) | 1/4 (`62a071662aa65b13`) | still refused; the cause is an fn defect, see below |

The operator_verbs failures after the change are:
- `test_init_without_a_group_is_usage_and_writes_nothing` (`0 != 5`): the
  (a) `Not A Group` defect in this image.
- `test_init_of_a_reserved_name_is_refused_and_writes_nothing` and
  `test_group_create_poster_is_refused_and_publishes_nothing` (`0 != 1`):
  dev tests for reserved group names (NNT-009), which this image predates.

## What each test checked, and what it checks now

- **raw scripts, `native_owner_group_codes_raw.lisp`.**
  - Before, the script `eval`d only `defun fnn-owner-attempt` and stubbed the
    conditions. The p2-wire `fnn-owner-attempt-handlers` macro was missing,
    so the stub refusal escaped.
  - Now it loads these deployed forms by name, and fails if one is missing:
    - the Store condition hierarchy from `host/native/io.lisp`, including
      `fnn-store-io-refusal`;
    - `defmacro fnn-owner-attempt-handlers` and `defun fnn-owner-attempt`
      from `host/native/owner.lisp`.
  - The same two refusal cases are asserted (an unknown group, then a charge
    refusal), each after the ACL2 group lookup. A refused attempt must also
    leave the store unfenced.
- **control, `test_the_reply_is_the_owners_status`.**
  - Before, a literal `'(:consumer-reply :consumer-poll-reply)`.
  - Now the expected set is every `(list :<kind>-reply ...)` built in
    `books/consumer-local-control.lisp` and
    `books/topic-history-local-control.lisp`, which gives topic, consumer,
    consumer-poll and consumer-status.
  - The host's after-submit `member` list must equal that set, and each kind
    must have its `fn-native-control-host-<kind>-encode` in
    `host/native-control-host.lisp`.
- **operator_cli, `test_operator_calls_existing_acl2_credential_plan_and_executor`.**
  - Before, the text `(cdr argv)`.
  - Now the argument that `fn-nop-parse-principal` passes to
    `fn-native-auth-admin-parse-argv` must be `(cdr argv)`, or `(F argv)`
    where `F` is defined exactly once in `books/` as
    `(if (consp x) (cdr x) nil)` under `:guard t`. `fn-ncfg-rest` is such a
    function.
  - Two mutations of a copy of the book fail the test: `fn-ncfg-second argv`
    and a bare `argv`.
- **operator_verbs, STORE-EXISTS.** `b"refused operator init STORE-EXISTS" in
  stderr.upper()` could never hold. It is now
  `b"REFUSED OPERATOR INIT STORE-EXISTS" in stderr.upper()`. No other test
  compares a lower-case literal with upper-cased output.
- **storage_codec, `test_native_and_python_cross_open_identical_acl2_frames`.**
  - Before, the two transaction files had to be byte-identical.
  - Now ACL2 unframes both files (`fn-store-frame-store-decode`) and decodes
    both records (`fn-record-decode-exact`). Both stamps (`fn-record-stamp`)
    must be naturals, not `:legacy`.
  - The native record, given the Python record's stamp with
    `fn-record-with-stamp`, must `fn-record-encode` to the Python record
    octets byte for byte. Framed again, it must equal the Python `.txn` file
    byte for byte, trailer included.
  - The stamp is found by the codec's definition, not by an offset.
- **bp_node, `test_older_mru_wait_allows_younger_forward_and_replays`.**
  - Before, dispatch had to add exactly 4 lifecycle files.
  - Now the frames are counted by the ACL2 decoder that opens each one:
    - `fn-bpnf-stored-record-unframe` gives kind 5;
    - `fn-bpnp-dispatch-unframe` gives kind 6;
    - `fn-bpnp-attempt-unframe` gives kind 8;
    - `fn-bpnp-result-unframe` gives kind 9.
  - Before dispatch there must be exactly two kind 5, at most two kind 6 and
    nothing else. After dispatch the counts must be exactly
    `{5: 2, 6: 2, 8: 1, 9: 1}`. The replay must leave the same names and
    counts.
  - **The machine is right.** specs/bp-node-machine.md §4.2 (the current
    native subset) says the serving node's `:progress` step "may install a
    `:pending` `:dispatch`" for a routed transit carrier. The receiver's
    fixture configures a bp-boundary for `dtn://sender/`, so a kind-6 at
    receive time is specified behaviour. How many of the two dispatches
    happen before the test stops the receiver depends on timing. The
    1a9dd747 diagnostic saw one, which gives 6 files instead of 7.
- **bp_app.**
  - The fixture now enrolls the sender the way the fragment fixture does:
    `operator CONFIG policy set path-identity receiver.bp.gate.invalid` and
    `bp-boundary add sender-boundary sender.bp.gate.invalid dtn://sender/
    PORT fn.test 32768 16`.
  - The refusal is unchanged with the enrollment
    ([diagnostic](stale-native-tests/bpapp_enrolled_diag.py), log
    `c799a8ab7c4be6a2`). The receiver prints
    `BP application refused xfer=0` and keeps running, and the sender prints
    `refused outbound xfer=0 reason=4` and sends KEEPALIVE until it is
    killed.

## Findings for the server

1. **(a) `bp-app receive` never passes the ingress to the application
   planner.**
   - `fnn-bpapp-accept-locked` (`host/native/bp-app.lisp:89`) takes 9
     parameters: `... bundle-identity ingress bundle-source
     bundle-destination`.
   - `fnn-bpapp-deliver` calls it with 8 arguments
     (`host/native/bp-app.lisp:213-215`, `... (fnn-octets identity) source
     destination`), so there is no `ingress`.
   - The only other caller, `host/native/bp-node.lisp:54`, passes 9 arguments
     with `(fifth view)` as the ingress.
   - With 8 arguments, `source` becomes the ingress and `destination` the
     bundle source, and the bundle destination is unbound. `fn-bpaj-ingress-peer`
     (`books/bp-transit-join.lisp:9`) then finds no CL ingress principal, so
     `fn-bpaj-transit-plan` answers `(:refused :no-principal)` and the plan
     is not `:ready`.
   - Dev `57cc5659` has the same code.
   - This is inferred from source and not traced. Under a checked arity call
     the service would stop with exit 4, but the receiver keeps running and
     prints `refused`. That points to the arity not being checked in the
     image's compiled host code. Either way, a missing argument reaches the
     planner.
   - This, not the enrollment alone, is why test_bp_app_native stays at 1/4.
     The enrollment is still required, by `fn-bpaj-ingress-peer`.
   - The fix belongs in fn: pass the CL ingress, as bp-node does. Then re-run
     test_bp_app_native on a new image. With a Path identity configured, the
     transit-436 regression (failure 1) may then show on this path.
2. **(a) The receiver logs no reason for the refusal.** The line is
   `BP application refused xfer=0` / `reason=REFUSED` (`bp-app.lisp:218`).
   `fn-owner-app-plan` and `fnn-bpapp-accept-locked` collapse every
   non-`:ready` plan to `:refused`, and the transit plan's reason
   (`:no-principal`, `:request`, ...) is dropped. This is unchanged from
   1a9dd747. The hybrid-feed-storm logging fix does not cover this path.
3. **(a) A one-shot `bp send` does not terminate after its only transfer is
   refused.** The sender stays in the session and sends KEEPALIVE. Two cases
   error with `TimeoutExpired` after 180 s (log `62a071662aa65b13`). This is
   unchanged, and is also P11's retry-policy question.

## Limitations

- For test_bp_node_native only the MRU case was re-run. The module's other 9
  failures are failure 1 (a) and were not touched.
- The bp_app enrollment is untested on a path that gets past the planner,
  because finding 1 prevents that on every image built so far.
- `make check` passed in the lane at `d03410ff`.
