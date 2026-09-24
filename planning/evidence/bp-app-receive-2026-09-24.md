# bp-app receive: the dropped ingress, raw host arity, the refusal line, one-shot send

Lane `bp-app-receive` from dev `552c763e`. Code commit `ec35b0d5`; test
commit `70f26cda`, which changes only `tests/test_bp_app_native.py`. This
closes findings 1 to 3 of [stale-native-tests](stale-native-tests-2026-09-24.md).
The logs, the runner and the `config check` outputs are in
[`bp-app-receive/`](bp-app-receive/), listed in [`SHA256SUMS`](bp-app-receive/SHA256SUMS).

## Defects and fixes

1. **The dropped ingress.** `fnn-bpapp-deliver` (`host/native/bp-app.lisp:213-215`
   at `552c763e`) called `fnn-bpapp-accept-locked` (`:89`, 9 required
   parameters) with 8 arguments and no `ingress`. The planner
   (`fn-bpaj-transit-plan`) found no principal and answered
   `(:refused :no-principal)` for every request.
   - The receiver now builds the CL ingress through `fnn-bps-tcpcl-ingress`,
     as bp-node's dispatcher does. Its inputs are:
     - the kernel-observed channel (`fnn-bpnode-observed-channel`);
     - a per-connection session counter, incremented under a mutex;
     - the epoch of `fn-bpnf-initial-state`, because `bp-app receive` runs no
       FNBS machine. The app plan reads only the ingress's principal and
       generation, and the epoch is not persisted on this path.
   - `fnn-bps-tcpcl-ingress` now takes the FNBS state instead of the
     service.
   - The test fixture enrolled the boundary on a reserved port, but the
     receiver listened on port 0. Admission
     (`books/bp-session-admission.lisp`) binds the boundary to the port the
     receiver listens on, so the receiver now listens on the enrolled port.
2. **Raw host arity is a `make check` failure.** `tools/harness_check.py
   raw-arity` covers raw Common Lisp code; `acl2-arity` only read ACL2
   `defun`s.
   - Each raw `defun` in a raw-loaded host file (`ledger.raw_host_paths`, 28
     files) bounds the number of arguments its callers may pass: from the
     required count up to the positional maximum, with no maximum under
     `&rest`, `&body` or `&key`.
   - It also checks the ACL2 dispatchers (`fnn-call`, `fnn-core`,
     `fnn-core-state`, `fnn-owner-core`, `fnn-owner-action` and
     `fnn-bpapp-core-record` applied to a quoted `fn-x`). The argument count,
     plus `state` for the state-taking dispatchers, must equal `fn-x`'s
     formals, from the books or the ACL2-mode host wrappers.
   - Run on `552c763e`, it made two findings, both real:
     - the bp-app call above;
     - `host/native/config.lisp:11`, where `fnn-command-config-profile` passed
       the state-free wrappers `fn-native-config-host-max-octets` and
       `-load` through `fnn-core-state`. As a result, `fn config check` could
       not run on any image: the 47bdb9a4 developer image exits 4 with
       `(ERP VAL &REST IGNORED): at least 2 expected, but got 1`
       (`config-check.before.out`). The fixed image answers
       `accepted config` and exits 0 (`config-check.after.out`).
   - On the fixed tree it makes 0 findings over 4676 raw applications and 704
     dispatched ones. One name is left undecided: `fn-native-entry`, which is
     defined both in raw code and in ACL2.
   - `tests/test_harness_check.py` `RawArityTests` (7 cases) checks:
     - that the 8-of-9 shape is caught and the 9-argument call is clean;
     - optional, rest and key bounds;
     - that binders, quotes and `flet` do not count as calls;
     - `funcall #'`;
     - a dispatched call counted with its state argument;
     - that the tree has zero findings.
   - Limits: backquote templates are walked only for their unquoted forms. A
     name reached by `apply` or a computed symbol is not decided.
3. **The refusal reason.**
   - `books/owner-log.lisp` defines `fn-olog-bp-app-refusal-line` (result,
     reason, xfer). Its class is `fn-olog-bp-app-class`:
     - `:refused` and `:clock-unusable` are refused;
     - `:busy` is deferred;
     - any other non-accepted word is uncertain.
   - Two theorems cover the line:
     - `fn-olog-bp-app-refusal-line-is-one-line`;
     - the keystone `fn-olog-bp-app-refusal-line-says-refused-iff-refused`.
   - `tests/acl2/owner-log-tests.lisp` has the witness line
     `refused bp-application xfer=0 result=refused reason=no-principal`, the
     deferred and uncertain lines, and two `must-fail`s. The first,
     "refused unless accepted", is separated by `:busy`. The second,
     "refused only for `:refused`", is separated by `:clock-unusable`.
   - `host/bp-native-app-host.lisp` `fn-owner-app-plan-answer` keeps the
     planner's reason in `fn-owner-app-refusal-reason`:
     - the transit plan's `(cadr plan)`, for example `:no-principal`;
     - the install check that failed: `:request`, `:intent`,
       `:bundle-source`, `:bundle-destination`, `:request-status`, or one of
       the legacy path's checks.
   - `fn-owner-app-refusal-log` renders the line and returns its class. The
     host writes the line through `fnn-owner-log` and returns `:refused`,
     or `:uncertain` for an uncertain class, to the convergence layer.
   - The host-formatted stdout line `BP application refused xfer=N` is gone.
   - Certified on hbox: `books/owner-log` and
     `tests/acl2/owner-log-tests` both passed (manifest
     `certify-20260924T170358Z-1691556.json`, run
     `run-20260924T170328Z-1a4e`).
4. **One-shot `bp send` termination.**
   - Who decides: the active side's SESS_TERM decision was host code, the
     `when` in `fnn-tcl-session` (`host/native/tcpcl.lisp:396-401` at
     `552c763e`). It waited for `inbound >= expect`. `bp send ... 1` waits
     for one receipt, and a refused bundle gets none, so the sender sent
     KEEPALIVE until it was killed.
   - `fn-bpnp-step` is not involved: `bp send` drives the TCPCL session
     machine directly.
   - **Machine gap:** the session machine (`books/tcpcl-session.lisp`) has no
     "nothing more to send or await, close" effect.
   - The decision is now ACL2's `fn-tcl-host-active-closep` in
     `host/tcpcl-host.lisp`. It is a `:program` host wrapper, and no theorem
     covers it. It closes once the transfer the host was given has an
     outcome, and then either the EXPECT inbound transfers have arrived or
     that outcome is `:refused` or `:uncertain`. The outcome is the one the
     machine's `:outbound-refused` or `:outbound-failed` events set.
   - `tests/test_bp_app_native.py` gained
     `test_unadmitted_channel_is_refused_with_the_planner_reason`. The
     receiver listens on a port no boundary names. The test checks the ACL2
     line on the receiver's stderr, sender exit 1, receiver exit 1 and no
     stored article.
5. **A stale expectation, now reachable.** With a principal admitted, the
   request takes the transit path that specs/bp-node-machine.md specifies
   (`:request-transit-intent`). The Store provenance is
   `peer-transit:sender-boundary`, from `fn-peer-injection-arguments`. The
   test had asserted `bp-receive node=... label=native-policy`, the
   historical control-submission binding, which a request reached only while
   the ingress was missing.

## Runs

- **Where:** hbox, 2026-09-24 17:05Z to 17:24Z, in
  `/tank/fn/scratch/bp-app-receive/tree` (`git archive ec35b0d5`).
- **Default artifact set:** `1da84a1b6dea9b24…`, 283 books, `loaded`.
- **Farm run** `run-20260924T170527Z-f077`: 17 BP books from the kind-8
  merge were uncached and were certified, all passed (manifest
  `certify-20260924T170545Z-1694114.json`).
- **DTN artifact set:** `14f23efe57415d1d…`.
- **Toolchain:** ACL2 8.7 w28 `acl2-literal-4g`, SBCL 2.6.8
  (`/tank/fn/sbcl`), OpenSSL 3.5.8.
- **Images:** built with `swarm-build sh tools/build_native_host.sh`; both
  builds exited 0.

| image | launcher SHA-256 | core SHA-256 |
| --- | --- | --- |
| `fn-host-developer` (build.lisp, developer) | `2f75f6a5f3a63d54…` | `2753bbc5cb4364a4…` |
| `fn-host-dtn-developer` (build-dtn.lisp, developer) | `cc179cac74f66ce1…` | `3be9f493e7cc8016…` |

`test_bp_app_native` drives `FN_NATIVE_DEVELOPER_HOST`, the default
developer image: the DTN build does not load `bp-app.lisp`. The DTN
developer image was built to cover the `bp.lisp`, `bp-service.lisp` and
`tcpcl.lisp` changes. Every run used the runner [`run.sh`](bp-app-receive/run.sh)
with the lane's tests (`70f26cda`). `before` is the 47bdb9a4 qualification
developer image, read only.

| module | before | after | log SHA-256/16 before → after |
| --- | --- | --- | --- |
| test_bp_app_native (5 cases: the 4, plus the refusal case) | 1/5: 3 `TimeoutExpired` on `bp send`, 1 failure | **5/5** | `513ad65d6c6ec5ed` → `be3ad3879c8bdc11` |
| test_bp_service_native (DTN developer) | 16/16 at 47bdb9a4 (`d8ba35fc11230537`) | 16/16 | → `8612348aae495b8b` |
| test_bp_receive_integrity_native (DTN developer) | 4/4 (`ea5ce4cbfe787cd4`) | 4/4 | → `c22d8dba95e4b3a1` |
| test_bp_fragment_node_native | 1/1 (`f6d4a2628e99509e`) | 1/1 | → `944761cc54478d6c` |

The earlier "before" on the 6c0626c5 image, with the tests as they stood
then, was 1/4 (`62a071662aa65b13`, stale-native-tests). The 47bdb9a4 row
above uses the lane's tests, port fix included, so the port fix alone
changes nothing. The server fix is what moves the module.

`make check` passed at `ec35b0d5` and again at the evidence commit.

## What remains

- A `(:busy reason)` transit plan is still answered `:refused` by
  `fn-owner-app-plan-install`, which is what it did before. Its line names
  the deferral reason with `result=refused`. The bp-node caller maps any
  non-refused, non-accepted word to `:uncertain`, so returning `:busy` from
  the plan would change bp-node's outcome. That is left for the P11 policy
  owner.
- `fn-tcl-host-active-closep` is not a theorem. The TCPCL session machine
  still lacks a close effect (the machine gap above).
- The bp-app ingress uses epoch 0 of `fn-bpnf-initial-state`. That is
  correct only while nothing on this path persists the ingress.
- The raw-arity lint does not decide calls inside backquote templates, or
  calls through `apply` or computed symbols.
