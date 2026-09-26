# outcome-algebra, 2026-09-26: one outcome classification, one code map (PRF-143, HST-009)

Lane outcome-algebra (wave 3; brief build/coordinator/queue/w3-outcome-algebra.txt),
implementing gpt-6's answers section 5 as the coordinator took it
(planning/review-2026-09-26-gpt6-answers.md): exit(f, x) = code(classify(f, x)).
Retires PKT-295, PKT-246 and PKT-275; what is left is PKT-329.

## What now works

| Code | Class | Before | Now |
| --- | --- | --- | --- |
| 0 | `:accepted` | 0 everywhere | unchanged |
| 1 | `:refused` | 1, except operator NO-STORE (6) | every known refusal: NO-STORE, CONFLICT, the clock-undecided `bp decode` |
| 3 | `:fenced` | 3, also `bp decode` clock-undecided and a lost `tcpcl` session | only an indeterminate publication (every family: 3 iff fenced) |
| 4 | `:fault` | 4 | unchanged |
| 5 | `:usage` | 5 | unchanged |
| 6 | `:interrupted` | BP lost connection, and operator NO-STORE | BP lost connection only (the `tcpcl` verb's lost session too) |
| 7 | `:not-connected` | BP | unchanged |

- One ACL2 constant, `*fn-outcome-codes*` (books/outcome-class.lisp), and
  `fn-outcome-code`. Every family's code function is `fn-outcome-code` of
  its classify function: `fn-bprc-exit-code` (BP), `fn-bprc-decode-exit-code`
  (`bp decode`), `fn-native-operator-exit-code` via
  `fn-native-operator-outcome-class`, `fn-native-control-status-exit-code`
  via `fn-native-control-outcome-class`, `fn-thlc-status-exit-code` via
  `fn-thlc-outcome-class`, and the host conditions via
  `fn-outcome-host-condition-exit-code` (called by host/native/io.lisp
  `fnn-exit-code-for`). host/native/io.lisp's `+fnn-exit-ok/refused/uncertain/fault/usage+`
  are `(fn-outcome-code :class)`, evaluated when the image loads io.lisp after
  every book is included (host/native/build.lisp, build-dtn.lisp,
  build-store-test.lisp include books/outcome-class first): the host writes no
  exit number of its own. host/native/tcpcl.lisp `fnn-tcl-exit-code` now goes
  through `fn-bprc-session-evidence` (a transfer lost after establishment is 6).
- `CONFLICT`: `:conflict` appended last to `*fn-nctrl-statuses*`, classed
  `:refused`. host/native/owner.lisp `fnn-owner-complete-bound-submission`
  (its new NAME-CONFLICT argument, passed by the operator post
  `fnn-owner-control-submit-serialized` and by `fnn-hybrid-control-author`,
  not by the BP application) answers `fn-native-control-completion-status`
  of the owner's result and the completion word. The clients print
  `refused operator post CONFLICT` / `refused hybrid-author CONFLICT`, exit 1.
  tools/fn_client.py prints `refused CONFLICT 441 ...` for the NNTP
  conflict line and its `--json` record carries `"scope": "server"` and
  `"reason": "conflict"`.
- specs/host.md "CLI exit codes" is the one table (HST-009's line under it),
  "BP run classes" points at it; docs/operator.md's outcome table rewritten
  once (seven rows, health named as the one exception); docs/agents.md's
  retry paragraph says CONFLICT and "upgrade the client with the node".

## Assurance chain

native entry (`fnn-main` -> `fnn-dispatch` -> a verb) -> the family's executed
ACL2 classify function (the subjects above, called by name through `fnn-core`,
or directly by `fnn-exit-code-for` in a handler) -> `fn-outcome-code` over
`*fn-outcome-codes*` -> the process exit (`fnn-exit`). There is no second
representation: the codes are the constant's integers, and the host constants
are evaluated from it once per image. The relation "the exit is the code of
the class" is established by definition at each family's code function; the
behavioural theorems are about those functions.

## Theorems (PRF-143), with the host line that calls each subject

books/outcome-class.lisp:
- `fn-outcome-code-separates-the-classes` (keystone): distinct classes, distinct codes.
- `fn-outcome-code-table-by-definition`: the seven codes are (0 1 3 4 5 6 7).
- `fn-outcome-code-is-fenced-iff-fenced`: over classes, 3 exactly for `:fenced`.
- `fn-outcome-of-status-fences-iff-uncertain`; `fn-outcome-host-condition-fences-iff-indeterminate`
  (subject `fn-outcome-host-condition-exit-code`, host/native/io.lisp `fnn-exit-code-for`).

books/bp-run-class.lisp:
- `fn-bprc-run-exit-code-is-fenced-iff-fenced` (host: bp.lisp `fnn-bp-exit-code`,
  bp-service.lisp `fnn-bps-exit-code`, tcpcl.lisp `fnn-tcl-exit-code`).
- `fn-bprc-decode-never-fences` (host: bp.lisp `fnn-command-bp-decode`): no
  decode verdict is 3; the clock-undecided verdict is 1.
- `fn-bprc-exit-code-separates-the-classes` still holds (now through `fn-outcome-code`).

books/native-operator.lisp:
- `fn-native-operator-exit-is-fenced-iff-uncertain` (host: native-operator-host.lisp
  `fn-native-operator-host-result-exit-code`, called by operator.lisp).
- `fn-native-operator-absent-store-is-refused` (keystone, restated): NO-STORE's
  exit is `(fn-outcome-code :refused)`, 1; `*fn-nop-no-store-exit*` is gone.

books/native-control.lisp:
- `fn-native-control-exit-is-fenced-iff-uncertain` (host: native-control-host.lisp
  `fn-native-control-host-status-exit-code`, called by operator.lisp's post client
  and hybrid-control.lisp's clients).
- `fn-native-control-conflict-is-a-refusal` (keystone, PKT-246): for an owner
  control result in `*fn-nctrl-owner-control-results*` (the range owner.lisp
  checks before it asks), the completion status is `:conflict` only for an
  owner refusal of the word `:conflict`; `:conflict` classes `:refused` and
  exits 1; any other word passes the result through.
- `fn-nctrl-conflict-keeps-every-earlier-octet` (keystone, the format): each
  status of `*fn-nctrl-statuses-before-conflict*` is sealed exactly as the
  enumeration before `:conflict` seals it. Proved over the payload with the
  seal left closed: the seal's digest is A-CRYPTO's constrained
  `fn-frame-digest`, which a proof cannot evaluate. The round trip of
  `:conflict` and the older decoder's `:bad` are therefore executed witnesses
  (tests/acl2/outcome-class-tests.lisp, under the digest's attachment), not
  theorems.

Teeth: tests/acl2/outcome-class-tests.lisp. For each keystone a reachable
witness (the seven codes; `:fenced` 3 and `:refused` not; the operator's
uncertain result 3 and NO-STORE 1; the control `:uncertain` 3 and `:conflict`
1; the decode's `:uncertain` 1; the owner refusal of `:conflict` answered
`:conflict`; `:article-exceeds-profile-bound` sealed alike), and per
hypothesis a witness plus a `must-fail` at that counterexample: without
class membership `:bogus` collides with `:fenced` and answers 3; without
distinctness `:usage` equals itself; without `outcome = :uncertain` the
accepted decode is 0; without the word hypothesis the refusal is renamed;
without enumeration membership `:conflict` is sealed now and was `:bad`.
tests/acl2/native-operator-tests.lisp's NO-STORE expectations move from 6 to
1, each citing specs/host.md's table.

The old-client fallback, measured in ACL2 and natively: the packet predicted
exit 4. The image before `:conflict` decodes the new octet as `:bad`; its
control client (host/native/control.lisp and hybrid-control.lisp `...-send`)
takes `fn-native-control-transport-outcome` of the stage it reached for any
reply outside its enumeration, and a reply is read only after submission, so
it answers `:uncertain`, exit 3. That is conservative (never a false
acceptance) but it sends an operator toward a recovery the node does not
need, hence docs/agents.md: upgrade the client with the node.

## Certification

| run | box | what | result | manifest |
| --- | --- | --- | --- | --- |
| run-20260926T091907Z-7369 | hbox | affected-by outcome-class at the first draft | failed: `fn-nctrl-reply-encode-with` guard (the enum spec's well-formedness); 17 dependents on it | `manifests/certify-20260926T091937Z-1092784.json` |
| run-20260926T092306Z-21c3 | persvati | affected-by native-control, native-operator, outcome-class at cd64c1ea | passed, 86 books, none over 10 s: native-operator 7.70 s, outcome-class-tests 2.07 s, bp-run-class-tests 1.72 s, native-control 1.27 s, topic-history-local-control 1.17 s, bp-run-class 0.21 s, outcome-class 0.07 s | `manifests/certify-20260926T092330Z-3847549.json` |
| run-20260926T092742Z-c432 | persvati | tests/acl2/outcome-class-tests after the must-fail forms were instantiated | passed, 1.98 s | `manifests/certify-20260926T092805Z-3892210.json` |
| run-20260926T094810Z-6ab7 | persvati | tests/acl2/docs-operator-grammar-tests regenerated (docs/operator.md's lines moved) | passed, 1.92 s | `manifests/certify-20260926T094832Z-4083496.json` |

The native-control changes were first admitted in an hbox `proof_repl`
session (w28 toolchain, /tank/fn/gates/outcome-algebra-r1, FN_CERT_CACHE
/tank/fn/certcache), and outcome-class-tests, native-control-tests,
topic-history-local-control-tests and native-operator-tests were `ld`'d in
it with no error before r2. native-operator went from 5.5 s (operator-walk)
to 7.70 s at two jobs on persvati: under the 10 s rule, and worth watching.

## Native (hbox, /tank/fn/scratch/outcome-algebra/, never /tank/fn/node)

Images at cd64c1ea (the book and host changes; the later commits change
tests, docs and registry only, plus the fixed test module shipped into the
tree): fn-host b7e04b95..., fn-host.core 9a5d8df7..., fn-host-developer.core
124ef006..., fn-host-dtn.core a581b31b... (full sums in each run's SHA256SUMS).

| run | module | result | log SHA-256 (prefix) |
| --- | --- | --- | --- |
| native-r1 (tools/hbox_native.sh) | test_native_outcome_algebra | import error (the module imported its sibling by bare name; harness, fixed) | 5bfd6ff9 |
| native-r1 | test_bp_app_native, test_bp_node_native | OK | 3c9b9cb9, 13ee3bc9 |
| native-r1 | test_native_control | 13 of 14; `test_operator_post_is_injected_and_refuses_what_post_refuses` expects a supplied Path refused, which D32 (694935ab) accepts: a stale expectation on dev, not this lane's | 3549ae20 |
| native-r1 | test_native_operator_verbs | 5 errors reading books/native-operator.lisp as ASCII (dev's file carries a `§` at byte 104,747, not this lane's) and `test_help_names_init` (the mission help line dev added): environment/stale, not this lane's | 39572db2 |
| native-r2 (the r1 tree + the DTN production image) | test_native_outcome_algebra | OK 8 | 4dc9a0f5 |
| native-r2 | test_bp_contact_native, test_bp_contact_relay_native, test_bp_app_native, test_bp_node_native | OK | 93d42249, e94487e0, 056cd7d9, 81213534 |
| native-r2 | the operator walk (planning/evidence/outcome-algebra-2026-09-26/walk.sh, the operator-walk script with NO-STORE expecting 1) | 44 steps ok, 0 DIFFERS; `refused operator status/health/run NO-STORE`, exit 1 | b27a194e (walk-summary.txt) |
| native-r3 (+ the DTN developer image) | test_native_outcome_algebra | OK 9 | see native-r3/SHA256SUMS |
| native-r3 | test_bp_service_native | OK 17 | ibid. |
| native-r3 | test_bp_receive_integrity_native | OK 4 | ibid. |
| native-r1, r2, r3 | test_bp_fragment_node_native | 6 of 7 OK; the 10 MiB case (SCN-077) times out at 120 s in `bp-node dispatch` (the recovered-held reopen) on this image, three times. Unclassified: the control, the same module against b6759850's developer image (native-r3/test-bp_fragment_node_b6759850.log, unit oa-native-r3), was still inside that case after 30 minutes at report time, under other lanes' load on the box; nothing this lane changed is on the dispatch path except the exit-code map at exit | 7ce98d4e, 2fd8d5a3 |

The per-class native cases (tests/test_native_outcome_algebra.py), each
against specs/host.md's table:
- operator: a second `init` refused 1; `init` with no group usage 5;
  `status` 0; `status` before init `refused operator status NO-STORE` with
  the `run: fn operator` line, 1; a frontier file that is not JSON, fault 4;
  the inherited lost durable outcome (developer `postpublish`), 3.
- store (developer image): `status` 0, `inspect` of an absent article 1, an
  unknown store command 5, a missing root 4, `post` with `postpublish` 3.
- control: `operator post` accepted 0, the resend `DUPLICATE` 0, the changed
  source under the held Message-ID `refused operator post CONFLICT`, 1.
- old client: b6759850's fn-host (the deployable candidate before
  `:conflict`) posting the changed source to this owner answers `uncertain
  operator post`, 3.
- bp: `bp send` to a port with no listener, 7; `bp decode` of that authored
  bundle without a clock: accepted 0 (its Bundle Age block decides the
  lifetime); `bp decode` of a hand-built bundle with a creation time and no
  Bundle Age block, without a clock: `BP decode outcome=uncertain
  reason=lifetime-uncertain`, exit 1 (was 3).

## Not done, and why (PKT-329)

- `operator CONFIG health` exits with its verdict (0, 19, 20..27; HST-007),
  outside the seven classes: the brief's "every native command exits one of
  seven codes" is not yet true for it. It is disjoint from 1..7 and named in
  the spec table as the one exception. Packet: keep the verdict scale and
  prove `fn-nh-exit-code` is 0 or at least 19 (default), or move health to
  0/1 with the state on the line (a monitor contract change for ember).
- The Python host (`tools/run_store.py` `exit_code_for`) and tools/fn_native.py
  keep their own tables; only tools/fn_client.py carries the scope field.
- `hybrid-author`'s CONFLICT is shown by ACL2 and the shared completion path,
  not natively (a native case needs an enrolled ML-DSA-65 key pair).
- books/outcome-class.lisp ends with no theory withdrawal (include-hygiene
  warn); host/native/io.lisp names ACL2 functions directly (host-names warn),
  which is how a handler must call them.
- The fragment timeout above, pending its control.
- No SCN id was assigned: HST-009 is linked to SCN-076 (the operator walk),
  whose NO-STORE expectation now reads exit 1.
