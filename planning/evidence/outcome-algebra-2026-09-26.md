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
