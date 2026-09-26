# operator-daily (wave 4, lane 5), 2026-09-26

Brief: build/coordinator/queue/done/w4-operator-daily.txt (mandate section
11: health that distinguishes the states). Base dev 7e62ed3e; branch
lane/operator-daily. Ids: PRF-172, HST-010, SCN-102, PKT-453, PKT-454.

## What an operator now reads

- `health` while a restarted owner recovers its store (the writer lock held,
  a control socket configured, nothing answering yet):
  `health exit=20 state=fenced reason=starting (a process holds the store
  lock and nothing answers on the control socket yet: an owner starting or
  recovering, or an offline command; retry)`. Before: `state=fenced` and a
  second line `reason=store-held`, the words of a stuck lock (PKT-283; the
  operator walk's item 4). `store-held` remains for a lock with no socket
  configured (no owner would ever answer) or a lock the probe could not read.
- After a SIGKILL, `control list` (and every offline `control`/`peer` verb)
  prints `stale control socket removed (...)` and answers offline; before,
  the mutating verbs were refused until the operator deleted the node by hand
  (PKT-344). With no socket node and a held lock the mutating verbs refuse
  `store-held` without starting the offline executor.
- The owner's log names the class of a control request it refused on a
  store, OS or socket error (`control request refused (store-error): ...`);
  before, those three were silent (PKT-264 (2), the logging part only).

## Theorems (PRF-172) and the host lines that call their subjects

- `fn-nh-exit-code-is-zero-or-past-the-outcome-codes` (books/native-health.lisp),
  no hypothesis: `(fn-nh-exit-code v)` is 0 or at least 19, and
  `(fn-outcome-codep code)` iff `code = (fn-outcome-code :accepted)`.
  `fn-outcome-codep` reads `*fn-outcome-codes*` (books/outcome-class.lisp), so
  an outcome code added at 19 or above breaks the proof: the tables cannot
  drift. Subject called: `fnn-operator-execute-health` returns
  `fn-native-health-host-exit` of the report, which equals `fn-nh-exit-code`
  of the verdict (`fn-nh-report-exit-of-render`). PKT-329 (1) retired.
- `fn-nh-exit-code-cases` exported (was local): at most eight outcomes, the
  code is in (0 19 20..27).
- `fn-nh-fence-of-starting-iff`: with no clone fence and a route that did not
  reach an owner, `fn-nh-fence-of` is `:starting` exactly when the lock is
  `:held` and an owner would listen; a free or absent lock is never fenced.
  Host: `fnn-operator-health-report` (host/native/operator.lisp) calls
  `fn-native-health-host-fenced` (host/native-live-status-host.lisp) with the
  fourth observation, `(and control-path (not (fnn-image-omits-p :control)) t)`.
  `fn-nh-fence-of-route` restated over the four observations.
- `fn-native-control-liveness-decides` (books/native-control.lisp): the offline
  executor starts (`fn-native-control-liveness-offlinep`) exactly when the lock
  was seen `:free` or `:absent`; the decision is `:stale` exactly when a socket
  node is present and the lock is free or absent; it is one of `:live :stale
  :offline :held`. Host: `fnn-operator-execute-admin` calls
  `fn-native-control-host-liveness` (host/native-control-host.lisp); `livep`
  is now `(eq liveness :live)`, not the file-type check. The host performs a
  `:stale` removal with `fnn-control-remove-stale-offline`
  (host/native/control.lisp) under the ACL2-derived control-path lease, as
  `fnn-control-listen` does, so an owner that starts meanwhile (it takes the
  lease before it binds) is never unlinked; the executor still takes the
  exclusive writer lock itself, so a race with a starting owner is refused by
  the lock.

Teeth: tests/acl2/native-health-tests.lisp (a positive `:starting` witness
whose rendered first line and exit 20 are asserted; must-fails without the
no-clone and the route hypotheses; the held/clear/unobserved witnesses 23, 0,
19 with `fn-outcome-codep` of each; `fn-nh-exit-code-cases` without the
length bound fails, `*nht-long*` exits 100); tests/acl2/native-control-tests.lisp
(one witness per arm; the pre-PKT-344 node-alone rule refuted on a stale
node; must-fails without the lock and without the node). Both books and
test books were loaded in persvati REPLs before the farm run.

## Assurance chain

native entry `fn operator CONFIG health` / `control VERB` -> host observations
(lstat of the socket node, `fnn-store-owner-observation`'s non-blocking
shared flock, the clone fence file, the configured path) -> ACL2 subject
(`fn-nh-fence-of`, `fn-native-control-liveness`) -> rendered words
(`fn-nh-fence-words`, `fn-native-control-liveness-note`) and exit
(`fn-nh-exit-code`, `fn-native-control-status-exit-code`) -> keystones above ->
native cases (SCN-102). No state is carried between invocations: each verb
takes its observations once, so there is no maintained relation to preserve.

## Decision (PKT-454)

`starting` is a reason of the fenced state (exit 20), not a ninth state with
its own code. Trace: the verdict's eight states and codes 20..27 are
monitored (HST-007) and the fenced state is exactly "the store cannot be
served now"; a ninth code would change the scale monitors read. Default
taken: exit 20, first line `state=fenced reason=starting`. Rejected
alternative: a state `starting` at index 0 (every other code shifts by one)
or at 28 (out of priority order: a starting owner would rank below
receipt-debt); cost: a monitor contract change. What continues without it:
everything; the words are ACL2's either way.

## Certification

- r1: persvati run-20260926T105331Z-c89c (`--affected-by` native-health,
  native-control, native-live-status, native-operator, outcome-class): 18
  books certified, 269 from the cache, none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T105358Z-645186.json.
- r2: persvati run-20260926T105609Z-b19e after 9f760025 (native-operator's
  comment, native-health, native-control): 8 certified, 206 from the cache,
  none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T105642Z-673835.json.
- r3: persvati run-20260926T110333Z-bd99, the regenerated
  tests/acl2/docs-operator-grammar-tests.lisp (docs/operator.md's line numbers
  moved): 1 certified, none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T110357Z-754509.json.

## Native (hbox, tools/hbox_native.sh, images developer and production)

n3 at 8a8c4bff (the final host code), hbox:/tank/fn/scratch/operator-daily/native-n3;
fn-host 2e83f3bd61f05a70419c3ebd4c337cd40c08b1735c6d20a9f360eacae160e392,
fn-host-developer d3d21e7339de0a290b7ab867e6a8fb474515be4e545dfbe6d86a815581e91f7b
(planning/evidence/operator-daily/SHA256SUMS-n3). n2 at 9f760025 (SHA256SUMS-n2)
ran test_native_operator_cli; 8a8c4bff changed only the DTN arm of
fnn-operator-execute-admin after it, which that module's cases do not reach
in these images.

| module | run | result | log (SHA-256) |
|---|---|---|---|
| tests.test_native_control (16 cases; both SCN-102 cases) | n3 | OK | operator-daily/native-control.log c047cb426ec360370dcf25f79654399f06fcd21b0f8eaf11263f089a95b7108f |
| tests.test_native_operator_verdicts (FN_NATIVE_HOST set; the one skip is the hybrid E2E's OpenSSL gate) | n3 | OK (skipped=1) | operator-daily/native-operator-verdicts.log 1d8921c262692a7956d0c77a45f2e50578e33d59c9189bb22d8c81f5632ef80d |
| tests.test_native_operator_cli | n2 | OK | 1e6a697f219e9d12fe77b5df1aa25e2de3e30e60392a40fe139f0d5e0db0340e (on hbox) |

The first run (n1, the dirty tree at 2da298d9) found one failure outside
this lane's change: test_native_operator_cli read books/native-operator.lisp
as ASCII and a section sign in a comment (85f35331) raised
UnicodeDecodeError. Classification: implementation (a non-ASCII byte in a
book). Repaired in 9f760025; green in n2.

## Not done (PKT-453)

- PKT-264 (2) and PKT-209, the reason on the wire: the FNCT reply is one enum
  and the injection reasons are open-ended (fn-inj-proto-reason passes the
  article parser's error words), so appending an enum value per reason does
  not close. Owed: a refusal reply carrying ACL2's reason word as a bounded
  field after the status, used by the operator post
  (fnn-owner-control-submit-serialized, fn-native-control-refusal-status) and
  the live reconfiguration (fnn-owner-live-admin-serialized returns bare
  :refused while fn-cfg-delta-reason has the word), with the theorem that the
  printed word is the decision's reason; `control evidence`, `control log`;
  the carrier-render theorem. Done: the owner's log names the class of the
  three refusals control.lisp swallowed.
- PKT-264 (1) `bp-node health`; PKT-220 live `bp-obligation status` and `store
  retention` (no control request kind was taken); PKT-098 alerts and
  `--explain`; PKT-016 `[acl2] heap_mb`; PKT-286 the walk as tests.
- PKT-269: the report functions stay `:verify-guards nil`, and so does the
  chain beneath them (books/store-budget.lisp fn-sbud-bytes-used,
  fn-sbud-headroom-at, fn-sbud-bytes-extend), which must be verified first.
- The seconds since the lock was taken: flock does not touch the lock file,
  so its mtime is not an observation of the holder.
- Include hygiene: native-health now includes outcome-class, which ends with
  no theory withdrawal (warn; PKT-329 item 4).

## Continuation (operator-daily-2, 2026-09-26)

Brief: build/coordinator/queue/done/w4-operator-daily-2.txt. Base dev
5c6825b2; branch lane/operator-daily-2. Ids: PRF-172, HST-010, SCN-102
(extended), PKT-453 (retired into PKT-472), PKT-472.

### What an operator now reads

- `operator CONFIG post` refused by the running owner prints ACL2's reason
  word after the status: `refused operator post REFUSED unknown-group`,
  `refused operator post REFUSED from-invalid`; before, every such line read
  `refused operator post REFUSED` and the reason was only in the owner's
  log. A named status keeps its word (`ARTICLE-EXCEEDS-PROFILE-BOUND
  oversize`). Exit codes unchanged (1).
- A live administrative verb refused by the owner does too: `control revoke`
  of a grant that is not there prints `refused operator control REFUSED
  no-such-grant` (fn-cfg-delta-reason's word, through the owner's staging
  step); a plan the owner refuses prints the plan's reason.
- `health` during an owner's start: unchanged words (`state=fenced
  reason=starting`, exit 20, PKT-454 decided), now with the theorem that it
  clears on the listening observation.

### Theorems and the host lines that call their subjects

- `fn-nh-starting-clears-on-listening` (books/native-health.lisp; PKT-454).
  Subject `fn-nh-health-step (socket-present outcome lock clone listener)`,
  the whole decision of one `health` invocation: (:answered OCTETS),
  (:refused), (:fenced REASON) or (:offline). Statement: the step is
  (:fenced :starting) iff no clone fence, lock :held, listener expected and
  `(fn-nls-route socket-present outcome)` is :offline; and with the socket
  present, (:done OCTETS) for the same lock, fence and listener is
  (:answered OCTETS), no fence. Host: `fnn-operator-health-report`
  (host/native/operator.lisp) now takes every observation first and calls
  `fn-native-health-host-step` (host/native-live-status-host.lisp); the host
  no longer branches on the owner's answer (the old `(if (:done ...))` and
  the route/fence calls are gone).
- `fn-native-control-printed-reason-is-the-decisions`
  (books/native-control-reason.lisp; PKT-453 (a)). For every status of
  `*fn-nctrl-statuses*`: the client's step on the reasoned reply the owner
  sealed, `(fn-native-control-reasoned-client-step
  (fn-native-control-reasoned-reply-read
  (fn-native-control-reasoned-reply-encode STATUS REASON)))`, is `(:status
  STATUS (fn-nctrl-reason-word REASON))`; and when STATUS classes :refused
  and REASON is non-nil, `fn-native-control-reply-detail` of it is
  `(fn-nctrl-reason-word REASON)`. Supporting: `fn-nctrl-reasoned-read-of-encode`
  (the round trip through the seal, `fn-nctrl-open-of-seal`),
  `fn-nctrl-reason-word-of-a-reason-is-not-none` (the no-reason word `NONE`
  is upper case, which no rendered symbol is), `fn-nctrl-reason-word-is-a-field`.
  Host: the owner seals it in `fnn-control-reply-octets` (the
  `:reasoned-reply` arm, `fn-native-control-host-reasoned-reply-encode`)
  for a frame `fn-native-control-reasoned-framep` names, with the reason
  `fnn-owner-control-submit-serialized` (host/native/owner.lisp;
  `fn-owner-operator-refusal-reason`) or `fnn-owner-live-admin-serialized`
  (host/native/admin.lisp; `fnn-admin-plan-reason`, or
  `fn-owner-reconfigure-reason` through `fnn-owner-live-reconfigure-locked`'s
  second value) answered as `(:reason STATUS REASON)`; the client is
  `fnn-control-reasoned-exchange` (host/native/control.lisp) and the line
  `fnn-operator-status-detail` (host/native/operator.lisp) from
  `fnn-operator-execute-post` and `fnn-operator-execute-admin`.

### The wire (the field's shape, and why it is not an appended field)

The brief asked for a reason field appended to the FNCT reply "so an old
client still parses the status". It cannot be: `fn-frame-fields-parse`
refuses a trailing octet (books/frame-fields.lisp: "a record payload is
exactly its fields"), and a client reads to EOF, so any octet after the
kind-2 frame, in its payload or as a second frame, makes an old decoder
answer :bad, which its client reports uncertain (exit 3). The reason
therefore goes only to a client that asks: request kinds 13 (a post) and 17
(an administrative vector) carry kinds 1 and 3's payloads unchanged, and the
owner answers them, and only them, with reply kind 18: `(:enum
*fn-nctrl-statuses*)` then `(:blob . 512)` the reason word. Kind 2 is
untouched: an old client's plain request reads what it always read (native
case `test_an_old_clients_plain_request_gets_the_plain_reply`, and the
executed witness that the plain decoder refuses kind 13 as :frame). A new
client that meets an old owner gets that owner's `:refused` to a frame it
could not decode (it acted on nothing) and resends the plain request once
(`fn-native-control-reasoned-client-step` :resend). control-reply-fit
(4f5167d3 and its uncommitted tree) changes FNLS in native-live-status.lisp
and none of the FNCT encoders; the LANEDUMP records the agreement. FNCT kinds
now: 1-3 native-control, 4-8 hybrid, 9-12 and 14 peer-invite, 13 17 18 this
lane; 15 and 16 were not taken (PKT-220 below).

### PKT-220 (not taken; findings)

- `store ROOT retention`: its figures (`pins=N reserved=R`, the store node's
  `fn-retain-pins` length and `fn-retain-reserved`) are already answered live
  by `operator CONFIG pins` and `operator CONFIG obligations` (FNLS kinds 2
  and 4, `fn-nls-report` over the owner's store node). The `store` verb takes
  a store root, not a configuration, so it has no control path to route by;
  owed is either its refusal naming `operator CONFIG obligations`, or the
  theorem that `fn-nls-report :obligations`'s two figures equal the offline
  `fn-store-sn-pin-count`/`fn-store-sn-reserved` on the same store node.
- `bp-obligation status`: the running NNTP owner does not carry the FNWF
  workflow state (`fn-workflow-state` is set only under
  `fnn-bpo-call-with-owner-journal`, which installs its own owner and takes
  the exclusive lock). A live answer needs the owner to open the workflow
  journal: a design decision, not a routing change.

### Teeth

tests/acl2/native-health-tests.lisp (PKT-454): the positive (:fenced
:starting) witness with every antecedent asserted (route :offline of a
present socket and a :before-submission connect; also no socket node at
all), the answered witness for the same lock, fence and listener; one
witness per iff conjunct failed alone (clone fence, free lock, no listener,
an uncertain route, a refused route); must-fails without the
socket-present hypothesis and without the route conjunct.
tests/acl2/native-control-reason-tests.lisp (PKT-453 (a)): the word of
:unknown-group and :no-such-grant, NONE for nil, `unnamed` for a non-word,
:none's word is not NONE; the positive round trip for :refused
:unknown-group (membership, class and reason asserted) and for
:article-exceeds-profile-bound :oversize; per hypothesis a witness and a
must-fail (membership: :bad and the :transport step; refusal class: an
acceptance prints nothing; a reason: NONE prints nothing); compatibility
witnesses: the plain decoder refuses kind 13 as :frame, the reasoned
decoders equal the plain ones on the same payload, framep of each kind, a
plain kind-2 :refused reads :legacy and steps :resend, a plain :accepted
reports no reason, and the old decoder answers :bad to kind 18. Both books
were loaded form by form in persvati REPLs before the farm.

### Certification

- r1: persvati run-20260926T124231Z-f25a (`--affected-by` native-health,
  native-control, native-control-reason, native-live-status, native-operator,
  and the test books native-control-host-tests, accounts-wire-tests,
  native-control-reason-tests): 26 certified, 202 from the cache, none over
  10 s; manifest planning/evidence/manifests/certify-20260926T124258Z-1868925.json.
- r2: persvati run-20260926T124704Z-3530, the regenerated
  docs-operator-grammar-tests: 1 certified, none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T124728Z-1913800.json.
- 45a6b818 after r1 changed only host/native/control.lisp (raw Lisp, not a
  book).

### Native (hbox, tools/hbox_native.sh, n2 at 45a6b818)

hbox:/tank/fn/scratch/operator-daily-2/native-n2; fn-host
96063a4dacd4e3c25b64ce494744dc0784d0c2a0b225d3c947e6e61856f7d5d4,
fn-host-developer 2bfc750dd29a3e0b1ef075a76153f23c51e2d2a778f9d4a0dd4330413da48b57
(planning/evidence/operator-daily-2/SHA256SUMS-n2; FN_NATIVE_HOST = the
production launcher).

| module | result | log (SHA-256) |
|---|---|---|
| tests.test_native_control (18 cases; the two new SCN-102 cases ok) | FAILED (failures=1, not this lane's: below) | operator-daily-2/native-control.log f2a5e741cc6a2ab7e4c73f22c20234b980f4c1dd548845605963853e20aebd0d |
| tests.test_native_operator_verdicts | OK (skipped=1, the hybrid E2E OpenSSL gate) | operator-daily-2/native-operator_verdicts.log 62b331ad71db5c08583d097427d32cae3b9d91c1d4e923f6369633727cd815aa |
| tests.test_native_operator_cli | OK | operator-daily-2/native-operator_cli.log 7815be36685f67819f5436ce2a3af858679db2c7feda615f5dcf7b0c238d8cd1 |

The one failure: `test_operator_post_is_injected_and_refuses_what_post_refuses`
line 654 asserts `inspect(path_id)` exits 0 after the same test asserted
that `path_id` (`Path: not a path`) is refused (exit 1) and absent from the
store (the loop above it). The two expectations contradict each other on
dev 5c6825b2 as well; this lane changed neither the case nor the injection
decision, and the refusal the case expects is the one observed (exit 1).
Classification: harness (a stale block, probably meant for `supplied_id`,
from qual-harness-c18's C4 refresh). Not repaired here: changing an expected
answer is not this lane's to do; it is in PKT-472's scope note for the
coordinator.

n1 (39f7c8cf) ran with FN_NATIVE_HOST set to the developer launcher, which
made test_native_control's production-only selector case run the developer
image (each selector starts an owner that never exits: timeouts). Harness
mistake (mine), stopped by PID and rerun as n2; its other results matched
n2's except `test_the_reply_is_the_owners_status`, a static source check of
fnn-control-handle-client's send form, repaired in 45a6b818 by keeping
`(fnn-control-send-reply socket status)` and rebinding status before it.

### Assurance chain

native entry `fn operator CONFIG post` / live `control VERB` -> the client
seals kind 13/17 (`fn-native-control-reasoned-request-encode`/`-admin-encode`)
-> the owner decides (`fn-own-operator-decision-of` via
`fn-owner-operator-refusal-reason`; `fn-native-admin-plan`, or
`fn-ocfg-reconfig-refusal`/`fn-cfg-delta-reason` via the staging slot) ->
the owner seals kind 18 with that reason (`fn-native-control-reasoned-reply-encode`)
-> the client reads and steps (`fn-native-control-reasoned-reply-read`,
`-client-step`) -> the printed detail (`fn-native-control-reply-detail`) ->
keystone `fn-native-control-printed-reason-is-the-decisions` -> SCN-102's
native lines. `health`: host observations -> `fn-nh-health-step` ->
`fn-nh-starting-clears-on-listening`. No state is carried between
invocations, so no maintained relation.

### Not done: PKT-472

(a) PKT-209 `control evidence`, `control log`, the carrier-render theorem;
(b) PKT-220 (findings above; kinds 15 and 16 not taken); (c) `bp-node
health`, alerts and `health --explain`, `[acl2] heap_mb`, the walk as tests;
(d) PKT-269, the lock age, include hygiene (carried from PKT-453); (e) the
owner's host-classified refusals (store, OS, socket errors) answer a
reasoned frame with NONE: no ACL2 decision names them.
