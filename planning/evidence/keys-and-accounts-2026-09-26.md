# keys-and-accounts, 2026-09-26: the operator re-decides a key statement

Lane keys-and-accounts (Opus 5.5), wave 4 lane 6 (planning/backlog-triage-2026-09-26.md),
from dev eb79070b. Ids: PRF-166, SEC-005, SCN-096, PKT-433. PKT-434 was not needed (below).

## What a friend can now do

A friend's key succession (or revocation) that arrived before its `keys` grant declined, and
stayed declined across restarts (PRF-124). Now the operator grants and runs

    fn operator CONFIG keys redecide <msgid>

against the running node; the successor is enrolled at once, with no restart and no new
statement from the friend. A second redecide of the same statement, or one naming a Message-ID
that is no stored key statement, is refused by name and changes nothing; offline the verb is
refused (it needs the owner). `tools/fn_verify.py` now renders the node's `revoked HEX keyring G`
verdict (PKT-212's verifier half).

## The record shape (PKT-325's open question): no new record, no re-filed composite

The redecide's one durable record is the kind-3 key change itself, committed at the redecide's
own Store coordinates (fn-hl-enroll-event / fn-hl-revoke-event at fn-hl-next-generation). The
statement is not re-filed (its kind-4 composite, with its Message-ID, is already stored: a
re-filed composite would be a second record for one Message-ID) and no redecide record kind is
added. Consequences: there is no cut (the change is durable or it never happened); the next
open's recorded recovery sees a newest record that is no statement (fn-ks-a-key-change-is-no-
pending-statement) and repeats nothing, so PRF-124 and PRF-140 carry over unchanged
(fn-ks-reopen-after-a-redecide). A redecide that declines again files nothing (the review: no new
decline record). The Store format is unchanged, so no PKT-434 packet for ember.

Rejected alternative: a re-filed kind-4 composite at the redecide's txid followed by the kind-3
change. It would make the reopen reproduce the redecide via fn-ks-recover-recorded, but it adds
a cut, a duplicate Message-ID record (a Store identity question), and a D27 charge, to buy
nothing the atomic kind-3 commit does not already give.

"Already acted" is decided in ACL2 from the keyring alone: fn-ks-acted-p holds when a kind-3
snapshot after the statement's verdict generation is the statement's change (the principal
revoked, or enrolled under exactly the statement's new keys). A statement merely superseded by
another declines `not-current` through fn-ks-plan.

## PRF-166 (books/key-statements.lisp, section "PKT-325, PRF-166")

Subject: fn-ks-redecide (model transition over (RECORDS . SNAPSHOTS)), fn-ks-redecide-plan and
fn-ks-redecide-event. Host: host/native/keys.lisp `fnn-keys-owner-redecide` (under
fnn-owner-serialized, control request 12) calls host/owner-host.lisp
`fn-owner-key-statement-redecide-find` (fn-ks-find-statement over fn-sf-records of the owner's
Store), `fn-owner-key-statement-request` (fn-ks-pop-request, the one primitive observation),
`fn-owner-key-statement-redecide-plan` / `-event` (over fn-sn-keyring-snapshots and the live rows
`fn-owner-key-statement-rows event nil`) and `-log-line` (fn-ks-redecide-log-line).

1. `fn-ks-redecide-decides-under-the-configuration-at-its-own-txid`: journal CONFIGS all at or
   before TXID and replaying => the redecide under the replay's authorities (the live rows) equals
   the redecide under `fn-ks-redecide-rows TXID CONFIGS` (fn-ctl-config-at the redecide's txid).
2. `fn-ks-reopen-after-a-redecide` (no hypotheses): fn-ks-recover-recorded of the redecided state,
   any journal, any coordinates = the redecided state if it committed a change, else the recovery
   of the unchanged state. fn-ks-reopen-is-blind-to-later-configuration (PRF-124) is cited, not
   restated: the statement event's shape did not change.
3. `fn-ks-redecide-of-no-stored-statement-is-refused-by-name`,
   `fn-ks-redecide-of-an-acted-statement-is-refused-by-name`: (:refused :not-a-key-statement) /
   (:refused :already-acted), state unchanged. The second's "MSGID names a statement" hypothesis
   was dropped after proving the weakened theorem (fn-ks-acted-p-needs-a-statement).
4. `fn-ks-redecide-of-an-unacted-statement-is-its-acceptance-decision`: the plan and event are
   fn-ks-plan / fn-ks-execute of the stored statement, so PRF-098's keystones apply to it.
5. `fn-ks-a-redecide-that-acted-is-refused-the-second-time`: after an acting redecide, with the
   statement's generation below the keyring's next, the same MSGID is refused :already-acted.

Teeth (tests/acl2/key-statements-tests.lisp, "PRF-166"): the declined state of the PRF-124
fixture, the grant published after the statement's txid, the redecide at txid+2. Positive
witnesses assert every antecedent literal and the conclusion (the redecide acts: `key-statement
redecide enrol-successor committed`); must-fails: (1) the redecide decided at the statement's own
txid (not all-through), a grant whose generation does not follow (replay faults); (2) both arms
reached; (3) the real MSGID is found and acts, the not-yet-acted plan is not the refusal, a
redecide that did not act is decided again; (5) CORRUPTED STATE: a keyring whose newest snapshot
is older than the statement's generation -- the redecide acts at generation 2, not after 4, and
the second is `declined not-current`, not refused; (4) the absent statement, the acted statement.
Also tests/acl2/native-operator-tests.lisp (the grammar: accepted plan, action :keys, the
Message-ID octets; usage for a bare word, a missing Message-ID, another verb) and
tests/acl2/peer-invite-tests.lisp (request 12 round trip; not an issue request; :bad bounds).

Not covered by a theorem: that the owner's live configuration is the replay of
fn-sn-config-history is the owner's maintained relation, established at open and preserved by
fn-ocl-publish (fn-ocl-no-reader-observes-a-half-change, PRF-028, which planning/current.md lists
as uncertified-at-current-digest: cited, not claimed); the host-to-model link of
fnn-keys-owner-redecide is by construction, as PRF-098.

## PKT-240: the transit refusal class through the seven-class verdict

`fn-pcb-admission-verdict` had no host caller. books/peer-carriage.lisp now has
`fn-pcb-verdict-refusal-class` (the verdict's four refusal names mapped to the class words:
:malformed, :cryptographically-invalid -> :signature-failed, :unenrolled -> :no-local-binding,
:unsupported-profile) and the keystone `fn-pcb-admission-verdict-refusal-arms-are-the-refusal-class`
(no hypotheses): that map of the verdict equals `fn-pcb-refusal-class` on every input. The two
agree, so there is no finding to record and no reach_check baseline entry. host/owner-host.lisp
`fn-owner-transit-refusal-class` (called by host/native/owner.lisp `fnn-owner-transit-class`
inside `fnn-owner-attempt-transit`) computes the class through the verdict, so the verdict is on
the served path and the reply and log words are unchanged. Witnesses: all seven verdicts reached
in tests/acl2/peer-carriage-tests.lisp, and the equality on three of them. The log still prints
the four class words, not the seven verdict names (PKT-433 (d)).

## Assurance chain

native entry (`fn operator CONFIG keys redecide MSGID`, host/native/operator.lisp
fnn-operator-dispatch-plan :keys -> host/native/keys.lisp fnn-keys-execute -> control request 12)
-> owner fnn-keys-control-handle -> fnn-keys-owner-redecide under the owner mutex -> ACL2
fn-ks-find-statement / fn-ks-redecide-plan / fn-ks-redecide-event over the decoded Store records,
keyring snapshots and live rows -> model fn-ks-redecide (by construction) -> relation: live rows
= grants at the redecide's txid (PRF-028's publish relation, uncertified) -> behavioural theorems
PRF-166 1-5, PRF-124/PRF-140 carried -> observed: SCN-096 below.

## Native (hbox /tank/fn/scratch/keys-and-accounts/)

native-n1 (e10e0c99, developer image under swarm-build, module under systemd-run MemoryMax=24G):
`test_redecide_a_declined_statement_after_its_grant` OK. Witness lines: POST without a grant
`240`; log `key-statement declined no-grant`, `key-statement redecide enrol-successor committed`,
`key-statement redecide refused already-acted`, `key-statement redecide refused
not-a-key-statement`; history generation 2 active, 1 retired; offline redecide exit 1 `refused
operator keys`; restart: no new line, history unchanged.

```
7d00891599f18b3021a8ca780621052d8956d8ac74856305661680d17674ed44  logs/test-...test_redecide_a_declined_statement_after_its_grant.log
26c176d2d232be2c2c4e14bc214d8011e41efff87a10e4de9611ba3fdf8e00f7  tree/build/fn-host-developer
ede9b4c10f44026914747e5d7872778fc9501e007eeebcd8d63bab6b5b88cdd5  tree/build/fn-host-developer.core
```

The whole module at the same image (`--no-build`): `tests.test_native_key_statements` 5 OK (the
four existing cases unchanged), log edf5a1e3fa7369b34c9e9d3be004839b495c792ae1b93dbd61f021aa7a614900.

native-n2 (6f426a66, with PKT-240's host change): `tests.test_native_key_statements` 5 OK
(7ab7333629308b7e0301aadf7764a73e3ddd36db0f41740153d4210cd283dc81); image fn-host-developer
7aee2be4d33bb6a14c808dd269fbac595f619d2ab5d461b1d89467938b30f926. The refusal-class case
`test_native_hybrid_author ... test_carried_budget_and_refusal_classes` is gated on
FN_RUN_HYBRID_E2E=1 (hbox_native.sh skipped it), so it ran by hand in the n2 tree under
`systemd-run --user --scope -p MemoryMax=24G` with FN_RUN_HYBRID_E2E=1 and
FN_TEST_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl: OK, the class words (through the
verdict now) unchanged; logs/hybrid-author-e2e.log
87e87f7cec21f7ea75d28a5f07bd0a5f1bb551bd489790110defc9e3b38aca2b.

fn_verify (hbox /tank/fn/scratch/keys-and-accounts/verify-t1, the cryptography and dilithium_py
modules are on hbox, not the laptop): `tests.test_fn_verify.FakeNodeVerifyTests` 18 OK, including
`test_a_revoked_verdict_is_rendered_and_never_verified` (revoked + the revoked principal's
signature: exit 1; revoked + another principal's signature: exit 2; `revoked legacy` undecided).
verify-t1.log af454b03e35cab5d83df721db3f853bfbf4780f1826f8735abcf300a3eefd037.

## Certification

Every changed form ran first in the REPL on persvati (/home/ember/fn-gates/keys-and-accounts-repl:
key-statements 99 forms and its test book's 175 forms with the must-fails checked to fail for the
stated reason; native-operator 184 forms and its test book; peer-invite with the request-12 round
trip; peer-carriage 67 forms and its test book).

- r1: persvati run-20260926T100602Z-3152 (`--affected-by books/key-statements.lisp
  books/native-operator.lisp books/peer-invite.lisp tests/acl2/docs-operator-grammar-tests.lisp`,
  2 jobs, 300 s, w25 toolchain), at cd282ce8's books: passed 11, failed 0, 152 from the cache;
  manifest planning/evidence/manifests/certify-20260926T100646Z-90653.json. key-statements 4.5 s,
  key-statements-tests 1.6 s, native-operator 9.4 s, native-operator-tests 3.7 s, peer-invite 2.7 s,
  peer-invite-tests 3.9 s, docs-operator-grammar-tests 2.3 s, native-mission(-tests),
  native-operator-host(-tests). None over 10 s.
- r2: persvati run-20260926T100847Z-9938 (`--affected-by books/peer-carriage.lisp`) at 6f426a66:
  peer-carriage 5.1 s, peer-carriage-tests 1.7 s, passed 2; manifest
  planning/evidence/manifests/certify-20260926T100935Z-127907.json.
- `make check-lane` green (ledger.* and current.md regenerated in the temp dir only).

## Not done (PKT-433)

- PKT-221, the live login binding (step 2 of the brief): not started. It moves the binding table
  from the credential file (read once at startup, host/native/auth.lisp fnn-native-auth-install)
  into a configuration slot published through fnn-owner-live-reconfigure-locked / fn-ocl-publish,
  with a per-connection pinned binding; it touches books/config* and books/owner (large dependent
  closures) and shares its table with friends-peer-2's PKT-401 accounts. Sized for its own lane.
- PKT-211 (succession-era invitations, `peer list` budget, native signature-failed row), PKT-212's
  served half (the POST reply and served-post log naming a refused key change beside a durable
  composite; the transit log already prints `detail=key-change-refused` with the accepted class),
  PKT-240 (the seven-class verdict in the transit log): not started.

## Continuation: keys-and-accounts-2 (PKT-221, the live login binding)

Lane keys-and-accounts-2 (Opus 5.5), from dev fac2c417. Ids taken: PRF-175 (new target), SEC-005,
SCN-096, PKT-433 (narrowed), PKT-463.

### What a friend can now do

The operator re-binds a login's signing principal on a running node and it applies at once:
`fn operator CONFIG principal bind LOGIN HEX` (or `unbind LOGIN`) rewrites the credential file and
then asks the owner (control request 14) to publish the file's bindings; the verb answers
`accepted operator principal bind applied`. A session already authenticated keeps the binding in
force when its connection opened; the next connection is decided under the new one. No restart.

### Design

A redeemed account row is (DIGEST LOGIN VERIFIER 1) and carries no principal (the brief assumed one),
so the binding is its own row kind in the same slot: mark-2 rows (LOGIN PRINCIPAL-HEX "" 2) of the
`accounts` slot, written only by the new delta kind `:login-binding` (books/config.lisp, code 17),
which replaces that login's binding rows (by login octets) and leaves the account rows (marks 0/1)
in place and in order. One credential table, three row kinds; no binding global (the host's
`fn-owner-login-bindings` is deleted). The credential file stays the operator's statement: the owner
publishes its `signing` fields at start (host/native/auth.lisp fnn-native-auth-install, under the
owner mutex, through fnn-owner-live-reconfigure-locked) and on request 14
(host/native/login-bindings.lisp), with ACL2's plan fn-lb-sync-plan: one delta per login whose
binding differs, in records of at most 64 deltas (no ceiling on the table: records compose,
fn-lb-pairs-deltas-ignore-the-record-coordinates). PRF-164's statements are unchanged; only
fn-acct-accounts-of-apply-delta-unfolds (a third writer) and one hint in books/accounts.lisp moved.

Format consequence (joins PKT-440, for ember): an image older than this one refuses a store whose
configuration log holds code 17; a store whose file binds no login and was never re-bound writes no
code-17 record (the start plan is empty when the configuration already agrees).

### PRF-175 (books/login-binding-live.lisp)

Host lines: host/owner-host.lisp fn-owner-login-gate calls fn-lb-ocfg-gate (called by
host/native/owner.lisp fnn-owner-attempt-served); host/native-auth-host.lisp
fn-native-auth-host-bindings-plan calls fn-lb-sync-plan (from fnn-native-auth-publish-bindings);
records staged by fn-owner-reconfigure-deltas and published by fn-owner-reconfigure-complete
(fn-ocl-publish).

- fn-lb-binding-delta-binds-the-login / -keeps-other-logins / -is-admitted (the delta).
- fn-lb-sync-binds-every-login-as-the-file-does (the start and reload plan), with the fold
  fn-lb-pairs-deltas-set-exactly-their-logins.
- fn-lb-a-publication-keeps-every-open-connections-table (no hypotheses, over reconfigure then
  fn-ocl-publish); fn-lb-an-open-session-is-decided-under-its-pinned-table (any owner trace that does
  not re-pin the connection: the gate decides under the pinned table).
- fn-lb-a-connection-opened-after-a-publication-is-bound-anew (nothing staged; durable; the history
  relation before, fn-ocl-config-historyp; fn-ocfg-statep after; the open admitted).
- fn-native-auth-admin-effect-word-applied-only-when-published; PRF-095's
  fn-native-auth-admin-effect-word-restart-unless-no-owner restated with the owner's answer (PRF-095's
  statement text updated to match).

The posting policy is still read from the LIVE configuration (behaviour unchanged); only the table is
pinned. PRF-028 (fn-ocl-no-reader-observes-a-half-change) is listed uncertified at the current digest
in planning/current.md: cited, not claimed; the keystones above use fn-ocl-publish-leaves-connections-
and-pins and fn-ocl-publish-installs-the-whole-staged-record instead.

Teeth: tests/acl2/login-binding-live-tests.lisp (witness per keystone with every antecedent asserted;
one must-fail per hypothesis; the gate witness is login-binding-tests' CONSTRUCTED owner (a
submission in flight on connection 5), evaluated with guard checking off; the publication witness is
config-owner-live-tests' replayed ground owner through reconfigure and fn-ocl-publish);
tests/acl2/native-auth-admin-tests.lisp (effect word); tests/acl2/peer-invite-tests.lisp (request 14).

### Assurance chain

native entry (`operator CONFIG principal bind`, host/native/auth-admin.lisp after the durable file
write -> request 14 -> host/native/login-bindings.lisp under the owner mutex; and the start hook) ->
ACL2 fn-lb-sync-plan over the file's bindings and the live configuration value -> deltas staged
(fn-ocfg-reconfigure) and published (fn-ocl-publish) -> relation: live configuration = replay of the
history (maintained; PRF-028's, uncertified) and each open connection's pin = the configuration it
opened at (fn-ocfg-statep) -> PRF-175 -> observed: tests.test_native_auth (below).

### Certification

REPL first (persvati /home/ember/fn-gates/keys-and-accounts-2-repl, sessions over books/config and then
books/login-binding-live): config.lisp, config-invariants.lisp and accounts.lisp over the new config;
every form of login-binding-live.lisp (75) and its test book's forms (98, the must-fails checked to
fail) before r3.

- r1: persvati run-20260926T115148Z-e9c3 (`--affected-by` config.lisp, login-binding.lisp,
  peer-invite.lisp, native-auth-admin.lisp, login-binding-live.lisp, native-operator.lisp: config.lisp's
  closure, most of the tree), at ddc05fe2: passed 398, failed 4 (login-binding-live's last keystone hit
  the preprocessor's call depth; host/native-auth-host could not see the owner; the two books that
  include them). Manifest planning/evidence/manifests/certify-20260926T115220Z-1347243.json. Every
  other book of the closure passed, config.lisp, accounts.lisp, config-invariants.lisp,
  native-auth-admin(-tests), peer-invite(-tests), native-operator(-tests) included; over 10 s only
  books/owner-invariants 10.3 s (unchanged bytes; on the PKT-371 list).
- r2: run-20260926T120439Z-88c8 certified nothing (explicit root combined with --affected-by
  selected no book): a harness misuse, not evidence.
- r3: persvati run-20260926T120522Z-4a12 at fabf99ea, roots books/login-binding-live,
  tests/acl2/login-binding-live-tests, tests/acl2/native-auth-host-tests,
  tests/acl2/docs-operator-grammar-tests: passed 5, failed 0, 177 from the cache. Manifest
  planning/evidence/manifests/certify-20260926T120553Z-1490002.json. OVER 10 s:
  tests/acl2/login-binding-live-tests 11.8 s at 2 jobs: one must-fail search took 8.8 s.
- r4: persvati run-20260926T121304Z-1f17 at b83ac6da (that search bounded; its counter-witness
  *lblt-wrong* unchanged): tests/acl2/login-binding-live-tests passed, no book over 10 s. Manifest
  planning/evidence/manifests/certify-20260926T121324Z-1564124.json.

### Native (hbox /tank/fn/scratch/keys-and-accounts-2/native-n1, fabf99ea)

Developer image built under swarm-build (certify, image-developer exit 0); modules under systemd-run
MemoryMax=24G with FN_NATIVE_HOST=$T/build/fn-host-developer and FN_TEST_OPENSSL=openssl 3.5.8 (the
first pass without FN_NATIVE_HOST skipped the whole module: a harness miss, rerun `--no-build`).

- tests.test_native_auth: 5 OK, including
  `test_a_rebinding_applies_live_and_an_open_session_keeps_its_binding`: witness
  `NATIVE-AUTH-REBIND-WITNESS 240 article received OK | 441 posting failed; the login is not bound to
  this signing principal`; the live bind printed `accepted operator principal bind applied`; the owner
  process was the same throughout; the log has `post login=native-reader bound=<P>` and
  `post login=native-reader refused login-not-bound`.
- regression: tests.test_native_key_statements 5 OK, tests.test_native_peer_invite 4 OK (request 12
  and the peering requests with request 14's handler in the chain; the start publication with no
  bindings is empty).

```
c9199034b5d6779f0ee6b92f68021834788d78ffd4ec324a747a1b660bf0c643  tree/build/fn-host-developer
a84b78fe9db7945c3ccf8e03e13bedb3207188668a33479e490b0b335a79ec13  tree/build/fn-host-developer.core
15cf5e9e8a9ccea547c6e6ad4c75844accb2324c0394e426c60cecaa50949243  logs/test-tests.test_native_auth.log
0c6b5eb04c9a21d39269a9b827b4e88750c36d10cc03930bde5598d85ae0b90a  logs/test-tests.test_native_key_statements.log
af12ec406f30f2d791c3e2d5c560f840356caba9c1c9b85f2ccc9772b3d9b323  logs/test-tests.test_native_peer_invite.log
```

Not run: tests.test_native_hybrid_author (untouched by this slice; its signature-failed row is
PKT-463), tests.test_native_visibility_join's restart-based rebinding case (still valid: the start
publication re-reads the file).

### Not done (PKT-463)

PKT-211 (succession-era invitations: fn-pinv-genesis-okp still refuses a principal whose current keys
are not its genesis keys; `peer list` does not render the carriage budget; no native signature-failed
row), PKT-433 (c) the POST reply naming a refused key change beside a durable composite, (d) the seven
verdict names in the transit log, fn_verify's `revoked` natively. Teeth gap: fn-lb-a-connection-opened-after-a-publication-is-bound-anew has a
must-fail for its durable hypothesis and witnesses for every antecedent, not a must-fail for each of
its seven hypotheses. Decision for ember (joins PKT-440): code 17 makes an older image refuse a store
that ever published a binding.

## Continuation 2: keys-and-accounts-3 (PKT-463)

Lane keys-and-accounts-3 (Opus 5.5), from dev 5c6825b2. Ids taken: PRF-179 (new target: the
succession-era documents are a subject of their own, books/peer-invite.lisp, not PRF-175's login
binding), SEC-005 (extended), SCN-096 (extended), PKT-463 (narrowed to PKT-473), PKT-473.
Deputy 3's sweep 14 added PKT-391 (done here) and asked about PKT-399 (below).

### What a friend can now do

- A friend whose keys have succeeded since genesis is peered under their current keys: when this
  node's keyring already holds the friend's principal, the friend's acceptance signed with the
  current keys is confirmed (consumption and peer record; nothing to enrol). A superseded key set is
  refused `not-current-keys`, a revoked principal `revoked`; a node that never enrolled the
  principal decides by the genesis identity as before (`genesis`).
- `peer list` ends each budgeted peer's line with `budget-octets=OCTETS budget-count=COUNT`.
- The transit log of a refused present carrier reads `detail=CLASS verdict=VERDICT`
  (`detail=signature-failed verdict=cryptographically-invalid`, `detail=no-local-binding
  verdict=unenrolled`, ...): the four class words stay where an older reader finds them.
- `account list` lists a login-binding row as `binding LOGIN HEX`, never `pending expires `
  (PKT-391).

### PRF-179 (books/peer-invite.lisp, "PRF-179 (PKT-211)")

Subject fn-pinv-document under the owner's keyring. Host lines: host/native/peer-invite.lisp
fnn-pinv-owner-issue (fn-pinv-host-issue-plan, now passed fn-owner-hybrid-snapshots),
fnn-pinv-owner-accept (fn-pinv-host-accept-record-plan, fn-pinv-host-accept-step),
fnn-pinv-owner-confirm (fn-pinv-host-confirm-record-plan) and fnn-pinv-owner-enrol-confirmed
(fn-pinv-host-confirm-step: `(:current)` is accepted with a log line).

1. fn-pinv-document-binds-a-known-principal-only-at-its-current-keys.
2. fn-pinv-document-of-a-current-enrolment-is-accepted (the genesis-keys enrolment is the instance).
3. fn-pinv-document-of-an-unknown-principal-is-the-genesis-decision (rule-classes nil; the rule
   before PKT-211).
4. fn-pinv-an-enrolling-accept-is-the-clis-plan (the CLI's fn-pinv-acceptance-source asks the plan
   under the empty keyring; equal whenever the owner enrolled).
5. fn-pinv-confirm-step-current-only-for-the-consuming-current-acceptor,
   fn-pinv-confirm-of-a-current-acceptor-completes-at-its-consumption.
6. books/native-admin-peer-budget.lisp (new; books/native-admin-peer.lisp unchanged):
   fn-native-admin-peer-budget-decode-reads-the-configured-budget,
   fn-native-admin-peer-extra-decode-reads-past-the-budget,
   fn-native-admin-peer-budget-row-octets-extends-the-older-line. Served by
   fn-native-admin-query-report (host fn-native-admin-host-query-report, host/native/admin.lisp) and
   fn-nls-report :peers.
7. fn-pcb-transit-refusal-detail-is-the-class-and-the-verdict (books/peer-carriage.lisp, no
   hypotheses): host/owner-host.lisp fn-owner-transit-refusal-class returns (CLASS VERDICT), called by
   host/native/owner.lisp fnn-owner-transit-class; books/owner-log.lisp fn-olog-detail-fields prints
   both (its theorem is a by-definition restatement, flagged SUSPECT by the ledger and not cited).
8. fn-acct-list-word-is-pending-only-for-a-pending-row (books/account-list.lisp, new, served by
   books/native-live-status.lisp for `account list`; books/accounts.lisp is unchanged because it is
   under books/owner's closure).

Teeth: tests/acl2/peer-invite-tests.lisp "PRF-179" (A's keyring: B at genesis keys, then B2 at
generation 2; every antecedent of 2 asserted, one must-fail per hypothesis: unverified, wrong kind,
body naming other keys, a 3-octet nonce, the keyring before the succession; for 1: an empty keyring,
the superseded keys; `revoked` by name; for 3 and 4: the equality and its failure when the principal
is known / has moved; for 5: the record plan configures, the step answers (:current), each
conclusion asserted, the genesis step enrols without "current", a superseded acceptance's step is its
refusal). tests/acl2/native-admin-peer-budget-tests.lisp (through the `peer add` and `peer budget`
plans; a 4294967295-page budget renders every digit; must-fails: no budget, a digit after the count, a
dirty group). tests/acl2/peer-carriage-tests.lisp (all four refusal pairs and nil on verified,
carried, unsigned), tests/acl2/owner-log-tests.lisp (the line), tests/acl2/account-list-tests.lisp
(the older report's defect reproduced, the new one's lines).

Assurance chain: native entry `operator CONFIG peer confirm` (control request 11) -> owner
fnn-pinv-owner-confirm -> ACL2 fn-pinv-confirm-record-plan / fn-pinv-confirm-step over the decoded
acceptance, the invitations slot and fn-sn-keyring-snapshots -> relation: the owner's keyring
snapshots are the Store's kind-3 records (fn-owner-hybrid-snapshots, maintained by the Store) ->
PRF-179 1-5 -> observed: SCN-096's new case below.

### PKT-399 (deputy's question)

Not in this lane's path. The redeem admission's USED count ((len creds)) and TAKENP are computed in
host/native-admin-host.lisp fn-acct-host-owner-redeem-stage (friends-accounts-2's XREDEEM); left for
control-reply-fit's sweep. fn-lb-sync-plan counts nothing. From the code: binding rows do NOT count
against max-credentials (fn-auth-account-creds takes only mark-1 rows; the credential file's own
table is loaded under the bound).

### Certification

REPL first on persvati (/home/ember/fn-gates/keys-and-accounts-3-repl): peer-invite 144 forms and its
test book 231; native-admin-peer-budget 43, native-admin's 69 over it, its test book 37;
peer-carriage 70 and the fixture chain (42, 86) and its test book 105; owner-log 73 and tests 114;
account-list 10 and tests 18; must-fails checked to fail.

- r1: persvati run-20260926T125449Z-5d0b (`--affected-by` peer-invite, native-admin-peer,
  key-statements, peer-carriage, native-admin-peer-budget, account-list, owner-log,
  native-live-status) at fb3a1e13: passed 28, failed 0, 200 from the cache, no book over 10 s
  (native-admin 9.9 s, native-operator 7.8 s, peer-invite-tests 4.4 s). Manifest
  planning/evidence/manifests/certify-20260926T125534Z-1995979.json.
- r2: persvati run-20260926T130249Z-3583 (`--affected-by` native-admin-peer-budget, account-list) at
  6567be5e: tests/acl2/native-admin-peer-budget-tests and tests/acl2/account-list-tests passed, 214
  from the cache, no book over 10 s. Manifest
  planning/evidence/manifests/certify-20260926T130312Z-2065168.json.
- r3: persvati run-20260926T130502Z-510f (tests/acl2/docs-operator-grammar-tests, regenerated for the
  docs/operator.md line shift) at d6721738: passed 1, no book over 10 s. Manifest
  planning/evidence/manifests/certify-20260926T130524Z-2084756.json.
- `make check-lane` green at the final commit.

### Native (hbox /tank/fn/scratch/keys-and-accounts-3/native-n1, fb3a1e13)

Developer image built under swarm-build; modules under systemd-run MemoryMax=24G with
FN_NATIVE_HOST, FN_OPENSSL / FN_TEST_OPENSSL (openssl 3.5.8) and FN_RUN_HYBRID_E2E=1.

- tests.test_native_peer_invite (rerun `--no-build` at 6567be5e after the case read the key history
  while the owner held the store: a test defect): 5 OK, including
  test_a_succeeded_friend_is_confirmed_under_its_current_keys: A confirm -> 0, a second confirm 1
  (already-confirmed), `peer list` ends `budget-octets=1048576 budget-count=16`, D's acceptance under
  B's genesis keys 1 (not-current-keys), C's 1 (genesis), A's history for B: generation 2 active,
  1 retired, no generation 3.
- tests.test_native_hybrid_author: test_carried_budget_and_refusal_classes OK with
  `NATIVE-REFUSAL-CLASS unsupported-profile unsupported-profile`, `no-local-binding unenrolled`,
  `signature-failed cryptographically-invalid` (the new signature-failed row: the relay enrols the
  author, one body letter's case flipped). test_portable_carrier_verifies_exact_source_and_keyset
  FAILED at line 369: `hybrid-sign-carrier` of a source 26,000 octets over the fixture EMITTED a
  carrier (exit 0) where the test expects the total-article bound to refuse. It is NOT the
  altered-key check (lines 354-358 pass). Classified a DEV defect: the same single test fails on
  dev's own developer image (dev 1770d687, /tank/fn/scratch/throughput-gate/native-img-1770d68709bb,
  log ae4bbcb1a8bdb46f9aa3835dd9e67bbe7d4fbadcd691f471ef55af3be3f59959) exactly as on this lane's
  (log d12b3cfed7ff257b1b23e3e91854965a1ebc93e5293218c20c6446a160e99017). Candidate cause: carrier v2
  (bounds-p4-carrier, e2b17943 / merge 6166adc1) raised the signer's source bound, so the fixture no
  longer exceeds it; whether the test's expectation or the emission bound is wrong is the fix lane's.
- tests.test_native_key_statements: 5 OK (regression over the owner changes).

```
0651bfbb2fb3d804851c9605db6b902bc0281338d0da4acc5b49ba7b6599ab76  tree/build/fn-host-developer
3c5de7a611f0108db6849556e22e52d2a0facbceab11f35bbabb6b36cda10334  tree/build/fn-host-developer.core
5adb11ea1c32f6b503b0031bb8b0fc50d6c533f7fa6ec63a7683e56116490dc2  logs/test-tests.test_native_peer_invite.log
26526cf4d1cc39ee6e6bc2dee5dd7f6b0059981138c1da49fc593edb283da8a6  logs/test-tests.test_native_hybrid_author.log
bae788d8fcaccacf3e0650c90aaedf15e7004ffc6cef2365ffe9ae0aa5fe4897  logs/test-tests.test_native_key_statements.log
```

### Not done (PKT-473)

PKT-433 (c) the POST reply naming a refused key change (the reply is fn-nntp-post-outcome's from
the completion word alone; a second durable word runs through books/owner's outcome and its
invariants: its own lane); the verdict field on accepted transit arms; fn_verify `revoked` against a
native node; the must-fails owed for fn-lb-a-connection-opened-after-a-publication-is-bound-anew
beyond its durable hypothesis; a succession-era inviter known to the invitee (still
`already-enrolled` at the accept); a succession chain carried with the document for nodes that
never enrolled the principal; the dead fn-acct-list-report. The hybrid_author failure is dev's (above).
