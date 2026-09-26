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
