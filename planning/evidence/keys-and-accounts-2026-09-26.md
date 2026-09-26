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

fn_verify (hbox /tank/fn/scratch/keys-and-accounts/verify-t1, the cryptography and dilithium_py
modules are on hbox, not the laptop): `tests.test_fn_verify.FakeNodeVerifyTests` 18 OK, including
`test_a_revoked_verdict_is_rendered_and_never_verified` (revoked + the revoked principal's
signature: exit 1; revoked + another principal's signature: exit 2; `revoked legacy` undecided).
verify-t1.log af454b03e35cab5d83df721db3f853bfbf4780f1826f8735abcf300a3eefd037.

## Certification

(filled in below after the farm run)

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
