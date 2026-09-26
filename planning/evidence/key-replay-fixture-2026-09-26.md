# key-replay-fixture, 2026-09-26: historical key replay stays historical

Lane key-replay-fixture (Opus 5.5), from dev 8ca933b1, on gpt-6's review of
wave 2 (planning/review-2026-09-26-gpt6-wave2.md section 5) and PKT-173 a.
Ids: PRF-140, SCN-082, PKT-325.

## What changed

1. **No supported `:current`.** `*fn-ks-reopen-policy*` is gone. The grants a
   statement is decided under are `fn-ks-statement-rows EVENT AT-OPEN LIVE
   CONFIGS` (books/key-statements.lisp): the live rows at acceptance, the
   configuration at the statement's own txid at open, with no policy
   argument. host/owner-host.lisp `fn-owner-key-statement-rows` is now a call
   of it (it decides nothing), and `fn-ks-recover-recorded` (the open's
   recovery) uses the same function with AT-OPEN t, so the keystones'
   subject and the host's rows are one definition. No theorem statement
   moved: `fn-ks-reopen-is-blind-to-later-configuration`,
   `fn-ks-a-decline-replays-as-a-decline` and
   `fn-ks-recorded-recovery-completes-the-cut` are unchanged (their hints name
   `fn-ks-statement-rows` for the folded constant).
2. **The old behaviour as a counterexample fixture only**
   (tests/acl2/key-statements-tests.lisp, "COUNTEREXAMPLE FIXTURE"). The
   Packet 7 trace: statement declined for want of a grant, the grant
   published after it, a restart. The removed reopen (plan under the open's
   live rows) gives `fn-ks-log-line` = `key-statement enrol-successor
   committed at-open` and changes the state; the recorded reopen (rows from
   `fn-ks-statement-rows` with AT-OPEN) gives `key-statement declined
   no-grant at-open` and leaves the state. Must-fails: the old plan is not
   `:decline`; the two reopens are not equal.
3. **PRF-140** (below), with teeth.
4. **Native** case `test_an_accepted_statement_cut_then_its_grant_revoked`.
5. **Re-evaluation** is an explicit action, specified as PKT-325 and not built
   (below).

## PRF-140: an accepted statement finishes under its admission context

```
fn-ks-accepted-statement-finishes-under-its-admission-context
  (implies (and (fn-ctl-configs-all-through-p (fn-ks-txid event) configs)
                (not (equal (fn-config-replay reserved ceiling configs) :fault))
                (fn-ks-configs-after-p (fn-ks-txid event) more))
           (equal (fn-ks-recover-recorded (fn-ks-cut records snapshots event)
                                          (append configs more) observed ed ml
                                          sequence txid store-generation)
                  (fn-ks-accept records snapshots event
                                (fn-cfg-authorities (fn-cfg-value
                                  (fn-config-replay reserved ceiling configs)))
                                observed ed ml sequence txid store-generation)))
```

CONFIGS is the journal the acceptance ran under (every record at or before
the statement's txid, so its replay is the live configuration the acceptance
read); MORE is everything published after (a revoked grant, say). The cut,
then the open's recorded recovery over the whole journal, is exactly the
uninterrupted acceptance under the ORIGINAL configuration. It composes the
cut keystone (`fn-ks-recorded-recovery-completes-the-cut`, which it cites
and discharges) with the blindness keystone, and covers the non-statement
case. The `true-listp configs` hypothesis of the cut keystone is not needed:
a journal that replays is a true list (`fn-ks-config-replay-needs-a-true-list`,
proved, then the hypothesis dropped).

Subject and host: `fn-ks-recover-recorded`; host/native/owner.lisp
`fnn-owner-key-statement-recover` calls `fnn-owner-key-statement` with
AT-OPEN, whose plan and kind-3 event are `fn-ks-plan`/`fn-ks-execute` over the
rows of host/owner-host.lisp `fn-owner-key-statement-rows` =
`fn-ks-statement-rows`. The host-to-model link (the owner's newest-record
recovery is `fn-ks-recover`) is by construction, as PRF-098 recorded, not a
theorem.

Teeth (tests/acl2/key-statements-tests.lisp, "PRF-140"): records carry a real
clock stamp so they replay (`*kst-admit*` grant at the txid, `*kst-revoke*`
one txid later). Positive witness: every antecedent literal asserted; today's
rows would decline (`declined no-grant at-open`); the recovery equals the
acting acceptance (`enrol-successor committed at-open`), which differs from
the cut. One must-fail per hypothesis, each with the other hypotheses
asserted and the removed one's failure asserted: the grant only after the
txid (not all-through); a grant whose generation does not follow
(config-at folds it, replay faults); the revocation at the txid itself (not
after).

## Reconstruction inputs (review: sufficient, versioned historical inputs)

- **What the reopen reads.** `fn-sn-config-history` of the opened Store: the
  whole configuration journal, which the open installs from every
  configuration generation file (host/native/io.lisp
  `fnn-bridge-recover` -> host/store-node-host.lisp `fn-store-sn-recover` ->
  `fn-cpr-replay`), and `fn-ctl-config-at TXID` folds its prefix through the
  statement's txid (`fn-ctl-configs-through`). The statement is the newest
  Store record (`fn-ks-pending`); its txid is its kind-4 composite's
  (`fn-ks-txid`).
- **Compaction past the txid is not reachable today** (the reachability
  argument; no refusal theorem added):
  1. The open replays the configuration journal from its first record with
     a sequence check (books/config-physical-replay.lisp `fn-cpr-loop`,
     `:config-sequence`), so a journal missing its prefix does not open:
     the Store is refused, never re-decided under a partial history.
  2. No transition removes a configuration record: checkpoint, compaction
     and reclaim write none of the configuration records
     (books/checkpoint-compaction-preservation.lisp header; host/native
     unlinks only transaction packs, stage files and the state checkpoint).
     The journal is append-only (`fn-ocl-success-appends-exact-config-history`).
  3. `max-config-generations` (profile field 11) bounds the journal by
     refusing a new configuration record (`fn-native-admin-publication-authorize`,
     `:max-config-generations`), never by dropping an old one; raising it is
     `store upgrade-profile` (raise-only).
  If a future lane adds configuration compaction or rotation, the reopen of a
  statement whose txid precedes the retained prefix must be a named refusal
  or a recorded disposition decided in ACL2 (the obligation goes with that
  lane; the book comment and specs/peering.md state it).
- **Software-upgrade stability.** The replay rule is part of the Store
  format's meaning: the statement record plus the journal determine the
  disposition only under `fn-ks-statement-rows`. Changing the rule is a
  Store format version with its own reader and upgrade, never a constant
  edit that reinterprets bytes already written. (This is why the switch
  went: flipping it would have silently changed reconstructed decisions of
  existing stores.) The sentence is in the book comment and
  specs/peering.md.

## PKT-325: `operator CONFIG keys redecide MSGID` (specified, not built)

Contract: an operator action over the control socket (never an effect of
open); ACL2 decides it as a new acceptance of the stored statement under the
grants of the configuration in force at the redecide's own txid (`fn-ks-plan`
over `fn-ks-statement-rows` at that txid); filed as a new durable record
whose txid is its own, so the next open's recorded reopen reproduces it and
PRF-124/PRF-140 carry over; refused by name when MSGID is not a stored key
statement or its statement already acted. Open design question: the
record's shape (a re-filed kind-4 composite or a redecide record, charged at
admission under D27); the review says no new decline record now. Not built:
the budget went to PRF-140 and the native cases. Supersedes PKT-241.

## Assurance chain

native entry (`fn operator CONFIG run`, the open) -> `fnn-owner-key-statement-recover`
-> `fnn-owner-key-statement` AT-OPEN -> ACL2 `fn-owner-key-statement-rows` =
`fn-ks-statement-rows` (the representation is the decoded record and the
decoded journal) -> model `fn-ks-recover-recorded` (by construction) ->
relation: the journal is the append-only history the open replayed
(established by the open's replay, preserved by publication's exact append)
-> behavioural theorems PRF-124 (declines replay) and PRF-140 (accepted
statements finish under their admission context) -> observed: the native
cases below.

## Native (hbox, /tank/fn/scratch/key-replay-fixture/)

`tools/hbox_native.sh --label r2 af119e41 tests.test_native_key_statements`
(tree af119e41 = a32ecd33 plus the harness fix; developer image under
swarm-build, module under systemd-run MemoryMax=24G), native-r2: **OK, 4
tests** (the existing module is the regression gate).

- `test_an_accepted_statement_cut_then_its_grant_revoked` (PRF-140, SCN-082
  step 1): grant, start with `FN_NATIVE_KEY_STATEMENT_FAULT=statement-committed:kill`,
  POST a succession -> owner exit -9, no key-statement line, history
  generation 1 only; offline `control revoke P keys fn.keys`; `control list`
  then shows no grant; restart -> `['key-statement enrol-successor committed
  at-open']`, history generation 2 active, 1 retired; second restart -> the
  same single line, history unchanged. Under the removed `:current` reopen
  the open would have decided under no grant (`declined no-grant at-open`,
  the ACL2 fixture's line).
- `test_a_decline_across_a_restart_with_a_grant_added` (SCN-069/SCN-082
  step 2): `key-statement declined no-grant` at acceptance; after each of
  two restarts `key-statement declined no-grant at-open`; history
  generation 1 unchanged.
- `test_kill_at_the_cut_and_recovery_at_open` and
  `test_succession_revocation_and_carried_statement`: unchanged, OK.

SHA-256 (hbox:/tank/fn/scratch/key-replay-fixture/native-r2/SHA256SUMS):
```
a978da072121fcb027036dca42d470598c0dd065b42562c4b864a999049b9b3c  logs/test-tests.test_native_key_statements.log
1dc840e0cb9b42611abc7d414b2e679f8ff657b661739bb2cc0bfcc581673979  tree/build/fn-host-developer.core
633369a312beaef55db39e3f1396d3fdbba11b55b3a8579eb56dcf8ce42a32b8  tree/build/fn-host-developer
da0d2f837bbabcc149cc7687c5bc404f7fd1eb3c5b3ae4ab8c88e2ab819582be  logs/native-build-developer.log
```
native-r1 (a32ecd33) failed only the new case, at the offline revoke
(`refused operator control`, exit 1): harness, see the finding below; log
`af768a8a81d604d417b803b3451844728fcdbfea9d979ce6311e099e88ab44ea`.

Finding (harness, and a product gap noted, not fixed): after SIGKILL the
owner's control socket file remains, and an offline `operator ... control
revoke` finds it and hands the plan to it; nobody listens, so it is refused
before submission (`refused operator control`, exit 1). The native case
removes the dead owner's socket first. An operator after a crash meets the
same refusal; the stale socket should be recognized by the lock (the
exclusive lock is free) rather than by the socket's presence. Not owned
here.

## Certification

CERT_PLACEHOLDER

## Not done

- `keys redecide` (PKT-325): contract only.
- The host-to-model correspondence of the owner's recovery remains by
  construction (as PRF-098), not a theorem.
- The stale control socket after a kill (finding above).
