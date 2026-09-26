# The signed mission's refusal, found in two layers; custody only over an admitted channel (lane mission-signed, 2026-09-26)

Brief: `build/coordinator/queue/w2-mission-signed.txt` (continuation of
mission-four-node; mandate §9 and §4 "Offline forwarding", D23). Ids:
PRF-128, SCN-074, PKT-247. Previous record:
[mission-four-node](mission-four-node-2026-09-25.md) (its assurance chain,
PRF-120 and the unsigned run are not repeated here). Branch
`lane/mission-signed` from `lane/mission-four-node` b565c27e, dev merged at
51808446. Nothing here is deployed: every run is loopback in
`/tank/fn/scratch/mission-signed/` on images built from this lane's commits.

## What a node can now do

1. **Every refused delivered request names ACL2's reason** on one line of
   `bp-node serve`'s log: `BP node delivery refused result=R reason=C`.
   `fn-owner-bp-request-refusal-line` (host/bp-native-app-host.lisp, ACL2
   program mode) renders it from values ACL2 already returned: the D23
   source decision's refusal, the planner's or dispatcher's reason (the
   plan's `:intent` split into `intent-unformed` / `intent-store-conflict`),
   the transfer decision's reason on a refused BP transit submission
   (`fn-owner-bp-transit-submit`), or the Store attempt's plan reason
   (`fnn-owner-transit-refused`, and `submission-intent`). The host
   (`fnn-bpnode-request-result`, host/native/bp-node.lisp) prints it on
   every answer that is not accepted or duplicate; it decides nothing.
2. **A transit request is read with the relaying agent's check.** An injected
   article (every Store-rendered hybrid-signed carrier, and any article a node
   posted: it carries `Injection-Info`) was refused by the transit lookups
   (see "The reason", layer 1). Fixed in ACL2: `fn-bpaj-transit-article-fields`.
3. **A relay takes custody only over an admitted channel** (PRF-128, D23;
   PKT-170 retired). A bundle whose channel admission is refused is refused
   at reception with the admission's reason, before any FNBS step.
4. **The mission's relays listen per boundary**, so their channels are
   admitted (0 `channel admission refused` lines in the signed run, against
   several per run before).

## The reason (task 1), in two layers, both reproduced natively

Layer 1, image 45d13c8a (`mission-45d13c8a/signed`): B, for A's signed report,
`BP node delivery refused result=refused reason=intent-store-conflict`.
`fn-bpaj-transit-record-lookup(-fast)` and the transit context match read the
Message-ID through `fn-bpaj-article-fields`, the injecting agent's check
(RFC 5537 §3.4.1), which refuses `Injection-Info`; the signed carrier A's
Store rendered carries `Injection-Info: a.mission.invalid`, so the lookup
answered `(:conflict)` before any Store attempt. The transit plan itself
already used the relaying check (§3.6 step 1). Not enrollment, not the PRF-099
budget. The same class explains source-corpus-2's unsigned refusals after A's
injection (its raw `store post` records, without Injection-Info, passed).
Fix (8515ca02): `fn-bpaj-transit-article-fields` in books/bp-native-app.lisp
is the relaying check; the transit lookups (logical and fast) and the transit
context match use it. Witness in tests/acl2/bp-transit-join-tests.lisp: an
injected article's request plans `:submit`, `fn-bpaj-article-fields` refuses
it, the relaying fields are `:ok`, and the lookup over a Store without it is
`(:absent)` (must-fail: `(:conflict)`).

Layer 2, image f1734955 (`mission-f1734955/signed`, report.json sha256
9d0896affb2a81b4…, signed.out 6a96050e…, b-serve-1.log 42c134ad…,
a-serve-3.log 12e10afa…): B now **stores** A's signed report (B's Store
transaction 4, 120b91eb…: the kind-4 acceptance with Path
`b.mission.invalid!!a.mission.invalid!not-for-mail`, and B's copy verifies
with `hybrid-verify-source`, step 5 held), and then answers
`BP node delivery refused result=refused reason=history`; A does the same
for B's signed reply. Diagnosis from the code: a signed article is committed
as a kind-4 acceptance event (`fn-stxa-p`, its article record encoded inside),
not as a plain `fn-record-p` record. The BP application's Store binding reads
only plain records: `fn-bpaj-record-for-msgid` and
`fn-bpr-store-record-acceptedp` / `fn-bpaj-store-record-accepted-fast`
(`fn-record-p` and `member-equal` in `fn-sf-records`). After the commit the
dispatcher's lookup is `(:absent)`, it submits again, and the owner's
transfer decision answers `(:have :history)`, which the submission step
reports as refused. The verdict class is correct for a second submission;
the defect is that the first, durable one is never bound. Classification:
implementation (the BP receiver's Store binding does not know kind-4
acceptances). Not turned green; PKT-247.

## PRF-128 (task 3), books/bp-channel-ingress.lisp

Host line: `fnn-bps-receive` (host/native/bp-service.lisp) calls
`fn-bpaj-admitted-receive-event` with the admission answer of
`fnn-bps-tcpcl-admission` (`fn-owner-bp-tcpcl-ingress` =
`fn-bpaj-tcpcl-ingress-result` over the live owner configuration), and only
its `:ready` answer reaches `fnn-bps-foundation-step`; `fnn-bp-deliver-node`
(host/native/bp.lisp) is the caller.

| keystone | statement |
| --- | --- |
| `fn-bpaj-refused-channel-takes-no-custody` | admission answer not `:admitted` ⇒ the answer is exactly `(:refused R)`, R the admission's reason (`fn-bpaj-channel-refusal-reason`), and not `:ready`: no kind-5 row, hence no job, `:attempting`, family or owed receipt from that bundle |
| `fn-bpaj-admitted-channel-receives-under-its-ingress` | admission `:admitted` ⇒ the answer is `fn-bpnf-receive-wire-event` under the admitted ingress (whose principal is the policy's selection, `fn-bpaj-admitted-ingress-binds-announcement-and-selection`) |

Teeth (tests/acl2/bp-channel-ingress-tests.lisp): reachable positive
witness through the allowlisted neighbour `peer` on its own listener (`:ready`,
event ingress names `peer`, `fn-bpnf-step` proposes kind-5 `:persist`); the
refused keystone on two boundaries sharing listener 4556 (`(:refused
:ambiguous-peer)`, not `:ready`) and on a missing trust profile
(`(:refused :no-trust-profile)`); hypothesis removal for each keystone (the
admitted answer is `:ready`; over the refused channel the answer differs
from the receive boundary's on the anonymous ingress); a labelled mutation
witness: the anonymous ingress handed straight to the receive boundary (the
pre-PRF-128 host) is `:ready`. Assurance chain: native entry
`fnn-bp-deliver-node` → `fnn-bps-tcpcl-admission` (ACL2 admission) →
`fn-bpaj-admitted-receive-event` (the executed subject, guard-verified) →
keystones above → observed `BP channel admission refused reason=R` and
`BP refused xfer=N reason=R`, no `BP accepted`. The relation is the admission
answer itself, established per transfer; there is no carried state.

A found-and-fixed host defect on the way: renaming the parameter left
`fnn-bps-receive`'s callback reading an unbound `ingress`, and image d3d17977
answered every transfer `uncertain reason=machine-answer`; f1734955 reads the
ingress from the ready event (f1734955's commit).

Native: `test_bp_node_native` two tests restated for the decided behaviour
(`test_absent_bp_trust_refuses_custody_with_the_policy_reason`,
`test_absent_bp_trust_refuses_the_receipt_at_reception`: refused with
`reason=no-trust-profile`, no `BP accepted`, no delivery, exit 1, pin kept);
they encoded the old anonymous custody. Filtered module on f1734955
(`-k receipt -k request -k uncertain_transfer -k kind_eight -k unrouted
-k removed_route -k absent_bp_trust -k admitted_channel`): 13/13 OK
(`units-f1734955/bp-node.log`). The ambiguous-peer case and the four request
labs: see "Native runs".

## Certification

hbox, ACL2 8.7 `w28/acl2-literal-4g`, 2 jobs, 300 s:
`run-20260926T012109Z-b923` (95 roots affected by bp-native-app,
bp-native-app-fast, bp-channel-ingress and the two test books; 96 of 97 books
passed, bp-transit-join-tests lacked the fast book's include;
`manifests/certify-20260926T012131Z-51846.json`; slowest 9.99 s,
bp-node-forwarding-teeth-tests, unchanged by this lane; bp-channel-ingress
4.8 s, bp-native-app 4.1 s, bp-native-app-fast 4.5 s, bp-channel-ingress-tests
5.3 s) and `run-20260926T013602Z-f42b` (bp-transit-join-tests 4.2 s,
`manifests/certify-20260926T013624Z-82003.json`). Two of three runs used.

## Native runs (hbox, systemd-run MemoryMax=24G)

Images, built by tools/runbooks/hbox-image-build.sh in
`/tank/fn/gates/mission-signed-img-<rev8>` (validation OK, 58 hashes, composed
artifact sets, rejected=0): 30697048 (the reason line), 45d13c8a (finer
`:intent`: layer 1 observed), d3d17977 (the unbound-ingress defect,
superseded), **f1734955** (the served code of this lane; later commits change
no file the image loads except the driver, tests, registries and this record).

- **Signed mission** (`mission-f1734955/signed`, 627 s, exit 1): steps 0, 1,
  2 and 5 hold (A's signed report fragmented to X, reassembled, X SIGKILLed
  and restarted, forwarded through r1, r2 and Y; B's stored copy verifies
  with `hybrid-verify-source`; B's consumer polls and acks; B's signed reply
  authored and requested); steps 3, 4 and 6 fail at layer 2
  (`reason=history`). 0 channel-admission refusals on any node (the relays
  listen per boundary); FNBS frames A 5, B 5, X 12, Y 8. report.json
  9d0896affb2a81b4…, b-serve-1.log 42c134ad…, a-serve-3.log 12e10afa….
- **ambiguous-peer case** (`mission-f1734955/ambiguous`, `--case
  ambiguous-peer`, exit 0, both steps held): X logs `BP channel admission
  refused reason=ambiguous-peer` and `BP refused xfer=0 reason=ambiguous-peer`,
  no `BP accepted`; A's request answers refused and A's obligation stays
  `pinned=yes`. report.json e76d90c94117ecf4…, x-serve-1.log c58c83f5….
  The previous record's X took kind-5 custody on the same provisioning.
- **Request labs (regression gate)**, 4/4 exit 0 with the gate's outcomes:
  control, one and two dtn7 relays `request-accepted`, `receipt-accepted`,
  `pinned=no` (outs 173a558a…, 7b0745ce…, 4a9614da…); unauthorized
  `request-refused`, `pinned=yes` (dced8af4…).
- **Filtered test_bp_node_native**: 13/13 OK (log 51574f5e…).

## Not done, and why (PKT-247)

- The signed mission does not pass: layer 2 above. The fix is in the BP
  receiver's Store binding (bp-native-app, bp-native-app-fast, bp-receipt's
  `fn-bpr-store-record-acceptedp`, the transit context codec): a kind-4
  acceptance's article record must bind as the plain record does, with the
  replay, context and receipt theorems carried over. bp-receipt is deep in
  the closure, and this lane is at its farm budget. SCN-066 stays
  `specified`; SCN-074 is `specified` with the layered finding.
- `bp-node serve` listens on one port: a relay with two boundaries can hear
  only one neighbour at a time, so the mission turns its relays' listeners
  with the direction of travel. A multi-listener serve is open (PKT-247).
- The fast transit functions are not guard-verified (they were not before).
- The 13 stale C1 expectations in test_bp_service_native/test_bp_contact_native
  (previous record) are harness-repair-2's (PKT-248).
