# M4 native request: A authors the request from its own workflow, through a real BPA, to a released obligation

Lane `m4-native-request`, 2026-09-24 23:00Z to 23:40Z, on hbox. Source: branch
`lane/m4-native-request`, `41799aaf` (dev `19709182` plus `bd56f9c5` and
`41799aaf`). Everything ran under `/tank/fn/scratch/m4-native-request/`.
Reports, logs, runners and the image build log are in
[`m4-native-request-2026-09-24/`](m4-native-request-2026-09-24/), with a
`SHA256SUMS`. dtn7-rs is the pinned 0.21.0 checkout `/tank/fn/dtn7/repo`
(`4daf02d7`).

## Result in one paragraph

A's request is now authored by A: `bp-obligation request` publishes ACL2's
attempt for the work in A's FNWF journal, takes the one `:submit`, and hands
ACL2's request ADU (6314 octets, `fn-bpo-request-adu`) to A's FNBS carrier.
No lab bridge and no ION helper is involved. Through dtn7-rs with one and two
relays, the first hop SIGKILLed mid-transfer and restarted, B's `bp-node
serve` takes custody once, decides `carried carrier=ingress-boundary
author=sender-author`, answers `request-accepted` and commits to its Store.
B's receipt crosses the relays back, A decides `carried carrier=return-boundary
author=receiver-author`, answers `receipt-accepted`, and exactly that work
becomes `receipted pinned=no`. A second, never-requested obligation on A stays
`outstanding pinned=yes` in every run. With B's boundary for the relay
carrying nothing, B refuses with `BP node source refused
reason=source-not-carried`, `request-refused`: no receipt, A still pinned. A
SIGKILL inside either request publication leaves the work outstanding,
pinned and visible. The receipt release still rests on D23's carriage trust:
the issuer lane has not landed, so the release has **no issuer-authority
check** yet.

## What changed

- **Decision** `fn-bprq-plan S WORK ATTEMPT` (`books/bp-request-plan.lisp`, new;
  prefix `fn-bprq-` registered). It returns nil or
  `(:request ATTEMPT OUTCOME KEY ADU DESTINATION RETRY)`:
  - `fn-bprq-attempt-record`: the generic `:attempt` record (the body the ION
    constructor had).
  - Its durable `:outcome`, with the txid chosen above every txid the image has used.
  - `KEY`: the FNBS job key `(work attempt generation)`.
  - `ADU`: `fn-bpo-request-adu` over the image those records make.
  - `DESTINATION`: the work's peer EID.
  - `RETRY`: when a reopen has marked the work's last attempt
    `:restart-observed`, a `:retry-request` for that attempt, published first
    (see finding 1).
- **Host-called subject**: `fn-workflow-request-plan`
  (`host/workflow-host.lisp`), called by `fnn-bpo-request-publish`
  (`host/native/bp-obligation.lisp`).
- **Verb** `bp-obligation request STORE WORKFLOW WORK ATTEMPT FNBS NODE-ID
  CONTACT-HOST CONTACT-PORT [LIFETIME CRC HOP-LIMIT TRANSFER-MRU WALL
  WALL-ERROR]`:
  - Inside the owner-mode journal, it publishes RETRY (if any), then the
    attempt (with reserve-resolution), then the outcome.
  - It checks `fn-workflow-take-submit`.
  - It enqueues the ADU as one FNBS job under KEY (`:enqueue` through
    `fn-bpnp-step`), then offers the job once. `bp-service resume` re-offers
    a durable job.
  - Its three outcomes are the carrier's exit codes. ACL2's refusal of the
    plan exits 1.
  - Developer cuts: `FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT` and
    `FN_BP_OBLIGATION_TEST_PAUSE_AFTER_SUBMIT`.
  - `bp-obligation.lisp` now loads after `bp-service`/`bp-contact` in both
    images.
- **ION is an adapter.** `fn-workflow-ion-attempt-record` now calls
  `fn-bprq-attempt-record`. The test book proves
  `fn-bpiw-attempt-record-is-the-generic-attempt`. The generic verb reads no
  ION record, route or helper.
- **`bp-node.lisp` forwarding** (the old `:225`): `fnn-bpnode-forward-contact`
  passes no expected TCPCL peer (see finding 2).
- **Lab** `tests/bp-dtn7/run_fn_dtn7_app_receipt.py --native`:
  - Step 1 uses the verb instead of the bridge-authored ADU and `bp-service run`.
  - Steps 4b and 5 are new: the control obligation, and the two process-death cuts.
  - Without `--native`, the old behaviour is unchanged.

## Theorem (subject is what the host calls)

| theorem | statement | host line |
| --- | --- | --- |
| `fn-bprq-plan-is-the-works-request` | if `fn-bprq-plan S WORK ATTEMPT` is non-nil, then: its attempt is an `:attempt` naming exactly WORK and ATTEMPT; KEY is `(WORK ATTEMPT g)` for that attempt's generation g; ADU `fn-bpa-decode-exact`s to `(:ok R)`, where R is `fn-bpa-make-request` over work WORK in the published image (`fn-bprq-published-state`: retry, attempt, outcome applied), R is `fn-bpa-requestp`, and R's work id is WORK; DESTINATION is that work's peer EID | `fn-workflow-request-plan` (`host/workflow-host.lisp`), called by `fnn-bpo-request-publish` (`host/native/bp-obligation.lisp`) |

- **Hypothesis:** the plan exists.
- **Not claimed:** the work's fields in the published image are stated
  there, not equated to the pre-image. No transport or receipt property is
  claimed, and no recovery of a fenced attempt.
- **Teeth** (`tests/acl2/bp-request-plan-tests.lisp`):
  - Reachable witness over the committed-article image of
    `bp-outbound-tests`: the plan's attempt equals the hand trace's exact
    record, and its ADU equals the hand trace's request octets.
  - Live `fn-bpiw-apply` of the plan's records reaches exactly
    `fn-bprq-published-state` with one `:submit`.
  - `must-fail` on the conclusion at the refusal witness (an absent work),
    for the one hypothesis.
  - Refusals:
    - an in-flight attempt;
    - a pending image;
    - a fenced image;
    - a work bound to no article, where the attempt alone *is* admitted
      and so separates the ADU clause.
  - A restart-observed work's plan carries the retry. Its history replays
    through `fn-bpiw-replay-journal`. The same history without the retry is
    refused.

**Certification** (hbox, ACL2 8.7, w28 `acl2-literal-4g`, 2 jobs):

| run | source | result | manifest |
| --- | --- | --- | --- |
| `run-20260924T230214Z-b86d` | `bd56f9c5` (plan without the retry clause) | passed: bp-request-plan 6.5 s, tests 1.8 s | `manifests/certify-20260924T230223Z-2118502.json` |
| `run-20260924T230759Z-4d2f` | `41799aaf` | **passed**: bp-request-plan 7.6 s, tests 1.9 s | `manifests/certify-20260924T230813Z-2144048.json` |

No existing book changed, so there are no dependents to recertify. The
`dtn` profile (109 roots, which now include `books/bp-request-plan`) validated
`result=loaded` from the cache before the image was built.

## Image (scratch, unfrozen)

`fn-host-dtn-developer` was built from `git archive 41799aaf` by
[`build-image.sh`](m4-native-request-2026-09-24/build-image.sh) (the
dtn-node-image recipe). The build log has 0 `undefined` lines.

- Launcher `7d86ee6a4382c79b…`, core `e291d542c2c02422…`.
- Full hashes: `image.sha256`.

## Labs (`final/`, runner [`labs.sh`](m4-native-request-2026-09-24/labs.sh); log SHA-256 16-hex prefixes)

| step | control (A to B direct) | 1 dtn7 relay, carried | 2 dtn7 relays, carried | 1 relay, B's boundary carries nothing (unauthorized origin) |
| --- | --- | --- | --- | --- |
| 1 `bp-obligation request`: attempt, submit, carrier durable (adu=6314); held after 600 bytes, first hop SIGKILLed | **uncertain** `fdbee5bd5d311b06`; fn-B PID 2148132 | **uncertain** `7945ee97f8d017f6`; dtnd PID 2148951 | **uncertain** `7945ee97f8d017f6`; dtnd PID 2149734 | **uncertain** `7945ee97f8d017f6`; dtnd PID 2151161 |
| 2 first hop restarted, `bp-service resume` | **accepted** `abc3ed70c4698260` | **accepted** `d1a429842bd6a561` | **accepted** `9c77bd58b8a80997` | **accepted** `f72da18293369af2` |
| 3 B custody / source decision | 1, `direct principal=ingress-boundary` | 1, `carried carrier=ingress-boundary author=sender-author` | 1, same | 1, **`refused reason=source-not-carried`** |
| 3 B application (Store commit, FNRJ) | **request-accepted**, receipt queued `eadd49357d42247c` | **request-accepted** `6795fbc6c6660730` | **request-accepted** `4ca49b4826c48612` | **request-refused**, nothing queued `91e928f0b275eda7` |
| 4 receipt at A (`bp-contact tick` on B, A `bp-node serve`) | **receipt-accepted** `a46c150c59e529d8` (tick `86daef364c2c7bdd`) | **receipt-accepted**, `carried ... author=receiver-author` `3d6b692fc82fac70` (tick `22866592d09d4635`) | **receipt-accepted** `bb7c1a54b658b908` (tick `5f8481ccda087999`) | **no-receipt** `ad4e6aa2f7b43756` |
| A's requested obligation after | `receipted pinned=no` | `receipted pinned=no` | `receipted pinned=no` | `restart-observed pinned=yes` |
| 4b control obligation (never requested) | `outstanding pinned=yes` `ffb4358713b86382` | same `e28981d81cb15ec6` | same `6a4eb47185f976ec` | same `619c30065477a3e0` |
| 5a SIGKILL after `:submit`, before carrier | marker reached, PID 2148381; status `restart-observed pinned=yes`; re-request publishes the retry, attempt gen 1, carrier durable (dead contact, **uncertain**) `fab0fffdffa3f870`; journal reopens | same, PID 2149522, `aa7dfba58baf535b` | same, PID 2150903, `c721223d96068505` | same, PID 2152832, `80d85508e83a6c66` |
| 5b SIGKILL after attempt, before its outcome | marker reached, PID 2148559; status `outstanding pinned=yes` `9d881522205e0949`; re-request **refused** (`ACL2 refused a request`, fenced image) `7ceef8c5d97948ac` | same, PID 2149595 | same, PID 2150939 | same, PID 2152875 |
| report.json | `9de54ab2f303f308` | `4bd9f4eaeb427a8e` | `d58e71300783da1c` | `ba7c3d5e49216d80` |

In the two-relay run, dtn7's epidemic routing handed A's own request back to
A (`BP accepted xfer=2 adu=6314`), as in the m4-app-receipt record. A's
`bp-node serve` then forwarded it on its own session to dtn7-r1, which
announced `dtn://dtn7-r1/`: `TCPCL bp-node-forward ... SESSION-UP`,
`accepted outbound`, `BP forwarding result durable arrival=1 status=sent`
(`a-serve.log`). Before this change, that session was refused at SESS_INIT.
This is the only run that exercises the `bp-node.lisp` forwarding path.

## Findings

1. **A live re-attempt after a reopen bricked the journal. Found and fixed
   here.**
   - What happened: in the first control run (`r1`, on `bd56f9c5`), after the
     5a cut, the second `bp-obligation request` was admitted live and
     published. The next open then failed: `ACL2 rejected application
     journal replay`, and every later verb on that journal failed with it.
   - Why: the reopen's `:restart` is not a record. Disk replay applies it
     only after the last record, so replay sees an `:attempt` straight after
     an `:intent` attempt.
   - Fix: the plan now journals the old attempt's `:retry-request`
     (`fn-bp-request-retry`, the explicit local retry decision) first. Replay
     and the live image then agree (test book).
   - Still open: ION's `workflow-ion-submit` retries through the same
     constructor with no retry record. It would hit the same defect if it
     re-attempts after a restart.
2. **Routing: the machine has no next-hop or outbound-neighbour decision.**
   - ACL2 decides *which* held bundle goes on a session, by its destination:
     `fn-bpnp-has-forward-pendingp` and `fn-bpnp-step`'s `:session` event,
     keyed by PEER-ID.
   - The next hop is operator configuration: CONTACT-HOST:PORT.
   - No ACL2 function decides the outbound neighbour's identity. Session
     admission (`fn-bpaj-session-principal`) is inbound only, keyed by the
     local listener port.
   - The change therefore widens what an outbound `bp-node serve` session
     accepts, to whatever the contact announces. `bp-service` and
     `bp-contact` already did this.
   - Owed receipts are not sent by `bp-node serve` at all. It queues them as
     FNBS base jobs, and `bp-contact tick` sends them; the lab uses it.
     `fnn-bpnode-forward-contact` forwards held transit only.
3. **A cut between the attempt and its outcome fences A's workflow image, and
   no native verb recovers it.**
   - The work stays `outstanding pinned=yes` and every status read works.
   - Every further request is refused (5b). Other works' receipts on that
     journal would be refused too, because the image is fenced.
   - Recovery needs a `(:outcome txid gen :recovery :committed)`
     publication, which `fn-bpiw-replay-fence` already replays. No verb
     writes it.
   - The refusal line is generic (`ACL2 refused a request`): the plan
     returns nil without a reason.
4. **The release rests on today's carriage trust.**
   - A accepts the receipt because the relay's boundary carries
     `dtn://receiver/`, which is enrolled as `receiver-author` (D23).
   - The issuer lane (`d23-issuer-authority`, release-issuer rows) has not
     landed in dev. This lab ran with today's rows, so no ACL2 check ties
     the receipt's issuer to an authority allowed to release the obligation.
     That is not the milestone.
5. **The 5a re-request goes to a dead contact on purpose.** Its carrier job
   is durable and `uncertain`, not delivered, so these runs do not show a
   retried work receipted end to end.

## M4's exit clause, now

- **Has, on a scratch DTN developer image through dtn7-rs 0.21.0:**
  - Native request authoring from the workflow.
  - A contact SIGKILLed mid-transfer and restarted, with one and two relays.
  - B's own admission and Store commit under the author's enrollment.
  - The receipt carried back, and exactly the requested obligation released.
  - An unrequested obligation that keeps its pin.
  - An unauthorized carrier refused with its logged reason.
  - Both publication cuts leave the work visible and pinned.
- **Lacks:**
  - Issuer authority on the release (finding 4).
  - Recovery of a fenced attempt (finding 3).
  - An outbound-neighbour/routing decision in ACL2 (finding 2).
  - Receipts sent by the node itself rather than `bp-contact tick`.
  - The ION retry path (finding 1).
  - Frozen images.

## Other runs

- `r1/` (on `bd56f9c5`, not kept in the record) is finding 1's evidence.
- Native test modules ([`tests.sh`](m4-native-request-2026-09-24/tests.sh),
  [`tests.log`](m4-native-request-2026-09-24/tests.log), module logs in
  `tests/`) ran on this DTN developer image and on a default developer image
  built from the same tree. That image's launcher is `346ef43e71d0c96e…` and
  its core `38d4400980ea1413…`. It had 0 `undefined` lines and validated 124
  roots, `result=loaded`, which checks the moved `bp-obligation.lisp` load in
  `build.lisp`.

  | module | result | s | log SHA-256 (16) |
  | --- | --- | --- | --- |
  | test_bp_obligation_native (default developer) | OK | 2 | `6a144a1065938d3d` |
  | test_native_image_profiles | OK (4 skipped) | 1 | `72c7e66feae1d224` |
  | test_bp_node_native (DTN developer) | OK | 431 | `d3cb6d99aa7a4609` |

## Stopped and released

- **Stopped by PID** (from each `report.json`):
  - fn: 2148132, 2148159, 2148277, 2148381, 2148559, 2149005, 2149339,
    2149522, 2149595, 2149860, 2150450, 2150903, 2150939, 2151224, 2151875,
    2152832, 2152875.
  - dtnd: 2148951, 2149039, 2149734, 2149892, 2150086, 2151161, 2151301.
  - The earlier `r1`/`r2` runs are recorded in their own reports.
- Ephemeral ports only. `/tank/fn/node` untouched.
