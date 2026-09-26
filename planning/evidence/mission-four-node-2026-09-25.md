# The four-node mission, the fair base job offer and the report effect join (lane mission-four-node, 2026-09-25/26)

Brief: `build/coordinator/queue/w2-mission-four-node.txt` (mandate §9, §5.7,
§15 "Multi-relay outage"). Ids: PRF-120, REP-009, SCN-066, PKT-170.
Nothing in this record is deployed: every run is on loopback in hbox scratch,
on images built from the lane's own commits.

## What now works

1. **The base job offer is fair.** The host's contact loop asks
   `fn-bpnj-contact-next` before every base offer (receipts, requests,
   status reports). It offers the first *ready* queued job for the peer. The
   previous question, `fn-bpnp-contact-next`, ended the contact at the first
   queued job when that job was held (`:route-changed`) or already offered on
   this contact (a refused transfer), so one such job starved every younger
   job for the peer. The witness is reachable from the lower machine's own
   events (`tests/acl2/bp-node-job-offer-tests.lisp`: the previous driver
   answers `(:held KEY1 :route-changed)` and `(:close)`; the fair one offers
   KEY2 in both states).
2. **A transport result names its attempt.** The host reads the job's attempt
   token (`fn-bpnj-attempt-token`) before the transfer and answers
   `(:job-result KEY TOKEN OUTCOME)`. Another token settles nothing.
3. **A report or receipt is "sent" only by the durable record of its
   accepted transfer.** `:report-due` (kind-10 durable, logged as
   "outbound queue pending") and the queued report job are not sent;
   `:transport ... :forwarded` comes only from the durable answer to the
   pending `:finished` record of an `:attempting` job, which only the named
   `:accepted` result proposes. A TCPCL XFER_ACK is a transport fact, never a
   retention receipt: the receipt that releases A's pin is B's application
   receipt, matched by A's own `bp-node serve`.
4. **An encoder refusal settles its pending record.** The host answered a
   lifecycle frame the ACL2 encoder refused with a process fault, leaving the
   pending proposal unanswered; it now answers `:refused`, which clears the
   pending record and answers its refusal effect.

## Assurance chain

`fnn-bps-foundation-step` (host/native/bp-service.lisp) -> `fn-bpnj-step`
(books/bp-node-job-offer.lisp; the named equation
`fn-bpnj-step-delegates-every-other-event` makes every `fn-bpnp-step`
keystone a fact about it on the other events) -> the lower machine
`fn-bpn-step` through the bridge `fn-bpnp-step-base-event-refines-fn-bpn-step`
-> maintained relations `fn-bpnp-step-guard-premisesp` (base machine
invariant, session list, held list) and `fn-bpn-lifecycle-invariantp`
(pending authorization) -> behavioural keystones below -> observed log lines
`BP job result stale`, `BP transport work=... status=forwarded`,
`BP queued job held ...`, `BP lifecycle record encoder refused`.
The relation is established at `fnn-bps-open` (the initial base state
invariant is checked once at open, `fn-bpn-initial-machine-state-has-lifecycle-invariant`)
and preserved by the two new arms (`fn-bpnj-step-preserves-guard-premises`,
`fn-bpnj-new-arms-preserve-the-lifecycle-invariant`) and by every delegated
event (`fn-bpnp-step-preserves-guard-premises`).

Host lines that call the subjects: `fnn-bps-foundation-step` calls
`fn-bpnj-step` and `fn-bpnj-host-eventp`; `fnn-bpc-drive-contact` and
`fnn-bpnode-send-receipts` call `fn-bpnj-contact-next`;
`fnn-bps-send-effect` calls `fn-bpnj-attempt-token` and answers
`:job-result`; `fnn-bps-persist-record` answers `:refused` on an encoder
refusal.

## Theorems (PRF-120), statements in books/bp-node-job-offer.lisp

| keystone | property | hypotheses |
| --- | --- | --- |
| `fn-bpnj-contact-offers-while-a-ready-job-remains` | the answer is an offer | gate open; the job KEY names ready (queued for the peer, unoffered, routed on its durable route) |
| `fn-bpnj-contact-offer-starts-the-ready-job` | the offer's event persists exactly that job's `:attempting` record and owes its `:cl-send` | well-formed base, token below the journal bound, true-list state |
| `fn-bpnj-stale-job-result-settles-nothing` | state unchanged, one `:job-result-stale` effect | token is not the job's current attempt token |
| `fn-bpnj-named-result-is-the-transport-outcome` | `:finished` for `:accepted`, `:requeued` (never `:forwarded`) otherwise | current token, nothing issued or pending, token bound |
| `fn-bpnj-step-forwarded-needs-a-durable-finished-record` | `:forwarded` only at `(:persist-result T :durable)` of a pending `:finished` record of an `:attempting` job | lifecycle invariant; a base event |
| `fn-bpnj-encoder-refusal-settles-the-pending-record` | pending cleared, not fenced, jobs unchanged, exactly the refusal effect | a pending record; nothing issued; well-formed base |
| `fn-bpnj-step-preserves-guard-premises` | the maintained relation | host event, true-list state |
| `fn-bpnj-contact-offers-a-ready-job-within-its-prefix` | the contact offers KEY | KEY ready with a stable prefix in every asked state; asks at least the unoffered prefix |
| `fn-bpnj-contact-offers-a-ready-job-under-a-bp-contact` | the contact offers KEY | A-BP-CONTACT (`fn-assume-bp-contact-asks`, books/assumptions.lisp, specs/failures.md); prefix no longer than the asks |

Teeth: `tests/acl2/bp-node-job-offer-tests.lisp`, one reachable witness per
keystone and one hypothesis-removal witness per hypothesis (gate removed: the
pending state; readiness removed: the held job; token mismatch; the
`:uncertain` answer fences instead of settling; one ask fewer than the
prefix).

Certification (hbox, ACL2 8.7 `w28/acl2-literal-4g`, two jobs):
`run-20260926T000703Z-9511` (32 roots affected by the new book and
`books/assumptions.lisp`, all passed; manifest
`planning/evidence/manifests/certify-20260926T000727Z-4086470.json`;
`books/bp-node-job-offer` was 12.9 s, a D26 defect, fixed by proof work in
abbd8aef) and `run-20260926T001009Z-d138`
(`planning/evidence/manifests/certify-20260926T001035Z-4091853.json`:
bp-node-job-offer 7.6 s, bp-node-job-offer-progress 5.7 s, tests 5.3 s).

## Not proved, and why

- Token monotonicity across every served event and restart. Within a process
  a fresh attempt's token is the next token at its proposal, above every
  earlier record's; a process death ends every earlier callback. No theorem
  states it over all events.
- That non-base events never propose a `:finished` base record: not a
  theorem; the base-event statement is.
- `fn-bpnp-contact-next` and its PRF-103 keystones stay in the tree; the host
  no longer calls it. PRF-103's statement names it as the host's question and
  needs the coordinator's note (this lane took no other id).

## Native evidence on the lane image

Image: `abbd8aef8586d17f451010d3e2490686de8aeb95`, built on hbox by
`tools/runbooks/hbox-image-build.sh` in `/tank/fn/gates/mission-four-node-img-abbd8aef`
(image validation OK; `fn-host-dtn-developer` 4986f14b…, its core fb8103d7…).
Later lane commits change no file under `books/` that the image loads and no
file under `host/` (the progress book, the tests, registries and this record
only), so this image is the image of the final commit's served code.

**Regression gate, the four request labs (task 4): 4/4 exit 0, the gate's
outcomes** (`request-labs-and-units.tgz`, sha256 db8c9fba…):
- control (direct), one dtn7 relay, two dtn7 relays: `request-accepted`,
  `receipt-accepted`, A's obligation `receipted pinned=no`
  (outs 9ef79f65…, ec6af666…, f30329f7…);
- unauthorized: `request-refused`, no receipt, A `restart-observed pinned=yes`
  (deaebffb…).

**Filtered native modules** (units in the same archive):
`test_bp_node_native -k receipt -k request -k uncertain_transfer -k kind_eight
-k unrouted -k removed_route`: 13/13 OK (log a08113c2…).
`test_bp_service_native` + `test_bp_contact_native`: 5/18 pass, 13 fail, every
failure `AssertionError: 0 != 3` on a connect to port 1 that answers
`reason=failed`, exit 0: the stale-expectation class C1 that
qual-bbf52159 records for the same modules on the bbf52159 image
(`planning/evidence/qual-bbf52159-2026-09-25.md:421`); reproduced by hand on
both images with identical output. Classification: harness (stale test
expectation after spec 4.3.2), not this lane's behaviour; not turned green.

## The four-node mission (task 1, SCN-066)

Topology tested (loopback on hbox, nothing deployed):
`A (dtn://fn-a/) -> X (fn relay) -> dtn7 r1 -> dtn7 r2 -> Y (fn relay) -> B (dtn://fn-b/)`
and back; four `bp-node serve` processes of `fn-host-dtn-developer`, owners
and consumers on `fn-host-developer`, dtn7-rs at the pinned
`/tank/fn/dtn7/repo`, every process under `systemd-run -p MemoryMax=24G`.
Driver: `tests/bp-dtn7/run_mission_four_node.py` (Python is only the external
driver; every verdict is a native line, exit code or verb output). Runs on
image abbd8aef: `mission-four-node/mission-abbd8aef.tgz` (sha256 eafa1ab2…;
keys, stores and journals excluded; each report.json lists every log's
SHA-256).

**Unsigned report and reply: all seven steps held, exit 0, 105.8 s**
(`unsigned/report.json` sha256 180a94ea…; the same on bbf52159, aac52d4c…):
A fragments its request to X (`BP fragmenting length=5680 peer-mru=4096
fragments=2`), X reassembles (`BP fragment family durable`), holds it while
r1 is down, is SIGKILLed, recovers `held=1` and forwards `status=sent`;
B takes custody and answers `request-accepted`, queues the receipt; the
receipt crosses its own outage (X down, A SIGKILLed and restarted, X
restarted) and A answers `receipt-accepted`, obligation `receipted
pinned=no`, **before B's owner and consumer start**; B's consumer polls
`<mission-report@fn-a.invalid>` and acks; B's reply crosses back, A answers
`request-accepted`, B's `work-b-reply` is `receipted pinned=no`; A's
consumer polls and acks the reply. Restarts: A SIGKILL and SIGTERM, X SIGKILL
and SIGTERM, B and Y SIGTERM.

Identities (unsigned, abbd8aef): work `work-a-report` / attempt
`work-a-report-a1`, Message-ID `<mission-report@fn-a.invalid>`, authored
source a658ee53… (B's stored copy 0c9cf40f…: B's own Path prepended);
`work-b-reply` / `work-b-reply-a1`, `<mission-reply@fn-b.invalid>`, source
8f151d4f…; bundles `dtn://fn-a/-843697605139-{0,1}` and
`dtn://fn-b/-843697605139-{0,1}`; one kind-8 attempt and one `status=sent`
per hop per bundle; FNBS lifecycle frames A 10, B 10, X 18, Y 16.

**Signed report: FAILS, exit 1 (the brief's user-visible result is not
reached).** A's `hybrid-author` carrier verifies at A
(`hybrid-verify-source` rc 0) and crosses every hop, but B answers
`BP node source carried carrier=y-boundary author=a-author | BP application
handoff durable | BP node delivery request-refused`, and A refuses B's signed
reply the same way. Classification: implementation (both images, both
directions). The refusal names no reason (a second, observability defect):
it is one of `fn-bpaj-transit-plan`'s `(:refused reason)` or
`fn-owner-transit-decide` not `:want` (host/native/owner.lisp:1557). Not
turned green: the unsigned pass is recorded as what it is.

Other findings: an fn relay forwards held transit only toward its PEER-ID
(`fn-bpnp-has-forward-pendingp`), so X and Y are restarted with the other
peer when traffic turns (capability limit; a multi-peer relay is open); X and
Y log `BP channel admission refused reason=ambiguous-peer` on some sessions
and still take kind-5 custody of transit (two boundaries on one loopback
address; a decision packet below); a consumer registered after a Store post
still polls that post first.

## PKT-170 (for ember): does transit custody need an admitted principal?

Trace: X logs `BP channel admission refused reason=ambiguous-peer`, then
takes kind-5 custody of the same session's transit bundle and forwards it.
Constraint: D23 (carriage is not authorization; the receiving authority is
bound to the author at the destination). Default (kept): a relay may hold
and forward transit from an unadmitted channel; the destination judges.
Rejected alternative: refuse custody without an admitted principal; cost:
two boundaries sharing a loopback address stop relaying in the lab until
boundaries are told apart by node ID. Affected: `fn-bpnp` receive step,
spec §4.1. Continues without it: everything in this record.

## Next exact actions

1. Log the refusal reason on `BP node delivery request-refused`, then find why
   a Store-rendered FN-Authorship carrier is refused at the destination (the
   signed mission); rerun `run_mission_four_node.py` (signed) on the new image.
2. Stale test expectations C1 in test_bp_service_native/test_bp_contact_native.

Harvested by assurance-triage (2026-09-26) as the scenario catalog's evidence log: [`unsigned.out`](mission-four-node/unsigned.out), the unsigned run's output, extracted from mission-four-node/mission-abbd8aef.tgz, sha256 `c41e4c412af28b15096c1fa538c1dc234826eb811af81499e3c82a08b5f49694`.
