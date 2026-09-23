# A3 application handoff logical checkpoint, not an integrated service

`books/bp-app-handoff.lisp` selects the oldest locally addressed,
dispatch-pending held bundle in the single `fn-bpnf` state. It classifies
the exact canonical ADU as request, receipt, or unsupported. The receipt
trust predicate requires the configured peer to match the admitted TCPCL
ingress principal, receipt issuer, and bundle source; it does not claim
cryptographic authentication. The reachable held request and wrong-node
witnesses are in `tests/acl2/bp-app-handoff-tests.lisp`.

`books/bp-fnbs-delivery-codec.lisp` defines a bounded FNBS kind-7 row
`(epoch, op, arrival, primary-identity, disposition, detail)`. A successful
request result requires a non-placeholder committed receipt ID. The decoder
requires an exact re-encode, and its test book exercises round trip,
malformed identity, missing receipt ID, and trailing bytes. The
`fn-bpnf-step` `:deliver`/`:deliver-result` arms allocate an epoch/marker,
authorize only an exact result, and fence every non-recovery event after
an ambiguous application result. The kind-7 publication authorizer binds
the state-owned pending record, final name, frame, lock and empty final
slot. Live durable application completion and mixed kind-5/7 replay call
the same `fn-bpah-apply-delivery` function; an orphan, duplicate,
wrong-identity, wrong-class or out-of-order kind-7 row faults replay.
Successful request results create an owed handoff only after kind-7
durability. The native service is not yet a caller of these new arms, so
no native application-delivery/release property is claimed yet.

Selected persvati certification used ACL2 8.7 / SBCL 2.6.8, executable
`/home/ember/fn-gates/toolchains/w25/acl2-literal`, jobs 2 and a 90-second
per-book timeout. `bp-app-handoff` and its test passed in run
`run-20260923T190429Z-3a18`, [manifest](manifests/certify-20260923T190436Z-3106016.json).
The kind-7 codec book passed in the later partial run's
[manifest](manifests/certify-20260923T191208Z-3186882.json); its test passed
in run `run-20260923T191254Z-52fb`,
[manifest](manifests/certify-20260923T191257Z-3194375.json). A final
same-source cache-composition run `run-20260923T191354Z-986d` installed both
passing pairs and completed with status passed,
[manifest](manifests/certify-20260923T191357Z-3204778.json). No new ACL2
certificate was authored by that final cache-only run.

`tests/test_bp_contact_relay_native.py` is a prepared byte-only relay test
using two real native processes, an interrupted transfer, receiver restart,
closed/open contact windows, and expiry. `python3 -m py_compile` passed.
The test has not run against the new shared image yet. The relay controls
socket cuts and copies bytes; it creates no TCPCL ACK, BP outcome, or receipt.

At the current logical bytes, selected persvati run
`run-20260923T194847Z-b499` passed foundation, host event gate, mixed replay,
publication, and their direct tests in
[manifest](manifests/certify-20260923T194907Z-3565364.json). The publisher
test evaluates its constrained digest attachment inside `make-event`.
Fifteen affected
namespace, kind-5 invariant, family and test roots passed at the current
foundation bytes in `run-20260923T195026Z-dbd4`,
[manifest](manifests/certify-20260923T195034Z-3581950.json). The native A3
bridge and end-to-end article/receipt process-death test remain open.
The final wrong-class replay negative witness and its dependent publisher
test passed in `run-20260923T195220Z-03ce`,
[manifest](manifests/certify-20260923T195226Z-3601699.json).

The native caller checkpoint adds `bp-node serve` and `bp-node dispatch`
in the full image. It opens the single clock-gated FNBS service before the
owner Store, selects only canonical request or receipt held items, and sends
the foundation's exact delivery marker/result around the existing FNRJ or
FNWF/Store join. An ambiguous application result fences that service until
cold recovery. TCPCL's kind-5 custody answer is returned before application
dispatch. The ACL2 outbox view binds an owed handoff to its original delivered
request; FNRJ supplies the durable receipt ADU, and the old FNBS base queues
one return job for a later explicit contact tick. A recovered exact job key
includes the state-owned held arrival, so a fresh retry carrier with the
same receipt ID gets a distinct return job. A recovered job prevents a
second creation sequence only after ACL2 compares its exact receipt ADU and
peer; a conflicting key fences the caller. The caller has passed SBCL reader checks,
not a native image or packet scenario yet.

The FNWF automatic transaction selector, its reachable receipt witness, and
the release callback refactor passed selected persvati run
`run-20260923T200331Z-a350`,
[manifest](manifests/certify-20260923T200334Z-3710893.json). The final
outbox selector, replay witness, and affected publication test passed runs
`run-20260923T201124Z-f0ea` and `run-20260923T201208Z-12f6`,
[manifests](manifests/certify-20260923T201129Z-3790241.json) and
[publication manifest](manifests/certify-20260923T201213Z-3798200.json).
The final trigger-bound key and exact-job matcher passed selected run
`run-20260923T201751Z-e703`,
[manifest](manifests/certify-20260923T201756Z-3856408.json).
`green_check.py --changed-since 4276c1fc` found zero stale changed/dependent
books at those source bytes. The durable base job currently suppresses a
second outbox enqueue, but the stored foundation handoff remains `:owed`;
the ACL2 effective `:handed-off` projection and native article/receipt
process-death scenario remain open.

The first combined developer image at source `5930f4f2` exposed a caller
argument defect in the new native test: kind-5 custody and kind-7 publication
were durable, but the request was refused because the new caller converted
source/destination strings to internal EID objects before calling the existing
owner Store/FNRJ join. The follow-on caller source restores the exact string
shape of `fn-bpapp-receive` and adds deterministic developer-image pauses
after the modeled FNRJ decision, kind-7 publication, and return-job queue.
The corrected source has not yet run in a rebuilt image.

The next combined developer image at source `00c34fb5` reached a durable
Store acceptance, then exited with a fault because the new pause selector
was not registered in `host/native/io.lisp`; the caller queries registered
selectors even when the environment variable is unset. The following source
registers both new modeled-cut selectors and extends the native driver with
kind-5 ambiguity, FNRJ decision, kind-7, outbox, and conflicting-job cuts.
That driver has not yet passed on an image with these selectors.

The combined developer image from source `4e7dd362` (SHA-256
`694528285f74f37a32b8bfd7123da30b1e2599fb14a64a156c1a1f78e765479a`)
ran the two-carrier request/return scenario. Both requests reached durable
Store acceptance, both distinct return carriers reached TCPCL custody, and
both sender handoffs were durably marked `:receipt-refused`. This is a failed
end-to-end test, not receipt-release evidence. The cause is the A3 ACL2 trust
predicate comparing the receipt's `peer-eid` to the return carrier destination
(sender). FNRJ constructs that field from the original request destination
(receiver), and FNWF binds it to its outstanding work peer. The predicate now
compares it to the configured admitted peer while retaining independent
principal, source, and issuer checks. A reachable two-node receipt witness
and negative peer/source witnesses were added. The book, test, and three
affected replay/publication roots passed selected persvati run
`run-20260923T203900Z-dc90`,
[manifest](manifests/certify-20260923T203907Z-4069328.json).
The corrected trust predicate has not yet run in a combined native image.

The same `4e7dd362` developer image ran five independent native fault cases
from `tests/test_bp_node_native.py` with `FN_ACL2` at
`/tank/fn/toolchains/w28/acl2-literal-4g`, the source-matched image, and
OpenSSL 3.5.8. The conflicting return-job, FNRJ decision-death, kind-7
death, durable outbox-death, and ambiguous kind-5 publication tests all
passed (5/5, 74.319 seconds). These cases do not exercise the corrected
receipt trust predicate or prove sender pin release. The image's source was
`4e7dd362`; the test driver was the tracked source at `7e62af7c` copied to
`/tmp/test_bp_node_native_a3.py` on hbox, with only its marker assertion
changed since that image.

The trust-fixed combined developer image from exact source `7ad230b5`,
SHA-256 `337124282e0b98faa1666f6c3daaae661ba793d19e7e153a7faddb9c34face9b`,
artifact set `fd95947d1bfb7fae`, passed
`NativeBpNodeTests.test_request_retry_queues_distinct_receipt_carriers_and_releases_pin`
on hbox (1/1, 11.406 seconds). Its runtime used the same ACL2 executable and
OpenSSL library above. The test authored a request ADU, delivered it twice in
distinct carriers, observed one receiver article and two return-job
publications, byte-relayed a later contact, and verified a receipt under the
current configured-peer and announced-EID checks released the exact sender
forwarding pin while an unrelated pin survived.
This is native behavior evidence; the separate ACL2 effective handoff-status
projection over kind-7 owed evidence and the exact durable return job remains
open.

The receive boundary still derives the admitted principal from the CLI
configured peer after TCPCL's announced-EID check. It does not call the
specified observed-channel `fn-bpaj-session-principal` decision, which is not
yet implemented. These loopback tests establish no authentication against a
spoofing co-resident process or untrusted relay; receipt authorization beyond
the configured local profile remains open under §2.3 and D-14.

The same image passed a separate uncertain-FNRJ cut (1/1, 17.826 seconds):
an injected ambiguous receipt-decision namespace barrier returned exit 3
without kind-7 handoff, and a cold `bp-node dispatch` recovered the durable
decision, published the handoff, queued its return carrier, and retained one
receiver article. This cut is expressed as the journal's existing ambiguous
publication event; it is not a manufactured application result.

An exact FNRJ replay receipt ADU was then queued under the owed job key with
the wrong BP carrier peer. Cold `bp-node dispatch` fenced with exit 3 before
claiming handoff; the receiver still held one article. This additional
native test passed on the same `7ad230b5` image (1/1, 17.626 seconds). It
separates peer binding from the earlier wrong-ADU collision witness.

The ACL2 effective handoff projection is now in `books/bp-handoff-status.lisp`
with exact FNRJ receipt-ID/ADU, trigger, durable return-job payload and peer
binding; see [its separate evidence](bp-effective-handoff-2026-09-23.md).
The native caller now requires its `(:handed-off sequence)` result both for
an existing outbox key and after a new enqueue. It returns uncertain after
an ambiguous queue publication before checking that projection, and keeps a
definitive queue refusal separate. The companion ambiguous-outbox native
test is present but this host join has not yet run in a rebuilt image.
