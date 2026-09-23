# Native BP received FNBS join, 2026-09-23

The `bp receive` command now opens the same `fnn-bps` handle used by the outbound service, under one spool and FNBS lifecycle lock. On open it uses the ACL2 mixed namespace plan, reads bounded legacy and kind-5 rows, constructs `fn-bpnf-recover-auto-event`, and passes it to the actual `fn-bpnf-step`. A replay fault terminates startup before listening. The existing outbound path calls `fnn-bps-step`, which wraps its event as `(:base event)` for that same owner.

An inbound TCPCL transfer supplies exact wire octets, observed clock, and separately admitted configured principal and announced EID. `fn-bpnf-receive-wire-event` reuses `fn-bpn-receive` policy and constructs a canonical `:receive-bundle` event. The service feeds the resulting `:persist` proposal into `fn-bpnf-publication-authorize`; ACL2 provides the final name, frame, and immutable-publisher initial state. The physical outcome returns as `:persist-result` to the same step. `fn-bpnf-callback-result` selects accepted, refused, or uncertain; accepted is limited to a matching durable result or a duplicate. The operator evidence namespace is a secondary publication, not FNBS acceptance authority.

The boundary book and test certified on hbox ACL2 8.7 / SBCL 2.6.8 with toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`, jobs 2, no closure: `run-20260923T185628Z-fab3`, manifest `planning/evidence/manifests/certify-20260923T185630Z-4116579.json`. Mixed namespace book and test passed at final bytes in `run-20260923T185538Z-124b`, manifest `planning/evidence/manifests/certify-20260923T185541Z-4114809.json`; the simultaneous earlier boundary attempt failed on a guard dependency and was repaired before fab3. Boundary host-called guards are verified using `bp-node-machine-guards`. The mixed namespace behavior is certified but its guard verification remains open because inherited lifecycle helper guards are unverified. SBCL source-load verified `host/native/bp.lisp` and `host/native/bp-service.lisp` with expected unresolved image dependencies. There is no saved-image or network-process result for this new source cut yet.

Application delivery, FNRJ receipt handoff, outbox retry, and returned receipt release are separate A3 work. An FNBS custody ACK does not establish those facts. The epoch restart contract assumes physical callbacks do not survive process death; kind-5 records choose the later epoch when present, while an empty directory cannot persist an epoch on its own.

The contact-window caller was composed into this lane from its independently certified source. Its book/test dependency closure changed against this foundation source, so both were recertified at exact combined bytes in hbox `run-20260923T190146Z-9daa`, manifest `planning/evidence/manifests/certify-20260923T190147Z-4125980.json`. `green_check.py --changed-since 2009cedd --strict` then reported six changed book/test roots and zero ungreen. The three native source files `bp.lisp`, `bp-service.lisp`, and `bp-contact.lisp` loaded together in SBCL with the expected image-only dependencies unresolved; this is not an image result.

Root integration with current stamped Store and repaired TCPCL delivery was checked by `run-20260923T190525Z-2d0f`, manifest [certify-20260923T190532Z-4130808.json](manifests/certify-20260923T190532Z-4130808.json). The three roots whose dependency bytes differed passed on hbox, reusing matched cached dependencies; the complete changed-root gate then had no ungreen roots. `make check` passed. This is source qualification; the combined native image and network campaign remain pending.

For the native ADU integrity witness, `fn-bpnf-inspect-adu` now decodes a bounded retained kind-5 frame in ACL2 and projects its payload. The read-only `bp-service inspect-received` command writes only that ACL2-selected ADU. The TCPCL lab compares it byte for byte with the source ADU and flips the frame's last trailer bit without changing length; the inspector must refuse the damaged frame and leave no ADU output. The inspector book passed hbox `run-20260923T190735Z-bdef`, manifest `planning/evidence/manifests/certify-20260923T190738Z-4134184.json` (its simultaneous test attempt failed on an ACL2 constant-evaluation issue). The repaired test book passed `run-20260923T190936Z-2d8c`, manifest `planning/evidence/manifests/certify-20260923T190939Z-4137190.json`. The new native command was source-loaded, and `tools/tcpcl_lab.py` compiled; its process test awaits the combined image.

On the frozen integrated source `8cfaeb9f` (root `66bf9e55` plus this inspector and test migration), both inspector roots passed again in hbox `run-20260923T191124Z-cf57`, manifest `planning/evidence/manifests/certify-20260923T191130Z-4139592.json`. Strict changed-since-66bf9e55 green check found zero ungreen roots. This source is the production/developer image qualification cut.

The first full-node production image exposed a host boundary mismatch after durable kind-5 publication: `fn-bpnf-host-eventp` returned a truthy `member-equal` tail for `:persist-result`, while `fnn-bps-foundation-step` requires the ACL2 result to equal `t`. The retained frame decoded to the exact 1500-byte ADU, but the matching completion was rejected as a malformed event and both peers exited uncertain. The predicate now normalizes that arm to canonical `t`/`nil`, with equality-to-`t` witnesses for all four accepted event kinds. Hbox `run-20260923T191540Z-9e26`, manifest `planning/evidence/manifests/certify-20260923T191542Z-4151016.json`, passed the boundary book and test at the repaired bytes. The image must be rebuilt and the process campaign rerun; the prior image result is a regression witness, not a passing native result.

The full developer campaign exposed a recovery log mismatch, not lost outbound state: the foundation `:restart-ready` effect reports received-held count, while the host labeled it queue jobs. `fn-bpnf-base-job-count` now projects the actual recovered outbound job count in ACL2; the host logs both counts separately. Hbox `run-20260923T192158Z-6ff3`, manifest `planning/evidence/manifests/certify-20260923T192200Z-4164437.json`, certified the boundary book and test at these bytes. The mixed namespace enumeration fixture now uses its widened two-record-family entry bound. Tests that advanced wall time alone now assert retained work because the durable Bundle Age anchor controls `fn-clock-expiry-decision`; a wall jump cannot force expiry or release.

The frozen `d86eb86d` full-node images loaded 191 books and 76 artifact roots with hbox ACL2 8.7 / SBCL 2.6.8 and toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`. Production `build/fn-host.core` SHA-256 was `241afbe1e9708f5d508f915b7d72f4790d340f374929c40ab1abd78eff62e9b3`; developer `build/fn-host-developer.core` was `2a6e5cd26db607ea4b6f8842412cfc92550ef73a320fa8e69480d4b5d557509c`. The exact full developer image passed all 18 tests in `tests.test_bp_service_native`, `tests.test_bp_contact_native`, and `tests.test_bp_receive_integrity_native` (remote log `build/bp-native-focused-tests-developer3.log`). The full production image passed `tools/tcpcl_lab.py --scenario adu`: each endpoint accepted one bundle, the received kind-5 frame decoded to the exact transmitted 1500-byte ADU, the reverse 700-byte ADU matched, and a same-length trailer corruption was refused. This image result is limited to same-boot behavior and does not establish application handoff or receipt completion.

A separate expiry witness then found a real process-restart clock defect: `fnn-tcl-now` used Common Lisp `get-internal-real-time`, whose origin on this SBCL host is process-relative. A queued bundle with a 1500 ms lifetime, followed by 1700 ms elapsed time and a new process, was attempted rather than expired. The host observation is being changed to Linux `CLOCK_BOOTTIME`, and an ACL2-selected durable boot-domain gate is being added before replay. Until that gate and its native tests pass, the above full-image campaign does not establish expiry after restart or safe comparison after reboot.

The clock-domain join uses `books/bp-clock-domain.lisp` to validate the exact
37-byte Linux boot-ID observation, frame a canonical 82-byte kind-6 marker,
and decide initialization, same-domain reuse, or a recovery fence. The native
`fnn-bps-open` checks that decision under the shared spool/FNBS owner before
reading any lifecycle records or comparing a retained age anchor. A standalone
`bp send` holds the same owner before reserving sequence evidence. Real
publication uses `fn-jpub-initial` and the immutable file and directory
barriers; a dedicated developer cut can fail the marker's directory barrier
without redirecting older application-record fault selectors.

On frozen source `b0e7a8cd`, the changed clock-domain book and test passed hbox
run `run-20260923T194925Z-9467`, manifest
`planning/evidence/manifests/certify-20260923T194927Z-4191297.json`; the
follow-up canonical-ID hypothesis tooth passed exact-source test run
`run-20260923T195031Z-6361`, manifest
`planning/evidence/manifests/certify-20260923T195034Z-4192489.json`.
`make check` and strict changed-since-`66bf9e55`
green check passed with six changed roots and zero ungreen. Explicit shared
cache acquisition loaded the full 192-book production image closure:
artifact set `6b5017b5de53342623c81cb4adbafd30b08fd364e4d1d2a36995d2e5944db3d0`,
source identity `1e463034435c0cce3722ecc6c966827b9bff2b63cc444cc9964fac3f1c0e34ee`,
toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`;
ACL2 load validation passed all 77 roots. Both full `host/native/build.lisp`
profiles built on hbox. Production core SHA-256 is
`17c5964418d0618d30ab459efd1e69f25dc1fc971343c4fdc132988f325348ea`;
developer core SHA-256 is
`766184986700ed0323ac25c8af51f27a16d5be844ca3f4991ca4a704d6e0773b`.

The full developer image passed all 22 tests in
`tests.test_bp_service_native`, `tests.test_bp_contact_native`, and
`tests.test_bp_receive_integrity_native` (remote log
`build/bp-clock-focused-developer-final.log`). The restart witness now records
`BP transport work=work-aged status=expired` after 1700 ms real elapsed time
for a 1500 ms lifetime. The suite also confirms same-boot marker reuse,
corrupt and absent-legacy marker fences, and recovery of a visible marker
after an injected directory-barrier error without creating outbound work.
The full production image passed the ADU roundtrip with sender and receiver
domain markers present, exact payloads both directions, and same-length
kind-5 trailer corruption refused. A valid alternate boot-ID marker is tested
by ACL2 with lower and higher incomparable counters, not by a physical reboot
test. Cross-boot reanchoring remains open; the current service fences instead.

The developer TCPCL lab passed all seven scenarios: exchange, refusal,
keepalive, crash/reconnect, size profile, ADU, and replay. Its refusal scenario initially counted the
shared `.spool.lock` owner file as a staged bundle, although the peer refused
the oversized transfer before any segment and no bundle stage existed. The
lab now excludes that lock file from its staged-bundle projection; the
corrected refusal scenario passed on the full production image with zero
segments and no staged bundle. The exact logs are archived under
`planning/evidence/native-bp-clock-2026-09-23/`; their SHA-256 digests are
`build/bp-clock-focused-developer-final.log`
(`11b625e7df0618cd8f0892c19477d4c422196ce66966bed66662ce7c53030354`),
`build/bp-clock-lab-all-developer-final.log`
(`dae51957784dd3ecf8951dd289c2d28b23cc71e334766f692b1ded2f84e2dd8f`),
`build/bp-clock-adu-production-final.log`
(`91f9fc600ae9dc953c4aa7ded435270c03e21e8d79a9bf338ff5557ec5992088`),
and `build/bp-clock-refused-production-final.log`
(`110ba905f76b634e9ed8bbdf88f95ce1301d632da7807938abd8c88056e3a0eb`).
A production `--scenario all` invocation is
not a valid campaign because its crash scenario deliberately uses a
developer-only fault selector and production correctly refuses to start with
that selector. The production ADU and refusal runs and the developer suite
above are the claimed native coverage.
