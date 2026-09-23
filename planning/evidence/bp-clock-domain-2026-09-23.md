# BP clock-domain gate, finite ACL2 packet

Source: branch `implement/bp-clock-domain`, based on `d23c2f50`. This is the
ACL2 marker/decision packet for PRF-061 and SCN-029. Native service wiring and
its source-matched image are a separate combined-source result.

`books/bp-clock-domain.lisp` owns an exact FNBS kind-6 `clock-domain.fnb`
frame: one length-counted blob containing a canonical 36-octet lowercase UUID
with hyphens at 8, 13, 18 and 23. The host supplies the exact 37 octets read
from Linux `/proc/sys/kernel/random/boot_id`, including LF. ACL2 rejects an
invalid observation or frame and exports the exact 82-byte read limit. The
frame is sealed by the shared `fn-frame-trailer` owner, so this packet claims
no new hash implementation or cryptographic guarantee.

The host-facing function is `fn-bpnf-clock-domain-plan`, selected in
`host/native/bp-service.lisp`'s startup gate in the foundation native packet.
It returns `:initialize` with the exact frame and `fn-jpub-initial t` only
under a valid observed boot ID, absent final name, empty ACL2-classified
legacy namespace/sequence evidence, and held journal lock. A valid saved
marker with the same boot ID returns `:same`. A malformed marker, different
boot ID, missing marker with legacy evidence, invalid boot observation, or
missing publication authority returns a distinct `:fence` reason. The host
must fsync the journal root before inspecting the marker final, publish the
initial marker with file and directory barriers, and stop before replay or
clock use on `:fence` or uncertain publication. Those I/O obligations are not
discharged by the ACL2 book.

The certified `fn-bpcd-unframe-of-frame` theorem uses the canonical UUID
hypothesis; its reachable witness is the exact sealed 82-byte frame and its
negative cases include short/tampered bytes and invalid UUID observations.
`fn-bpnf-clock-domain-same-binds-durable-id` is about the called planner:
every `:same` result has a present, valid saved frame whose decoded ID equals
the validated current observation. `fn-bpnf-clock-domain-different-boot-fences`
requires both valid unequal IDs and a present saved frame; the actual plan
fences without reading numeric uptime. The test shows why both smaller and
larger new-boot readings are unsafe for a bare `(age . monotonic)` anchor.
`fn-bpnf-clock-domain-legacy-without-marker-fences` requires a valid current
observation, an absent marker, absent final-name observation and positive
legacy evidence. Mixed legacy outbound rows, received kind-5 rows, hidden
stages, a sequence frontier and a malformed namespace all count as evidence.
Guard verification succeeds for the encoder, decoder, mixed-plan evidence
wrapper and startup planner. The `fn-jpub-crash-outcome` witness classifies
process death after link begin and before the directory barrier as uncertain;
it does not claim a physical crash-image correspondence.

ACL2 8.7 on hbox, exact toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
certified `books/bp-clock-domain` and `tests/acl2/bp-clock-domain-tests` with
jobs 2 in `run-20260923T194339Z-9ca6`, manifest
`planning/evidence/manifests/certify-20260923T194345Z-4180941.json`.
The test book subsequently gained the explicit lower/higher incomparable
counter examples, sequence-frontier evidence, and truncated-marker case;
`run-20260923T194603Z-e595` certified that expanded test source with
manifest `planning/evidence/manifests/certify-20260923T194606Z-4188122.json`.
The assurance follow-up added a `must-fail` witness for dropping the
canonical-ID hypothesis from the byte roundtrip; final test certification is
`run-20260923T194907Z-a01a`, manifest
`planning/evidence/manifests/certify-20260923T194910Z-4190492.json`.
The two direct conditional fence facts remain certified helper theorems; the
curated proof registry cites the byte roundtrip and the unconditional
same-result binding theorem as its keystones.

This slice supports same-Linux-boot process restart with `CLOCK_BOOTTIME`
anchors and safely **fences** a different boot or legacy journal. It does not
reanchor across a reboot or establish reboot liveness. The Linux boot ID's
stability/uniqueness and `CLOCK_BOOTTIME` progression are host/environment
assumptions, not ACL2 conclusions. No theorem here says the observed kernel
source, filesystem barriers, or saved image satisfy those assumptions.
