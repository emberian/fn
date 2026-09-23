# BP status-report codec D1a, 2026-09-23

RFC 9171 §6.1.1 payloads are implemented by `fn-bpn-report-encode` and
`fn-bpn-report-decode` in `books/bp-status-report.lisp`. Whole reports have
four status assertions, a reason, source EID, and creation tuple. Fragment
reports have two further scalar fields: offset and payload length. An
assertion is `[false]`, `[true]`, or `[true, dtn-time]`; generation through
`fn-bpn-report-encode-for-subject` requires the subject's time-request flag.
The decoder accepts either incoming timed form. Reasons 0 through 11 are
accepted in this local profile.

The certified keystone `fn-bpn-report-decode-of-encode` says that every
`fn-bpn-reportp` value decodes from its encoding to exactly that value with no
remainder. It has no separate encoded-size premise: the certified
`fn-bpn-report-encode-length-bound` caps a valid encoding at 1,194 octets,
while the decoder preflight is 4,096 octets. This pessimistic cap is 70.8%
below the preflight limit and is deliberately loose; its components count
four assertions at at most 44 octets, an EID at at most 1,100 including a
1,024-octet DTN SSP, and at most nine octets for each integer. The certified
`fn-bpn-report-accepted-input-is-canonical` says each accepted input
re-encodes byte for byte. `fn-bpn-report-encode-octets` covers output shape.
These are codec properties; no node path yet calls the decoder, and received
reports grant no release or retry authority. Generation, correlation and
consumption remain D1b/D2.

`tests/acl2/bp-status-report-tests.lisp` checks independent literal whole
and fragment wire vectors, timed/untimed subject-flag handling, nonminimal
integers, invalid assertions, wrong fragment shape, trailing octets, reason
12, and the one-past-input-limit refusal. Round-trip witnesses include the
whole and fragment vectors and a 1,024-octet DTN SSP with maximal 64-bit
creation and fragment integers; the latter's encoding exceeds 1,024 octets.
A `must-fail` witness removes the report-recognizer hypothesis with an
out-of-profile reason. The prior encoded-size premise was removed rather
than given a spurious falsifying tooth, because the record shape proves it.

Incremental certification submitted with `python3 tools/farm.py --jobs 2
--root /Users/ember/dev/fn/build/lanes/status-codec --remote-root
/home/ember/fn-gates/takeover-status-codec --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache submit persvati books/bp-status-report-invariants
tests/acl2/bp-status-report-tests`. Farm run
`run-20260923T164645Z-9809`, manifest
`planning/evidence/manifests/certify-20260923T164648Z-1822489.json`:
ACL2 8.7, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
status passed, two roots certified, six dependencies kept/installed from two
cache origins, zero slot wait. The invariant book took 6.535 seconds, the
test book 0.908 seconds, and certification wall time was 7.449 seconds.
The invariant book's previous 11.379-second run was diagnosed in its event
log: `fn-bpn-reportp-components` alone cost 5.23 seconds. Factoring the
reason-size fact and keeping recognizers closed reduced the book to 6.535
seconds at the current bytes. Source digests and exact per-book provenance
are in the manifest. `green_check --changed-since df5097b6` reported three
changed books and zero lacking matching evidence.
