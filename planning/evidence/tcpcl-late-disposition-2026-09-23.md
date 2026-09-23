# TCPCL late delivery disposition, 2026-09-23

`host/native/tcpcl.lisp:fnn-tcl-act` now calls the ACL2
`fn-tcl-delivery-plan` after the durability callback returns. The native
buffer holds ACL2 message objects, not pre-encoded bytes. The plan requires
the matching END XFER_ACK after earlier control outputs and partial ACKs,
including partial ACKs for a different transfer, in the same read batch.
An accepted result releases those messages; a definitive refusal preserves
the partial ACKs and replaces the END ACK with XFER_REFUSE; uncertainty and
malformed callback results release no final ACK. The `bp` and `bp-app`
callbacks now return explicit accepted/refused/uncertain values, and the
shared FNBS service callback is a separate integration join.

The keystone `fn-tcl-late-refusal-gets-no-final-ack` concerns that exact
host-called planner under `fn-tcl-held-final-ackp`: its result is a refusal
with an ACL2-selected RFC 9174 Table 6 reason and no final END ACK for the
transfer. The held-prefix premise also rejects any earlier END ACK, so
preserving the prefix cannot accidentally release a completed transfer.
`fn-tcl-uncertain-delivery-withholds-final-ack` gives the ambiguous
publication case. `fn-tcl-complete-produces-held-final-ack` connects the
planner precondition to the actual completion event. The test book uses an
established two-node session with coalesced partial and END ACKs, a separate
coalesced prior-transfer partial ACK/refusal before the next transfer, plus a
missing-held negative tooth. It does not yet prove every native I/O cut or
the new FNBS callback's composition.

ACL2 8.7 / SBCL 2.6.8 on hbox, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
executable SHA-256
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`:

- `run-20260923T184719Z-67a7`, manifest
  `planning/evidence/manifests/certify-20260923T184725Z-4097776.json`:
  `books/tcpcl-delivery` passed at SHA-256
  `b4e5c8e753207558aa83d084b3dddf0902b84945fcd0a1fed2ff99a01b18a5b8`.
  The invariant/test roots failed at a subsequent theorem and were corrected.
- `run-20260923T184947Z-ad00`, manifest
  `planning/evidence/manifests/certify-20260923T184950Z-4102682.json`:
  `books/tcpcl-delivery-invariants` and
  `tests/acl2/tcpcl-delivery-tests` passed with jobs 2 and no closure rebuild.
  Their source SHA-256 values are respectively
  `205bbdac3ed0753db15c9a8eab710765ad9a7411adb4f49345d6b6973ae42aba`
  and
  `affcf9a844d981eae22f102a5db7cdd98ff3e6d8fa166cea0cf21fdbc4bf0f30`.

`make check` passed after locally regenerating the generated ledger. The
updated native refusal test is prepared for the next combined image; no
source-matched native image has run this callback path yet. RFC 9174 §5.2.3
requires cumulative ACKs for processed segments, while §5.2.4 permits a
transfer refusal and names No Resources and Not Acceptable. fn's stronger
local policy holds the final END ACK until the durable disposition is known.
