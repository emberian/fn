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

The first source packet above was strengthened after review of coalesced
`fn-tcl-drive` output. A single read can emit a partial ACK for transfer 0,
then XFER_REFUSE for transfer 0, then a final ACK and `:bundle-received` for
transfer 1. The planner now preserves that earlier output exactly and rejects
any earlier END ACK. `tests/acl2/tcpcl-delivery-tests.lisp` evaluates this
reachable drive trace. The final exact-source hbox run
`run-20260923T185810Z-def9`, manifest
`planning/evidence/manifests/certify-20260923T185812Z-4118399.json`, passed
all three roots with jobs 2 and one cached origin. The three book/test source
SHA-256 values are `de710829578d60c37ae89e9dfd3177dd022478566efe09a87425b77535590c8c`,
`7a3d24c424927658080eff2fbb0475eb63f6801dc5770c6a39b971b749a32204`,
and `eed0d6cb115e6259daf16dafdf05f852456b651c3f7a50e8f077bb34fb0eabc7`.
This final run supersedes the earlier proof packet for the broadened held-list
premise; the native image limit remains.

The next packet closes the driver-to-held-list gap left by the standalone
`fn-tcl-complete` lemma. The unchanged `fn-tcl-host-triple` and
`fn-tcl-host-drive` bodies moved to certifiable `books/tcpcl-host-drive.lisp`;
`host/tcpcl-host.lisp` includes that book, and native
`host/native/tcpcl.lisp:fnn-tcl-session` still calls the same function.
`fn-tcl-drive-delivery-events` inducts over actual recursive `fn-tcl-drive`
and proves, without input hypotheses, that each final ACK is immediately
followed by its matching `:bundle-received`. Its step proof covers segment,
control, denial and decode-error arms under the carried cheap session
invariant. `fn-tcl-delivery-events-imply-held-final` projects the `:send`
messages preceding the first delivery into the exact
`fn-tcl-held-final-ackp` premise used by the host-called planner;
`fn-tcl-delivery-eventsp-after-first-bundle` carries this to each later
completion in one read. `fn-tcl-host-drive-bundle-has-held-final` is the
named actual-wrapper bridge. The ACL2 test drives two completed transfers in
one read, and must-fail teeth drop either held-projection premise and the
accepted callback path-type premise.

Exact-source hbox ACL2 8.7 / SBCL 2.6.8 run
`run-20260923T191848Z-d306`, manifest
`planning/evidence/manifests/certify-20260923T191855Z-4158317.json`,
passed `books/tcpcl-host-drive`, `books/tcpcl-delivery-invariants`, and
`tests/acl2/tcpcl-delivery-tests` with jobs 2. Source SHA-256 values are
`68a8d763cce8e9ce4e1673efe15a0b2e718c1ee4fb6f36994734429c51ae06ad`,
`09e5aca0ce9b497d6d2a09aee77b691a476e255938d7fef1c12ea92656f15376`,
and `e02b71e1c632d3838c06c2eba678c98d888f03c116f1f3bfa624dfb72836039c`.
The proof assumes the native `fnn-tcl-act` collection/reset loops as written;
it does not verify raw Lisp execution or a source-matched combined image.
