# Consumer poll and exact-file envelope, 2026-09-23

The source examined was `1d26e01f`. The saved developer launcher on hbox was
`/tank/fn/gates/poll-live-group-native-1d26-20260923/build/fn-host-developer`
(SHA-256 `177c47f453e9d65c126a62bee664fe77a80a624fcdd0c4c2fe0a0a82810a48a7`).
The commands used `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`,
`LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib`, and disposable files
under `tempfile.TemporaryDirectory` on hbox. They did not start an owner or
touch a live node.

`consumer-project` on that exact image read a 347-byte cursor or a
196,609-byte event no further than the ACL2-owned 346/196,608-octet limits,
but exited 4 with `store file exceeds bound`. One-byte malformed files exited
1 with `fn-consumer-project-refused-v1 codec`. The source repair gives the
bounded-reader overlimit its own fault subtype; only this user-supplied
exact-file command maps it to `fn-consumer-project-refused-v1 limit` and exit
1. Other bounded readers retain their fault classification. A new native
driver checks both overlimit inputs and the within-limit ACL2 codec refusal;
it needs a source-matched rebuilt image to qualify the repaired behavior.

The ACL2 poll reply caps are 346 cursor octets, 196,608 event octets and
196,963 payload octets. `tests/acl2/consumer-local-control-tests.lisp` now
constructs a schema-1 event with every independently bounded field at its
maximum, including two 65,538-byte children and a 32,768-byte authored
source, and checks that the actual FNCT encoder accepts it. It also checks
that a 196,609-byte report is rejected before framing. The selected ACL2
test certification on persvati passed in 3.049 seconds (ACL2 8.7,
`run-20260923T234418Z-23f6`,
`planning/evidence/manifests/certify-20260923T234427Z-1749031.json`).
This shape witness is intentionally not a valid bound-authorship composite;
it tests the enclosing byte envelope, not Store admission. Existing poll
position tests show that polling does not itself advance the durable ACK.

The current `fn-col-poll-drop` still traverses the committed prefix up to the
cursor before inspecting its 16-event window. Its cost is proportional to
the cursor position; the independent derived-index work is replacing that
called path. This packet makes no constant-work poll or new native-image
qualification claim.
