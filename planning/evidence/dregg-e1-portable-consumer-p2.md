# Portable fn E1 authorship to durable Mini operation, 2026-09-23

This bounded public test joined fn's real native dual-signature portable
verifier to Mini's P1 durable operation/reply transaction. The local operation
is an offline Mini processing experiment under an independently selected fn
hybrid keyset, Mini origin pin and current Mini grant. It does **not** establish
fn Store admission, historical T10 verdict, E2 fetch/cursor/ack, a durable
full-carrier inbox, or a posted fn application reply.

Mini's `portable-consumer-decide` is called with the consumer config, separate
origin pin, fn image/full-public-key pin, source identity and signed-header
claim, local operator policy, and exact carrier. It invokes the fn native
`hybrid-verify-source`, parses its bounded six-token result, compares the full
principal/Ed/ML keyset and claimed source ID, derives the E1 package only
from the returned exact authenticated source, and re-admits its native Mini
origin prefix. The group claim compares the signed `Newsgroups` header, not
fn Store membership. The application `mini-e1` and local subject 7/content
target 600/capability 61 come from the operator policy. Its operation ID is
cSHAKE-domain-separated over the re-admitted origin domain, semantics,
genesis pin and original transaction ID, not the fn source identity. The
route reads current authority and typed content-target roots from Mini's
verified reopened history; native admission checks them and the grant again
on submission. A bounded accepted-history check refuses a later policy
change of subject, target or capability for an already bound app/operation.
The result still says `storeAdmission: unestablished`; its explicit absent-
Store provenance sentinels are not fn history/incarnation or T10 verdicts.

The fn developer image was the shared frozen `884e4816` build at
`/tank/fn/gates/integrate-reader-repair-20260923/build/fn-host-developer`,
launcher SHA-256
`ec8442a896d4b1b1ab242bfe649e5e595567c4bfb278fc7ce4091da581f0680a`,
core SHA-256
`4a49fe97136f8c592464eac64921b02b9f1482d38d90c46b5d219ccebecb17c1`,
with `/tank/fn/toolchains/openssl-3.5.8`. The Mac-to-hbox shell shim in the
P2 fixture only transported exact carrier and public PEM bytes and forwarded
the fn process result. Mini used Lean 4.30.0 on arm64 macOS and the existing
3,090-object native response closure, recompiling `Kernel.FnConsumerOperation`
and `Host.Main` only with one Lean compiler thread and one C compiler job.
The runtime-tested executable was
`/Users/ember/dev/minidregg-wt/fn-evidence/.lake/build/bin/minidregg-fn-portable-consumer-v5`,
SHA-256
`f76227abcfb6c59aaa979a7fdd47afaf839a52ffe9e13c9123674d92a92353b1`.
The later Mini commit `6b2f7420` changed only the module header comment;
a relink from its exact committed source produced
`minidregg-fn-portable-consumer-final`, SHA-256
`fbd78712606e4f220b7dda10da4cf0c2fc5e4e0837c722940866edc6ba1a0c3d`.
The native acceptance/reopen outcomes below belong to the v5 runtime-tested
binary; the final relink was not separately put through that native journey.
`lake env lean` passed for those modules and
`Kernel/FnConsumerOperationProofs.lean`; that is typechecking, not new
certification of physical CAS or cryptographic primitives.

A fresh scratch signer, genesis and content-resource birth gave one accepted
consumer event. The original public fn `signed.eml` (29,918 bytes, SHA-256
`dc5c8b864227ad808f8feef7b574bce6d8be2f1798ca1a3db8c14a7e63872e1e`)
verified under its independent public keyset. The new route emitted
`decision-first.json` as `proposed-fresh`, operation
`6df49d3b28b9c17fdf4360aeee7d45b76327b7d9a4bc047f370356001eb54e1`,
and a 17,159-byte canonical observation intent. Rust `mini submit --intent-kind
binary` used the scratch consumer key to sign the intent; normal
`NativeHost.submit` confirmed the exact signed call as event 2, transaction
`70360611303694322337604368053237362508687541099117391143116789337668566898783`.
A new process ran the same carrier and recovered `historical-repeat` with
byte-identical 254-byte Q (SHA-256
`831c48795503e74ed5bf6cd0a375b1d4c7d4b88a990f99156b4bd9c6ec48a5ae`)
and no proposed intent.

For a changed authenticated source, a scratch ML-DSA-65 key and the public
Ed25519 test vector signed an E1 source with only its Message-ID changed;
the package body stayed identical. `changed-carrier.eml` is 29,918 bytes,
SHA-256 `bf8cd877ba5aaa5cd2c308aeb386d3695b02c63cf854df1cbb3a5d88d3e6ed3f`.
The fn native verifier returned distinct ACL2 source ID
`666e2f7375626a6563742f7631000101c43cabcd3a87c4888c59d2fd528e3b71ad8ef6f840971425b5fdec9daaf0bd2e`
under its separately pinned full keyset. Mini derived the same operation ID,
proposed separate conflict evidence, and the normal signed native receiver
confirmed it as accepted event 3, transaction
`89258857000345942612172306515354544993903528512009618789513125245033493802878`.
A new process recovered `historical-conflict-evidence` without another intent;
the original source still recovered the exact Q. Wrong full ML key pin and
tampered carrier exited 1 before any intent; changing the local capability
from 61 to 999 exited 1 with `consumer operation already bound under another
local grant`, likewise with no intent or decision file. These are native
observations of the called fn verifier, Mini decision, and receiver paths.

Public exact consumer genesis, signed birth/first/conflict calls, original
outcomes, decision JSON, Q and changed carrier/keyset are in
`tests/fixtures/dregg-e1/portable-consumer-p2/`. The first call's SHA-256 is
`9c2d3633aff8c48d05b9468ff0da4e07f4934d66bef06747ba94138b7e26c8f7`;
the conflict call's is
`339d11038e8064f54dca56bab2d58ddaa12b3c24639fee8416c8c4e4f3c6d54e`.
No private key or SQLite file is included. The verifier image, native
signature helper, SQLite CAS and OS durability remain trusted physical
boundaries. P1's 18,432-byte binding retains the verified 48-byte source ID
and exact 16,136-byte Mini package but cannot hold the 22,393-byte source or
29,918-byte carrier, so this does not satisfy a complete durable fn inbox.
There is no E2 Store-position join or ack; a Mini accepted Q is separate from
an fn transport attempt ACK and from a posted fn application reply.
