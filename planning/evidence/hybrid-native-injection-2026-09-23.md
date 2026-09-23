# Native hybrid author injection, 2026-09-23

The old native `hybrid-author` path stored a portable `FN-Authorship` carrier
without a Path. The real two-owner peering test accepted and transferred that
article, then failed while reading the missing source Path on the frozen 295
image (`build/launch-20260923/hybrid-peering-295.log`). That test is retained
for the next combined image; no new native runtime pass is claimed here.

`host/native/hybrid-control.lisp` now takes the owner post configuration and
clock observation while serialized, calls ACL2
`fn-hsig-injected-carrier-octets`, and passes those exact bytes to the
host-called `fn-hsig-authorized-injected-carried-submission-event`. The latter
recomputes the injection and refuses any different received payload before
making the atomic Store article/verdict event. ACL2 `fn-inj-decide` owns Path,
Injection-Date and Injection-Info. The portable `hybrid-sign-carrier` operation
and existing schema-1 record grammar are unchanged. Replay validates the
record's stored received/source binding without reapplying today's injection
policy, so an older pathless schema-1 article remains readable.

ACL2 8.7 certified `fn-hsig-injected-carrier-retains-exact-signed-source`:
**if the host-called projection returns nonnil**, the exact signed source is
a suffix of the received article. It also certified
`fn-hsig-injected-carrier-is-a-news-injection`: under that same successful
projection premise, the received bytes satisfy `fn-inj-reinjectionp` for the
rendered portable carrier and configured agent/Message-ID. The reachable
test constructs an injected schema-1 event and checks source reconstruction
and snapshot binding. Turning injection off makes the projection nil and
refutes the suffix conclusion without its premise; a plain portable carrier
and the nil result of disabled injection refute the injection-grammar
conclusion. These are byte-projection results,
not signature-primitive, physical durability, or peer-I/O proofs.

The focused hbox run `run-20260923T200002Z-8fee`, manifest
[`certify-20260923T200004Z-6303.json`](manifests/certify-20260923T200004Z-6303.json),
passed `books/hybrid-store-invariants` and
`tests/acl2/hybrid-store-tests`. The dependent hbox run
`run-20260923T200058Z-03ee`, manifest
[`certify-20260923T200101Z-7203.json`](manifests/certify-20260923T200101Z-7203.json),
passed `books/native-hybrid-control`, its test book and three Store identity
replay/trace/index test books. Both used `/tank/fn/toolchains/w28/acl2-literal-4g`
(SHA-256 `9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`),
jobs 2, at the exact staged source digests recorded per book in the manifests.
After adding the disabled-injection grammar counterexample, the changed test
book passed again in `run-20260923T200533Z-a82b`, manifest
[`certify-20260923T200539Z-17599.json`](manifests/certify-20260923T200539Z-17599.json).
The combined image and protected two-owner restart result remain open.
