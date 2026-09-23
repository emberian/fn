# E1 portable fn inbox, Q and conflict native evidence (2026-09-23)

Mini source `32ea942e70917248b2c6b936d0802c045b316746`, with exact
representation follow-ups `1e66baa5db1b8daea6b91829586622879a9612f2`
and `dc32b4048ac41790e256445705cca40da44b336d`, in isolated
`/Users/ember/dev/minidregg-wt/fn-evidence` adds a separate bounded canonical
portable inbox atom to the same signed content-resource invocation as the
small operation binding and immutable Q. It preserves the earlier atom IDs
and stable application/operation nonce. A different relay projection of the
same signed source retains another carrier without another application
effect; a different authenticated source retains conflict evidence. The
portable route derives its package only from fn-verified exact source bytes,
re-admits the independently pinned Mini origin, and reads its current local
grant from Mini. It does not infer fn Store acceptance or send an E2 ack.

The fixture directory `tests/fixtures/dregg-e1/portable-inbox-p1/` holds
three public original signed calls, their accepted outcomes, decoded native
decisions, canonical inbox exports and exact carriers. The first call
(`33655723ec58d5f7ea250ef049fe47dd560d746dcd132ae18dd0fdf57368bab3`)
confirmed count 2 with one binding, Q and inbox atom. The relay call
(`d13e05c479543ae0504ce1feec0bca122cef59e46acdd53e584fa64e07e1c359`)
confirmed count 3 as carrier variation evidence, sharing the original
source identity and Q. The changed-authenticated-source call
(`fc6e7dae37b66120fb35999503290932787041b544afd7c306f129d63c253c59`)
confirmed count 4 as conflict evidence. Native `consumer-export-inbox`
reopened the history and returned exact first, relay and changed carrier
bytes. The first and relay typed inboxes are 32,020 and 32,075 octets;
the changed-source inbox is 32,020 octets. Original Q bytes are
`831c48795503e74ed5bf6cd0a375b1d4c7d4b88a990f99156b4bd9c6ec48a5ae`
(SHA-256). First, relay and historical repeat decision reply hex values
compare equal. A deliberately wrong full ML-DSA public-key pin refused
before an intent was written, with CLI exit 1.

The native fn verifier was the frozen developer image at fn `884e4816`
(`/tank/fn/gates/integrate-reader-repair-20260923/build/fn-host-developer`,
launcher SHA-256 `ec8442a896d4b1b1ab242bfe649e5e595567c4bfb278fc7ce4091da581f0680a`,
core SHA-256 `4a49fe97136f8c592464eac64921b02b9f1482d38d90c46b5d219ccebecb17c1`),
with OpenSSL 3.5.8 at `/tank/fn/toolchains/openssl-3.5.8`. Mini compiled
incrementally using Lean 4.30.0 on arm64 macOS and the existing 3,090-object
closure; no second fn image or ACL2 farm run was made. The final measured
Mini binary was `minidregg-fn-portable-inbox-context`, SHA-256
`e9632cd9d8b72afc0669e604cb1e522eb8bc08ea24a0d6e1a19b9bba087aec57`.
Its changed controller and consumer/proof modules typechecked; the native
signed calls were confirmed by the ordinary receiver and their exact inboxes
were read through reopened verified history. SQLite CAS, fsync, OS/process
survival, native signature helpers, and cryptographic primitives remain
trusted physical boundaries; this was process reopen, not an injected
power-loss test.

On the same four-accepted-event synthetic history, one native one-pass
historical repeat took 218.30 s wall, with 210.77 s in Mini consumer history
re-admission, 2.90 s in independently pinned Mini origin replay, 2.22 s in
fn portable verification/source extraction, 1.10 s in grant/decision, and
865 MB maximum RSS. A proof-equivalent direct prepared-cell selector reduced
that repeat to 177.58 s, with 168.29 s in Mini replay. A Boolean physical
shape check that shares its derived write list and has a Lean theorem iff
for the original `PhysicalShape` proposition further reduced it to 170.95 s
wall, 161.70 s in Mini replay, 2.95 s in origin replay, 3.89 s in fn
verification/extraction, 1.09 s in grant/decision, and 865 MB maximum RSS.
Reusing the exact derived writes and read guards in both the admitted intent
and all charge lanes, with `dataIntent_original_exact` proving complete
intent equality, reduced the same repeat to 104.66 s wall, 97.13 s in Mini
replay. Sharing one exact `PolicyStepContext` per authorized leg further
reduced it to 83.15 s wall, 75.10 s in Mini replay, 3.45 s in origin replay,
1.96 s in fn verification/extraction, 1.11 s in grant/decision, and 775 MB
maximum RSS. That final process returned the byte-identical historical Q
and emitted no new intent. The exact first/relay/conflict calls were generated
before these representation changes and successfully re-admitted by the
resulting binary. Four-event conflict inbox export, run at the intermediate
170.95 s version, took 163.64 s wall. A 4-second macOS `sample` of that
intermediate repeat found its active stacks under
`NativeHostReplay.derive → DeclaredResourceController.physicalShapeCheck →
writes → ResourceBirthCodec.physicalRoot → Sp800185Cshake256.absorbPadded`.
The final binary's `consumer-export-reply` separately re-admitted all four
events in 78.47 s wall and returned the exact original Q bytes. A 5-second
sample during that final replay had 2,635 of 3,599 stacks under
`NativeHostReplay.derive → DeclaredResourceController.prepare/collect →
prepareTarget/computeTarget`, including repeated
`HyperdocumentContentPageMaterializer.rootBytes → Sp800185Cshake256`.
`Materialized.root` re-encodes and re-hashes its complete logical content
page by definition; no cross-call cached root representation is yet proved.

The final repeat timing invoked the exact native host with
`/usr/bin/time -lp minidregg-fn-portable-inbox-context CONSUMER-CONFIG.json
portable-consumer-decide ORIGIN-PIN.json FN-PIN.json CLAIM.json POLICY.json
CARRIER.eml INTENT.bin DECISION.json`. The synthetic consumer configuration
at `/tmp/mini-fn-portable-inbox-native-20260923/deployment/pinned-config.json`
had SHA-256 `a5deb16b0e5cb03becf5a2b2c2d8efbb632fd56a56cb635a0606f5a3678eec67`;
the original Mini origin pin and fn keyset pin had SHA-256
`259b821fb87d2728a4d07a039509cc5763d7a40d17583dd82ed7a6d67eca324b`
and `f7640d305ae1a6c02fb2800f8aa36c258a2027384ead980eb7711e570d221cdd`.
The original carrier is the fixture's `first-carrier.eml`, SHA-256
`dc5c8b864227ad808f8feef7b574bce6d8be2f1798ca1a3db8c14a7e63872e1e`.
The final four-event SQLite byte image was 461,188 bytes, SHA-256
`9cd1a733e7ad00370428fc6b376009b4eda0f5795f80b416059b3fe2f2829880`.
These scratch pins and image are not published in the fixture, so the public
packet preserves the exact signed calls and exports but is not a turnkey
recreation of the native process run.
The bounds are 32,768 carrier octets, 36,864 typed inbox octets, 18,432
binding octets and 16 accepted consumer events; these timings cover two
about-30 KB retained carrier atoms, not a scaling study. This remaining
Lean hash/re-admission cost is a practical performance gap before a live E2
consumer. A separate native Lean 4.30.0 cSHAKE benchmark over the exact
32,020-byte first typed inbox took 180.1, 182.3 and 180.7 ms for three
hashes. Its 16,010-byte prefix took 92.5, 91.9 and 92.4 ms; a 64,040-byte
double copy took 375.1, 378.8 and 375.5 ms. A single 30 KB hash therefore
does not explain the 75.10 s Mini replay, and these three sizes are near
linear for the hash alone. The sampled replay repeatedly reconstructs
content-resource physical writes and hashes their canonical post images;
the exact dynamic call count remains unmeasured. The actual Rust SQLite
byte-store CLI on the same synthetic 461,188-byte image took a median
4.84 ms for seven `read-to` processes, 4.14 ms for seven exact already-present
CAS calls, and 12.83 ms for seven installed CAS calls on isolated clones
with a one-byte-distinct **opaque** proposed value. These are physical
store timings, not Mini semantic admission of that distinct value; they
separate the dominant Lean replay work from SQLite on this Mac.
