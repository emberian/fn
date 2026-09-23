# E1 portable fn inbox, Q and conflict native evidence (2026-09-23)

Mini source `32ea942e70917248b2c6b936d0802c045b316746` in isolated
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
Mini binary was `minidregg-fn-portable-inbox-cached`, SHA-256
`af36badee9dea58c4c9b58952269986394444ce9598f00efe43fdad9ab3d621b`.
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
The exact first/relay/conflict calls were generated before those two
representation changes and successfully re-admitted by the resulting
binary. Four-event conflict inbox export took 163.64 s wall. A 4-second
macOS `sample` of the final repeat found its active stacks under
`NativeHostReplay.derive → DeclaredResourceController.physicalShapeCheck →
writes → ResourceBirthCodec.physicalRoot → Sp800185Cshake256.absorbPadded`.
The bounds are 32,768 carrier octets, 36,864 typed inbox octets, 18,432
binding octets and 16 accepted consumer events; these timings cover two
about-30 KB retained carrier atoms, not a scaling study. This remaining
Lean hash/re-admission cost is a practical performance gap before a live E2
consumer. A separate native Lean 4.30.0 cSHAKE benchmark over the exact
32,020-byte first typed inbox took 180.1, 182.3 and 180.7 ms for three
hashes. Its 16,010-byte prefix took 92.5, 91.9 and 92.4 ms; a 64,040-byte
double copy took 375.1, 378.8 and 375.5 ms. A single 30 KB hash therefore
does not explain the 161.70 s Mini replay, and these three sizes are near
linear for the hash alone. The sampled replay repeatedly reconstructs
content-resource physical writes and hashes their canonical post images;
the exact dynamic call count remains unmeasured. No SQLite time was inferred
from the replay sample.
