# Synthetic live fn consumer to Mini durable ACK, 2026-09-24

The live E2 join passed in an isolated synthetic fn Store. Mini consumed one
authenticated Store poll through the same-UID local control socket, committed
its signed operation and immutable Q in its own durable history, reopened that
history, then issued fn's advancing ACK. The same live fn owner returned the
ACK cursor at `consumer position` and an empty repeat poll. The owner test
completed its subsequent restart/no-repeat checks. This was not the live
`/tank/fn/node` service and was not a new native image qualification.

Fn used the existing source-qualified `1d26e01f` developer image at
`/tank/fn/gates/poll-live-group-native-1d26-20260923/build/`. Launcher SHA-256
`177c47f453e9d65c126a62bee664fe77a80a624fcdd0c4c2fe0a0a82810a48a7`;
core SHA-256
`12e223e3207341f8456a8d8d09d1a281b8efed56a5159f4cff9c223f9fd4d75f`.
The isolated source/test gate is
`/tank/fn/gates/mini-live-join-1d26-20260924/`. Its base source was copied
from the 1d26 gate without the image. The committed test-only handoff additions
are `63b4699e` and `d4c40484`; their combined driver SHA-256 is
`4a25623eccf524d08398e69993d92038c7382a8f527ec0c5eb3a4ac3bacbd573`.
The running driver SHA-256 was
`882327eabe4856ec17f585d0223698f23ce59d6a9dac4899ada17751a2b03ab0`.
Its sole further change printed the raw ACL2 result before retaining the same
boolean assertion; its exact bytes are archived at
`build/freeze/test_native_consumer_e2_running_diagnostic.py` in the gate.
`tests/native_process.py` SHA-256 was
`0cc6f659c159f20cea742e778af956d5d60ab11b5d7777b853a574f9d7abf13a`;
`tools/run_store.py` SHA-256 was
`e4515d5af906649d854e33ca04164c20f6b4c054f5746de45072a13a73b103cc`.
The signed source was the original unsigned public Mini E1
`tests/fixtures/dregg-e1/source.eml`, SHA-256
`fca9c81e8cd02281b3703df4e931ae82c55a0bda63b3cf3447c8e32e13199000`.
Runtime pinned w28 ACL2 at `/tank/fn/toolchains/w28/acl2-literal-4g`,
OpenSSL 3.5.8 CLI at `/tank/fn/toolchains/openssl-3.5.8/bin/openssl`, and
`LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib`.

The fn owner published `ready.json` by same-directory rename, SHA-256
`60deb4f591e9a17e92e92a827971af341a71047ea2554b9215ffc2b66f98a138`.
Mini source `d90b18ab459e8cfb4e935cd75bf250a3b2b469ed` passed
`lake build minidregg-host` with Lean 4.30.0; native binary SHA-256
`64d27b25c67cb28107c8eea2f003b673418ca617ab0ca22c9700284c9aa2e386`.
Mini driver SHA-256 was
`5c6e6ffe8cb948a779f263076d807f1f63bb74c8f6bad6f15a2c1f8451bad805`;
bounded SSH shim SHA-256 was
`d77b69e48e58dbd9c61bbb93c5dc75076a31f7f383b150b6169ea4f1bd70df54`.
The shim transported bytes and checked fn's post-ACK position and empty poll;
it made no Store or Mini operation decision.

Mini observed the exact Store event through native `consumer poll`, ran ACL2
`consumer-project`, verified the portable authored source with native fn,
re-admitted the separately pinned Mini origin and checked its local grant.
The selected decision was `proposed-fresh`, with Store sequence/txid 3/3.
Mini `submit --intent-kind binary` confirmed signed transaction
`22678727908680307285286663340486134448208253926548865573615580900981947362607`
with two accepted events. After reopening, Mini exported the exact fncu
(SHA-256 `1d51312a22e3a37aa7f586e13376f7764bdb8fa5434ea9f6619a9c80978ba308`),
fn-e (SHA-256 `f8223142643490a253553a9324ffe6626b0fa84ccffa4d4768762f5de6c3f4bf`),
and immutable Q (SHA-256
`80be18c5816a6dcb71e4567c47f2a925bb5a98a2514a95d26d630223fd46c777`).
Its reopened `consumer-ack-poll` received `fnAck=durable-accepted`; the shim
then checked same-owner position equality and empty repeat poll before writing
the atomic completion marker, SHA-256
`7134fe6667b4b2287cb806d21d2f2488b9b2077f52c6b8e06b16a4aa27c1cc13`.

The fn test finished `OK` (one test in 209.942 seconds, exit 0). Its log is
`build/freeze/mini-live-join-diagnostic.log` in the gate, SHA-256
`a162aa9c80b4c37c3670d9a57c0467e653e4defa0c46d327383d23a376dbbe9a`.
After Mini's advancing ACK, the test's killed reply exercised an idempotent
duplicate ACK, so the original positive lost-reply cut belongs to the prior
1d26 campaign. The Mini raw non-secret run archive, selected pins, driver,
shim, and SQLite byte image are at `build/mini-evidence/` in the gate.
Its 73-file SHA-256 manifest is `build/freeze/mini-evidence.sha256`, SHA-256
`b6a41995b265d8d30be80172b89e9781d938ee8f457210425ab10940f2b0e03e`.
Mini's scoped record is `docs/FN-E2-LIVE-2026-09-24.md` at commit `11d57c3`.

Two setup attempts stopped before handoff: one lacked the OpenSSL library
path; another supplied an already-signed carrier or the tiny default source
to `hybrid-author`. A later unsigned-source attempt reached the ACL2 exact
source assertion but returned a non-boolean; that raw ACL2 output was not
captured, so its cause is open. The final driver added only raw-result logging;
that assertion returned `T` and no condition was bypassed. The failed
pre-handoff log/exit file remains in `build/freeze/` and is distinct from the
passing diagnostic log/exit file.

The fn scope and key pins came from this synthetic native fixture. Mini's
origin and grant were selected separately. The run does not establish an
independently auditable fn Store certificate, a posted fn reply article from Q,
exchange between two administered Stores, physical power-loss durability, or
deployment readiness.
