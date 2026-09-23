# Mini E1 P1 synthetic consumer operation, 2026-09-23

This local experiment processed the public `DREGG/FN/NATIVE-PREFIX/v1`
fixture into one Mini operation binding and immutable application reply Q.
It is not a live fn consumer, fn attribution verdict, fn acknowledgement,
application publication, SQLite power-loss test, or production authority
claim. The origin package is `tests/fixtures/dregg-e1/package.bin` (16,136
bytes, SHA-256 `1bea29c16a63e8722f1567705b7b58e6ccdd7a8d5872d6b6f8c4b10d396f612b`),
verified by the source-owned Lean P0 re-admission route against a separate
origin pin. The consumer store, key, and local grant were generated in
scratch; its public genesis, signed calls, reports, decisions, Q, and outcomes
are in `tests/fixtures/dregg-e1/consumer-p1/`. No private key or SQLite file
is included.

Mini source is isolated worktree branch `implement/fn-evidence`. The native
host was built source-matched at `4b480472ff8c6aa57d43e007e74dc779986ca691`
with Lean 4.30.0, `MINIDREGG_NATIVE_JOBS=2`, `MINIDREGG_LEAN_THREADS=1`, and
`scripts/build-native-host.sh --output /tmp/mini-fn-consumer-build-20260923
--binary .lake/build/bin/minidregg-fn-consumer`: 156 modules, 3,089 objects,
827 seconds, binary SHA-256
`6b6d8e965a256d1671875651bc5fe13f829e686542aa82d942d74eeb1bab5c2b`.
The source-owned `Kernel/FnConsumerOperationProofs.lean` typechecked separately
with `lake env lean`; it contains properties of the actual `decide` called by
the host, not a theorem about Rust or physical CAS. The Rust resource client
`cargo test --locked` passed four tests and `cargo build --locked` passed.
The existing native SQLite CAS and signature helper were reused. This run
did not build an fn image or use the ACL2 farm.

The bounded adapter fixes one operator-selected application/subject/target/
capability and verifies the origin package before proposing a command. Its
operation nonce derives from consumer domain, semantics, application, and
operation, **without fn source identity**. A single signed content-resource
invocation creates a typed binding atom and Q outbox atom. The native
transaction ID/nullifier protects that stable operation key. A changed
source produces a separate conflict-evidence atom with an odd, domain-
separated nonce; it cannot change Q. The accepted signed event, rather than
the mutable page view, is used to recover Q on repeat. The Lean lemmas show
that an occupied marker cannot yield `fresh`, an exact repeat returns the
historical Q regardless of the new receipt argument, a changed source with
unrecorded conflict yields a conflict command, and binding, reply, and
conflict atom ID spaces are disjoint. They assume a matching accepted record;
collision resistance, native storage durability and external fn verdicts
remain trusted or open boundaries.

Both reports were decided and fully signed against the **same pre-state**
(one accepted consumer birth), each yielding `proposed-fresh`. The first
exact signed call was submitted after its preparing process exited and was
confirmed installed: transaction
`6935962946850994493358818796364126622182079017445341163948051629819780947714`,
event `75578360998625731239914702394451842210961386392086364192676736610603675457185`,
accepted count 2. The second independently signed stale call was then
submitted unchanged. The normal native receiver returned `refused` in the
admission phase and retained accepted count 2; it did not install a second
binding or Q. Its public refusal intentionally gives no precise cause, so
this run cannot assign that outcome specifically to the nullifier versus a
stale target root. The atomic receiver refusal, after both pre-state
decisions existed, is the observed guard against stale duplicate effects.

A new process reopened the consumer history. The original report returned
`historical-repeat` with byte-identical Q (181 bytes, SHA-256
`ead60ad3664379a503b23d93fc9c8bb37bc47688efb7d0f6f7480c661ab573c8`)
and no proposed intent. The changed-source report returned
`proposed-conflict-evidence`. After updating only its current root inputs, the
normal signed invocation confirmed a separate conflict event, transaction
`52713167064705379793660491453934525888181489397575980458336937544816850712658`,
event `47878756744344525981951091939236310839541027222764878097962685861921809279403`,
accepted count 3. Reopen again returned `historical-conflict-evidence` for
the changed source and `historical-repeat` with the same Q for the original.
An authorized resource query showed exactly three page atoms: binding, Q,
and conflict. Its root was
`73684348973737230312339583175232225755280283544428454201961302628661893526514`.

The local-policy negative changed report capability 61 to 999 while policy
remained 61; `consumer-decide-test` refused before an intent was emitted.
The current-grant negative selected capability 999 in both policy and a new
operation report; the adapter proposed a fresh intent, but the ordinary
native observation stage refused because that capability was unavailable.
No signed call or accepted event followed. This distinguishes a local
namespace/grant mismatch from actual current authority admission. A repeat
returns an already accepted Q without invoking a new effect; it must not be
treated as proof of current authority for another action. The prepare/exit/
retry test exercised exact-byte process reopen, not injected process death
inside CAS or a power-loss cut.

| Public artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `consumer-genesis.bin` | 1,944 | `339c8e7aabefc6616858ee2ed0702c0152c7cb9963750ca014d162bfe7666827` |
| `signed-consumer-birth-call.bin` | 5,217 | `c035c67a7cc518e2703569629acc8421fd6fadd732bc53a1391e10ea6d6c6320` |
| `signed-first-call.bin` | 17,847 | `1b6e5046e7b099181cc6cbdee9358ff8c5dd0fba66ab0357f354a6fb74ba1247` |
| `signed-stale-second-call.bin` | 17,828 | `b165fcbd0d896839a0385e1c8af4431cba805d07f56bc4cd6b12fd4ed042e417` |
| `accepted-first-outcome.bin` | 132 | `ef8f21c07b1468dbd7e65da12550a31e2f3f330ce7b755dc3b1de518d334b4cd` |
| `refused-stale-second-outcome.bin` | 58 | `cad60ad085bd57da8465cc0a556adaf35547ac11efba9191fbcc688d9c809b22` |
| `signed-conflict-call.bin` | 17,463 | `60ae4ca3d856190795ff7a5f979faecd99d09ee3671d766f2da57472664ace44` |
| `accepted-conflict-outcome.bin` | 132 | `0d664f5a18926e7dbc214e96dda31d480d6ad975a789c873e799dd89abf37be1` |
| `reply.bin` | 181 | `ead60ad3664379a503b23d93fc9c8bb37bc47688efb7d0f6f7480c661ab573c8` |

The synthetic `Provenance` currently holds fn history/incarnation, opaque
source identity and a verdict reference supplied by the trusted test
adapter. It does **not** yet carry or independently verify fn's exact article
carrier, Message-ID, local memberships, Store sequence/transaction ID/cursor,
or T10 historical authorship verdict. The planned E2 fn cursor/ack remains
separate: its durable progress is not proof of Mini execution. Production
ingest must add and check those fields and current application grant, then
ack fn only after Mini's own durable inbox/operation/outbox decision. A
durably stored, exact signed fn reply carrier is a later publication step;
neither these Mini reply bytes nor an fn transport attempt ACK perform it.
