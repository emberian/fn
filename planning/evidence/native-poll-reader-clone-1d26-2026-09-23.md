The integrated source `1d26e01f` passed full incremental ACL2 qualification on
hbox in run `run-20260923T232217Z-137f`, manifest
`build/acl2/certify-20260923T232249Z-467250/manifest.json` (534 matching
cached books, 17 newly certified, no failures); `make check` passed. The exact
native source snapshot at `/tank/fn/gates/poll-live-group-native-1d26-20260923`
has 2,775 files and SHA-256 file-list aggregate
`ea189de6f208d6bc40b54cfce767467b48f00a1f55ef7d60c2dc86ff79a48db8`.
The default artifact acquire loaded composed set
`87229008d4f487bfd603f684fee1be40d0448d6c83ce6385a5a7783013897ac0`
(223 books, no rejected candidates), and validation loaded all 88 production
image roots. The pinned toolchain was w28 ACL2
`/tank/fn/toolchains/w28/acl2-literal-4g` (identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`)
and OpenSSL 3.5.8. `swarm-build` produced production core SHA-256
`f120c0201baad1fb77b71b03568189a134b6d6be00606a202bb838f2279ec618`
and developer core SHA-256
`177c47f453e9d65c126a62bee664fe77a80a624fcdd0c4c2fe0a0a82810a48a7`.
These synthetic local images were not deployed.

The exact source driver `tests/test_native_reader_index.py` SHA-256
`62da466617897a76e36b7cc9e761ec9518bd608f16232672ae15431457b043d3`
passed all three saved-image tests with `FN_RUN_NATIVE_READER_INDEX=1` and the
production core in 5.684 s. It includes live group creation, historical
LISTGROUP pins across posts/restart, 24 groups and 96 LISTGROUP commands, and
96 concurrent Message-ID STAT reads. The socket workload reported 0.066 s
for the 96 LISTGROUP commands and 0.022 s for the STAT reads; these are
measurements, not a latency bound. Exact log:
`native-1d26-reader-pass.log` SHA-256
`0cb025be448940123f9d78f618377547f0b087c45a74e40336abc790fe024912`.

The signed E1 source poll, ACL2 exact `fn-e`/source binding, repeated read-only
poll, durable advancing ACK with killed reply, and reopened position/no-repeat
passed in 14.835 s with the developer core, `FN_RUN_CONSUMER_E2E=1`,
`FN_RUN_CONSUMER_POLL_E2E=1`, w28 ACL2 and pinned OpenSSL. The first run using
the frozen source driver SHA-256
`3ae5005836eebecbe586e12ccc8dfdaff9d05c20615618dcb068d4297afbe92f`
reached the assertion after a successful native poll but errored because the
Python test constructed an ACL2 `let` with one missing close parenthesis;
`native-1d26-e2-original-driver.log` SHA-256
`1993e4e194bb5bce67bc730cf2f3b7918da04c0af3e65f94823aab5d28a8ce5b`.
The test-only driver at commit `956199e4` has SHA-256
`d7769e8ad28a23567dc0303427e09a2d4bd5223c744b786fcf93cff032972a4a`;
it closes that `let` and exports the registration cursor captured before the
post. It ran as `tests/test_native_consumer_e2_scope_followup.py` with the
unchanged core; exact passing log `native-1d26-e2-scope-pass.log` SHA-256
`8ced9963404d835c123a83bcb68e43ba80f3c7d15c7ccb5ca8cd2e76d78ef159`.

The public synthetic E1 fixture is at
`/tank/fn/gates/poll-live-group-native-1d26-20260923/build/consumer-poll-scope-fixture/`:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `registered.fncu` (pre-poll scope pin) | 108 | `b3aebae694f47435d673fecb9d3da0e49386c59011d8c742b2a7724f92907882` |
| `continuation.fncu` | 108 | `bcc39947683051abb824c6209ba90937aa5a2a1a203f8ce922fd930519316ab1` |
| `accepted.fn-e` | 53,043 | `c7715fc2f4a6b93ec768b2f3e129dd3b365ff394d509d5e83bed7f6095436b05` |
| `authored.source` | 22,393 | `fca9c81e8cd02281b3703df4e931ae82c55a0bda63b3cf3447c8e32e13199000` |
| `principal.bin` | 32 | `84126d0dd850199be29021aadbaee68cb9199047b1cb7ec9894ddb1e3562783c` |
| `ed-public.bin` | 32 | `21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9` |
| `ml-public.pem` | 2,726 | `d8d8d95f4988bc2879f58b3cc8c85ff55bc5ea00b77decc48922005ce4e4e33d` |

`consumer-project` on the exported cursor and event exited 0; its exact line
is `build/freeze/consumer-project-scope.log` in that gate, SHA-256
`ac6dc5d8c9edfc9912536e1ff8d641947d638110811533ece72abc246e9998f6`.
That projection alone establishes structure of supplied bytes; the tested
local poll is the Store admission observation. The synthetic owner and Store
were cleaned after the test, so this fixture is for offline downstream joins,
not a live control endpoint or deployment pin.

The same core and test-only driver also admitted the public
`tests/fixtures/dregg-e1/portable-consumer-p2/changed-source.eml` source in a
*separate* synthetic Store. It differs from the first authored source at one
Message-ID byte; this establishes a second exact source/poll/ACK/reopen trace,
not a conflict outcome in one Store. The run passed in 13.008 s; exact log
`build/freeze/e2-poll-changed-source.log` in the gate has SHA-256
`d797e840b1a46234bc61829fec1c89f63620f53a41ecc21533b09346c6768eba`.
Its export directory is `build/consumer-poll-changed-source-fixture/` in that
gate: `registered.fncu` 108 bytes SHA-256
`3072aa3035306c42dfa583c626cda7593b6c33c851c5dd1df8f865d2324ea8d4`,
`continuation.fncu` 108 bytes SHA-256
`f79e8a52dfd628981cd5e2f42b6a5b951d40e5ecf4c6a69dec3c94d91e3583a8`,
`accepted.fn-e` 53,043 bytes SHA-256
`bcd6bcef45d1b7fb5177a9dea70e9d2abd57a68e4ee4a83675039c3809d5ff57`,
and `authored.source` 22,393 bytes SHA-256
`59593ab7d010b7af2ab9085cee9052fda2c9c5d501415285ce209c6d15472534`.
The separately generated ML public PEM has SHA-256
`069ce9772c1588f032b53cf500fe59a75fb7a7005db1bf2d4b162ffcea23388c`;
principal and Ed public key bytes match the first fixture. `consumer-project`
exited 0, projection log SHA-256
`78b521bff429ff4bb9beaff61f9bbdb265c2e90cb97dfaa3bc7f797c5eafcc69`.

The exact frozen clone driver `tests/test_native_checkpoint.py` SHA-256
`c89a056a69b2786d34bc0cda07e3b24458d14aeebc57eeda0318be9df5a0bb34`
passed canonical parent alias and historical authorship verdict clone cases,
but its advancing-ACK case expected seven physical records where the native
Store reported six: zero-position ACK is a no-op, while the later advancing
ACK is durable. Original log `native-1d26-clone-original-driver.log` SHA-256
`5599613503d2c1ac3b2f1b0becb3518aabdb6ec351a850202b760dc72fa47db8`.
The test-only correction at commit `1d086655` changed those three count
assertions to six; its driver SHA-256
`775cec4850024e6c9fa593d160d606b50d4539bf93b79c7230bb131f5b76cb5c`.
With unchanged developer core, the advancing-ACK selected-pack/reclaim and
fenced clone death cuts plus the two independent cases all passed (3/3,
4.561 s); exact log `native-1d26-clone-pass.log` SHA-256
`c7fc810ce0e2d597f1ce454b28720c9a020a92dfecd1574507112b214f2a547d`.
