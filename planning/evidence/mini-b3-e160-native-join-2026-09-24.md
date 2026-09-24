# Mini B3 reply: isolated native join on frozen e160442f

The synthetic Mini reply join passed against the already-qualified fn production
image in `/tank/fn/gates/luna-feature-e160442f`. It did not modify the live
`/tank/fn/node` service. This is evidence for one exact Mini reply and one fn
owner: Mini durably prepared and signed its reply, reused the signed slot in a
separate process with nonexistent private-key paths, and called native
`hybrid-author` successfully. The fn fixture stopped the owner, reopened the
Store, read `ARTICLE`, checked the authored source and complete public keyset
through native `hybrid-verify-source`, and obtained `HDR :fn-verified` ending
`keyring 1`. The test exited 0 (`Ran 1 test in 118.621s`).

The fn source is `e160442f`. Its four-job default, DTN and ACL2-test proof
manifest is `certify-20260924T031327Z-785374.json` under the gate's
`planning/evidence/manifests/`, SHA-256
`0d74ea04d26daf5140ced0e7b2de553f3400b15699c6604e08a0d1833e707fe8`.
The production launcher `build/fn-host` is SHA-256
`2ca6ce83f5d8e9598e0af74f77b49130ed02738d79e828e6498909e6c0081e57`;
its core is SHA-256
`9a1cd1fb267878b1134166a77aab0081236e783a5d8ff2a3edafb33a38720a4e`.
The native fixture copied from Mini commit `8eaa8fe` is
`tests/test_native_hybrid_b3_handoff.py`, SHA-256
`4925042545d8a6dbb6448aed419e1086c4348e91a9d25b03e86265558c4ee494`.
The selected OpenSSL is the pinned
`/tank/fn/toolchains/openssl-3.5.8` (OpenSSL 3.5.8, built 2026-09-22 20:33:55
UTC), with its `lib` selected from the outset. The Mini executable was built
from Mini code commit `1eb84a9a46e08aa423a99e39ad74a9be538b5385`, SHA-256
`11f451f7c14d55efcb16ee16f99bfffc20f551a7ebf173d5090966e1434f68f9`;
its 158-module Lean 4.30.0 build manifest is
`/tmp/mini-b3-native-build-1eb84a9/manifest.txt`, SHA-256
`ef9c3d923184218e2d12e9974538aa0d51b8d43161a85fe788da1ab409137265`.

The exact fn invocation from the e160 gate was:

```sh
FN_RUN_HYBRID_E2E=1 \
FN_NATIVE_HOST=/tank/fn/gates/luna-feature-e160442f/build/fn-host \
FN_TEST_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl \
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib \
FN_B3_HANDOFF_DIR=/tank/fn/gates/luna-feature-e160442f/build/mini-b3-handoff-retry-1 \
ACL2_CUSTOMIZATION=NONE \
python3 -m unittest tests.test_native_hybrid_b3_handoff.NativeB3Handoff.test_mini_reply_post_and_reopen -v
```

The gate captured the invocation's stdout/stderr in
`build/freeze/b3-e160-owner-retry-1.log` (SHA-256
`65061a383d69c7d930265b2d86c2df95c17e3c07b4a22ff21056d2a05ae21f37`)
and exit code 0 in `build/freeze/b3-e160-owner-retry-1.exit` (SHA-256
`9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa`).
Under `build/mini-b3-handoff-retry-1/`, the exact files and SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| `ready.json` | `50b070b71c912fab23c820579cb4b42d862de168cb079332efe3518cc9a4ec9f` |
| `mini-finished.json` | `a88a6803df6bd3519823b826a313b78fa762957906011b0655331819f0882ae8` |
| `posted.source` | `b8783ccbdcf21fdaf403ad24a1b6461b5a5f131781de24ade972668ebc7a28f6` |
| `reopened-carrier.eml` | `b365b1d23c4f13d1046e2c0746bd170ca199e464a4e9dd97790ee20a98c2efd1` |
| `verified-source.txt` | `fd4a4745238ad47fbb9c164d233f7ee0a4b7689c5e81e5813d4178fd1bcaca95` |
| `owner-timings.json` | `f494af1f9167028c10e0da304ce8d32cab56bdc70fa720e8eccb196f20432632` |

The owner measured 115.706 seconds from publishing `ready.json` to seeing
Mini's atomic finish marker, 0.057 seconds to stop, 0.105 seconds to reopen,
and 0.112 seconds for native readback. The marker alone is only a handoff; the
owner test's cold readback and native verifier provide the fn-side result.

An earlier attempt, retained separately, reached a durable Mini prepared plan
but native `hybrid-sign-carrier` refused it because that exact source lacked the
required `Date` field. It created no signed slot and posted no article. The
deliberately stopped fn owner log is `build/freeze/b3-e160-owner-2.log`, SHA-256
`4fc20b2ee2e95dc0874c028b8757e57aa7ed57672e94cb50374ae3b5ef9b8f9e`.
Mini's retry used a new Date-bearing source and v2 Message-ID; the old refused
prepared slot was preserved. This e160 result is not a source-matched claim for
the later topic/index/BP-fragment image, nor a public-network exchange.
