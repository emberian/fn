# Native anchor primitive evidence — 2026-09-21

Implementation revision: `88b0cd3` (`w14/native-primitives`).  The evidence
record is a later commit; no implementation or test source changed between
that revision and these runs.

## Exact source set

| File | SHA-256 |
| --- | --- |
| `host/native/crypto.lisp` | `4ee2a19a83d825ecbed8b0f70518411ae4c7597547318e3b8c8d653a3bf83192` |
| `tests/native_crypto_primitives.lisp` | `84731bd485a25384dbdf71bd6d5d0e3300e3e6cb344b495295ad16120edc1297` |
| `tests/native_crypto_saved_image.lisp` | `a2ea2018798794c04a560f14fb92fffcc14784d6926999072f60f021203adf9a` |
| `tests/test_native_crypto_saved_image.sh` | `6310c2420916bd643d843aa61d1db6812ec8cdfa020c307dc32e2709aac73073` |

The four hashes were recomputed on every host before execution and agree in
the archived logs.

## Invocations and results

On `nextop.local` (Darwin 25.6.0 arm64, SBCL 2.6.8, libsodium 1.0.22):

```sh
sbcl --noinform --disable-debugger --script tests/native_crypto_primitives.lisp
tests/test_native_crypto_saved_image.sh
```

Both printed their `passed` marker.  The complete output, tool versions,
timestamp and source hashes are in
[`2026-09-21-native-crypto-primitives-nextop.log`](2026-09-21-native-crypto-primitives-nextop.log).

The same four files were transferred without transformation to each Linux
host with:

```sh
tar -cf - host/native/crypto.lisp \
  tests/native_crypto_primitives.lisp \
  tests/native_crypto_saved_image.lisp \
  tests/test_native_crypto_saved_image.sh | ssh HOST '... tar -xf - ...'
```

Inside each temporary directory the two commands above ran.  `hbox` used
SBCL 2.2.9.debian and libsodium 1.0.18; `persvati` used the project's SBCL
2.6.8 and libsodium 1.0.18.  Both commands printed their `passed` marker on
both hosts.  Exact environment/output records:

- [`2026-09-21-native-crypto-primitives-hbox.log`](2026-09-21-native-crypto-primitives-hbox.log)
- [`2026-09-21-native-crypto-primitives-persvati.log`](2026-09-21-native-crypto-primitives-persvati.log)

The component vector run covers the RFC 8032 empty-message Ed25519 vector,
tampered signatures, shorter wrong widths, over-bound widths, malformed and
over-bound messages, the FIPS 180-4 SHA-512 `abc` vector, the two signatures
from the committed int08h response, and that response's one-nonce leaf/root.
The saved-image run serializes deliberately stale `:ready`, library and version
values, restores the core, calls `fnn-crypto-startup`, checks those values were
replaced, and calls SHA-512 through the new process binding.

Finally, the source was loaded in ACL2 8.7 raw mode under the existing
`:fn-native-host` trust tag, `fnn-crypto-startup` ran, and a wrong-width
observation returned `:refused`:

```sh
python3 tools/acl2 --timeout 60 < /tmp/fn-w14-crypto-driver.lsp
```

The complete transcript is
[`2026-09-21-native-crypto-primitives-acl2-package.log`](2026-09-21-native-crypto-primitives-acl2-package.log).

## Scope and limitations

This establishes that the bounded FFI seam produced the selected known answers
and restarted its dependency checks on these three installed systems.  It is
not a proof of Ed25519 or SHA-512, unforgeability, collision resistance,
library correctness, side-channel resistance, or platform qualification.
`hbox`'s SBCL is deliberately reported rather than treated as the selected
runtime.  Packaging still must pin/install the native dependency.

No native Roughtime wire parser, server configuration, UDP acquisition, OS
nonce source, FNAN persistence/recovery composition, or STARTTLS integration
was exercised.  Those remain the dependency gates stated in
[`planning/lanes/HANDOFF-w14-native-primitives.md`](../../planning/lanes/HANDOFF-w14-native-primitives.md).
