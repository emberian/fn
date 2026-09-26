# crypto-deps: no OpenSSL 3.5 (HST-016), 2026-09-26

D35 (the release is the product), ember's request: a node builds and runs
against the system's TLS library plus libsodium plus a vendored ML-DSA-65,
so the release bundles no OpenSSL and an OpenBSD friend needs no source
build of one. Lane `lane/crypto-deps` from dev `8dc094f93`.

## Symbol inventory (before this lane)

| Class | Library | Symbols |
| --- | --- | --- |
| TLS | libssl/libcrypto | `TLS_server_method`, `TLS_client_method`, `SSL_CTX_new/free/ctrl/use_certificate_chain_file/use_PrivateKey_file/set_default_passwd_cb/check_private_key/set_verify/load_verify_locations`, `SSL_new/free/set_fd/accept/connect/set1_host/ctrl/get_verify_result/get_error/pending/read/write/shutdown`, `ERR_clear_error/get_error/reason_error_string`, `OpenSSL_version(_num)` (host/native/tls.lisp) |
| Ed25519 | libsodium (already) | `crypto_sign_verify_detached`, `crypto_sign_detached`, `crypto_sign_keypair`, `crypto_sign_publickeybytes/bytes`, `sodium_init`, `sodium_version_string` |
| ML-DSA-65 | libcrypto 3.5 EVP | `EVP_SIGNATURE_fetch/free`, `EVP_PKEY_CTX_new_from_pkey/new_from_name/free`, `EVP_PKEY_sign_message_init/verify_message_init/sign/verify`, `EVP_PKEY_keygen_init/generate`, `EVP_PKEY_new_raw_public_key_ex/get_raw_public_key/free`, `PEM_read_bio_PrivateKey/PUBKEY`, `PEM_write_bio_PrivateKey/PUBKEY`, `BIO_new_file/new/s_mem/ctrl/free` (signatures.lisp, peer-invite.lisp) |
| Hashing | none from OpenSSL | SHA-512 is libsodium's `crypto_hash_sha512` (anchor); SHA-256 is ACL2's `books/sha256.lisp` |
| Randomness | none from OpenSSL | `/dev/urandom` (anchor.lisp, io.lisp, admin, auth-admin, owner) |

So only ML-DSA-65 needed OpenSSL 3.5; the 3.5 floor was imposed on TLS
because signatures.lisp shared TLS's loaded pair.

## What changed

- `third_party/pqclean-ml-dsa-65/`: PQClean `crypto_sign/ml-dsa-65/clean`
  plus `common/fips202.{c,h}`, `randombytes.h`, unmodified, at upstream
  commit `0586a824fc0d49df0b6b6e9179d8d15d06d0974f` (2026-08-04), licence
  CC0; `UPSTREAM.txt` has the commit and each file's SHA-256. It is FIPS 204
  final: `crypto_sign_signature/verify` are the `_ctx` functions with an
  empty context, hedged (rnd from `randombytes`), which is what OpenSSL 3.5's
  `EVP_PKEY_sign` for "ML-DSA-65" with no parameters produces.
- `host/native/fn-mldsa65.c` (trust boundary, ~450 lines) +
  `tools/build_mldsa65.sh` -> `lib/libfn-mldsa65.{so,dylib}` beside the
  core. Exported: `fn_mldsa65_public_from_pem(_file)`,
  `fn_mldsa65_public_from_private_pem`, `fn_mldsa65_sign_pem(_file)`,
  `fn_mldsa65_verify`, `fn_mldsa65_pem_from_seed`, `fn_mldsa65_generate_pem`,
  `fn_mldsa65_widths`, `fn_mldsa65_strerror`, `fn_mldsa65_implementation`.
  Key files by exact DER layout (no ASN.1 parser): SPKI; PKCS#8 with the
  "both" (seed + expanded, OpenSSL's default), seed-only and expanded-only
  ML-DSA-PrivateKey choices; a "both" key whose seed does not regenerate its
  expanded key is refused. Strict PEM armor and canonical base64.
  `PQCLEAN_randombytes` is `getentropy(2)`; an injected seed answers the one
  keygen draw for keypair-from-seed. The secret key is read, expanded and
  wiped in C; it never enters the Lisp heap (as with OpenSSL's BIO before).
- `host/native/signatures.lisp`: same Lisp interface
  (`fnn-hsig-ml-dsa-65-public-key/sign/verify/verify-raw/verify-key`,
  observations, the four authorize entries unchanged); loads the library
  from `FN_MLDSA_LIBRARY` or `lib/` beside `sb-ext:*core-pathname*`; no
  dependency on tls.lisp. A load/width failure is `:unsupported`, a key or
  primitive failure `:fault`, never a verdict. `peer keygen`
  (peer-invite.lisp) uses `fn_mldsa65_generate_pem`.
- `host/native/tls.lisp`: accepts OpenSSL 3.0+ or LibreSSL 3+
  (`fnn-tls-supported-version-p`: LibreSSL reports 0x20000000 and names
  itself in `OpenSSL_version`); `*fnn-tls-required-symbols*` is checked to
  resolve at initialization; OpenBSD candidates `libcrypto.so`/`libssl.so`;
  `FN_OPENSSL_PREFIX` optional. No 3.5-only call was used by TLS.
  `build.lisp`/`build-dtn.lisp` call `fnn-tls-initialize` at build (the
  feature check) and at every start, since signatures no longer imply it.
  crypto.lisp gains the OpenBSD libsodium candidate.
- Packaging: `freeze-native-image.sh BUILD_DIR OUTPUT_DIR` (no OpenSSL
  argument), launcher marker `v2` (no `FN_OPENSSL_PREFIX`, `LD_LIBRARY_PATH`
  only `$here/lib`), `lib/` holds `libsodium.so.23` and `libfn-mldsa65.so`;
  `install-native.sh` requires the system libssl (ldconfig on Linux,
  `/usr/lib/libssl.so.*` on OpenBSD) and copies `lib/`; `release-tarball.sh`
  docs; `tools/runbooks/hbox-image-build.sh`, `tests/friends_tarball.sh`,
  `tools/native_two_host_protected_gate.py` follow.
- hbox harness: `tools/hbox_native.sh` no longer sets `FN_OPENSSL_PREFIX`;
  the node runs on hbox's system OpenSSL 3.3.1. OpenSSL 3.5.8 remains only a
  TEST TOOL (independent ML-DSA-65 keys and signatures for the modules) via
  `$FN_TEST_OPENSSL_BIN`, a wrapper giving that binary its own libraries.
- Docs/specs: specs/host.md HST-016 (the table of the three seams),
  specs/identity.md, docs/operator.md, docs/peering-with-a-friend.md,
  docs/agents.md.

## Interop (tests/mldsa65_interop.py)

Both directions against OpenSSL, plus every committed signature OpenSSL 3.5
made. A disagreement is a FINDING (exit 1); none was normalized.

| Where | Reference | Result |
| --- | --- | --- |
| laptop, clang, macOS | OpenSSL 3.6.4 | keys 6 + committed keys 6, round trips 6, fixture signatures 10, findings 0 |
| hbox, gcc 14.2, Ubuntu 24.10 | OpenSSL 3.5.8 (the toolchain that made the fixtures) | same, findings 0; `interop-hbox-3.5.8.json` sha256 `63c23899...a81b` |
| hbox, + `--extra /tank/fn/scratch/fixtures/signed-n1000-2k-32` | OpenSSL 3.5.8 | fixture signatures 82 (the 10 committed + 32 store articles + 40 probes), findings 0; `interop-hbox-n1000.json` sha256 `1c0da9a0...b00b` |

The reports are in `planning/evidence/crypto-deps-2026-09-26/`
(`interop-laptop-3.6.4.json` `8bf6ac4b...c510`,
`interop-hbox-3.5.8.json`, `interop-hbox-n1000.json`).

What is checked: OpenSSL's default private PEM re-encodes byte-for-byte from
its seed alone (3 fresh keys), the public PEM likewise; seed-only and
priv-only PKCS#8 parse and sign (OpenSSL verifies); a seam-generated key's
public PEM is the one OpenSSL derives; for 1, 33 and 70000-octet messages
OpenSSL-signed verifies under the seam and seam-signed under OpenSSL, a
flipped bit is refused by both, a changed message by the seam; the empty
message seam-only (pkeyutl cannot sign an empty input). Committed keys:
`tests/fixtures/topic-history/ml-dsa-65-test-{private,public}.pem`,
`tests/fixtures/dregg-e1/**/*.pem` and `*.raw`, all equal OpenSSL's reading.
Committed carriers: the FN-Authorship articles in tests/fixtures and
planning/evidence (`.eml`, store `.txn`, BP `.adu`, peer invitation, the two
tin wire logs reconstructed from the transcript); six inbox/signed-call
containers whose framing the harness does not decode each hold a
byte-identical copy of a verified article. `relay-carrier.eml` first failed
extraction (an early parse took a truncated article); the harness now keeps
the parse OpenSSL verifies, and a parse only the seam verifies would be a
finding.

## Native (hbox)

Tree `cde3986a5` shipped by `tools/hbox_native.sh --images
developer,production` to `/tank/fn/scratch/crypto-deps/native-cde3986a5c78`;
the node ran on hbox's **system OpenSSL 3.3.1** (no `FN_OPENSSL_PREFIX`).
`LD_DEBUG=libs build/fn-host --fn operator ...` shows the image loading
`/lib/x86_64-linux-gnu/libcrypto.so.3`, `libssl.so.3`, `libsodium.so.23` and
`tree/build/lib/libfn-mldsa65.so` (whose only dependency is libc).
Images: `fn-host.core` `7b51e2c1...0c1`, `fn-host-developer.core`
`bcbdacac...dbb`.

| Module (image) | Result | Log SHA-256 |
| --- | --- | --- |
| tests.test_native_hybrid_author (production) | OK 11 ran | `efcd7f288564157c09dfe8bd590db988d32aa2484df55b9ca13aa141e1780e3a` |
| tests.test_native_starttls (production) | OK 2 ran | `15b6f6a4b3760a55222c4ad3b964f2a11e75293d5c3978e079924b890c49ced6` |
| tests.test_native_implicit_tls (production; the TLS-only listener) | OK 3 ran | `ad5c52826a985f7574f22125520f6ee9e9b5aa1c7275abc2138e7a50b14e2c63` |
| tests.test_native_tls_transport (plain SBCL + tls.lisp) | OK 2 ran | `45dd1499aea324690bcda03e9ae73e3327367d085fd2ec27ccba6b5e4f7d43e1` |
| tests.test_native_friends_feed (production; `peer keygen` on PQClean) | OK 2 ran | `bbdc1006560fa0758fec108382dda4faa3e9cf4a60a5d3190a280d6297c41343` |
| tests.test_native_peer_invite (production) | 2 FAILED: harness | first run; the two crash-cut cases set developer-image selectors (`FN_PEER_TEST_STOP_AFTER_*`) that the production image refuses by design |
| tests.test_native_peer_invite (developer, `--env FN_NATIVE_HOST=$T/build/fn-host-developer`) | OK 6 ran | `c0d458ad95f22e19c569b5aac6a19e177317314c8bbab33f9c5ce26de6734cd7` |
| tests.test_native_friends_accounts (developer; invitation account redeemed over implicit TLS) | OK 1 ran | `c0364eeac749f034a6b9de60a5e383e23a56fa48cd5bb0e124b8de1af60c2e88` |
| tests.test_fn_verify, `FN_RUN_VERIFY_E2E=1 FN_VERIFY_LARGE=1` (node-signed posts, v1 and 200 KiB v2, checked by fn_verify's dilithium-py and pyca, `check-article` offline) | OK 32 ran, 1 skipped (needs an image from before carrier v2) | `6c6224860fc8e52e8a556ea6794ff1f22acbfc5a705285bb2f80a8357f4d509a` |
| tests/native_hybrid_signatures.lisp (plain SBCL, OpenSSL 3.5.8-made keys, no TLS library loaded) | passed | laptop and hbox |
| `sh tests/friends_tarball.sh` (freeze, release tarball, the friend unpacks and runs friends_feed on the tarball's bin/fn) | OK 2 ran, rc 0 | `crypto-deps-2026-09-26/friends-tarball.log` `7583bc51...c5298` |

The tarball `fn-cde3986a5c78-linux-x86_64.tar.gz` (sha256
`5b31306e3009038df7065d9a2de92f5192cc0b8ac9b281c17dee47e3f3614b1a`)
carries `libexec/fn/lib/libfn-mldsa65.so` and `libexec/fn/lib/libsodium.so.23`
and no OpenSSL file.

Classification of the one red: harness (module-to-image mapping in
`tools/native_env.py` gives `test_native_peer_invite` the production image,
but two of its cases need the developer image's crash selectors). Not
changed here; noted for the deputy.

## Assurance chain

native entry (`fnn-hsig-*` in signatures.lisp, called from the owner's
submission/transit paths and `peer keygen`) -> C shim `fn-mldsa65.c` ->
PQClean ML-DSA-65 (trusted primitive, not proved) -> observation
(`:verified`/`:refused`/`:unsupported`/`:fault`) -> ACL2's
`fn-hsig-authorize`/`fn-hsig-host-*` conjunction (unchanged) -> observed
result. No ACL2 book changed; the logical interface (the constrained
verification in books/assumptions.lisp and books/hybrid-signature.lisp)
is untouched, so no farm run.

## Not done / open

- OpenBSD itself: not run here. The release-openbsd lane builds on the
  OpenBSD VM; the recipe is in this lane's LANEDUMP. LibreSSL acceptance of
  `SSL_CTX_ctrl(123)` (min protocol) and `SSL_ctrl(55)` (SNI) is from
  LibreSSL's ssl.h command numbers, to be observed on the VM.
- `freeze-native-image.sh` still finds libsodium with Linux `ldconfig -p`
  (or `FN_FREEZE_SODIUM`); an OpenBSD freeze sets `FN_FREEZE_SODIUM`.
- PKT-126 ("TLS reset preserves the selected library identity" failed):
  that assertion lived in the signature component test and contradicted
  `fnn-tls-reset`'s contract (it forgets the pair so a restart selects the
  frozen bundle's); signatures no longer touch TLS and the assertion is
  removed from tests/native_hybrid_signatures.lisp.
- A dedicated scenario for HST-016 needs an SCN id from the deputy; HST-016
  is attached to SCN-037 (hybrid author) and SCN-092 (implicit TLS) meanwhile.
