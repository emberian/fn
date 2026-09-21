# Native hybrid signature component evidence

Date: 2026-09-21. Source commits: `cc986f00`, `e61bc2c4`, `1c4b11bf`,
`0ba9527d`. Host: `nextop.local`, macOS 26.6.1 arm64, SBCL 2.6.8,
OpenSSL 3.6.4, and the installed libsodium loaded by
`host/native/crypto.lisp`.

The run generated two independent ML-DSA-65 PEM keypairs with
`openssl genpkey -algorithm ML-DSA-65`, selected the matched OpenSSL pair with
`FN_OPENSSL_PREFIX=/opt/homebrew/opt/openssl@3`, and ran
`sbcl --noinform --disable-debugger --script tests/native_hybrid_signatures.lisp`.
It printed `FN_NATIVE_HYBRID_SIGNATURE_TEST passed`.

The test exercises pure Ed25519 signing/verification, pure ML-DSA-65
signing/verification, a changed ML signature, a stripped ML component, NUL in
a PEM path, the scalar `fnn-core` convention used by
`fnn-hsig-authorize-profile`, and substitution of keypair B while the signed
profile enrolls key A. One EVP key handle supplies both the observed raw
public key and the ML verification operation; ACL2 receives that observation
and owns the equality with the enrolled key.

ACL2 certification of `books/hybrid-signature.lisp` and
`tests/acl2/hybrid-signature-tests.lisp` passed in local run
`certify-20260921T170749Z-64490` with ACL2 8.7 and SBCL 2.6.8. The launcher
fingerprint was unqualified, so this is local component evidence rather than
the frozen integrated gate.

The raw production-entry test stubs `fnn-core` with its real scalar calling
convention; it does not run a saved ACL2 image. Primitive correctness,
unforgeability, RNG, ABI and dynamic-library behavior remain trusted. This
does not establish key custody, recovery authority, durable article/verdict
composition, a Linux library build, or deployment qualification.
