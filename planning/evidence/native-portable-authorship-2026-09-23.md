# Portable authorship native caller packet (2026-09-23)

Source: `implement/authorship-integration` through `80527b2e` (base
`b7d13908`). The pinned production image at
`/tank/fn/gates/takeover-t2-image-daa6c15e/build/images/daa6c15ef9d5c900b6e31ec9c9b51b9aaa708789/fn-host`
ran `FN_RUN_HYBRID_E2E=1 python3 -m unittest tests.test_native_hybrid_author -v`
on hbox with the matched `/tank/fn/toolchains/openssl-3.5.8` library and CLI:
one real enroll/sign/refuse/submit/reopen/ARTICLE case passed in 3.88 seconds.
That image predates the new `hybrid-sign-carrier` and
`hybrid-verify-carrier` verbs. It establishes the existing native primitive and
Store baseline, **not** a portable carrier or reader verdict end to end.

The new verbs call the ACL2 carrier renderer and received-source projection,
then the native libsodium Ed25519 and OpenSSL 3.5.8 ML-DSA-65 observations,
with `fn-hsig-authorize` making the both-required decision. The signer writes
only after a successful received-carrier verification. The new native test
checks exact source and key-set alteration refusals, Path/Xref mutation
acceptance, and refusal when carrier expansion exceeds the complete article
cap. It still needs execution on the next combined saved image.

ACL2 8.7 on persvati, executable SHA-256
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`:

* `python3 tools/farm.py submit persvati --jobs 2 --affected-by
  books/hybrid-carrier.lisp --closure` passed both selected roots and all 27
  closure books, no failures, 53.423 seconds. [Manifest](manifests/certify-20260923T172934Z-2216743.json).
  The final `books/hybrid-carrier.lisp` digest is
  `04f7a116936da20d5f251edf4f1bcd8974d1e64fe6b27d92f1fe9010619b03cd`.
* The hybrid Store/control interface roots `books/hybrid-store`,
  `tests/acl2/hybrid-store-tests`, and
  `tests/acl2/native-hybrid-control-tests` passed their 85-book closure, no
  failures, 85.938 seconds, before the carrier theorem was renamed without
  changing that interface. [Manifest](manifests/certify-20260923T172727Z-2195275.json).

The new `fn-hc-render-at-most-emitted-bound-by-definition` states the direct
bound of the admitted complete-article refusal branch. It is a definitional
fact, not an independent length derivation. The selected v1 carrier's binary
and field-length evidence remains in `books/hybrid-carrier.lisp`; the new
wrapper makes the output and input article caps agree. `--affected-by
host/hybrid-signature-host.lisp` selects zero Makefile certification roots
because that program-mode wrapper is loaded by the saved-image build.

Store kind-4 historical verdict binding to a portable carrier, an explicit
authored-source identity distinct from received content identity, and served
`:fn-verified` exposure remain separate work. The current CLI result is an
independent artifact verification, never a durable acceptance verdict or a
current principal-succession claim. Native primitive correctness, key custody
and the host/library boundary remain trusted, not ACL2 theorems.
