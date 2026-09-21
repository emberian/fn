# Native served fast-path evidence, W26

This record covers the focused certification of the maintained fast wire
invariant, the served counted fast transition, and its correspondence test.
The archived machine-readable manifest is
[`certify-20260921T181808Z-2349117.json`](manifests/certify-20260921T181808Z-2349117.json).
The manifest's source digests are authoritative; its farm checkout did not
record a Git revision.  The ACL2 source snapshot was submitted from the W26
lane immediately after `01d73837`, with the relevant ACL2 and test files clean.

| fact | value |
| --- | --- |
| farm run | `run-20260921T181805Z-3433` |
| certification run | `certify-20260921T181808Z-2349117` |
| result | passed, 60 of 60 requested closure books |
| interval | 2026-09-21 18:18:08Z to 18:28:31Z |
| concurrency | one effective ACL2 job |
| toolchain | ACL2 8.7, SBCL 2.6.8 |
| toolchain identity | `13a22db3e92c0be5086847abf17c18909f9de6fd8f6a5a0adc92d051cac55b28` |
| ACL2 core SHA-256 | `3f5b101bb9437d66366dc2a299b7f9cb98fdaf40d1add5caf8baef9e451dd07d` |
| runner root | `tests/acl2/served-tls-prefix-tests` with its full local include closure |

The 60-book closure includes `books/wire`, `books/wire-invariants`,
`books/served`, `books/served-tls-prefix`, and
`tests/acl2/served-tls-prefix-tests`.  The manifest records every requested
book, source digest before and after certification, certificate digest, exit
code, and success marker.  All source-before/source-after digests agree and
`book_failures` is empty.  The key source digests are:

| source | SHA-256 |
| --- | --- |
| `books/wire.lisp` | `050c48733761b68532fb73713223298b489bc0b2a54175ccd60ddea8259b14bf` |
| `books/served.lisp` | `b9c015b6dc50775d8a480d215f0b9de98562202e1729a19d25389a5b2351aa40` |
| `books/served-tls-prefix.lisp` | `0a50713cc550a21897095edf39111cc53e1033ea2c96eb7f23d5535f2ac5e61d` |
| `tests/acl2/served-tls-prefix-tests.lisp` | `482f7b7dcf6f158f9314a9ad37b34a4e7affff5f14cc576182364c4a99e7f6a5` |

The correspondence event certified in this run is
`fn-served-step-counted-fast-is-reference`: under `fn-wire-statep`, the cheap
entry returns exactly the checked total reference result.  Its test book has a
reachable valid-state equality witness and a fixed-spine state retaining the
non-octet 300; that state satisfies `fn-wire-fast-statep`, violates
`fn-wire-statep`, and makes the equality claim fail when the full invariant is
removed.  The production-facing outer correspondence event is
`fn-ocfg-read-tls-prefix-is-full-read`, which is curated under PRF-006 because
`fn-ocfg-read-tls-prefix` is the function called by `fn-owner-chunk`.

This passing run does not include `books/owner-tls-prefix`.  The earlier W26
owner-closure attempt, `run-20260921T175932Z-305c`, reached and certified the
served books but failed first in the unrelated
`fn-sf-candidate-append-preserves-record-list` theorem in
`books/store-files-invariants`; the dependent owner books consequently could
not load.  Therefore this record makes no owner-book certification claim.  A
current-main certification of the outer correspondence event is required
after the store changes are integrated.

Integration comparison against main `220bcb05` also found changed dependency
sources in `cbor`, `cbor-invariants`, `frame-journal`, `nntp-auth`,
`peer-config`, `peer-inbound`, `replay`, `statement`, and `store-events`.
`wire` differs by the subsequent guard-comment correction. The served
transition and its focused test match the certified source, but this archived
closure is not a certificate of the current combined dependency tree.

The source-level cost check in `tests/test_native_served_cost.py` passed all
three tests.  It verifies the production call chain and counts a fixed set of
spine/scalar selector expressions; it is a static source-scope check, not a
runtime CPU or allocation measurement.
