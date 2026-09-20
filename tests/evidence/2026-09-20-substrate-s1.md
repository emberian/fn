# Substrate S1: the FN-Statement carrier, the verdict, S1-1 and the grounding theorem

Tool: ACL2 8.7 (`$HOME/fn-tools/acl2-8.7/saved_acl2`) on persvati, via
`python3 tools/farm.py submit persvati --remote-root
/home/ember/fn-lanes/w7-substrate-s1-2`. Environment on every invocation:
`ACL2_CUSTOMIZATION=NONE`, `ACL2_BOOK_HASH_ALISTP=NIL`. Input revision:
branch `w7/substrate-s1-2` at `57f54fc`, from `dev` `1c5b950`.

| Root | Run | Evidence directory | Result |
| --- | --- | --- | --- |
| `books/stx-carrier` | `run-20260920T052853Z-b82b` (w7/substrate-s1) | `build/acl2/certify-20260920T052855Z-*` | certified |
| `books/stx-verify` | `run-20260920T173829Z-2510` | `build/acl2/certify-20260920T173833Z-1235046` | certified |
| `books/stx-invariants` | `run-20260920T174338Z-6891` | `build/acl2/certify-20260920T174341Z-1287238` | certified |
| `tests/acl2/stx-tests` | `run-20260920T174716Z-9575` | `build/acl2/certify-20260920T174721Z-1322621` | certified, exit code 0 |

`tests/test_stx.py`, on persvati in the same remote root with
`FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2`: **5 tests ran, 0 skipped, OK**,
6.5 s. It drives `tools/stx.py`, which computes every value through an ACL2
session; the test contains no encoder.

Limitations, and they are the whole point of reading this file next to the
claim:

- The verdict runs under the **toy realisers** of
  `tests/acl2/crypto-seam-tests.lisp` (a polynomial mix digest and a
  sign-by-public-key scheme). Nothing here is evidence about unforgeability
  or collision resistance; those are A-CRYPTO. What is evidenced is the
  codec and the composition.
- PRF-020 is **not closed**. The grounding theorem
  `fn-stx-verified-implies-signature-over-own-octets` is certified, but its
  companion `fn-stx-transit-verdict-is-fn-stx-verdict` names
  `fn-peer-transfer` and needs K1's transit path, so the assurance rule "the
  theorem subject is the function the host calls" is not yet met for the
  transit path.
- `HEAD returns FN-Statement byte-identical` is half proved: the statement
  layer has no transition, and the field's survival through the article
  parser is asserted in the test book, but the nntp-side theorem that `HEAD`
  emits the retained header octets unchanged is owed by the nntp cluster.
