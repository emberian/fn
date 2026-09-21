# Bounded CBOR and Store profile component certification

These manifests record focused ACL2 component certification on `nextop.local`
with ACL2 8.7 and SBCL 2.6.8.  Both invocations used one worker and
`--no-publish`; they are local proof evidence, not a published reusable cache.

- `certify-20260921T174836Z-87529.json` certified `books/cbor`,
  `books/cbor-invariants`, and `books/records` from the corrected bounded
  decoder source.  The manifest records source digest
  `210c1103953ee93fdc97bfae0e16ca02d1ab020908d771fee711e8061268e330` for
  `books/cbor.lisp`.
- `certify-20260921T174846Z-87755.json` certified the focused dependency chain
  through `books/statement`: CBOR, CBOR invariants, defrecord, records, records
  invariants, crypto seam, and statement.

The later physical-caller closure
`certify-20260921T175017Z-88479` reached and passed those corrected component
books and the frame roots, but timed out after 1,200 seconds while proving the
legacy `FN-STMT-DECODE-ITEMS-OF-ENCODE-ITEMS` event in
`books/statement-invariants.lisp`.  That timeout is not included as passing
evidence.  It identified a proof-expansion problem in the wrapper theorem;
focused certification of its repair is tracked separately.

`certify-20260921T184656Z-18951.json` is that focused repair result.  On the
same host and toolchain, `books/statement-invariants` certified in 31.219
seconds.  The repair proves a bounded streaming-to-legacy correspondence for
the actual compatibility wrapper, carries octet-list and remaining-length
invariants through the recursive item decoder, and disables those internal
bridge rules after the public sequence theorems so later statement proofs do
not backchain into decoder arithmetic.
