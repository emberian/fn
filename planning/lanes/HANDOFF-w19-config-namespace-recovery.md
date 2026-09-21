# Configuration namespace recovery packet

Status: rebased onto `dev` at `995dd39a`; this packet is prepared for a
contained, non-publishing targeted ACL2 closure.  The archive ref
`w19/config-namespace-recovery-pre-rebase-6ec663a5` preserves the recovered
pre-rebase lane.

The recovered hbox manifest `certify-20260921T112854Z-2108022` failed first
because its older `books/journal-publish.lisp` had no verified
`fn-jpub-initial` guard.  Its journal-publish and native-admin-test digests
differed from the surviving corrected sources.  This lane therefore rebases
the observer onto the corrected `dev` dependency instead of treating that
cascading failure as an observer proof result.

## Packet

- `books/native-config-observation.lisp` owns the configuration-history
  decision: exact record decode, generation extraction, canonical filename
  binding, sort, and contiguous `1..n` plan.
- `host/native/io.lisp` bounds directory observation before retaining entries,
  checks every physical entry as a regular non-symlink, and passes every
  observed name/octet pair to that ACL2 decision.  It does not suffix-filter
  malformed or conflicting evidence.
- The raw host obtains the same bound and plan through
  `host/store-node-host.lisp`; the native admin path uses the returned
  canonical observation for authorization and post-publication verification.
- The book and its teeth are roots in `Makefile`; the generated ledger,
  prefix registry, host contract, HST-003 implementation note, and SCN-003
  now name the scope.

## Recorded checks

- `python3 -m unittest tests.test_native_storage_codec.NativeConfigNamespaceSourceTests -v`
- `sh tests/test_native_io_progress.sh`
- `make check`
- `python3 tools/certify_books.py --dry-run --no-publish --closure books/native-admin tests/acl2/native-admin-tests books/native-config-observation tests/acl2/native-config-observation-tests`

No ACL2 certification, certificate installation/publication, or native image
build ran in this packet.

### Sorter repair after source review

The originally landed insertion base case discarded an entry at the end of a
nonempty sort, so a malformed nonempty history could collapse to an accepted
empty plan.  The repair returns `(list entry)`, refuses an empty observed
history, and keeps the final close inside `fn-nco-observe`; an independent
Common Lisp reader sees 23 top-level forms in the book and 16 in its test.
The model teeth now evaluate a three-record reverse-order input to its exact
three-record canonical output and fault malformed names, name/generation
mismatches, and an empty history.  The sorter has occurrence-count,
cardinality, and membership preservation theorems, so duplicates cannot be
silently dropped before namespace rejection.

Contained ACL2 source evaluation loaded this exact book and test with proofs
enabled and completed successfully.  A narrow certification attempt could not
start because the local cache has no matching corrected `journal-publish` or
`native-admin` certificates; a 50-root no-publish closure was terminated at
its 180-second containment limit while certifying dependencies, before it
reached this book.  Neither result is certification evidence.

## Ready contained closure

After process-group containment is available, run exactly:

```sh
FN_CERTIFY_JOBS=1 FN_ACL2_TIMEOUT_SECONDS=600 \
python3 tools/certify_books.py --jobs 1 --timeout-seconds 600 --no-publish --closure \
  books/native-admin tests/acl2/native-admin-tests \
  books/native-config-observation tests/acl2/native-config-observation-tests
```

This resolves a 50-root local include closure.  On success, build a fresh
developer Store image from the same source and run
`NativeStorageCodecTests.test_native_config_namespace_refuses_mismatched_name_and_symlink`.

## Open scope

The packet does not prove physical directory enumeration, the whole native
host, existing/retry initializer correspondence, all process-death cuts, or
platform crash persistence.  An unreadable directory and a non-regular entry
fault before ACL2 receives octets; the remaining decoded namespace cases are
ACL2's decision.  A successful targeted closure would establish only its
books and teeth, not an integrated production image claim.
