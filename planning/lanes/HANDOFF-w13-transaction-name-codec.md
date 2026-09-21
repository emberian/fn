# Handoff: transaction-name codec and host attachment

Branch `w12/storage-codecs`, final implementation revision `687c2a9`, rooted
at the storage-codec packet that is already based on the W12 integration
line.  The portable proof checkpoint is `e16bb89`; `687c2a9` adds the hbox
closure manifest.

## Delivered contract

`books/byte-store-txn-name.lisp` realizes the constrained
`fn-bs-txn-name` seam as the ordinary decimal representation of every
natural, padded to a minimum of twenty characters, followed by `.txn`.
The renderer remains variable-width above twenty digits.  Its proof uses a
self-contained least-significant-first decimal renderer and arithmetic left
inverse, then proves padding removal, string/list equality, suffix
cancellation, and injectivity before `defattach`.

The book intentionally has no `std/strings` or `std/lists` dependency.  This
fixes the hbox failure where
`std/strings/explode-nonnegative-integer.cert` was unavailable.  Its only
system-book dependency is the already-required local `arithmetic/top` book.

The theoretical naming domain and the actual allocator domain remain
separate.  `fn-bs-txn-name-impl` is injective for all naturals.  The store's
frontier codec bounds actual allocation to the CBOR uint32 domain through
`fn-bs-frontier-next`; `Acl2Store.transaction_name` accepts the resulting
twenty-digit path component with `SEQ_NAME` and does not format it itself.

`host/store-host.lisp` exports these stable wrappers:

* `(fn-store-txn-name sequence)` returns the ACL2-owned string, or `""` for
  a non-natural boundary input.
* `(fn-store-txn-name-octets sequence)` returns its character octets for the
  Python bridge.

`tools/run_store.py` calls the octet wrapper from `Store.publish`; the former
Python `{:020d}.txn` implementation is gone.  The native lane owns its
`host/native/io.lisp` caller and consumes `fn-store-txn-name` directly.
Host directory recognition/parsing remains a bounded I/O check; it does not
choose or format the persisted name.

## Proof and executable teeth

`tests/acl2/byte-store-txn-name-tests.lisp` executes both the implementation
and the attached constrained function at sequence 17.  It also covers zero,
a 21-digit value, and unequal adjacent values.  Its three `must-fail` events
remove, one at a time, the left natural hypothesis, right natural hypothesis,
and name-equality hypothesis from the injectivity theorem.

The real host witness
`StoreTests.test_acl2_transaction_names_continue_after_nonempty_recovery`
publishes sequence 0, closes the process, runs recovery over nonempty durable
history, publishes sequence 1 in another process, and reopens once more.  It
checks both durable directory names against fresh ACL2 wrapper calls and
checks that the replayed article count is two.

## Exact evidence

Local ACL2 was version 8.7 at
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` on macOS 26.6.1.  At source digest
`778388548c99d46b406b37bf805ed84037483b33eef5a5fbd0aa2d217f6e65d0`
for `books/byte-store-txn-name.lisp`:

* `python3 tools/certify_books.py --jobs 1 books/byte-store-txn-name` passed;
  manifest `certify-20260921T074212Z-42131` is archived.
* `python3 tools/certify_books.py --jobs 1
  tests/acl2/byte-store-txn-name-tests` passed; manifest
  `certify-20260921T074227Z-42389` is archived.
* `FN_ACL2=/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2 python3
  tools/host_check.py host/store-host.lisp --log-dir
  build/host-check-txn-name` passed `1/1`; the host file loads alone.
* `python3 -m unittest
  tests.test_store.StoreTests.test_acl2_transaction_names_continue_after_nonempty_recovery
  -v` passed one test in 18.863 seconds against a real ACL2 process and real
  temporary directories.

Before the hbox run, load was 1.93/1.65/1.77 on 24 CPUs with 30 GiB memory
available.  The exact remote command was:

```text
python3 tools/farm.py submit hbox --jobs 4 --closure \
  --remote-root /tank/fn/lanes/w12-storage-codecs \
  books/byte-store-txn-name tests/acl2/byte-store-txn-name-tests
```

Farm run `run-20260921T074327Z-bfed` used ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2` and passed all 31 roots in the owned closure.
Its manifest `certify-20260921T074336Z-1779617` records every source and
certificate digest, the exact command, tool digests, host, and timing.  The
two requested roots each certified in under one second after their closure.

`make check` reached the generated-ledger comparison and failed because
`planning/ledger.json` and `planning/ledger.md` are stale.  The integration
root owns and regenerates those shared files.  A full in-process
`tests.test_store` run also retains the known test-harness isolation defect:
`frame_bridge._SESSION` may refer to an adopted `Acl2Store` after another test
closes it.  Fresh-process transaction-name and adjacent store tests pass; this
packet does not change that shared session lifecycle.

