# BP returned-sequence fidelity evidence

Source revision: `e022a70e7f6c18e0d9735053b90557c8f98c4733` in
`/Users/ember/dev/fn/build/lanes/w14-bp-sequence-fidelity`.  Nothing was
deployed or published.

## Certified subject

`books/bp-sequence-fidelity.lisp` models the final pathname observed by
`fnn-bp-reserve-sequence`, without preserving a rename or barrier phase bit
across process death.  Its named bridges are
`fn-bpn-sf-host-recover-is-core-recover` and
`fn-bpn-sf-host-reserve-is-core-reserve`; their subjects are
`fn-bpn-sequence-recover` and `fn-bpn-sequence-reserve`, the functions
selected by the thin wrappers in `host/bp-node-host.lisp:88-118` and called
from `host/native/bp.lisp:148-165`.

The keystone
`fn-bpn-sf-admissible-trace-returned-sequences-unique` says that every
finite trace whose continuing recoveries do not precede the
directory-barrier-confirmed frontier has no duplicate value returned at the
native reservation boundary.  Its witness book covers:

- fresh and existing namespaces, absent and malformed finals;
- staged residue ignored after restart;
- old-final retry and new-final burn after an unconfirmed rename;
- a confirmed successor lost before the accessor returns;
- a returned reservation lost with the process before later use; and
- both process death and power loss as volatile-state loss.

The concrete teeth trace returns zero twice when a valid frontier zero is
observed after frontier one was confirmed.  That trace is executable but
`fn-bpn-sf-trace-admissiblep` is false, so dropping the theorem's sole
physical-admissibility hypothesis makes its conclusion false.

ACL2 Version 8.7 on nextop.local, with SBCL 2.6.8, ran:

```sh
python3 tools/certify_books.py --jobs 1 \
  books/bp-sequence-fidelity tests/acl2/bp-sequence-fidelity-tests
```

`certify-20260921T091031Z-26507` certified both final owned roots.  Its
committed manifest pins the exact source digests, invocation, tool, host, and
per-book results.

## Native process-death cut

The native DTN image was built from the pinned revision with:

```sh
python3 tools/certs.py install
FN_ACL2=/opt/homebrew/bin/acl2 \
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
FN_NATIVE_LOG=build/native-host-build-w14-fidelity.log \
sh tools/build_native_host.sh
```

The executable SHA-256 was
`21b0252a0462b887a8fa3f7ed426a14b5eec0fd354350f861bc4348ffce0530c`;
the 280M core SHA-256 was
`dc8369623fef89ac32bb1cfa7badd610721944ba987efc4b1bb2b13b4a85d8bc`.
The runtime was ACL2 8.7 / SBCL 2.6.8.  Python 3.14.7 was the test driver only;
the process under test was the native Common Lisp image calling ACL2.

```sh
python3 tests/bp-dtn7/run_fn_bp_sequence_durability.py \
  --image build/fn-host-dtn \
  --work build/evidence-bp-sequence-fidelity \
  --source-revision e022a70e7f6c18e0d9735053b90557c8f98c4733 \
  --artifact-set \
    certify-20260921T085952Z-16806+certify-20260921T090509Z-21220
```

The run passed.  Independent native processes first returned sequences zero
and one.  A third process connected to a local hanging listener; after
`authored-2.wire` proved that `fnn-bp-reserve-sequence` had returned and
the bundle had been formed and recorded, the driver sent SIGKILL (exit -9).
The restarted native process returned sequence three and exited with the
expected failed-connect fault code 4.  Root-parent barrier injection remained
uncertain (3), lock contention remained refused (1), and a malformed final
remained uncertain (3), with no authored bundle in those three cases.

## Exact limit

The theorem is conditional on `fn-bpn-sf-trace-admissiblep`: successful
parent and sequence-directory barriers must make every later recovery that
continues expose a frontier at least as large as the confirmed frontier.
ACL2 does not prove filesystem, kernel, device, or power-loss behavior.  The
abstraction also assumes that the raw final-path read classified as
`(:valid n)`, `:absent`, or `:malformed` corresponds to the
`octets/presentp/freshp` arguments supplied by native Lisp.  Valid abstract
observations are decoded by the actual ACL2 recovery function using
ACL2-framed bytes; the remaining raw-I/O-to-observation relation is not a
proved refinement.

The native SIGKILL run checks one real cut after return.  It does not kill
inside `fsync`, emulate a power failure, or establish hardware persistence.
