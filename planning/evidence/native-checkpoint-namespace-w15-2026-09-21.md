# Evidence: ACL2-owned native checkpoint namespace (w15 successor)

Date: 2026-09-21.  The implementation revision is
`bc2c19a9cd9184d373fb35cd980c82a560a7dfa3`, based on integrated revision
`7a0b96f4`.  This successor removes the remaining checkpoint filename,
directory-plan, selection-name and bound decisions from the native Lisp and
Python adapters.  Both adapters call `checkpoint-publish.lisp` through
`host/checkpoint-host.lisp`; the native adapter retains only bounded directory
I/O and return-shape guards.

The compatible on-disk names remain `generation-N.fncp` and `selected.fncp`.
ACL2 now canonically renders and parses the generation decimal, rejects aliases
and values outside uint32, sorts the bounded observation, and decides gap and
exhaustion outcomes.  The local retention policy is at most 4096 generations;
the physical observation limit is 4097 entries including the selection marker,
and the sealed selection-frame read bound is 47 octets.

Full immutable-journal replay remains authoritative.  The selected checkpoint
plus suffix is a diagnostic comparison with that live state.  Any disagreement
is now always reported as checkpoint corruption and native exit 4; the former
`FN_CHECKPOINT_DIFFERENTIAL` environment switch no longer changes the outcome.
This packet makes no suffix-only fast-recovery claim.

## Certification

The owned hbox closure used ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2`, executable SHA-256
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`,
and at most four jobs:

```
python3 tools/farm.py --jobs 4 --closure --timeout-seconds 1800 submit hbox \
  books/byte-store-txn-name books/checkpoint-publish \
  tests/acl2/checkpoint-publish-tests
python3 tools/farm.py --wait-seconds 55 wait hbox \
  run-20260921T094239Z-9e2b
```

All 48/48 books passed in 154.764 seconds.  The generated manifest is
`planning/evidence/manifests/certify-20260921T094247Z-1977160.json`; it records
the exact source, certificate and tool digests.  The implementation commit was
amended afterward only to remove an obsolete environment argument from a
Python test; certified ACL2 source bytes are unchanged.

The actual default saved-image root union was then submitted from the same
source snapshot:

```
roots=($(python3 tools/proof_artifacts.py roots --profile default))
python3 tools/farm.py --jobs 4 --closure --timeout-seconds 1800 submit hbox \
  $roots
python3 tools/farm.py --wait-seconds 55 wait hbox \
  run-20260921T094603Z-0968
```

The union passed 126/126 books in 892.485 seconds.  Its generated manifest is
`planning/evidence/manifests/certify-20260921T094607Z-1982886.json`.  An earlier
image-build attempt after installing only the 48-book owned closure stopped at
the build script's uncertified-book gate; the successful build below followed
the complete default root union and did not copy certificates between origins.

## Saved image and behavior tests

The exact final Python test source was synchronized into the manifest-backed
hbox tree after its test-only correction.  These runtime-relevant hashes agreed
between the source and hbox trees:

```
0f4333c53c7731317aba594fe700b6a3219c4727202bbcd414b3697c7011adc5  tests/test_checkpoint.py
f7b6fe71cdd8d5a1a464fcdb65f0a388cffeb517bf1f9949d169cd7860f233fa  host/native/checkpoint.lisp
dada2eb077dafbb2b106673ebb750a2b846c5676aa6d73ebef4ae1d2bcff1d9c  books/checkpoint-publish.lisp
```

The saved image was rebuilt with:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 sh tools/build_native_host.sh
```

The 476-byte launcher has SHA-256
`34a0e05b8aa25192dd7da0b46fa1a26b6259fcd7bd06adff1e1687fda80664bf`;
the 293,045,736-byte core has SHA-256
`9d8ba27ff8df09334be62a1a4b5d00826dd89ad88a57dda0712b616d60a02f4d`.
The build log contains `FN_NATIVE_BUILD_LOADED` and exited successfully.

The exact commands were:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=$PWD/build/fn-host \
python3 -m unittest -v tests.test_native_checkpoint

FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
python3 -m unittest -v tests.test_checkpoint
```

The native suite passed 7/7 tests in 6.911 seconds.  The Python
interoperability/fault suite passed 7/7 tests in 108.550 seconds.  A local
rerun of the repaired six-cut crash test also passed in 202.503 seconds with
Homebrew ACL2 8.7 at `/opt/homebrew/bin/acl2`.

The native cases cover canonical namespace rejection, the exact physical
enumeration bound, generation exhaustion decisions, unconditional differential
corruption, and the existing publish/select/reopen, Python/native cross-open,
malformed/truncated frame, distinct refused/uncertain exit, and process-death
cut behavior.  Publication and marker replacement fence the live Store before
an ambiguity-producing syscall; only ACL2-classified durable or refused
outcomes clear that fence, so a caller that catches uncertainty cannot continue
mutating the same Store.
