# Native selected-pack retirement at 863c2141

On hbox, the shared developer image and exact source snapshot were
`/tank/fn/gates/capability-863c2141-20260924`, commit `863c2141`.  Launcher
SHA-256 was `c70fdd71c79d6c5379478f9f37d557a8d418902c1814d66dc59ad1776ecbf49e`
and core SHA-256 was
`e743ae19ea5ccbbb842acc6c60ecc1309fcf9ed9a018bdbe622a15f9a489e7c0`.
The exact command, using only temporary Stores created by the test, was:

```sh
PYTHONPATH=/tank/fn/gates/capability-863c2141-20260924 \
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
FN_NATIVE_DEVELOPER_HOST=/tank/fn/gates/capability-863c2141-20260924/build/fn-host-developer \
python3 -m unittest -v \
  tests.test_native_checkpoint.NativeCheckpointTests.test_retiring_old_pack_generations_keeps_exact_retained_sources \
  tests.test_native_checkpoint.NativeCheckpointTests.test_pack_generation_retirement_death_reopens_and_retries \
  tests.test_native_checkpoint.NativeCheckpointTests.test_active_reader_blocks_pack_reclaim_and_reopen_keeps_archive_pin
```

The [full test log](native-pack-retire-863/three-case.log) has SHA-256
`3832016605a0f0099d7bd02820c7311a9386ee021ea6d010dc709e13f1673600`.
Process death after the first and second older-pack unlink and after the
packs-directory barrier passed; active reader lock refusal and pinned archive
survival passed.  The capacity-recovery test failed when a later `checkpoint
pack` tried to publish after generation 0 had been retired: the host got
`ACL2 refused pack publication authority: (:ERROR :NAMESPACE)` and exit 4.
The allocator already returned generation 2, but `fnn-pack-publish` still
called gap-free `fn-cpp-publication-initial`.  The packet in this lane changes
only pack publication to `fn-cprt-publication-initial`, which validates the
gap-aware namespace and retains exclusive authority and final-name absence
checks.  Ordinary node-checkpoint publication remains gap-free.  This packet
requires a later source-matched native image to re-run the failed case; the
863 image result remains RED for that capacity test.  The test's scratch
Stores were removed by `TemporaryDirectory` cleanup.

The corrected ACL2 book and test certified on persvati with ACL2 8.7,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
via `python3 tools/farm.py --jobs 2 submit persvati
books/checkpoint-pack-retire tests/acl2/checkpoint-pack-retire-tests`.
The passing manifest is
`planning/evidence/manifests/certify-20260924T062815Z-1213319.json`
(five exact-byte dependencies/roots certified).  The corrected book's SHA-256
is `d928d01eadd034c84de4cff5d956b2193659e49a8e3f5c467a334f95904a9dc4`;
the test book's is
`aa4eee96d1caa19cae4cfc34a6904f30122faf2ba2d371ba21dcf8769014a225`.
`make check` passed in the isolated lane.  This certification does not test a
saved image or physical platform behavior.

An earlier invocation without `FN_OPENSSL_PREFIX` failed before Store init
because the system OpenSSL lacked ML-DSA.  That startup attempt is not a
storage verdict and was corrected in the invocation above.  This SIGKILL and
filesystem observation is not a power-loss or hardware durability claim.
