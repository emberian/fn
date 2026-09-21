# Evidence: ACL2-owned native storage codec (w13)

Date: 2026-09-21.  The implementation revision is
`bb9db2c816e18b8c8f6a979e67fcc5694fe36048`; its frozen hbox snapshot is
`452828c4bd9fa2c2e60122d0ab9f51a26101baba` at
`/tank/fn/lanes/w13-native-storage-codec`.  The snapshot's source digests are:

```
0d188dfc47bfc73d8ec20bf9b7850bf153b81513fbd5a921918636f19dbabc46  host/native/io.lisp
67a4e1f017a026e4055a3c9f2fc95cecaaa83c802036ad168fe9d796c056f18d  tests/test_native_storage_codec.py
19b117992dad754196ceb1e36fd07a949518cbdf7016c035e3bac0e1562e4526  books/byte-store-frame.lisp
778388548c99d46b406b37bf805ed84037483b33eef5a5fbd0aa2d217f6e65d0  books/byte-store-txn-name.lisp
11d7f521996cbfa35a2fe17ec2d2c03b6b68c914e94cc8a1e333266743e44da7  host/store-host.lisp
```

The native store now calls ACL2 for the complete FNSM configuration and
frontier frames, their decoders, the frontier successor/exhaustion decision,
transaction names, and local-post provenance.  The raw host only moves the
returned octets and checks boundary shape.  Legacy JSON is retained and
refused with an explicit offline-migration diagnostic; opening a store never
rewrites it.  Python participates below only as an interoperability test
oracle, not as a deployed native runtime component.

## Certification and profile closure

The certification host was hbox, Linux 6.11.0-29 x86_64, Python 3.12.7,
with ACL2 8.7 at `/tank/fn/acl2-8.7/saved_acl2`; that executable's SHA-256 is
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`.
The default and DTN root lists were generated explicitly as
`build/default-roots.txt` and `build/dtn-roots.txt`, then unioned with
`sort -u`.  The bounded commands were:

```
FN_ROOTS=$(sort -u build/default-roots.txt build/dtn-roots.txt | tr "\n" " ")
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
python3 tools/certify_books.py --jobs 4 --closure \
  --affected-by books/byte-store-frame books/byte-store-txn-name $FN_ROOTS

FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
python3 tools/certify_books.py --jobs 2 --closure \
  tests/acl2/byte-store-frame-tests tests/acl2/byte-store-txn-name-tests

FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
python3 tools/certify_books.py --jobs 4 --closure $FN_ROOTS
```

All three passed: 30 affected closure books in 100.060 seconds, the 32-book
codec test closure in 106.338 seconds, and the complete 108-book profile union
in 679.289 seconds.  Complete generated manifests are
`planning/evidence/manifests/certify-20260921T074354Z-1780243.json`,
`planning/evidence/manifests/certify-20260921T074543Z-1784563.json`, and
`planning/evidence/manifests/certify-20260921T074821Z-1788915.json`.

Those manifests identify the pre-host-fix frozen revision
`81e9a2259f180a854609764426cbcb3e3b1bf141`.  The later `bb9db2c` change
touches only raw `host/native/io.lisp` and its Python integration test; every
certified book digest above is unchanged.  On the final snapshot the actual
ACL2 load validator was run again:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
python3 tools/proof_artifacts.py validate --profile default \
  --acl2 /tank/fn/acl2-8.7/saved_acl2
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
python3 tools/proof_artifacts.py validate --profile dtn \
  --acl2 /tank/fn/acl2-8.7/saved_acl2
```

Both loaded: 26 roots for default and 25 for DTN.  The exact output is in
`native-storage-codec-w13-2026-09-21/profile-validation-w13-storage-codec.log`.

## Native images and tests

Both images were built from final snapshot `452828c` with explicit profile,
image and log selections:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_LOG=build/native-host-build-w13-storage-codec.log \
sh tools/build_native_host.sh

FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
FN_NATIVE_LOG=build/native-host-build-dtn-w13-storage-codec.log \
sh tools/build_native_host.sh
```

The default core is 274,625,152 bytes and the DTN core is 273,805,720 bytes.
The launcher/core SHA-256 pairs are default
`f6f9581fa1fd92c93de8eec9b5e50d3e44d48496aa289c5735b3242e45db29c9` /
`d4013cbdc76752793f494dd1b1bd11df03a9e06194109fc8007f90e2d093e8b0`,
and DTN
`93d90f80fd8278ab08ff36d0aeff2173662b50b09576cd0a2897c9c3f7cfca2b` /
`d6c35ba1d1b7630fa8667318c8a93d42171d016b09486fefed058976edac9a91`.
Both build logs contain `FN_NATIVE_BUILD_LOADED` and no uncertified or ACL2
error marker; the archived logs are in this evidence directory.

The focused suite was run once per image:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=$PWD/build/fn-host \
python3 -m unittest tests.test_native_storage_codec -v

FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=$PWD/build/fn-host-dtn \
python3 -m unittest tests.test_native_storage_codec -v
```

Each profile passed 7 of 7 tests.  Covered behavior is native init/post/reopen,
Python/native cross-open with byte-identical config, frontier and transaction
frames, the ACL2 scale profile, malformed/truncated/wrong-kind metadata,
legacy JSON refusal without rewrite, ACL2 domain exhaustion before staging,
post-publication recovery, and injected frontier/record directory-barrier
failures with uncertain exit status and recovery.

Four existing native store tests passed under `FN_HOST=native`: literal-byte
post/reopen, transaction naming after nonempty recovery, metadata truncation,
and legacy JSON retention.  The seven served differential tests also passed.
Their exact commands and output are archived as
`test-native-store-targeted-w13-storage-codec.log` and
`test-native-served-differential-w13-storage-codec.log`.

## Serialization counterexample and open recovery differences

The first full differential run found transaction frames 17 bytes shorter on
native.  Splitting each frame showed that both protected prefixes carried the
declared length, both trailers equaled SHA-256 of their own prefix, and each
runtime opened the other's record.  Decoding the record fields isolated the
difference: Python called ACL2 `fn-store-prov-post` and stored a 34-byte
`fnprov1:` value, while native typed the 18-byte string
`unsigned-legacy-v0`.  The 16 evidence bytes plus CBOR's one-byte longer length
head explain the entire 17-byte delta.  Commit `bb9db2c` routes native through
the same ACL2 wrapper; the strengthened cross-runtime test now requires the
complete transaction files to be byte-identical.

The final full differential command was:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 python3 tests/native_differential.py
```

It intentionally remains a failing evidence run: findings fell from 24 before
the provenance fix to 11 afterward, with all committed transaction records now
identical.  The remaining findings have two behavioral roots.  Native retains
the staged file after the injected known-abort cut and retains both staged
files after the following uncertain cut; Python removes them.  Native also
accepts a store whose `staging/` directory is missing, while Python exits 4.
Six stderr comparisons differ only in wording or the per-runtime temporary
path.  The exact final counterexamples are in
`test-native-differential-w13-storage-codec.log`; this packet makes no full
native/Python equivalence claim.  The initializer/recovery lane owns the
missing-directory and staged-orphan policy follow-up.

Local `make check` reached the generated-ledger gate and failed only because
`planning/ledger.json` and `planning/ledger.md` do not yet include the new
transaction-name book/test; root integration owns that generated registry
update.  Its warnings are the repository's recorded lint backlog.
