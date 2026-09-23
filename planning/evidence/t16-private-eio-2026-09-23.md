# Isolated hbox transaction-directory EIO, 2026-09-23

This is an **ext4-on-tmpfs-loop/device-mapper error profile**, not a physical
power-loss or hbox ZFS qualification. The host code under test is
`host/native/io.lisp` at `record-attempted`: it issued the final transaction
link and then treated an `EIO` from `fsync(store/transactions)` as an uncertain
publication. The test used only a new disposable `/tmp` backing file and its
positively identified loop device, private mapper, and ext4 mount. It never
faulted `/tank/fn/node`, the shared `tank` ZFS pool, or an existing mount.

The image was a developer-only targeted build from exact source
`80fc3b0089e90eb2f59d4e9c917d847ecd38ec44` (qualified ACL2 core base
`1836ed01cba287bea1633c6cd0c231443302de3f`, plus the native test-stop
host hook from `fb88f3c25b2874d5b957ffcecb347e5d7cfc22de`). The 466
matching ACL2 certificates were reused; this run did not recertify or prove
new books. Build invocation on hbox, under `swarm-build`:

```sh
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g \
FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp \
FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/t16-developer.log \
swarm-build sh tools/build_native_host.sh
```

The launcher SHA-256 was
`bcf4f8719098380855891f701d4fb158627bf1c45983589b547c578835e9f931`;
the core SHA-256 was
`eb7a5978291742e06be117e9d9ff491aa382c0cfbabe318f7b85df7224f49fe7`.
The ACL2 launcher SHA-256 was
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`.
hbox ran Linux `6.11.0-29-generic`, SBCL `2.6.8`, mke2fs `1.47.1`, and
device-mapper library `1.02.196` / driver `4.48.0` with `flakey` target `1.5.0`.
`/tmp` was tmpfs; `/tank/fn/gates` was the separate shared ZFS `tank` mount.

The campaign command was:

```sh
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
python3 tests/campaign/native_block_fault.py \
  --image /tank/fn/gates/t16-core-80fc3b00/build/fn-host-developer \
  --out /tank/fn/gates/t16-core-80fc3b00/build/block-error-run-6
```

The driver SHA-256 was
`f1f235554624a8ce835cb5b54fdd08159d705d82162179e1ec287f7bb5721c91`.
Its prior durable transaction hash was
`e33ddf29f84616e319abbc9ce0f1d69a046ee95be42c03d6607b8db92d1a1301`.
The final candidate link succeeded and the candidate file hash before the
barrier was
`4a1b744c9d7c6a32f02da85da7994be7c2302862af58056d28adbf8802ebdff3`.
The [syscall trace](t16-private-eio/strace.txt) records `link(...01.txn) = 0`,
then `fsync(.../transactions) = -1 EIO`. The native post exited `3` with
“transaction publication outcome is indeterminate”; it did not report
acceptance. After restoring the private mapper's linear table and unmounting
and remounting its ext4 filesystem, the candidate link was absent, the prior
transaction retained exactly its prior hash, and native `store recover` exited
`0` with one transaction and one article. The [machine-readable result](t16-private-eio/result.json)
contains device identity, hashes, exact return codes and the observed
`older-prefix` outcome. The [private mapper probe](t16-private-eio/probe.json)
first established that this mapper configuration yielded `EIO` on an ordinary
file `fsync`. Both runs cleaned their exact mount, mapper, loop device and
backing file; read-only checks found no `fn-t16` resources left.

The uncertainty window here is the existing model cut `record-attempted`,
with an independently observed successful final link. A stopped process at
that named phase alone would not establish that link. This injected write
error does not represent a completed successful directory fence, so it does
not test K8's after-fence survival implication. The tmpfs backing and
device-mapper error target do not model a physical power cut, firmware cache,
sector overwrite isolation, production ZFS behavior, or torn-write image.
T16 platform qualification and the physical assumptions remain open.
