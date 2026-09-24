# T16 private publication fault profile, partial hbox observation

This is a bounded ext4-on-tmpfs-loop observation, not a completed platform
qualification.  A read-only facility check on 2026-09-24 found that hbox has
a separate tmpfs `/tmp`, a free loop device, `strace`, and `dm-flakey` 1.5.0.
Persvati has disk-backed ext4 `/tmp` and no `flakey` target, so this harness
does not run there.  The driver refuses non-tmpfs `/tmp` and verifies every
private mapper dependency, mount, loop binding, and stopped tracee before a
fault, signal, or cleanup.  It never targets an existing device or service.

| Scenario | Actual host cut and model program | Fault/observation |
| --- | --- | --- |
| `frontier-dir-eio` | `frontier-attempted` after `fnn-replace` of `allocation-frontier.json`, `fn-bs-frontier-program` pair 12 | Private `dm-flakey` write EIO at root-directory `fsync`; native must fence and report indeterminate. Recovery may find the old or exact advanced frontier, with prior transactions unchanged. `fn-bs-k0-owner-frontier-root-eio-choice-run-fences-related-state` is the scoped model correspondence for `:apply`/`:drop`. |
| `record-dir-eio` | `record-attempted` after final link, `fn-bs-record-program` pair 10; directory error is pair 11 | Private `dm-flakey` write EIO at transaction-directory `fsync`; native must fence and report indeterminate. Recovery may find old prefix or exact candidate. The model error choices are `fn-bsrp-record-dir-error-outcomes`. |
| `record-dir-sigkill` | Same `record-attempted` pair 10 | Kill only the stopped, identity-checked tracee. A remount may expose old prefix or exact candidate. This is process death, not I/O error. |
| `record-cut-snapshot` | Same `record-attempted` pair 10 | Suspend only the private mapper without flushing, copy its tmpfs backing bytes, kill the stopped tracee, close the original mount, and reopen the copied image on a separately checked loop. This deliberately drops later volatile writes; it is a simulated write-loss image, not physical power loss. |

The shared exact `863c2141` developer image ran the three record-cut cases
one at a time on hbox.  Its launcher SHA-256 was
`c70fdd71c79d6c5379478f9f37d557a8d418902c1814d66dc59ad1776ecbf49e`
and core SHA-256 was
`e743ae19ea5ccbbb842acc6c60ecc1309fcf9ed9a018bdbe622a15f9a489e7c0`.
The source-overlay driver committed in `e5f089f0` had SHA-256
`4de00248ab17078989a6a874badf0e14b38408b1ad1faa245365db323b14dc05`.
These commands use the same image for all Store operations, with
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8` set in the environment:

```sh
python3 tests/campaign/native_block_fault.py --image "$DEV_IMAGE" \
  --scenario frontier-dir-eio --out "$GATE_OUT/frontier-dir-eio"
python3 tests/campaign/native_block_fault.py --image "$DEV_IMAGE" \
  --scenario record-dir-eio --out "$GATE_OUT/record-dir-eio"
python3 tests/campaign/native_block_fault.py --image "$DEV_IMAGE" \
  --scenario record-dir-sigkill --out "$GATE_OUT/record-dir-sigkill"
python3 tests/campaign/native_block_fault.py --image "$DEV_IMAGE" \
  --scenario record-cut-snapshot --out "$GATE_OUT/record-cut-snapshot"
```

The exact result and syscall traces are in
[`t16-private-publication-profile/`](t16-private-publication-profile/):

| Case | Host result | Reopened image | Result JSON SHA-256 |
| --- | --- | --- | --- |
| [private mapper probe](t16-private-publication-profile/probe.json) | `EIO` observed on file fsync | no native Store | probe in linked file |
| [record directory EIO](t16-private-publication-profile/record-dir-eio.json) | native exit 3, indeterminate; `link=0`, transactions `fsync=-1 EIO` | older prefix, exact prior transaction hash, recovery 1/1 | `e7fd5e69eec67d439c9e59596cfb0dbf1440dd7e7c1a151ac2ed02b4abd46d68` |
| [record SIGKILL](t16-private-publication-profile/record-dir-sigkill.json) | stopped tracee killed, exit -9 | exact candidate, prior hash unchanged, recovery 2/2 | `efabf144ba766c64a728005b5a92a2df8cd20e63c495b52d6b4e762d0ea1ffb2` |
| [cut backing snapshot](t16-private-publication-profile/record-cut-snapshot.json) | stopped tracee killed, exit -9; mapper suspended during private backing copy | older prefix on copied bytes, prior hash unchanged, recovery 1/1 | `65c6c5f29464362fcc15a325615977c6ba5da91efe588f546fc8c8713fa93713` |

All three native recoveries exited 0.  The [EIO trace](t16-private-publication-profile/record-dir-eio-strace.txt),
[SIGKILL trace](t16-private-publication-profile/record-dir-sigkill-strace.txt),
and [snapshot trace](t16-private-publication-profile/record-cut-snapshot-strace.txt)
have SHA-256 values recorded in their respective JSON and checked after copy.
The actual host was Linux
`6.11.0-29-generic`, mke2fs `1.47.1`, device-mapper library `1.02.196` and
driver `4.48.0`, with OpenSSL `3.5.8` loaded for the native image.  Each
private run restored the mapper, unmounted ext4, detached its owned loop, and
removed its `/tmp/fn-t16-block-*` backing.  Read-only final checks found no
`fn-t16` mapper, mount, or temporary directory.  The remote gate retains only
the copied result/trace evidence, not any mounted device.

The `frontier-dir-eio` case is **source-ready but unrun**: immutable 863 lacks
the new developer-only `frontier-attempted:stop` hook.  It requires a later
source-matched image; no second image was built for this packet.  A successful
old/new observation is one behavior of that filesystem and run.  No case
simulates a physical loss of power, proves a completed hardware barrier,
tests hbox ZFS, or discharges A-DURABILITY/A-WRITE-ISOLATION generally.
