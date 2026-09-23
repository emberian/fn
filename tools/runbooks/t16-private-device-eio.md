# Disposable native transaction-directory EIO campaign

This opt-in hbox campaign creates an ext4 filesystem on a new tmpfs-backed
loop device and a unique device-mapper mapping. It injects `error_writes`
only into that mapping after the native post's final transaction link and
before its directory `fsync`. It tests error handling, not power loss or the
production ZFS filesystem. The outcome and limits are recorded in
[the 2026-09-23 observation](../../planning/evidence/t16-private-eio-2026-09-23.md).

Use a disposable host where `/tmp` is a separate tmpfs, `sudo -n` can run
`losetup`, `dmsetup`, `mkfs.ext4`, `mount`, `umount` and `chown`, and `strace`
is installed. Check `sudo -n dmsetup targets` and `sudo -n losetup -f`
read-only first. Build a source-matched **developer** native image. Run the
private mapping probe, then the native campaign with fresh output paths:

```sh
python3 tests/campaign/native_block_fault.py --probe --out build/t16-probe
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
python3 tests/campaign/native_block_fault.py \
  --image "$PWD/build/fn-host-developer" --out build/t16-eio
```

The driver refuses `/tmp` unless it is tmpfs. Before formatting, switching,
unmounting, removing or detaching, it checks its exact owned backing path,
loop dependency and mapping/mount identities. A changed identity leaves the
resource in place and reports a cleanup error; inspect it manually instead
of using a broad `dmsetup`, `losetup` or mount cleanup command. The normal
path removes only these owned resources. Preserve `result.json` and
`strace.txt` with their SHA-256 hashes and record the launcher/core/source
hashes, exit codes, observed link and `fsync` returns, recovered bytes, and
any cleanup error.
