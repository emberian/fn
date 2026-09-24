# T16 private publication fault profile, source-ready

This is an execution plan and source map, not a completed platform
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

After the shared source-matched `863c2141` developer image qualifies, run the
four cases one at a time on hbox with distinct new output directories:

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

For each actual run, retain `result.json`, `strace.txt`, driver/image/core
SHA-256, platform and filesystem versions, mapper table, exact exit code,
namespace hashes, recovered outcome, and cleanup result.  A successful
old/new observation is one behavior of that filesystem and run.  No case
simulates a physical loss of power, proves a completed hardware barrier,
tests hbox ZFS, or discharges A-DURABILITY/A-WRITE-ISOLATION generally.
