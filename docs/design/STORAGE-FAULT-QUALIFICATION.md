# Storage fault qualification

The native device boundary now has deterministic controls for errors with physical
side effects. This is a boundary test, not a proof that a particular disk obeys
`fn2-a-fence-persists`, nor an application ACK/recovery theorem.

`tests/fixtures/device-faults/control.lisp` runs the actual `fn2-device-perform`
against replaced syscall leaves. Its independent byte oracle keeps visible and
persisted arrays separate. No production file, socket, or device is opened.

The fixture establishes an earlier fully written and fenced range, then checks:

- EIO and ENOSPC with zero, partial, and complete unreported write effects;
- a short successful write retaining its exact known prefix;
- failed fence after partial persistence, followed by loss of volatile bytes;
- successful physical fence with terminal completion withheld;
- exact preservation of the prior fenced range and all unrelated bytes.

The actual performer must make one syscall and preserve the returned result and
errno. Retry, rollback-on-error and cleared-errno mutants each fail a named control.
The fixed fixture image size is a test instance, not a supported-profile ceiling.
The earlier fenced range is not described as a protocol-accepted article.

Run the raw boundary and mutation controls directly:

```
python3 tests/test_native_device_faults.py
```

The companion `tests/native-device-fault-boundary.lsp` loads certified
`books/host-boundary`, then exercises the actual `fn2-n-storage-completions`,
`fn2-device-io-observation`, `fn2-n-complete` and ACL2 `fn2-host-result` pipeline.
It requires error outcomes and zero known progress despite changed bytes; short
writes must be failed/uncertain with their known count. A physically completed but
withheld fence leaves the adapter waiting. Empty repeat polling cannot duplicate
completion. This companion still requires qualification in an authenticated
cached world; a successful raw SBCL fixture does not substitute for that gate.

## Remaining connection

`sim/sim-transfer` currently rejects the no-space byte operation before changing a
byte. `sim/storage`'s failed fence likewise preserves the entire durable image.
`books/crash-model` admits broader uncertainty, so the simulator's fault matrix
does not yet span these new native-boundary fixtures. Do not call an exercised
no-space/fence-error counter evidence that unreported physical effects were tested.

The next generalization is a selected physical-progress effect independent of the
reported result, carried through the simulator and its crash-image comparison.
Keep a zero-effect case, an effectful error, a failed barrier with persisted effects,
and a lost terminal result distinguishable. Then connect the actual commit machine's
uncertain state and recovery to these traces, including prior accepted article
bytes. This must preserve the separate broad/crash-only fault domains and must not
infer native power-loss behavior from a SIGKILL campaign or this deterministic model.
