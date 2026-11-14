# Storage fault qualification

The native device boundary now has deterministic controls for errors with physical
side effects. This is a boundary test, not a proof that a particular disk obeys
`fn2-a-fence-persists`, nor an application ACK/recovery theorem.

`tests/fixtures/device-faults/control.lisp` runs the actual `fn2-device-perform`
against replaced syscall leaves. Its independent byte oracle keeps visible and
persisted arrays separate. No production file, socket, or device is opened.

The scripted I/O-error cases belong to the broader fault domain, not the
crash-only assumption that excludes such corruption/failure behavior.
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
completion. This companion passed in authenticated A world
`a5212f4c2fca5a3c1a01ac5e5a5313c6470331fb`: all 155 host-boundary closure
books were installed from qualified toolchain
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`,
with no missing or newly certified books. The gate ran inside a 2 GiB scope and
exited zero. The local receipt is `build/storage-fault-evidence/receipt.json`.
This is an executed raw boundary control over that qualified prefix, not current
B certification or a new ACL2 theorem. Re-run it in the next composed native gate.

## Remaining connection

`sim/sim-adapter-base` now selects a no-space write prefix with the fault word,
executes that prefix, and reports `:no-space` with zero known progress. The
underlying byte primitive still refuses a directly injected no-space byte.
The byte primitive's failed fence remains unchanged; the adapter now selects
either no persistence (word 0) or captured-image persistence (word 1) before
reporting `:io`. It uses the same existing fence operation for both endpoints.
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

## Pending simulator gate

`tests/storage-effectful-error.lisp` is a source probe, not yet executed or
certified. It checks zero/two/four-byte physical prefixes against literal expected
visible bytes, unchanged durable bytes and a separate prior fenced byte. It then
checks both failed-fence endpoints and the exact visible/durable bytes after
crash reset. A selected suffix-persistence control is now added below; arbitrary torn byte strings remain open. A second
control runs the real commit stepper: two accepted batches, reused rows, effectful
ENOSPC on the next writes, uncertainty, no new replies and recovery of the prior
two batches. These are distinct controls, not an independent full ACK proof.

Next gate, after a named compute slot and matching qualified prefix: source-load
changed `sim/sim-adapter-base` and its dependents in `proof_repl`, then execute
`tests/storage-effectful-error.lisp`. Reject a zero-effect mutant for nonzero
prefixes and an error-as-success mutant. Only after that passes, certify the
affected simulator closure. Effectful write EIO and arbitrary torn failed-fence bytes still need controls.
The endpoint and suffix cases do not cover those broader fault families.

The staged replay is based on integration root `36ac58cfd`. The byte control now
uses `fn2-sim-native-stage` and `fn2-sim-native-post` for its actual issued fence.
Three additional cases retain a physically successful fence's real raw packet,
assert no new posted result and active state 4, then check persisted bytes after
crash reset. They exercise withheld adapter completion, not the commit timeout
path; the commit uncertainty control remains the ENOSPC scenario above. No
staged state field or OWN proof hint was replaced by the fault patch.

The physical cases are isolated in `tests/storage-effectful-physical.lisp`,
which includes only `sim/sim`: its 117-book closure avoids loading the executor
and recovery machinery for the first byte-effect gate. The combined
`tests/storage-effectful-error.lisp` includes those controls and the commit probe
(178 books). The first source overlay is only `sim/sim-adapter-base`, `sim/sim`
and the physical test; the combined gate additionally loads the three commit/
recovery consumers. Both require compatible cached dependencies and a named slot.

## Held completion through commit timeout (source candidate)

`sim/commit-proof-step` now accepts `:stage-fence` and `:post-fence` commands.
The `:auto-lost-fence` schedule stages the actual successful fence, retains the
saved raw return, and uses the existing `:timeout` command to post the clock,
run the mailbox and dispatch the commit machine. `:auto-staged-fence` posts the
same saved return as a control. No physical operation is repeated at post.

`fn2-see-held-commit` first accepts two batches, then starts a third. The lost
completion branch expects two reply records and uncertainty; the delivered
branch expects three reply records without uncertainty. Both explicitly expect
three recovered batches, since the third fence physically succeeded. These
assertions have not yet executed and are not current assurance evidence.

The TLS simulator patch `02400e95e` dispatches TlsStart before generic transfer.
Its OWN observation remains separate from the Write-only hidden-error branch
and Fence branch changed here. The patches are source-compatible; combined
execution awaits the frozen root gate and pending borrow repair.

## Partial failed-fence landing (source candidate)

`fn2-storage-fence-complete-from` factors the existing completion operation by
a starting byte. It reuses `fn2-storage-fence-bytes`, including its captured
versions and anti-rollback stamp check; no second landing loop is introduced.
The ordinary `fn2-storage-fence-complete` remains a start-zero wrapper. A nonzero
start always returns `:io`, including when that suffix is fully persisted.

The adapter preserves fault words 0 and 1 for no/all persistence. Larger words
select `(word - 1) mod (disk-bytes + 1)` as the suffix start. Three added controls
use word 3 (start 2) after zero/two/four hidden write bytes. With four bytes written,
the independent expected durable image is `(0 0 23 24)`; after crash reset the
visible image must equal it, and the earlier fenced byte remains 91. The existing
zero-start wrapper and prior accepted commit controls remain part of the gate.
This changes the storage dependency and therefore needs a newly computed source
overlay; it is not covered by the earlier frozen 803 physical inventory.

## Separate write-I/O fault family (source candidate)

The extraction commit moves only the `fn2-fault` data family into `sim/faults`,
using the existing enum/constant producers under `fn2-sim-faults`. It does not
invoke the action producer or add served action IDs. A copied-tree source control
shows a subsequent fault edit changes the simulator key but not `assembly-init`.
The initial removal from `books/operations` still requires one served ancestor
requalification and must be batched deliberately.

Write EIO is a new class 27; read EIO remains 6, ENOSPC remains 12 and the none
sentinel remains 26. The indexed domain has size 28. `fn2-sim-real-faultp`
explicitly excludes none from forcing, probabilistic selection, initialization
and effect counting. Thus an old numeric none does not become a write error.
Result range facts now bound the indexed domain by count, rather than incorrectly
using none as its upper limit. The full named-fault control skips the sentinel.

The new Write EIO path uses the same selected physical prefix as ENOSPC, then
returns `:io` with zero known progress. Tests cover zero/two/four-byte effects,
partial/full failed-fence persistence, held successful completion, and the actual
commit/recovery scenario after prior acceptance. A separate domain control forces
class 27 and checks exactly one effect count with none's probability/count zero.
All these ACL2 controls remain unexecuted source candidates.
