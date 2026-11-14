# Checkpoint allocation journal — source milestone

The actual B allocation producer is `fn2-checkpoint-allocation-begin`, `-step`,
`-submit`; `fn2-retirement-poll` consumes its exact settlement. An empty final scan
uses `fn2-checkpoint-allocation-finish-empty`. No caller chooses the batch or record
cut: each step scans one physical extent, up to the existing commit planner's
`*fn2-checkpoint-allocation-records-per-ticket*` records per owned workspace.
Unfinished owned reservations hold the scan before a partially filled ticket is
submitted. Completed rows retain exact extent/epoch/counter identities in shared
lifecycle control rows 1 through that derived capacity. The exact freeze token
is captured at begin and checked at scanning, submit, install and settlement.
Normal accepted settlement retains the next physical scan cursor for the same
token; begin resets it on a new token or after retirement, and refused settlement
resets it so still-reserved constructions are revisited. Row zero serializes
retirement and checkpoint allocation and retains owner/workspace/batch/event.

`fn2-commit-lifecycle-step` retains the actual publish-phase deps/log/fence and
installed-root prerequisites. Its allocation branch checks the private control's
containing workspace, batch, event and owner before decoding; then compares each
record with its staged identity and monotonic install offset before using the
existing allocation installer. Accepted settlement requires the entire staged
member installed; refused settlement after any install becomes uncertain. Pool
ownership remains retained on uncertainty. General transaction admission still
excludes allocation and retirement records.

Validation here is source only: balanced forms and `git diff --check` pass.
`tests/checkpoint-allocation-coordinator-unit.lisp` prepares actual-entry controls
for scanning, incomplete-source backpressure, ownership, serialization and
unpersisted installation rejection, plus stale-token packing/submission/install
rejection controls. These fixtures have not been executed.
No ACL2 admission, guard verification, certification, simulator, native or remote
computation was run. The new function declarations request guard verification;
that request is not evidence of admission.

Remaining integration boundaries: descriptor/master completion must authorize
phase2; a checkpoint worker must drive begin/step/submit/poll and handle the empty
scan; execute these controls and add full-capacity/multiple-ticket, actual persisted
writer, refusal/uncertainty and stale control mutation fixtures; admit and certify
the changed closure and discharge preservation/critical evidence obligations.
Recovery ordering and final publication/FREE remain the parent lane's scope.
This change does not enable phase2, publication or FREE.
