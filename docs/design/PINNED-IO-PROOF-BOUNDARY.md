# Pinned I/O proof boundary

Source review of retirement slice `c68d8b006` found a missing proof interface:
`fn2-block-read-children` now delegates to the disabled
`fn2-pinned-block-io-children`, but its existing queue/history/operation
semantic proofs could only open the outer function. This patch supplies the
owning helper's contracts, then composes read and write wrappers through them.
It changes no preexisting runtime DEFUN, guard, measure, or result ABI.

The new identity event producer derives slot/generation-on-success from the
existing `fn2-env-op-reserve-ok-facts`, first through the actual common issue
pipeline, then the read/write action wrappers. It uses actual admitted formals
and the existing ABI validator. This eliminates the pinned helper's impossible
successful-issue/mismatched-candidate branch without weakening its existing
queue equation. The helper's full eight-result ABI is asserted explicitly:
code/slot/generation, pool, ops, control, extents, edges. Ops remains result 4;
new mutable carriers are results 6 and 7.

Existing `fn2-issue-wrapper-effect-events` and `fn2-issued-wrapper-events`
emit the helper's queue/row/history contracts. Both outer read/write wrappers
consume that interface with the helper closed. Existing `fn2-oss-child`
emits the corresponding operation-semantic contract, then both outer faces'
contracts. Allocation and pin-drop internals stay opaque in local proof
contexts. No alternate runtime pipeline or hand-written effect formula is
introduced.

The source lifetime review found acquisition before descriptor publication,
generation-matched release on primary read/write completion after pool
settlement and before operation recycling, retention on stopped/partially
issued paths, and rollback only for ordinary prepublication refusal. A cancel
secondary cell alone cannot release the pin. The tuple changes in core faces
and operation-semantic consumers keep the actual ops output position. This
is source analysis, not certification or completed lifecycle evidence.

Validation so far: structural reader, diff check, secrets scan, and exact
byte comparison of all preexisting literal DEFUNs in the two changed books.
No ACL2 or certification ran. The next author probe must admit the identity
chain and helper contracts against the actual pinned implementation before
replaying outer wrappers; it must preserve refusal equations and never add a
shape/semantic premise to an existing public effect statement. Completion,
failure/cancel, stale generation, ordinary refusal, and retained stopped
issuance controls remain necessary for the integrated lifecycle claim.
