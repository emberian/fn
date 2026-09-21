# Wide capability cycle — 2026-09-21

The user explicitly reaffirmed full v0/v1 scope and requested larger parallel
implementation steps. Remaining usage does not reduce that scope. The unit of
delegation in this cycle is a complete operational capability, rather than a
small book or adapter followed by another handoff.

## Parallel ownership

| Lane | Complete capability and immediate work |
| --- | --- |
| `service_join` / Sol | Native news and peering: compose HST/admin/TLS with public startup, activate ingress/feed, implement supported non-loopback configuration in ACL2, resolve transit authentication and exercise two-way exchange/requeue/restart. |
| `bp_recovery_join` / Sol | BP/DTN: recovered lifecycle/fast/authored-wire packets, interrupted contacts and exhaustion, then durable responsibility/release tied to canonical Store pins rather than a workflow-only copy. |
| `preservation_vertical` / Sol | Preservation/reclamation: executable protected-closure decisions and durable publication/recovery, starting with obsolete checkpoint generations; progress toward full compaction without discarding retained articles, obligations or duplicate history. |
| `identity_vertical` / Sol | Durable keyring/authority, acceptance-recorded statement verdicts and native retrieval; exact authored bytes and separate relay projections. Concrete D09/D11 choices remain explicit questions, not inferred approvals. |
| `crash_correspondence` / Sol | Actual native publication/recovery trace relation, missing K0 and prerequisite-ready crash obligations, and fault campaigns whose cuts correspond to model transitions. |
| `config_recovery` / Terra | Complete bounded configuration-namespace observation and canonical record/generation binding, integrate corrected dependencies and source-matched recovery witnesses. |
| `process_containment` / Terra | Contain development commands and test descendants across timeout/cancellation; finite directory traversal; exercise leader-death and resistant-child cases. |
| `toolchain_recovery` / Sol | Finish bounded launcher/core/runtime qualification and coherent certificate reuse without treating runner-source changes as changed prover identity. |
| Root / Astra | Shared contracts, TLS integration, coherent batch review/merges, exact evidence scopes, frozen combined images and native feature matrix. |

## Working contract

1. Send a short interface/state/format contract when work crosses a lane boundary.
   This is coordination, not an approval gate. Continue independent work while
   the shared choice is resolved. Do not invent competing owners or codecs.
2. Implement model, native caller, focused tests and proof obligations within the
   same capability lane. Passing components may be committed and integrated
   before the entire capability is qualified; their claims remain scoped.
3. Run focused roots and scenarios during implementation. Reserve expensive
   combined certification/image builds and release matrices for frozen batches.
   Reuse recovered exact-source results; do not duplicate a closure merely
   because another lane started the same dependency.
4. Root reviews coherent deltas once, repairs concrete defects, and keeps other
   lanes moving. Review does not mean every component waits for every sibling.
5. A vertical continues beyond its first useful tranche. A checkpoint cleanup
   operation is progress toward preservation, not completion of compaction and
   history pruning. A two-node transfer is progress toward v0, not its definition.

## Shared contracts already identified

- Retention has one canonical Store ledger. Releasing a workflow shadow pin
  cannot establish that Store capacity is free. New retention-only mutations
  need a durable Store transition and coordinated replay.
- Reclamation must preserve recovery's namespace predicate. A collector cannot
  create holes while its next recovery insists on contiguous generations.
  Transaction and checkpoint namespace rules are separate contracts.
- Acceptance-recorded verdicts retain their original policy/key generation.
  Key rotation may change a separate current-trust view; it must not rewrite
  what acceptance recorded or cause per-query signature/history replay.
- Shared state/record format changes are versioned and coordinated with recovery,
  the owner and reader. No opaque host field bypasses the logical representation.
- TLS authenticates the transport boundary only after a successful handshake;
  it does not choose author signatures, portable authority or peer honesty.
- Test containment tracks the process group after its shell leader exits.
  Cleanup and transcript collection must both be bounded. SIGKILL of the
  supervisor and deliberately escaped sessions remain explicit limitations.

The governing requirements, proof targets and release criteria remain in their
existing registries. This execution plan changes how the work is divided and
integrated, not the acceptance or assurance contracts.
