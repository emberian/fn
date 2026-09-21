# Wide capability cycle — 2026-09-21

The user explicitly reaffirmed full v0/v1 scope and requested larger parallel
implementation steps. Remaining usage does not reduce that scope. The unit of
delegation in this cycle is a complete operational capability, rather than a
small book or adapter followed by another handoff.

## Parallel ownership

| Lane | Current capability and next work |
| --- | --- |
| `bp_recovery_join` / Sol | Shared Store identity writer/replay, exact enrolled snapshot binding, profile admission before reservation/publication, and refusal/recovery composition. |
| `hybrid_signatures` / Sol | Mandatory Ed25519 plus ML-DSA-65 primitives and signing CLI are integrated; complete native live-owner authored submission and durable acceptance/restart. |
| `bounded_event_profiles` / Sol | Large canonical events and linear bounded streaming codecs are integrated; finish real closure certification and persisted profile/publication composition. |
| `peer_tls_vertical` / Sol | Outbound AUTHINFO, private profile descriptor handling and command framing are integrated; composed phase proofs and real two-peer runtime remain. |
| `compaction_vertical` / Sol | Partial-deletion compaction packet is integrated; next independent assignment is full hybrid subject/preimage injectivity in a separate proof book. |
| `crash_correspondence` / Sol | Reclaim cut/model packet is integrated; source-matched process-death execution and broader physical relation remain. |
| `served_fast_path` / Sol | Fixed-shape framing execution and called-path correspondence; resolve fresh node-config preservation prerequisites without changing semantics to fit proofs. |
| `service_join` / Sol | Native distribution: relocate actual saved image, runtime and support dependencies; qualify task-local installation and service lifecycle. |
| `toolchain_recovery` / Sol | Scoped frozen repair evidence archived; repair old snapshot's missing public peer dispatch and exercise real two-node native exchange/requeue/restart. |
| Root / Astra | Shared contracts, concrete batch review/merges, assurance scopes, next coherent image and qualification matrix. |

Luna completed a bounded landed-worktree inventory; root removed only clean,
fully ancestral historical worktrees and retained their branches. Earlier
configuration and containment packets remain integrated; they are not idle
implementation assignments in the current cycle.

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
- The accepted article and its recorded verdict need one atomic durable
  binding. An article commit followed by an independent verdict append leaves
  a crash gap. Standalone evidence records do not close that gap; the native
  acceptance representation or its preparation protocol must preserve the
  exact binding without recomputing historical trust during recovery.
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
