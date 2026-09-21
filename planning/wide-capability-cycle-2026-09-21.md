# Wide capability cycle — 2026-09-21

The user explicitly reaffirmed full v0/v1 scope and requested larger parallel
implementation steps. Remaining usage does not reduce that scope. The unit of
delegation in this cycle is a complete operational capability, rather than a
small book or adapter followed by another handoff.

## Parallel ownership

| Lane | Current capability and next work |
| --- | --- |
| `bp_recovery_join` / Sol | Shared writer/replay and raw refusal/fault witness integrated; next prove the maintained journal-sequence relation for actual Store transitions under PRF-050. |
| `hybrid_signatures` / Sol | Mandatory Ed25519 plus ML-DSA-65 primitives and signing CLI are integrated; live-owner authored submission is integrated; qualify real primitive admission/restart and missing-enrollment recovery against the frozen image. |
| `bounded_event_profiles` / Sol | Large canonical events and linear bounded streaming codecs are integrated; finish real closure certification and persisted profile/publication composition. |
| `peer_tls_vertical` / Sol | Actual identity/recovery trace integrated; next prove general durable peer-row round trips for legacy and TLS/AUTHINFO records. Real two-peer runtime remains with the gate lane. |
| `compaction_vertical` / Sol | Compaction and injectivity packets integrated; shared-owner cost measurement archived with provenance limits. Persistent trie foundation is integrated; continue maintained owner and pinned-reader propagation with actual-caller correspondence and measurement. |
| `crash_correspondence` / Sol | Reclaim cut/model packet integrated; total-accessor/guard and actual-plan witnesses are integrated; prove general uncovered-suffix byte preservation across arbitrary reclaim prefixes. Source-matched process-death execution and broader physical relation remain. |
| `served_fast_path` / Sol | Fast framing transition integrated with focused certification; close actual outer-owner correspondence on current combined dependencies after the gate's prerequisite closure. |
| `recovery_pillars` / Sol | Portable hybrid authorship carrier and exact-source projection for NNTP and BP; reuse bounded codec mechanisms while keeping signature subjects and receiver authority distinct. |
| `service_join` / Sol | Native distribution and principal operator route integrated; finish prerequisite closure then qualify frozen `773e9ae3` for immutable production/developer/DTN images on persvati. |
| `toolchain_recovery` / Sol | Scoped frozen repair evidence archived; immutable `915d5c72` bidirectional/requeue evidence is archived; implement and run protected two-host exchange and negative authentication/CA cases on hbox and persvati. |
| `process_containment` / Sol | Run native v0 matrix accounting with structured runtime witnesses and actual process artifact identities; archive failed and corrected attempts without publishing a misleading current release result. |
| `preservation_vertical` / Sol | Repeated unlink and exact-byte cut campaign is integrated; execute it against the frozen developer image. |
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
